module
/-
# Obend.Elab.DeriveRepair — the polynomial signature of an inductive type, derived

`Obend.Repair.AlgConfig` repairs along a pair of initial algebras of one polynomial `(A, B)`; there
the polynomial of `UnaryNat` and both initial algebras are written by hand. Here they are read off
the declaration.

`#derive_poly_alg T`, for an inductive `T : Type` with no parameters, indices, mutual or nested
occurrences, whose constructor fields are either `T` itself or a closed type in `Type`, declares

* `T.PolyShape`: one constructor per constructor of `T`, carrying its non-recursive fields (the tag
  and the payload);
* `T.PolyArity : T.PolyShape → Type`: `Fin n` at a constructor with `n` recursive fields;
* `T.polyAlg : PAlg T.PolyShape T.PolyArity T`, the constructors packed as one algebra, and
  `T.polyUnpack`, its inverse (`T.polyPack_unpack`, `T.polyUnpack_pack`);
* `T.polyFold` with `T.polyFold_beta` and `T.polyFold_eta`, and `T.polyInit : InitPAlg …`.

`#derive_alg_config cfg : C ≃ D` checks that `D` has `C`'s signature constructor by constructor
(the same payload types in order, the same number of recursive fields; names and the position of
the recursive fields are free), derives `D`'s initial algebra over `C`'s shape (`cfg.dAlg`,
`cfg.dFold`, `cfg.dInit`, …) and declares `cfg : AlgConfig C.PolyShape C.PolyArity C D`. Every
theorem of `AlgConfig` then applies: `cfg.forward`, `cfg.repair_by_instantiation`,
`cfg.elim_repair_ok`.

`#check_scar_free_bridge cfg` walks the declarations: `D`'s side of `cfg` does not mention `C`,
and `C`'s side does not mention `D`. The shape is shared; neither type is defined through the other.
-/
public meta import Lean
public import Obend.Repair.AlgConfig
public section
namespace Obend.Repair
set_option autoImplicit false

universe u

/-! ## Children as tuples -/

/-- No children. -/
@[expose] def finNil {X : Type u} : Fin 0 → X := fun j => j.elim0

/-- A first child and the rest. -/
@[expose] def finCons {X : Type u} {n : Nat} (x : X) (k : Fin n → X) : Fin (n + 1) → X
  | ⟨0, _⟩ => x
  | ⟨i + 1, h⟩ => k ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem finNil_ext {X : Type u} (g : Fin 0 → X) : finNil = g := funext fun j => j.elim0

/-- A tuple is `finCons` of its first component and the rest. -/
theorem finCons_ext {X : Type u} {n : Nat} {x : X} {k : Fin n → X} {g : Fin (n + 1) → X}
    (h₀ : x = g ⟨0, Nat.succ_pos n⟩) (hs : k = fun j : Fin n => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :
    finCons x k = g := by
  subst h₀ hs
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- A nonempty child tuple round-trips through the constructor decomposition. -/
theorem finCons_inhabited : ∃ g : Fin 2 → Nat,
    finCons 7 (finCons 11 finNil) = g ∧ g ⟨0, by decide⟩ = 7 ∧ g ⟨1, by decide⟩ = 11 :=
  ⟨finCons 7 (finCons 11 finNil), rfl, rfl, rfl⟩

/-! ## The derivation -/

section Derive
open Lean Meta Elab Command

/-- The signature of `T`: for each constructor, which fields are recursive (in order) and the types
of the others. Refuses what a polynomial `(A, B)` with `B a = Fin n` does not describe. -/
meta def polySignature (T : Name) : MetaM (Array (Name × Array Bool × Array Expr)) := do
  let iv ← getConstInfoInduct T
  unless iv.all.length == 1 do
    throwError "#derive_poly_alg: {T} is declared in a mutual block"
  unless iv.numParams == 0 && iv.numIndices == 0 do
    throwError "#derive_poly_alg: {T} has parameters or indices"
  if iv.isNested then
    throwError "#derive_poly_alg: {T} is a nested inductive"
  unless iv.type == mkSort Level.one do
    throwError "#derive_poly_alg: {T} is not in `Type`"
  if iv.ctors.isEmpty then
    throwError "#derive_poly_alg: {T} has no constructors"
  let self := mkConst T
  iv.ctors.toArray.mapM fun c => do
    let cv ← getConstInfoCtor c
    let mut ty := cv.type
    let mut flags : Array Bool := #[]
    let mut payload : Array Expr := #[]
    repeat
      match ty with
      | .forallE x d b _ =>
        if d.hasLooseBVars then
          throwError "#derive_poly_alg: field {x} of {c} depends on an earlier field"
        if d == self then
          flags := flags.push true
        else
          if d.getUsedConstantsAsSet.contains T then
            throwError "#derive_poly_alg: field {x} of {c} mentions {T} under another type"
          unless (← whnf (← inferType d)) == mkSort Level.one do
            throwError "#derive_poly_alg: field {x} of {c} is not in `Type`"
          flags := flags.push false
          payload := payload.push d
        ty := b
      | _ => break
    return (c, flags, payload)

/-- The last component of a constructor's name. -/
meta def shortName (c : Name) : Name :=
  match c with
  | .str _ s => Name.mkSimple s
  | _ => c

/-- Declare the initial algebra of `carrier` over the shape `shape`/`arity`, whose constructor `i` is
`shapeCtors[i]`: packager, unpacker, fold, the two fold laws, the two inverse laws, the `InitPAlg`. -/
meta def deriveInitOver (carrier : Name) (sig : Array (Name × Array Bool × Array Expr))
    (shape arity : Name) (shapeCtors : Array Name)
    (algN unpackN foldN betaN etaN packUnpackN unpackPackN initN : Name) : CommandElabM Unit := do
  let T := mkCIdent carrier
  let Shape := mkCIdent shape
  let Arity := mkCIdent arity
  let γ := mkIdent `γ
  let k := mkIdent `k
  let h := mkIdent `h
  let hc := mkIdent `hc
  let decl (n : Name) : Ident := mkIdent (`_root_ ++ n)
  let algId := mkIdent algN
  let unpackId := mkIdent unpackN
  let foldId := mkIdent foldN
  let etaId := mkIdent etaN
  let mut algAlts := #[]
  let mut unpackAlts := #[]
  let mut foldAlts := #[]
  let mut betaAlts := #[]
  let mut etaAlts := #[]
  let mut packUnpackAlts := #[]
  let mut unpackPackAlts := #[]
  for i in [0:sig.size] do
    let (c, flags, _) := sig[i]!
    let C := mkCIdent c
    let sc := mkCIdent shapeCtors[i]!
    let n := (flags.filter id).size
    let mut fieldIds : Array Term := #[]
    let mut payloadIds : Array Term := #[]
    let mut recIds : Array Term := #[]
    let mut algArgs : Array Term := #[]
    let mut wild : Array Term := #[]
    for j in [0:flags.size] do
      wild := wild.push (← `(_))
      if flags[j]! then
        let r : Term := mkIdent (Name.mkSimple s!"r{j}")
        algArgs := algArgs.push
          (← `(($k (Fin.mk $(quote recIds.size) (by decide) : Fin $(quote n)))))
        fieldIds := fieldIds.push r
        recIds := recIds.push r
      else
        let p : Term := mkIdent (Name.mkSimple s!"p{j}")
        algArgs := algArgs.push p
        fieldIds := fieldIds.push p
        payloadIds := payloadIds.push p
    let shapePat : Term := Syntax.mkApp sc payloadIds
    let ctorPat : Term := Syntax.mkApp C fieldIds
    let children (f : Term → CommandElabM Term) : CommandElabM Term := do
      let mut acc ← `(Obend.Repair.finNil)
      for r in recIds.reverse do
        acc ← `(Obend.Repair.finCons $(← f r) $acc)
      return acc
    -- `finCons x₀ (finCons x₁ … finNil) = g`, from a proof of each `xᵢ = g i`
    let chain (g : Term) (proofs : Array Term) : CommandElabM Term := do
      if proofs.isEmpty then
        `(Obend.Repair.finNil_ext $g)
      else
        let mut acc ← `(Obend.Repair.finNil_ext _)
        for j in [1:proofs.size] do
          acc ← `(Obend.Repair.finCons_ext $(proofs[proofs.size - j]!) $acc)
        `(Obend.Repair.finCons_ext (g := $g) $(proofs[0]!) $acc)
    let kPat : Term ← if n == 0 then `(_) else pure k
    algAlts := algAlts.push (← `(Lean.Parser.Term.matchAltExpr| | ⟨$shapePat, $kPat⟩ => $(Syntax.mkApp C algArgs)))
    let kids ← children pure
    unpackAlts := unpackAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorPat => ⟨$shapePat, $kids⟩))
    let foldKids ← children fun r => `($foldId $γ $r)
    foldAlts := foldAlts.push
      (← `(Lean.Parser.Term.matchAltExpr| | $ctorPat => Obend.Repair.PAlg.op $γ ⟨$shapePat, $foldKids⟩))
    let rfls ← recIds.mapM fun _ => `(rfl)
    let betaChain ← chain (← `(fun b => $foldId $γ ($k b))) rfls
    betaAlts := betaAlts.push (← `(Lean.Parser.Term.matchAltExpr|
      | ⟨$shapePat, $k⟩ =>
        congrArg (fun (c : $Arity $shapePat → _) => Obend.Repair.PAlg.op $γ ⟨$shapePat, c⟩) $betaChain))
    let ihs ← recIds.mapM fun r => `(Eq.symm ($etaId $γ $h $hc $r))
    let etaChain ← chain (← `(fun b => $h ($kids b))) ihs
    etaAlts := etaAlts.push (← `(Lean.Parser.Term.matchAltExpr|
      | $ctorPat =>
        Eq.trans ($hc ⟨$shapePat, $kids⟩)
          (congrArg (fun (c : $Arity $shapePat → _) => Obend.Repair.PAlg.op $γ ⟨$shapePat, c⟩)
            (Eq.symm $etaChain))))
    packUnpackAlts := packUnpackAlts.push
      (← `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkApp C wild) => rfl))
    let kChain ← chain k rfls
    unpackPackAlts := unpackPackAlts.push (← `(Lean.Parser.Term.matchAltExpr|
      | ⟨$shapePat, $k⟩ =>
        congrArg (fun (c : $Arity $shapePat → $T) => (⟨$shapePat, c⟩ : Obend.Repair.PolyF $Shape $Arity $T))
          $kChain))
  elabCommand (← `(@[expose] def $(decl algN):ident : Obend.Repair.PAlg $Shape $Arity $T :=
    ⟨fun t => match t with $algAlts:matchAlt*⟩))
  elabCommand (← `(@[expose] def $(decl unpackN):ident : $T → Obend.Repair.PolyF $Shape $Arity $T :=
    fun x => match x with $unpackAlts:matchAlt*))
  elabCommand (← `(@[expose] def $(decl foldN):ident {Y : Type} ($γ : Obend.Repair.PAlg $Shape $Arity Y) :
      $T → Y :=
    fun x => match x with $foldAlts:matchAlt*))
  elabCommand (← `(theorem $(decl betaN):ident {Y : Type} ($γ : Obend.Repair.PAlg $Shape $Arity Y)
      (t : Obend.Repair.PolyF $Shape $Arity $T) :
      $foldId $γ (Obend.Repair.PAlg.op $algId t) =
        Obend.Repair.PAlg.op $γ (Obend.Repair.PolyF.map ($foldId $γ) t) :=
    match t with $betaAlts:matchAlt*))
  elabCommand (← `(theorem $(decl etaN):ident {Y : Type} ($γ : Obend.Repair.PAlg $Shape $Arity Y)
      ($h : $T → Y)
      ($hc : ∀ t : Obend.Repair.PolyF $Shape $Arity $T,
        $h (Obend.Repair.PAlg.op $algId t) = Obend.Repair.PAlg.op $γ (Obend.Repair.PolyF.map $h t)) :
      ∀ x : $T, $h x = $foldId $γ x :=
    fun x => match x with $etaAlts:matchAlt*))
  elabCommand (← `(theorem $(decl packUnpackN):ident :
      ∀ x : $T, Obend.Repair.PAlg.op $algId ($unpackId x) = x :=
    fun x => match x with $packUnpackAlts:matchAlt*))
  elabCommand (← `(theorem $(decl unpackPackN):ident :
      ∀ t : Obend.Repair.PolyF $Shape $Arity $T, $unpackId (Obend.Repair.PAlg.op $algId t) = t :=
    fun t => match t with $unpackPackAlts:matchAlt*))
  elabCommand (← `(@[expose] def $(decl initN):ident : Obend.Repair.InitPAlg $Shape $Arity $T :=
    { alg := $algId, fold := $foldId, fold_beta := $(mkIdent betaN), fold_eta := $etaId }))

/-- `#derive_poly_alg T`, as a function: the shape, the arity and the initial algebra of `T`. -/
meta def derivePolyAlg (T : Name) : CommandElabM Unit := do
  let sig ← liftTermElabM <| polySignature T
  let shape := T ++ `PolyShape
  let arity := T ++ `PolyArity
  let Shape := mkIdent shape
  let ctors ← sig.mapM fun (c, _, payload) => do
    let mut ty : Term := Shape
    for d in payload.reverse do
      let a ← liftTermElabM <| PrettyPrinter.delab d
      ty ← `($a → $ty)
    `(Lean.Parser.Command.ctor| | $(mkIdent (shortName c)):ident : $ty)
  elabCommand (← `(inductive $(mkIdent (`_root_ ++ shape)):ident : Type where $ctors:ctor*))
  let arityAlts ← sig.mapM fun (c, flags, payload) => do
    let wild ← payload.mapM fun _ => `(_)
    let pat : Term := Syntax.mkApp (mkCIdent (shape ++ shortName c)) wild
    `(Lean.Parser.Term.matchAltExpr| | $pat => Fin $(quote (flags.filter id).size))
  elabCommand (← `(@[expose, reducible] def $(mkIdent (`_root_ ++ arity)):ident : $Shape → Type :=
    fun s => match s with $arityAlts:matchAlt*))
  deriveInitOver T sig shape arity (sig.map fun (c, _, _) => shape ++ shortName c)
    (T ++ `polyAlg) (T ++ `polyUnpack) (T ++ `polyFold) (T ++ `polyFold_beta) (T ++ `polyFold_eta)
    (T ++ `polyPack_unpack) (T ++ `polyUnpack_pack) (T ++ `polyInit)

/-- `#derive_poly_alg T` declares the polynomial signature of the inductive type `T`
(`T.PolyShape`, `T.PolyArity`) and its initial algebra (`T.polyAlg`, `T.polyUnpack`, `T.polyFold`,
`T.polyFold_beta`, `T.polyFold_eta`, `T.polyInit`). -/
elab "#derive_poly_alg " T:ident : command => do
  derivePolyAlg (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo T)

/-- `#derive_alg_config cfg : C ≃ D` checks that `D` has the signature of `C` and declares
`cfg : AlgConfig C.PolyShape C.PolyArity C D`, deriving `C`'s signature first if it has none. -/
elab "#derive_alg_config " cfg:ident " : " C:ident " ≃ " D:ident : command => do
  let C ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo C
  let D ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo D
  unless (← getEnv).contains (C ++ `polyInit) do
    derivePolyAlg C
  let sigC ← liftTermElabM <| polySignature C
  let sigD ← liftTermElabM <| polySignature D
  unless sigC.size == sigD.size do
    throwError "#derive_alg_config: {C} has {sigC.size} constructors and {D} has {sigD.size}"
  for i in [0:sigC.size] do
    let (c, flagsC, payloadC) := sigC[i]!
    let (d, flagsD, payloadD) := sigD[i]!
    unless (flagsC.filter id).size == (flagsD.filter id).size do
      throwError "#derive_alg_config: {c} has {(flagsC.filter id).size} recursive fields and {d} has {(flagsD.filter id).size}"
    unless payloadC.size == payloadD.size do
      throwError "#derive_alg_config: {c} has {payloadC.size} payload fields and {d} has {payloadD.size}"
    for j in [0:payloadC.size] do
      unless ← liftTermElabM <| isDefEq payloadC[j]! payloadD[j]! do
        throwError "#derive_alg_config: payload field {j} of {c} is {payloadC[j]!} and of {d} is {payloadD[j]!}"
  let name := (← getCurrNamespace) ++ cfg.getId
  let shape := C ++ `PolyShape
  let arity := C ++ `PolyArity
  deriveInitOver D sigD shape arity (sigC.map fun (c, _, _) => shape ++ shortName c)
    (name ++ `dAlg) (name ++ `dUnpack) (name ++ `dFold) (name ++ `dFold_beta) (name ++ `dFold_eta)
    (name ++ `dPack_unpack) (name ++ `dUnpack_pack) (name ++ `dInit)
  elabCommand (← `(@[expose] def $(mkIdent (`_root_ ++ name)):ident :
      Obend.Repair.AlgConfig $(mkCIdent shape) $(mkCIdent arity) $(mkCIdent C) $(mkCIdent D) :=
    ($(mkCIdent (C ++ `polyInit)), $(mkIdent (name ++ `dInit)))))

/-- Whether `root` reaches `scar` through the types and bodies of the declarations it uses. A
declaration of a module imported before `scar`'s cannot mention it and is not entered. -/
meta def reachesConst (env : Environment) (root scar : Name) : Bool := Id.run do
  let scarIdx := env.getModuleIdxFor? scar
  let mut seen : NameSet := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let n :: rest := todo | unreachable!
    todo := rest
    if seen.contains n then continue
    seen := seen.insert n
    if n == scar then return true
    let before : Bool := match env.getModuleIdxFor? n, scarIdx with
      | some ni, some si => ni.toNat < si.toNat
      | some _, none => true
      | _, _ => false
    if before then continue
    let some info := env.find? n | continue
    let mut used := info.type.getUsedConstantsAsSet
    if let some v := info.value? (allowOpaque := true) then
      used := used ++ v.getUsedConstantsAsSet
    if let .inductInfo iv := info then
      used := used ++ .ofList iv.ctors
    todo := used.toList ++ todo
  return false

/-- `#check_scar_free_bridge cfg`, for `cfg : AlgConfig A B C D` made by `#derive_alg_config`: `D`'s
initial algebra `cfg.dInit` does not reach `C`, and `C.polyInit` does not reach `D`. -/
elab "#check_scar_free_bridge " cfg:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo cfg
  let env := (← getEnv).setExporting false
  let some info := env.find? name | throwError "#check_scar_free_bridge: unknown constant {name}"
  let args := info.type.getAppArgs
  unless info.type.isAppOf ``Obend.Repair.AlgConfig && args.size == 4 do
    throwError "#check_scar_free_bridge: {name} is not an `AlgConfig`"
  let (.const C _, .const D _) := (args[2]!, args[3]!)
    | throwError "#check_scar_free_bridge: the carriers of {name} are not constants"
  unless env.contains (name ++ `dInit) && env.contains (C ++ `polyInit) do
    throwError "#check_scar_free_bridge: {name} was not made by `#derive_alg_config`"
  if reachesConst env (name ++ `dInit) C then
    throwError "#check_scar_free_bridge: {name ++ `dInit} depends on {C}"
  if reachesConst env (C ++ `polyInit) D then
    throwError "#check_scar_free_bridge: {C ++ `polyInit} depends on {D}"
  logInfo m!"scar-free bridge {name} : {C} ≃ {D} over {C ++ `PolyShape}: {name ++ `dInit} does not mention {C}, {C ++ `polyInit} does not mention {D}"

end Derive

end Obend.Repair
end
