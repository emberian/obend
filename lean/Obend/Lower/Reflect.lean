module
/-
# Obend.Lower.Reflect — prototype lowering bridge connecting Leaf.Flatten to Lower.Transport

Provides:
- `LayoutEnv`: Layout environment mapping member names and record positions.
- `lowerTerm` & `lowerLeafDef`: Lowers acyclic first-order method definitions into `LExpr`.
- `ReflectedObject`: Reflected object bundling lowered definitions with `specSlot` pin witnesses.
- `reflectComposition`: Compiles flattened prototype compositions into reflected objects.
- `reflect_override_blocks`: Proves that modifying any ancestor layer immediately transitions `specSlot` to `.blocked`.
-/
public import Obend.Logic.Obligation
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Slot.World
public import Obend.Lower.Syntax
public import Obend.Lower.Lower
public import Obend.Lower.Transport
public import Obend.Tactic.Tooth

@[expose] public section
namespace Obend.Lower.Reflect

open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty)
open Obend.Logic (Composition)
open Obend.Leaf (LeafDef LeafPin LeafView specSlot Candidate moved_pin_blocks)
open Obend.Slot.World (holdsAt)
open Obend.Lower (LExpr lowerT)

set_option autoImplicit false

/-- Layout Environment mapping record field names and method slots to de Bruijn indices. -/
structure LayoutEnv where
  fields : List (String × Nat)
  selfIndex : Nat
  arity : Nat
  deriving DecidableEq, Repr

/-- The UTF-8 bytes of a string: the `String.toByteArray` projection, read as a list. Not
`String.toUTF8`, whose body `Init` does not expose: inside a `module` the kernel cannot unfold it,
so the earlier `toUTF8` walk left `labelToNat` and `strEq` stuck, and every `#import_obend`
`<def>_lowerTerm_eq` whose term carries a label failed its kernel `Eq.refl` (2026-11-05). Not
`String.toList` either, which depends on `Classical.choice`. -/
def utf8Bytes (s : String) : List UInt8 :=
  s.toByteArray.data.toList

/-- Byte-level equality on `String` (kernel-reducible and choice-free, see `utf8Bytes`). -/
def strEq (a b : String) : Bool :=
  utf8Bytes a == utf8Bytes b

/-- Structural lookup by `strEq`. -/
def lookupByStr {α : Type} (k : String) : List (String × α) → Option α
  | [] => none
  | (m, v) :: rest => if strEq k m then some v else lookupByStr k rest

/-- Deterministic numeric encoding of surface labels for `.label`, `.inject`, and `.case`: the
UTF-8 bytes in order, `acc * 257 + byte + 1` (the same number the earlier `ByteArray` walk gave). -/
def labelToNat (s : String) : Nat :=
  (utf8Bytes s).foldl (fun acc b => acc * 257 + b.toNat + 1) 0

/-- Structural insertion helper for `canonicalizeFields` (avoids `Array.qsort` / `Classical.choice`). -/
def insertFieldByLayout (env : LayoutEnv) (x : String × LExpr) : List (String × LExpr) → List (String × LExpr)
  | [] => [x]
  | y :: ys =>
    if Nat.ble ((lookupByStr x.1 env.fields).getD 1000000) ((lookupByStr y.1 env.fields).getD 1000000) then
      x :: y :: ys
    else
      y :: insertFieldByLayout env x ys

/-- Canonicalize record field ordering using slot indices in `env.fields` if populated. -/
def canonicalizeFields (env : LayoutEnv) (loweredFields : List (String × LExpr)) : List (String × LExpr) :=
  if env.fields.isEmpty then
    loweredFields
  else
    loweredFields.foldr (insertFieldByLayout env) []

/-- Lower `.extend base fields` by updating/appending field projections on `baseLow`. -/
def lowerExtend (env : LayoutEnv) (baseLow : LExpr) (newFields : List (String × LExpr)) : LExpr :=
  let inheritedFields : List (String × LExpr) :=
    match baseLow with
    | .record baseFs =>
        let envProjs := env.fields.foldr (fun (m, _) acc =>
          if baseFs.any (fun (k, _) => strEq k m) then acc else (m, .proj m baseLow) :: acc) []
        baseFs ++ envProjs
    | _ =>
        env.fields.map (fun (m, _) => (m, .proj m baseLow))
  let keptInherited := inheritedFields.filter (fun (m, _) => !(newFields.any (fun (k, _) => strEq k m)))
  .record (canonicalizeFields env (newFields ++ keptInherited))

/-- Lower `.case scrut branches` into nested conditionals over the `"tag"` field literal,
    binding `.proj "payload" scrutLow` at de Bruijn index 0 for each branch body. -/
def lowerCaseArms (scrutLow : LExpr) : List (String × LExpr) → LExpr
  | [] => .erased
  | (tag, bodyLow) :: rest =>
      .boolRec .emptyRow
        (lowerCaseArms scrutLow rest)
        (.letE .emptyRow (.proj "payload" scrutLow) bodyLow)
        (.natBin .beq (.proj "tag" scrutLow) (.lit (labelToNat tag)))

/-- Structural helper mapping a fuel-stepped lowering function over `(String × Term)` pairs. -/
def lowerFieldList (f : Term → Option LExpr) : List (String × Term) → Option (List (String × LExpr))
  | [] => some []
  | (m, t) :: rest => do
      let v ← f t
      let vs ← lowerFieldList f rest
      pure ((m, v) :: vs)

/-- Structural recursion on `fuel : Nat` (first parameter) so Lean compiles `lowerTermFuel`
    via `Nat.rec` with `0 Classical.choice`. -/
def lowerTermFuelAux : Nat → LayoutEnv → Term → Option LExpr
  | 0, _, _ => none
  | fuel + 1, env, t =>
    match t with
    | .bound i =>
        if Nat.blt 0 env.arity && Nat.blt (env.selfIndex + env.arity + 128) i then
          none
        else
          some (.bvar i)
    | .nat n => some (.lit n)
    | .boolean b => some (.boolLit b)
    | .label tag => some (.lit (labelToNat tag))
    | .binary .add l r => do return .natBin .add (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .binary .subtract l r => do return .natBin .sub (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .binary .multiply l r => do return .natBin .mul (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .binary .divide l r => do return .natBin .div (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .binary .modulo l r => do return .natBin .mod (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .binary .equal l r => do return .natBin .beq (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .binary .lessEqual l r => do return .natBin .ble (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .binary .less l r => do
        return .natBin .ble (.natSucc (← lowerTermFuelAux fuel env l)) (← lowerTermFuelAux fuel env r)
    | .binary .conjunction l r => do
        return .boolRec .boolean (.boolLit false) (← lowerTermFuelAux fuel env r) (← lowerTermFuelAux fuel env l)
    | .binary .labelEqual l r => do
        return .natBin .beq (← lowerTermFuelAux fuel env l) (← lowerTermFuelAux fuel env r)
    | .app f a => do return .app (← lowerTermFuelAux fuel env f) (← lowerTermFuelAux fuel env a)
    | .lam b => do
        let childEnv := { env with selfIndex := env.selfIndex + 1, arity := env.arity + 1 }
        return .lam .emptyRow (← lowerTermFuelAux fuel childEnv b)
    | .get t m => do
        let tLow ← lowerTermFuelAux fuel env t
        if !env.fields.isEmpty && (lookupByStr m env.fields).isNone then
          none
        else
          return .proj m tLow
    | .record fs => do
        let loweredFields ← lowerFieldList (lowerTermFuelAux fuel env) fs
        return .record (canonicalizeFields env loweredFields)
    | .extend base fields => do
        let baseLow ← lowerTermFuelAux fuel env base
        let loweredFields ← lowerFieldList (lowerTermFuelAux fuel env) fields
        return lowerExtend env baseLow loweredFields
    | .ifBool c x y => do
        return .boolRec .emptyRow (← lowerTermFuelAux fuel env y) (← lowerTermFuelAux fuel env x) (← lowerTermFuelAux fuel env c)
    | .ifZero c z s => do
        let lc ← lowerTermFuelAux fuel env c
        let lz ← lowerTermFuelAux fuel env z
        let childEnv := { env with selfIndex := env.selfIndex + 1, arity := env.arity + 1 }
        let ls ← lowerTermFuelAux fuel childEnv s
        return .boolRec .emptyRow (.letE .natural (.natBin .sub lc (.lit 1)) ls) lz (.natBin .beq lc (.lit 0))
    | .inject tag payload => do
        let payloadLow ← lowerTermFuelAux fuel env payload
        return .record [("tag", .lit (labelToNat tag)), ("payload", payloadLow)]
    | .case scrut branches => do
        let scrutLow ← lowerTermFuelAux fuel env scrut
        let childEnv := { env with selfIndex := env.selfIndex + 1, arity := env.arity + 1 }
        let loweredBranches ← lowerFieldList (lowerTermFuelAux fuel childEnv) branches
        return lowerCaseArms scrutLow loweredBranches
    | .split target names fn => do
        let targetLow ← lowerTermFuelAux fuel env target
        let fnLow ← lowerTermFuelAux fuel env fn
        return .split names fnLow targetLow
    | .done v => lowerTermFuelAux fuel env v
    | .perform p => lowerTermFuelAux fuel env p
    | _ => none

/-- Lower a first-order Core4 term into an `LExpr` under fuel, actively utilizing LayoutEnv. -/
def lowerTermFuel (env : LayoutEnv) (fuel : Nat) (t : Term) : Option LExpr :=
  lowerTermFuelAux fuel env t

/-- Helper to construct a canonical LayoutEnv from an emitted Leaf Book. -/
def layoutEnvOfBook (b : Obend.Leaf.Book) (selfIndex : Nat := 0) : LayoutEnv :=
  { fields := b.defs.mapIdx fun idx d => (d.member, idx),
    selfIndex := selfIndex,
    arity := 0 }

/-- Lower a first-order Core4 term into an `LExpr`. -/
def lowerTerm (env : LayoutEnv) (t : Term) : Option LExpr :=
  lowerTermFuel env 1024 t

/-- Lower a first-order flattened Book definition into Lean-lite `LExpr`.
    Because `Flatten` statically substitutes `super` lookups into provider records,
    `def.code` contains no dynamic mix or open prototypes. -/
def lowerLeafDef (env : LayoutEnv) (d : LeafDef) : Option LExpr :=
  lowerTerm env d.code

/-- The reflected object: a table of lowered expressions paired with the specialization pins
    that guard their contextual validity. -/
structure ReflectedObject where
  name : String
  composition : Composition
  defs : List (String × LExpr)
  pins : List LeafPin
  pins_eq : pins = (Candidate.book name composition).supports := by rfl

/-- Compile a prototype composition into a reflected object guarded by specSlot pins. -/
def reflectComposition (name : String) (C : Composition) (env : LayoutEnv) :
    Option ReflectedObject := do
  guard (C.closedB == true)
  let book := Obend.Leaf.emit C
  let defs ← book.defs.mapM fun d => do
    let e ← lowerLeafDef env d
    pure (d.member, e)
  let pins := (Candidate.book name C).supports
  pure ⟨name, C, defs, pins, rfl⟩

/-- **Dynamic Override Invalidation Theorem**:
    If any ancestor layer in `C` is modified or overridden with different code,
    `specSlot` immediately transitions to `.blocked`, invalidating the reflected `LExpr`
    and preventing stale proofs from being admitted. -/
theorem reflect_override_blocks (v : LeafView) (ref : ReflectedObject)
    (hj : ref.composition.closedB = true)
    {p : LeafPin} (hp : p ∈ ref.pins) (hd : holdsAt v p = false) :
    ∃ dead, specSlot.read (holdsAt v) (some (.book ref.name ref.composition)) =
      .blocked (.book ref.name ref.composition) dead ∧ p ∈ dead := by
  have hp' : p ∈ (Candidate.book ref.name ref.composition).supports := by
    rw [← ref.pins_eq]; exact hp
  obtain ⟨d, hr, hp_in_d, _⟩ := moved_pin_blocks hj hp' hd
  exact ⟨d, hr, hp_in_d⟩

/-- **Soundness of lowered `.ifZero` on `0`**:
    When `c` lowers to `.lit 0`, the lowered `.ifZero` conditional reduces via `SSteps` to `lz`. -/
theorem lowerTerm_ifZero_zero_steps (lz ls : LExpr) :
    Obend.Lower.SSteps
      (.boolRec .emptyRow (.letE .natural (.natBin .sub (.lit 0) (.lit 1)) ls) lz (.natBin .beq (.lit 0) (.lit 0)))
      lz := by
  refine .next (.boolRecMajor .emptyRow _ _ (.binLit .beq 0 0)) ?_
  exact .next (.boolRecTrue .emptyRow _ lz) (.refl lz)

/-- **Soundness of lowered `.ifZero` on `n + 1`**:
    When `c` lowers to `.lit (n + 1)`, the lowered `.ifZero` conditional reduces via `SSteps`
    to `ls` instantiated with the predecessor expression `.natBin .sub (.lit (n + 1)) (.lit 1)`. -/
theorem lowerTerm_ifZero_succ_steps (n : Nat) (lz ls : LExpr) :
    Obend.Lower.SSteps
      (.boolRec .emptyRow (.letE .natural (.natBin .sub (.lit (n + 1)) (.lit 1)) ls) lz (.natBin .beq (.lit (n + 1)) (.lit 0)))
      (ls.inst (.natBin .sub (.lit (n + 1)) (.lit 1))) := by
  refine .next (.boolRecMajor .emptyRow _ _ (.binLit .beq (n + 1) 0)) ?_
  have hneq : ((n + 1 == 0) = false) := by simp
  change Obend.Lower.SSteps
    (.boolRec .emptyRow (.letE .natural (.natBin .sub (.lit (n + 1)) (.lit 1)) ls) lz (.boolLit (n + 1 == 0)))
    (ls.inst (.natBin .sub (.lit (n + 1)) (.lit 1)))
  rw [hneq]
  refine .next (.boolRecFalse .emptyRow _ lz) ?_
  exact .next (.zeta .natural (.natBin .sub (.lit (n + 1)) (.lit 1)) ls) (.refl _)

/-- **Soundness of lowered `.ifZero` predecessor projection on `n + 1`**:
    When the successor branch is `.bvar 0` (returning the bound predecessor),
    the lowered `.ifZero` on `.lit (n + 1)` reduces via `SSteps` all the way to `.lit n`. -/
theorem lowerTerm_ifZero_succ_bvar0_steps (n : Nat) (lz : LExpr) :
    Obend.Lower.SSteps
      (.boolRec .emptyRow (.letE .natural (.natBin .sub (.lit (n + 1)) (.lit 1)) (.bvar 0)) lz (.natBin .beq (.lit (n + 1)) (.lit 0)))
      (.lit n) := by
  refine .next (.boolRecMajor .emptyRow _ _ (.binLit .beq (n + 1) 0)) ?_
  have hneq : ((n + 1 == 0) = false) := by simp
  change Obend.Lower.SSteps
    (.boolRec .emptyRow (.letE .natural (.natBin .sub (.lit (n + 1)) (.lit 1)) (.bvar 0)) lz (.boolLit (n + 1 == 0)))
    (.lit n)
  rw [hneq]
  refine .next (.boolRecFalse .emptyRow _ lz) ?_
  refine .next (.zeta .natural (.natBin .sub (.lit (n + 1)) (.lit 1)) (.bvar 0)) ?_
  have hinst : (LExpr.bvar 0).inst (.natBin .sub (.lit (n + 1)) (.lit 1)) =
      .natBin .sub (.lit (n + 1)) (.lit 1) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  have hsub : Obend.Lower.NatOp.sub.eval (n + 1) 1 = .lit n := by
    simp [Obend.Lower.NatOp.eval]
  have hstep : Obend.Lower.SStep (.natBin .sub (.lit (n + 1)) (.lit 1)) (.lit n) := by
    rw [← hsub]
    exact .binLit .sub (n + 1) 1
  exact .next hstep (.refl (.lit n))

/-- **Soundness of lowered `.inject` / `.case` head branch**:
    Matching a lowered `.inject tag payload` against `(tag, bodyLow) :: rest` reduces via `SSteps`
    to `bodyLow` instantiated with the payload projection. -/
theorem lowerTerm_inject_case_head_steps (tag : String) (payloadLow bodyLow : LExpr)
    (rest : List (String × LExpr)) :
    let scrutLow : LExpr := .record [("tag", .lit (labelToNat tag)), ("payload", payloadLow)]
    Obend.Lower.SSteps
      (lowerCaseArms scrutLow ((tag, bodyLow) :: rest))
      (bodyLow.inst (.proj "payload" scrutLow)) := by
  intro scrutLow
  rw [lowerCaseArms]
  have hproj : Obend.Lower.SStep (.proj "tag" scrutLow) (.lit (labelToNat tag)) := by
    exact .projRecord "tag" [("tag", .lit (labelToNat tag)), ("payload", payloadLow)] (.lit (labelToNat tag)) rfl
  refine .next (.boolRecMajor .emptyRow _ _ (.binLeft .beq (.lit (labelToNat tag)) hproj)) ?_
  refine .next (.boolRecMajor .emptyRow _ _ (.binLit .beq (labelToNat tag) (labelToNat tag))) ?_
  have heq : Obend.Lower.NatOp.beq.eval (labelToNat tag) (labelToNat tag) = .boolLit true := by
    simp [Obend.Lower.NatOp.eval]
  rw [heq]
  refine .next (.boolRecTrue .emptyRow _ _) ?_
  exact .next (.zeta .emptyRow (.proj "payload" scrutLow) bodyLow) (.refl _)

/-- **Soundness of lowered `.inject` / `.case` branch skipping**:
    When `labelToNat tag != labelToNat armTag`, `lowerCaseArms` steps past `(armTag, bodyLow)`
    to `lowerCaseArms scrutLow rest`. -/
theorem lowerTerm_inject_case_skip_steps (tag armTag : String) (payloadLow bodyLow : LExpr)
    (rest : List (String × LExpr)) (hneq : (labelToNat tag == labelToNat armTag) = false) :
    let scrutLow : LExpr := .record [("tag", .lit (labelToNat tag)), ("payload", payloadLow)]
    Obend.Lower.SSteps
      (lowerCaseArms scrutLow ((armTag, bodyLow) :: rest))
      (lowerCaseArms scrutLow rest) := by
  intro scrutLow
  rw [lowerCaseArms]
  have hproj : Obend.Lower.SStep (.proj "tag" scrutLow) (.lit (labelToNat tag)) := by
    exact .projRecord "tag" [("tag", .lit (labelToNat tag)), ("payload", payloadLow)] (.lit (labelToNat tag)) rfl
  refine .next (.boolRecMajor .emptyRow _ _ (.binLeft .beq (.lit (labelToNat armTag)) hproj)) ?_
  refine .next (.boolRecMajor .emptyRow _ _ (.binLit .beq (labelToNat tag) (labelToNat armTag))) ?_
  have heval : Obend.Lower.NatOp.beq.eval (labelToNat tag) (labelToNat armTag) = .boolLit false := by
    simp [Obend.Lower.NatOp.eval, hneq]
  rw [heval]
  exact .next (.boolRecFalse .emptyRow _ _) (.refl _)

/-- Constructive reflexivity of `==` from `DecidableEq` without `String.instLawfulBEq`. -/
theorem beq_refl_of_decEq (m : String) : (m == m) = true := by
  show @Decidable.decide (m = m) (instDecidableEqString m m) = true
  cases instDecidableEqString m m with
  | isFalse h => exact False.elim (h rfl)
  | isTrue _ => rfl

/-- Constructive head match for `List.find?`. -/
theorem find?_cons_head {α : Type} (p : α → Bool) (x : α) (xs : List α) (h : p x = true) :
    List.find? p (x :: xs) = some x := by
  unfold List.find?
  rw [h]

/-- **Soundness of lowered `.extend` field projection**:
    Projecting an updated head field `(m, v)` from `lowerExtend` with an unpermuted layout
    steps in one `SStep.projRecord` to `v`. -/
theorem lowerExtend_proj_head_step (env : LayoutEnv) (hempty : env.fields = [])
    (baseLow : LExpr) (m : String) (v : LExpr) (rest : List (String × LExpr)) :
    Obend.Lower.SStep (.proj m (lowerExtend env baseLow ((m, v) :: rest))) v := by
  unfold lowerExtend canonicalizeFields
  rw [hempty]
  exact .projRecord m _ v (find?_cons_head _ _ _ (beq_refl_of_decEq m))

/-- **Soundness of lowered `.split` on a record**:
    When `targetLow = .record fields` and `splitValues fields names = some values`,
    `LExpr.split names fnLow (.record fields)` steps in one `SStep.splitRecord` to `fnLow.spine values`. -/
theorem lowerSplit_record_step (names : List String) (fnLow : LExpr)
    (fields : List (String × LExpr)) (values : List LExpr)
    (hsplit : Obend.Core.Term.splitValues fields names = some values) :
    Obend.Lower.SStep (.split names fnLow (.record fields)) (fnLow.spine values) :=
  .splitRecord names fnLow fields values hsplit

/-! ## Fused Open-Recursive `Composition → Flatten → Book → LExpr` Slot Lowering (`NEXT-MATHEMATICA.md` §4.1) -/

/-- Denotation of a lowered `LExpr` in the `Core4` `Term` semantics (`lowerT`). -/
abbrev _root_.Obend.Lower.LExpr.denote (e : LExpr) : Term :=
  lowerT e

/-- The open-recursive read-cone member names of `targetMethod` in `C`:
    the union of `slotReadCone C targetMethod` and `extractReadMembers (C.symUnfold targetMethod)`. -/
def openRecursiveConeMembers (C : Composition) (targetMethod : String) : List String :=
  Obend.Leaf.slotReadCone C targetMethod ++ Obend.Leaf.extractReadMembers (C.symUnfold targetMethod)

/-- Pin a member `m` of `C` to its flattened symbolic unfolding `C.symUnfold m` at `.layer m`. -/
def openRecursiveMemberPin (C : Composition) (m : String) : LeafPin :=
  ⟨.layer m, C.symUnfold m⟩

/-- Convert a first-order `transportSlot` `Support` (`methodSupport m providerLayer f_lean`)
    into its corresponding `.layer sp.member` `LeafPin`. -/
def transportSupportPin (C : Composition) (sp : Obend.Logic.Support) : LeafPin :=
  ⟨.layer sp.member,
    match sp.unfolded with
    | some (_, code) => code
    | none => C.symUnfold sp.member⟩

/-- Certificate for the fused `Composition → Flatten → Book → LExpr` slot lowering bridge. -/
structure FusedPrototypeCert where
  objectName : String := "default"
  targetMethod : String
  env : LayoutEnv := { fields := [], selfIndex := 0, arity := 0 }
  loweredExpr : LExpr
  transportSupports : List Obend.Logic.Support := []

/-- Member names in the fused support of `c` at `(C, targetMethod)`:
    the union of the open-recursive read cone (`slotReadCone` ++ `extractReadMembers`)
    and the `transportSlot` `methodSupport` member names. -/
def fusedSupport (C : Composition) (targetMethod : String) (c : FusedPrototypeCert) : List String :=
  openRecursiveConeMembers C targetMethod ++ c.transportSupports.map Obend.Logic.Support.member

/-- Support pins of `c` at `(C, targetMethod)`:
    the exact union of the open-recursive `specSlot` read-cone pins and the first-order
    `transportSlot` `methodSupport` pins. -/
def fusedSupportPins (C : Composition) (targetMethod : String) (c : FusedPrototypeCert) : List LeafPin :=
  (openRecursiveConeMembers C targetMethod).map (openRecursiveMemberPin C) ++
    c.transportSupports.map (transportSupportPin C)

/-- Judge for `fusedPrototypeSlot`: verifies that `C` is closed (`C.closedB`), `c.targetMethod`
    matches `targetMethod`, `C.symUnfold targetMethod` lowers via `lowerTerm c.env` to an
    `e : LExpr` whose denotation equals `c.loweredExpr.denote`, and `c.loweredExpr.denote` (`lowerT`)
    is term-equivalent to `C.symUnfold targetMethod`. -/
def fusedPrototypeJudge (C : Composition) (targetMethod : String) (c : FusedPrototypeCert) : Bool :=
  C.closedB &&
  (c.targetMethod == targetMethod) &&
  match lowerTerm c.env (C.symUnfold targetMethod) with
  | some e =>
    Obend.Law.termEq e.denote c.loweredExpr.denote &&
    Obend.Law.termEq c.loweredExpr.denote (C.symUnfold targetMethod)
  | none => false

/-- **Fused Prototype Slot (`fusedPrototypeSlot`)**:
    An `Obend.Slot.Slot LeafPin FusedPrototypeCert` whose support pins are the exact union of
    the open-recursive `specSlot` read-cone pins (`slotReadCone C targetMethod` / `extractReadMembers`)
    and the first-order `transportSlot` `methodSupport` pins. -/
def fusedPrototypeSlot (C : Composition) (targetMethod : String) :
    Obend.Slot.Slot LeafPin FusedPrototypeCert where
  supports := fusedSupportPins C targetMethod
  judge := fusedPrototypeJudge C targetMethod

/-- Canonical member-level `LeafView` induced by a `Composition` `C` at clock `k`. -/
def fusedMemberView (k : Nat) (C : Composition) : LeafView where
  clock := k
  decl
    | .layer m => some (C.symUnfold m)
    | .object _ => some C.code

/-- Override a single method `m` in a `LeafView` `v` with `newCode`, advancing the view clock by 1. -/
def overrideMethodView (v : LeafView) (m : String) (newCode : Term) : LeafView where
  clock := v.clock + 1
  decl cell :=
    if cell == .layer m then
      some newCode
    else
      v.decl cell

theorem fusedSupportPins_cover_extractReadMembers
    (C : Composition) (targetMethod : String) (c : FusedPrototypeCert) :
    Obend.Leaf.SupportsCoverMembers (fusedSupportPins C targetMethod c)
      (Obend.Leaf.extractReadMembers (C.symUnfold targetMethod)) := by
  intro m hm
  refine ⟨C.symUnfold m, ?_⟩
  unfold fusedSupportPins openRecursiveConeMembers openRecursiveMemberPin
  apply List.mem_append_left
  rw [List.mem_map]
  exact ⟨m, List.mem_append_right _ hm, rfl⟩

theorem mem_fusedSupport_of_pin
    {C : Composition} {targetMethod : String} {c : FusedPrototypeCert} {p : LeafPin}
    (hp : p ∈ fusedSupportPins C targetMethod c) :
    ∃ m ∈ fusedSupport C targetMethod c, p.cell = .layer m := by
  unfold fusedSupportPins at hp
  rcases List.mem_append.1 hp with hcone | htrans
  · rw [List.mem_map] at hcone
    obtain ⟨m, hm, rfl⟩ := hcone
    exact ⟨m, List.mem_append_left _ hm, rfl⟩
  · rw [List.mem_map] at htrans
    obtain ⟨sp, hsp, rfl⟩ := htrans
    refine ⟨sp.member, List.mem_append_right _ ?_, rfl⟩
    exact List.mem_map.2 ⟨sp, hsp, rfl⟩

theorem pin_of_mem_fusedSupport
    {C : Composition} {targetMethod : String} {c : FusedPrototypeCert} {m : String}
    (hm : m ∈ fusedSupport C targetMethod c) :
    ∃ p ∈ fusedSupportPins C targetMethod c, p.cell = .layer m := by
  unfold fusedSupport at hm
  rcases List.mem_append.1 hm with hcone | htrans
  · refine ⟨openRecursiveMemberPin C m, ?_, rfl⟩
    unfold fusedSupportPins
    apply List.mem_append_left
    exact List.mem_map.2 ⟨m, hcone, rfl⟩
  · rw [List.mem_map] at htrans
    obtain ⟨sp, hsp, rfl⟩ := htrans
    refine ⟨transportSupportPin C sp, ?_, rfl⟩
    unfold fusedSupportPins
    apply List.mem_append_right
    exact List.mem_map.2 ⟨sp, hsp, rfl⟩

theorem fusedPrototypeJudge_true_iff
    {C : Composition} {targetMethod : String} {c : FusedPrototypeCert} :
    fusedPrototypeJudge C targetMethod c = true ↔
      C.closedB = true ∧
      c.targetMethod = targetMethod ∧
      (∃ e : LExpr,
        lowerTerm c.env (C.symUnfold targetMethod) = some e ∧
        e.denote = c.loweredExpr.denote) ∧
      c.loweredExpr.denote = C.symUnfold targetMethod := by
  unfold fusedPrototypeJudge
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hc, htm⟩, hlow⟩ := h
    cases hlt : lowerTerm c.env (C.symUnfold targetMethod) with
    | none => rw [hlt] at hlow; cases hlow
    | some e =>
      rw [hlt] at hlow
      simp only [Bool.and_eq_true] at hlow
      obtain ⟨he_eq, hteq⟩ := hlow
      exact ⟨hc, htm, ⟨e, rfl, Obend.Law.termEq_sound he_eq⟩, Obend.Law.termEq_sound hteq⟩
  · rintro ⟨hc, htm, ⟨e, hlt, he_den⟩, hden⟩
    have he_teq : Obend.Law.termEq e.denote c.loweredExpr.denote = true := by
      rw [he_den]
      exact Obend.Logic.termEq_refl' c.loweredExpr.denote
    have hteq : Obend.Law.termEq c.loweredExpr.denote (C.symUnfold targetMethod) = true := by
      rw [hden]
      exact Obend.Logic.termEq_refl' (C.symUnfold targetMethod)
    simp [hc, htm, hlt, he_teq, hteq]

theorem holdsAt_overrideMethodView_outside
    (C : Composition) (targetMethod : String) (c : FusedPrototypeCert)
    (v : LeafView) {m : String} (hm : m ∉ fusedSupport C targetMethod c) (newCode : Term)
    {p : LeafPin} (hp : p ∈ fusedSupportPins C targetMethod c) :
    holdsAt (overrideMethodView v m newCode) p = holdsAt v p := by
  obtain ⟨m', hm', hcell⟩ := mem_fusedSupport_of_pin hp
  rw [Obend.Leaf.holdsAt_eq, Obend.Leaf.holdsAt_eq]
  unfold overrideMethodView
  have hne : (p.cell == .layer m) = false := by
    rw [hcell]
    cases hbeq : ( Obend.Leaf.LeafCell.layer m' == Obend.Leaf.LeafCell.layer m ) with
    | false => rfl
    | true =>
      have heq : Obend.Leaf.LeafCell.layer m' = Obend.Leaf.LeafCell.layer m := beq_iff_eq.1 hbeq
      injection heq with hm_eq
      subst hm_eq
      exact False.elim (hm hm')
  simp [hne]

theorem holdsAt_overrideMethodView_same
    (v : LeafView) (m : String) (newCode : Term) (p : LeafPin)
    (hcell : p.cell = .layer m) :
    holdsAt (overrideMethodView v m newCode) p = Obend.Law.termEq newCode p.code := by
  rw [Obend.Leaf.holdsAt_eq]
  unfold overrideMethodView
  rw [hcell]
  simp

/-- **1. Soundness & Conservatism of `fusedPrototypeSlot` (`fusedPrototypeSlot_usable_sound`)**:
    When `c` is `.usable` in `fusedPrototypeSlot C targetMethod` at view `v`:
    - `C.symUnfold targetMethod` lowers via `lowerTerm c.env` to `e : LExpr` with `e.denote = c.loweredExpr.denote`,
    - `c.loweredExpr.denote` equals `C.symUnfold targetMethod`,
    - `.get C.flatten targetMethod ≈b .get C.object targetMethod` (`flatten_sound`) and
      `.get (Obend.Leaf.emit C).link targetMethod ≈b .get C.object targetMethod` (`book_sound`),
    - For any canonical `v_can : LExpr` to which `c.loweredExpr` reduces (`SSteps c.loweredExpr v_can`),
      `c.loweredExpr.denote` and `C.symUnfold targetMethod` evaluate in `Core4` to a value `w`
      related to `v_can.denote` by `AheadChain` (`lower_sound`). -/
theorem fusedPrototypeSlot_usable_sound
    {C : Composition} {targetMethod : String} {c : FusedPrototypeCert} {v : LeafView}
    (hus : (fusedPrototypeSlot C targetMethod).usable (holdsAt v) c = true) :
    C.closedB = true ∧
    (∃ e : LExpr,
      lowerTerm c.env (C.symUnfold targetMethod) = some e ∧
      e.denote = c.loweredExpr.denote ∧
      e.denote = C.symUnfold targetMethod) ∧
    c.loweredExpr.denote = C.symUnfold targetMethod ∧
    (.get C.flatten targetMethod ≈b .get C.object targetMethod) ∧
    (.get (Obend.Leaf.emit C).link targetMethod ≈b .get C.object targetMethod) ∧
    (∀ (v_can : LExpr), Obend.Lower.SSteps c.loweredExpr v_can → Obend.Lower.Canonical v_can →
      ∃ w, Obend.Core.Term.Evaluates c.loweredExpr.denote w ∧
        Obend.Core.Term.Evaluates (C.symUnfold targetMethod) w ∧
        Obend.Lower.AheadChain v_can.denote w) := by
  obtain ⟨hj, _⟩ := (Obend.Slot.usable_iff (fusedPrototypeSlot C targetMethod) (holdsAt v) c).1 hus
  obtain ⟨hc, _, ⟨e, hlt, he_den⟩, hden⟩ := fusedPrototypeJudge_true_iff.1 hj
  refine ⟨hc, ⟨e, hlt, he_den, he_den.trans hden⟩, hden, Obend.Leaf.flatten_sound C hc targetMethod,
    Obend.Leaf.book_sound C hc targetMethod, ?_⟩
  intro v_can hsteps hcan
  obtain ⟨w, hev, hchain⟩ := Obend.Lower.lower_sound hsteps hcan
  refine ⟨w, hev, ?_, hchain⟩
  rwa [← hden]

/-- **2. Non-Supported Override Invariance (`fusedPrototypeSlot_override_outside_usable`)**:
    Any override to a method `m ∉ fusedSupport C targetMethod c` leaves
    `(fusedPrototypeSlot C targetMethod).usable` invariant (`= true`) and preserves the
    specialized method body under `substMemberEnv`. -/
theorem fusedPrototypeSlot_override_outside_usable
    {C : Composition} {targetMethod : String} {c : FusedPrototypeCert} {v : LeafView}
    (hus : (fusedPrototypeSlot C targetMethod).usable (holdsAt v) c = true)
    {m : String} (hm : m ∉ fusedSupport C targetMethod c) (newCode : Term) :
    (fusedPrototypeSlot C targetMethod).usable (holdsAt (overrideMethodView v m newCode)) c = true ∧
    Obend.Leaf.substMemberEnv (Obend.Leaf.viewLayerEnv (overrideMethodView v m newCode)) (C.symUnfold targetMethod) =
      Obend.Leaf.substMemberEnv (Obend.Leaf.viewLayerEnv v) (C.symUnfold targetMethod) := by
  obtain ⟨hj, hall⟩ := (Obend.Slot.usable_iff (fusedPrototypeSlot C targetMethod) (holdsAt v) c).1 hus
  have hall' : ∀ p ∈ (fusedPrototypeSlot C targetMethod).supports c,
      holdsAt (overrideMethodView v m newCode) p = true := by
    intro p hp
    rw [holdsAt_overrideMethodView_outside C targetMethod c v hm newCode hp]
    exact hall p hp
  have hus' : (fusedPrototypeSlot C targetMethod).usable (holdsAt (overrideMethodView v m newCode)) c = true :=
    (Obend.Slot.usable_iff (fusedPrototypeSlot C targetMethod) (holdsAt (overrideMethodView v m newCode)) c).2 ⟨hj, hall'⟩
  have hcov := fusedSupportPins_cover_extractReadMembers C targetMethod c
  have hcons := (Obend.Leaf.candidate_supports_conservative hcov hall' hall).1
  exact ⟨hus', hcons⟩

/-- **3. Single-Step Override Blocking on Pinned Support (`fusedPrototypeSlot_moved_pin_blocks`)**:
    Any mutation to a pinned method `m ∈ fusedSupport C targetMethod c` with a non-equivalent
    body `newCode` (`termEq newCode p.code = false`) immediately transitions
    `fusedPrototypeSlot C targetMethod` to `.blocked c dead` with `p ∈ dead`. -/
theorem fusedPrototypeSlot_moved_pin_blocks
    {C : Composition} {targetMethod : String} {c : FusedPrototypeCert} {v : LeafView}
    (hj : (fusedPrototypeSlot C targetMethod).judge c = true)
    {p : LeafPin} (hp : p ∈ (fusedPrototypeSlot C targetMethod).supports c)
    {m : String} (hcell : p.cell = .layer m)
    {newCode : Term} (hdiff : Obend.Law.termEq newCode p.code = false) :
    ∃ dead,
      (fusedPrototypeSlot C targetMethod).read (holdsAt (overrideMethodView v m newCode)) (some c) =
        .blocked c dead ∧
      p ∈ dead ∧
      (∀ q, q ∈ dead ↔ q ∈ (fusedPrototypeSlot C targetMethod).supports c ∧
        holdsAt (overrideMethodView v m newCode) q = false) := by
  have hd : holdsAt (overrideMethodView v m newCode) p = false := by
    rw [holdsAt_overrideMethodView_same v m newCode p hcell, hdiff]
  have hmem : p ∈ (fusedPrototypeSlot C targetMethod).dead (holdsAt (overrideMethodView v m newCode)) c :=
    (Obend.Slot.mem_dead_iff _ _ _ _).2 ⟨hp, hd⟩
  have hread : ∃ dead,
      (fusedPrototypeSlot C targetMethod).read (holdsAt (overrideMethodView v m newCode)) (some c) =
        .blocked c dead ∧ p ∈ dead := by
    unfold Obend.Slot.Slot.read
    simp only [hj, ite_true]
    cases hdd : (fusedPrototypeSlot C targetMethod).dead (holdsAt (overrideMethodView v m newCode)) c with
    | nil => rw [hdd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩
  obtain ⟨dead, hr, hpd⟩ := hread
  exact ⟨dead, hr, hpd, (Obend.Slot.read_blocked_exact (fusedPrototypeSlot C targetMethod) _ _ _ _ hr).2⟩

/-- **Master Theorem (`fusedPrototypeSlot_sound_and_conservative`)**:
    Unifies all three guarantees of the fused `Composition → Flatten → Book → LExpr` slot bridge:
    1. **Soundness (`flatten_sound` + `lower_sound`)**: when all pins in the fused support hold at `v`,
       `C.symUnfold targetMethod` lowers via `lowerTerm` to `e : LExpr` whose denotation
       `e.denote = c.loweredExpr.denote` equals `C.symUnfold targetMethod`,
       `.get C.flatten targetMethod ≈b .get C.object targetMethod`,
       and `SSteps` evaluation of `c.loweredExpr` is sound with respect to `Core4` evaluation (`lower_sound`).
    2. **Conservatism under non-supported overrides**: any override to a method `m ∉ fusedSupport C targetMethod c`
       leaves `(fusedPrototypeSlot C targetMethod).usable = true` and `substMemberEnv` invariant.
    3. **1-step invalidation on supported overrides (`moved_pin_blocks`)**: any mutation to a pinned method
       `m ∈ fusedSupport C targetMethod c` with `termEq newCode p.code = false` blocks `fusedPrototypeSlot`
       in 1 step, naming the stale pin `p ∈ dead`. -/
theorem fusedPrototypeSlot_sound_and_conservative
    {C : Composition} {targetMethod : String} {c : FusedPrototypeCert} {v : LeafView}
    (hus : (fusedPrototypeSlot C targetMethod).usable (holdsAt v) c = true) :
    (C.closedB = true ∧
      (∃ e : LExpr,
        lowerTerm c.env (C.symUnfold targetMethod) = some e ∧
        e.denote = c.loweredExpr.denote ∧
        e.denote = C.symUnfold targetMethod) ∧
      c.loweredExpr.denote = C.symUnfold targetMethod ∧
      (.get C.flatten targetMethod ≈b .get C.object targetMethod) ∧
      (∀ (v_can : LExpr), Obend.Lower.SSteps c.loweredExpr v_can → Obend.Lower.Canonical v_can →
        ∃ w, Obend.Core.Term.Evaluates c.loweredExpr.denote w ∧
          Obend.Core.Term.Evaluates (C.symUnfold targetMethod) w ∧
          Obend.Lower.AheadChain v_can.denote w)) ∧
    (∀ m, m ∉ fusedSupport C targetMethod c → ∀ newCode,
      (fusedPrototypeSlot C targetMethod).usable (holdsAt (overrideMethodView v m newCode)) c = true) ∧
    (∀ m ∈ fusedSupport C targetMethod c,
      ∃ p ∈ (fusedPrototypeSlot C targetMethod).supports c,
        p.cell = .layer m ∧
        ∀ newCode, Obend.Law.termEq newCode p.code = false →
          ∃ dead,
            (fusedPrototypeSlot C targetMethod).read (holdsAt (overrideMethodView v m newCode)) (some c) =
              .blocked c dead ∧ p ∈ dead) := by
  have h1 := fusedPrototypeSlot_usable_sound hus
  obtain ⟨hj, _⟩ := (Obend.Slot.usable_iff (fusedPrototypeSlot C targetMethod) (holdsAt v) c).1 hus
  refine ⟨⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.2⟩, ?_, ?_⟩
  · intro m hm newCode
    exact (fusedPrototypeSlot_override_outside_usable hus hm newCode).1
  · intro m hm
    obtain ⟨p, hp, hcell⟩ := pin_of_mem_fusedSupport hm
    refine ⟨p, hp, hcell, fun newCode hdiff => ?_⟩
    obtain ⟨dead, hr, hpd, _⟩ := fusedPrototypeSlot_moved_pin_blocks hj hp hcell hdiff
    exact ⟨dead, hr, hpd⟩

end Obend.Lower.Reflect
end
