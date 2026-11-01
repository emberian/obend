module
/-
# Obend.Lower.Fragment — Lean-lite: which kernel terms are in, read into `LExpr`

`read env e` decides, relative to the environment, whether a closed kernel `Expr` is in the fragment,
and reads it into `LExpr` (`Obend.Lower.Syntax`); `inFragment` is its success. It is a total
computation (a fuel bounds the unfolding of definitions); its type queries are Lean's own (`inferType`,
`whnf`, `isProof`, `isType`, `isTypeFormer` in `MetaM`), so the reader is the trust boundary of the
pipeline exactly as `TrExpr` is for Lean4Lean and the `Expr`-to-λ□ bridge is for the 2025 report
(`sdima2025`, §3.3): it is not verified here. Everything after it is.

**In.**
* Closed terms built from `fun`, application, `let`, `Nat` literals, bound variables.
* `Nat`: `Nat.zero`, `Nat.succ`, the literal operations the kernel computes (`Nat.add`, `Nat.sub`,
  `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`; partially applied ones are η-expanded), and
  `Nat.rec`. `Bool`: `true`, `false`, `Bool.rec`.
* Structures without indices (their parameters erased, so universe-polymorphic library structures such
  as `PProd`, `PUnit`, `HAdd`, `OfNat`, and `Decidable`, a structure in 4.35 whose `decide : Bool` is its
  content, are in): the constructor, the recursor, `Expr.proj`.
* Inductives without indices that are not recursive (a constructor's field of the type itself is
  out): their constructors and recursor.
* Definitions, δ-unfolded at their use: every `casesOn`, `recOn`, matcher (`f.match_1`), `ite`/`dite`
  (to `Bool.casesOn` of `Decidable.decide`), the instances (`instHAdd`, `instOfNatNat`), `Nat.decEq`,
  `Nat.decLt`, `Nat.decLe`, and the elaborator's structural recursion (`Nat.brecOn`, `Nat.below`,
  `PProd`): read once per use, with the use's type arguments let-bound so binder types are concrete.
* Erasable subterms: every subterm whose type is a proposition (a proof) or whose type is a sort or a
  type former (a type): read as `erased`, whatever they are (a proof by `Acc.rec`, `Eq.rec`, a
  universe-polymorphic type).

**Out, and why.**
* Well-founded recursion (`WellFounded.fix`, `Acc.rec` in computational position) and `Prop`
  inductive elimination into `Type` (`True.rec`, `And.rec`, `Eq.rec`, `False.rec`): every proof of a
  `Prop` erases to `.erased` (`{}`), so eliminating a `Prop` inductive into `Type` would either lack
  the erased constructor fields (`And.rec`) or reduce an unreduced proof (`True.rec`).
* Indexed inductives, recursive user inductives, mutual and nested inductives: a recursive type needs a
  Core4 alias and a recursive-call ι through `fix`, the pattern `Nat.rec` shows; not done here.
* `Eq.rec`/casts, `Quot`, `String` and `Char` literals, `Float`, `UInt*`, arrays, axioms, `opaque`,
  `implemented_by`/`extern` definitions (their kernel value is what is read, so `@[extern]` is fine
  when its kernel definition is in the fragment; `opaque` has none), `unsafe`/`partial` definitions (no kernel value).
* `Nat.pow` as a primitive: it δ-unfolds through its structural `Nat.rec` definition instead; `Nat.gcd`,
  `Nat.log2`, and `Nat.bitwise` use `WellFounded.fix` (`Acc.rec`) in `Init` and are outside the fragment.
* Open terms (free variables, metavariables).

**Typing.** The reader also records each binder's and recursor's Core4 type (`lowerTy`); where a
type has none in the fragment (a polymorphic type left abstract, a type computed by recursion such as
`Nat.below` inside `Nat.brecOn`), it records `untyped`, which no `LTyped` derivation accepts: such a
term is lowered and runs (`lower_sound`) but the checker refuses it (`lower_checks` does not apply).
-/
public import Lean
public import Obend.Lower.Lower
public import Obend.Lower.Typing
public section
namespace Obend.Lower.Fragment
open Lean Meta
open Obend.Core.Ty (Ty)
open Obend.Lower
set_option autoImplicit false

/-- The annotation of a binder whose type has no Core4 type in the fragment. -/
def untyped : Ty := .variable 0

/-- The read's state: the unfolding budget. -/
abbrev ReadM := ReaderT (Array Expr) (StateRefT Nat MetaM)

def tick : ReadM Unit := do
  let n ← get
  if n == 0 then throwError "the fragment's unfolding budget is exhausted"
  set (n - 1)

def literalOp? : Name → Option NatOp
  | ``Nat.add => some .add | ``Nat.sub => some .sub | ``Nat.mul => some .mul | ``Nat.div => some .div
  | ``Nat.mod => some .mod | ``Nat.beq => some .beq | ``Nat.ble => some .ble
  | _ => none

/-- A type, a proof, or a type former. -/
def erasable (e : Expr) : MetaM Bool := do
  if ← isProof e then return true
  if ← isType e then return true
  isTypeFormer e

def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

/-- The constructor's fields (after its parameters) as `(name, type)` under fresh variables. -/
def ctorFields {α : Type} (ctor : Name) (us : List Level) (params : Array Expr) (k : Array (String × Expr) → MetaM α)
    : MetaM α := do
  let info ← getConstInfoCtor ctor
  let ty ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) params
  forallTelescopeReducing ty fun xs _ => do
    let fields ← xs.mapM fun x => do return (shortName (← x.fvarId!.getUserName), ← inferType x)
    k fields

/-- An inductive of the fragment: computational (not in `Prop`), not recursive, no indices, one inductive in its block. -/
def fragmentInductive? (n : Name) : MetaM (Option InductiveVal) := do
  match (← getEnv).find? n with
  | some (.inductInfo v) =>
    let isPropInd ← forallTelescopeReducing v.type fun _ s => pure s.isProp
    if !isPropInd && v.numIndices == 0 && !v.isRec && v.all.length == 1 && !v.isNested then return some v else return none
  | _ => return none

mutual
/-- The Core4 type of a binder of type `T`. -/
partial def binderTy (T : Expr) : MetaM Ty := do
  if ← isProp T then return .emptyRow
  if ← isTypeFormerType T then return .emptyRow
  return (← lowerTy T).getD untyped

/-- **`lowerTy`**: the Core4 type of a fragment type (proofs and types erased to `{}`). -/
partial def lowerTy (T : Expr) : MetaM (Option Ty) := do
  let T ← whnf T
  if ← isProp T then return some .emptyRow
  if ← isTypeFormerType T then return some .emptyRow
  match T with
  | .forallE n A B bi =>
    withLocalDecl n bi A fun x => do
      let a ← binderTy A
      if a == untyped then return none
      let some b ← lowerTy (B.instantiate1 x) | return none
      return some (fn a b)
  | _ =>
    let .const c us := T.getAppFn | return none
    if c == ``Nat then return some .natural
    if c == ``Bool then return some .boolean
    let some v ← fragmentInductive? c | return none
    let params := T.getAppArgs.extract 0 v.numParams
    if params.size != v.numParams then return none
    let row ← v.ctors.mapM fun ctor => ctorFields ctor us params fun fields => do
      let mut out : List (String × Ty) := []
      for (n, t) in fields.toList.reverse do
        let some ty ← binderTy' t | return none
        out := (n, ty) :: out
      return some (shortName ctor, fieldRow out)
    if row.any Option.isNone then return none
    let row := row.filterMap id
    if isStructure (← getEnv) c then
      match row with
      | [(_, r)] => return some r
      | _ => return none
    else return some (.variant (fieldRow row))

partial def binderTy' (T : Expr) : MetaM (Option Ty) := do
  let t ← binderTy T
  return if t == untyped then none else some t
end

def localIndex (x : Expr) : ReadM LExpr := do
  let locals ← read
  match locals.findIdx? (· == x) with
  | some i => return .bvar (locals.size - 1 - i)
  | none => throwError "the term is open: {x}"

def withBinder {α : Type} (n : Name) (T : Expr) (value? : Option Expr) (k : Expr → ReadM α) : ReadM α := do
  match value? with
  | none => withLocalDeclD n T fun x => withReader (·.push x) (k x)
  | some v => withLetDecl n T v fun x => withReader (·.push x) (k x)

mutual
/-- Read a fragment term. -/
partial def readExpr (e : Expr) : ReadM LExpr := do
  tick
  if ← erasable e then return .erased
  match e with
  | .mdata _ b => readExpr b
  | .fvar _ => localIndex e
  | .lit (.natVal n) => return .lit n
  | .lit (.strVal _) => throwError "out of the fragment: a string literal"
  | .lam n T b _ =>
    let A ← binderTy T
    withBinder n T none fun x => return .lam A (← readExpr (b.instantiate1 x))
  | .letE n T v b _ =>
    let A ← binderTy T
    let v' ← readExpr v
    withBinder n T (some v) fun x => return .letE A v' (← readExpr (b.instantiate1 x))
  | .proj S i t =>
    let some _ ← fragmentInductive? S | throwError "out of the fragment: projection of {S}"
    let fields := getStructureFields (← getEnv) S
    let some f := fields[i]? | throwError "a projection out of range"
    return .proj (shortName f) (← readExpr t)
  | .app .. | .const .. => readApp e
  | _ => throwError "out of the fragment: {e}"

partial def readSpine (head : LExpr) (args : Array Expr) : ReadM LExpr := do
  let mut acc := head
  for a in args do acc := .app acc (← readExpr a)
  return acc

partial def resultTy (e : Expr) : ReadM Ty := do
  return (← lowerTy (← inferType e)).getD untyped

/-- An application, by its head. -/
partial def readApp (e : Expr) : ReadM LExpr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const c us := f | do
    readSpine (← readExpr f) args
  let env ← getEnv
  let etaThen (arity : Nat) (k : Array Expr → Array Expr → ReadM LExpr) : ReadM LExpr := do
    if args.size < arity then readExpr (← etaExpand e)
    else k (args.extract 0 arity) (args.extract arity args.size)
  if c == ``Nat.zero then return (← readSpine (.lit 0) args)
  if c == ``Nat.succ then
    return (← etaThen 1 fun a rest => do readSpine (.natSucc (← readExpr a[0]!)) rest)
  if let some op := literalOp? c then
    return (← etaThen 2 fun a rest => do readSpine (.natBin op (← readExpr a[0]!) (← readExpr a[1]!)) rest)
  if c == ``Bool.true then return (← readSpine (.boolLit true) args)
  if c == ``Bool.false then return (← readSpine (.boolLit false) args)
  match env.find? c with
  | some (.recInfo r) =>
    let arity := r.numParams + r.numMotives + r.numMinors + r.numIndices + 1
    etaThen arity fun a rest => do
      let T ← resultTy (mkAppN f a)
      let minors := a.extract (r.numParams + r.numMotives) (r.numParams + r.numMotives + r.numMinors)
      let major ← readExpr a[arity - 1]!
      let ind := r.getMajorInduct
      if ind == ``Nat then
        return (← readSpine (.natRec T (← readExpr minors[0]!) (← readExpr minors[1]!) major) rest)
      if ind == ``Bool then
        return (← readSpine (.boolRec T (← readExpr minors[0]!) (← readExpr minors[1]!) major) rest)
      let some v ← fragmentInductive? ind | throwError "out of the fragment: the recursor {c}"
      let params := a.extract 0 r.numParams
      let arms ← v.ctors.toArray.mapIdxM fun i ctor => do
        let names ← ctorFields ctor us params fun fs => return fs.toList.map (·.1)
        return (shortName ctor, names, ← readExpr minors[i]!)
      if isStructure env ind then
        let some (_, names, minor) := arms[0]? | throwError "a structure without a constructor"
        return (← readSpine (.split names minor major) rest)
      readSpine (.cases T arms.toList major) rest
  | some (.ctorInfo k) =>
    let some v ← fragmentInductive? k.induct | throwError "out of the fragment: the constructor {c}"
    etaThen (k.numParams + k.numFields) fun a rest => do
      let params := a.extract 0 k.numParams
      let names ← ctorFields c us params fun fs => return fs.toList.map (·.1)
      let values ← (a.extract k.numParams a.size).toList.mapM readExpr
      let fields := names.zip values
      if isStructure env v.name then return (← readSpine (.record fields) rest)
      readSpine (.inject (shortName c) fields) rest
  | some (.defnInfo d) =>
    let body := d.value.instantiateLevelParams d.levelParams us
    let b ← readSpecialized body args.toList
    readSpine (.const (toString c) b) args
  | some _ => throwError "out of the fragment: {c} has no kernel value the fragment reduces"
  | none => throwError "unknown constant {c}"

/-- A definition's value read at a use: each leading λ whose argument is a type is let-bound to it,
so the binder types under it are concrete. -/
partial def readSpecialized (v : Expr) (args : List Expr) : ReadM LExpr := do
  match v, args with
  | .lam n T b _, a :: rest =>
    let A ← binderTy T
    let isTy ← (do return (← isType a) || (← isTypeFormer a) : MetaM Bool)
    withBinder n T (if isTy then some a else none) fun x =>
      return .lam A (← readSpecialized (b.instantiate1 x) rest)
  | .mdata _ b, _ => readSpecialized b args
  | _, _ => readExpr v
end

/-- The fuel for one read: the number of nodes read, definitions unfolded included. -/
def budget : Nat := 2000000

/-- **The fragment's reader**: `e` read into Lean-lite, or the reason it is out. -/
def read (e : Expr) : MetaM (Except String LExpr) := do
  try
    let (r, _) ← (readExpr e).run #[] |>.run budget
    return .ok r
  catch ex => return .error (← ex.toMessageData.toString)

/-- **The fragment** (decidable: `read` is a total computation): `e` is in when it reads. -/
def inFragment (e : Expr) : MetaM Bool := do
  match ← read e with
  | .ok _ => return true
  | .error _ => return false

/-- **`lower`**: the fragment term `e` (relative to the environment of the `MetaM` context), lowered
to Core4, or `none` outside the fragment. -/
def lower (e : Expr) : MetaM (Option Obend.Core.Term.Term) := do
  match ← read e with
  | .ok l => return some (lowerT l)
  | .error _ => return none

/-! ## Reading Theorem Decision Procedures (`readTheoremDecider`) -/

/-- Standard axioms permitted in a source theorem prior to `transport`. `sorryAx` and custom axioms
are rejected. -/
def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Quot.sound || n == ``Classical.choice

/-- Synthesize the `Bool`-valued decision expression for proposition `p` in the fragment
(supporting `Eq` and `Ne` on `Nat` and `Bool`, `<`, `≤`, `>`, and `≥` on `Nat`, `And`, `Or`, `Not`,
`Iff`, `True`, `False`, and propositional implication `P → Q`), working even in standalone
`importModules` environments where typeclass extensions are not initialized. -/
partial def synthFragmentDeciderBool (p : Expr) : MetaM Expr := do
  let boolTy := mkConst ``Bool
  let motive := mkLambda `_ .default boolTy boolTy
  let bTrue := mkConst ``Bool.true
  let bFalse := mkConst ``Bool.false
  if let .forallE _ P Q _ := p then
    if (← isProp P) && !Q.hasLooseBVars then
      let dp ← synthFragmentDeciderBool P
      let dq ← synthFragmentDeciderBool Q
      return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bTrue dq dp
  let fn := p.getAppFn
  let args := p.getAppArgs
  if fn.isConstOf ``True && args.size == 0 then
    return bTrue
  if fn.isConstOf ``False && args.size == 0 then
    return bFalse
  if fn.isConstOf ``Eq && args.size == 3 then
    let ty ← whnf args[0]!
    let lhs := args[1]!
    let rhs := args[2]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decEq) lhs rhs
      return mkApp2 (mkConst ``Decidable.decide) p inst
    if ty.isConstOf ``Bool then
      let inst := mkApp2 (mkConst ``Bool.decEq) lhs rhs
      return mkApp2 (mkConst ``Decidable.decide) p inst
  if fn.isConstOf ``Ne && args.size == 3 then
    let eqProp := mkApp3 (mkConst ``Eq fn.constLevels!) args[0]! args[1]! args[2]!
    let dp ← synthFragmentDeciderBool eqProp
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bTrue bFalse dp
  if (fn.isConstOf ``LT.lt && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLt) args[2]! args[3]!
      return mkApp2 (mkConst ``Decidable.decide) p inst
  if (fn.isConstOf ``LE.le && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLe) args[2]! args[3]!
      return mkApp2 (mkConst ``Decidable.decide) p inst
  if (fn.isConstOf ``GT.gt && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLt) args[3]! args[2]!
      return mkApp2 (mkConst ``Decidable.decide) (mkApp2 (mkConst ``Nat.lt) args[3]! args[2]!) inst
  if (fn.isConstOf ``GE.ge && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLe) args[3]! args[2]!
      return mkApp2 (mkConst ``Decidable.decide) (mkApp2 (mkConst ``Nat.le) args[3]! args[2]!) inst
  if fn.isConstOf ``Nat.lt && args.size == 2 then
    let inst := mkApp2 (mkConst ``Nat.decLt) args[0]! args[1]!
    return mkApp2 (mkConst ``Decidable.decide) p inst
  if fn.isConstOf ``Nat.le && args.size == 2 then
    let inst := mkApp2 (mkConst ``Nat.decLe) args[0]! args[1]!
    return mkApp2 (mkConst ``Decidable.decide) p inst
  if fn.isConstOf ``And && args.size == 2 then
    let dp ← synthFragmentDeciderBool args[0]!
    let dq ← synthFragmentDeciderBool args[1]!
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bFalse dq dp
  if fn.isConstOf ``Or && args.size == 2 then
    let dp ← synthFragmentDeciderBool args[0]!
    let dq ← synthFragmentDeciderBool args[1]!
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive dq bTrue dp
  if fn.isConstOf ``Iff && args.size == 2 then
    let dp ← synthFragmentDeciderBool args[0]!
    let dq ← synthFragmentDeciderBool args[1]!
    let eqProp := mkApp3 (mkConst ``Eq [Level.one]) boolTy dp dq
    let inst := mkApp2 (mkConst ``Bool.decEq) dp dq
    return mkApp2 (mkConst ``Decidable.decide) eqProp inst
  if fn.isConstOf ``Not && args.size == 1 then
    let dp ← synthFragmentDeciderBool args[0]!
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bTrue bFalse dp
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  return mkApp2 (mkConst ``Decidable.decide) p inst

/-- Peel leading computational universal quantifiers `∀ (x₁ : A₁) ... (xₖ : Aₖ), P` and synthesize
`Decidable.decide P` at the propositional body `P`. -/
partial def buildDeciderExpr (ty : Expr) : MetaM (Expr × List Ty) := do
  match ty with
  | .forallE n A B bi =>
    let aIsProp ← isProp A
    let aIsType ← isTypeFormerType A
    if !aIsProp && !aIsType then
      let some argTy ← lowerTy A
        | throwError "quantifier domain {A} has no Core4 type in the fragment"
      withLocalDecl n bi A fun x => do
        let (bodyDec, restTys) ← buildDeciderExpr (B.instantiate1 x)
        let lamExpr ← mkLambdaFVars #[x] bodyDec
        return (lamExpr, argTy :: restTys)
    else
      return (← synthFragmentDeciderBool ty, [])
  | _ =>
    return (← synthFragmentDeciderBool ty, [])

/-- **`readTheoremDecider`**: given a theorem or proposition declaration `declName` in the
environment:
1. verifies `declName` has a kernel proof term, is not `unsafe`, and does not depend on `sorryAx` or
   non-standard axioms (`Lean.collectAxioms`),
2. verifies its type is a `Prop`,
3. strips leading computational universal quantifiers and synthesizes `Decidable` for the body, and
4. reads the resulting decision procedure `fun x₁ ... xₖ => decide P` into `LExpr` along with the
   lowered argument types `argTys : List Ty`. -/
def readTheoremDecider (declName : Name) : MetaM (Except String (LExpr × List Ty)) := do
  let env ← getEnv
  let some info := env.find? declName
    | return .error s!"unknown declaration {declName}"
  if info.isUnsafe then
    return .error s!"declaration {declName} is unsafe"
  match info with
  | .thmInfo _ | .defnInfo _ => pure ()
  | .axiomInfo _ => return .error s!"declaration {declName} is an unproved axiom"
  | .opaqueInfo _ => return .error s!"declaration {declName} is opaque"
  | _ => return .error s!"declaration {declName} has no proof term"
  let axioms ← Lean.collectAxioms declName
  for ax in axioms do
    unless allowedAxiom ax do
      return .error s!"declaration {declName} depends on disallowed axiom {ax}"
  let ty := info.type.instantiateLevelParams info.levelParams (info.levelParams.map fun _ => Level.zero)
  unless (← isProp ty) do
    return .error s!"declaration {declName} is not a proposition"
  try
    let (decExpr, argTys) ← buildDeciderExpr ty
    match ← read decExpr with
    | .ok lexpr => return .ok (lexpr, argTys)
    | .error msg => return .error msg
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Obend.Lower.Fragment
end
