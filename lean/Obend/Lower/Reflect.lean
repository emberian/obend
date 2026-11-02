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

/-- Structural byte-list equality on `String` (avoids `String.decEq` / `Classical.choice`). -/
def strEq (a b : String) : Bool :=
  List.beq a.toUTF8.data.toList b.toUTF8.data.toList

/-- Structural lookup by `strEq`. -/
def lookupByStr {α : Type} (k : String) : List (String × α) → Option α
  | [] => none
  | (m, v) :: rest => if strEq k m then some v else lookupByStr k rest

/-- Deterministic numeric encoding of surface labels for `.label`, `.inject`, and `.case`. -/
def labelToNat (s : String) : Nat :=
  s.toUTF8.data.toList.foldl (fun acc b => acc * 257 + b.toNat + 1) 0

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

/-- **Soundness of lowered `.extend` field projection**:
    Projecting an updated head field `(m, v)` from `lowerExtend` with an unpermuted layout
    steps in one `SStep.projRecord` to `v`. -/
theorem lowerExtend_proj_head_step (env : LayoutEnv) (hempty : env.fields = [])
    (baseLow : LExpr) (m : String) (v : LExpr) (rest : List (String × LExpr)) :
    Obend.Lower.SStep (.proj m (lowerExtend env baseLow ((m, v) :: rest))) v := by
  unfold lowerExtend canonicalizeFields
  simp [hempty]
  exact .projRecord m _ v (by simp)

/-- **Soundness of lowered `.split` on a record**:
    When `targetLow = .record fields` and `splitValues fields names = some values`,
    `LExpr.split names fnLow (.record fields)` steps in one `SStep.splitRecord` to `fnLow.spine values`. -/
theorem lowerSplit_record_step (names : List String) (fnLow : LExpr)
    (fields : List (String × LExpr)) (values : List LExpr)
    (hsplit : Obend.Core.Term.splitValues fields names = some values) :
    Obend.Lower.SStep (.split names fnLow (.record fields)) (fnLow.spine values) :=
  .splitRecord names fnLow fields values hsplit

end Obend.Lower.Reflect
end
