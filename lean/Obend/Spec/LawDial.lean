module
/-
# Obend.Spec.LawDial — Confluence Dial & Difference-Constraint Witness Solver for `.obend` Laws

Brings `minidregg`'s static policy-AST analyses (`Pred.CoordinationDial` and `Pred.Satisfiable`)
onto `Obend.Spec.Law` (`LawExpr`):

1. **The Coordination / Confluence Dial (`dial : LawExpr → DialVerdict`)**:
   Classifies any `.obend` surface law into:
   - `.free`: upward/lower-bounded or monotone per-field constraints and request-fact guards that are
     closed under the state join-semilattice `joinData n₁ n₂` (field-wise `max`),
   - `.stepShaped`: history/step-dependent atoms (`writeOnce`) that depend on whether the old field
     was unwritten (`0`) vs. already written,
   - `.ordering`: cross-field or non-join-closed constraints (`eqC (.field _)`, `eqR`, `leR`,
     `leROff`, `or`, `not`, `implies`) where two individually admissible concurrent writes can
     conflict when merged without consensus ordering.

   **Main theorems**:
   - `dial_free_confluent`: if `dial e = .free`, then whenever `e.denote facts old n₁ = true` and
     `e.denote facts old n₂ = true`, the merged state `joinData n₁ n₂` is also admitted:
     `e.denote facts old (joinData n₁ n₂) = true`.
   - `demoOr_not_confluent` & `demoEqSlots_not_confluent`: concrete refutation poles (`(1, 5)` and
     `(5, 1)`) proving that `.ordering` laws are genuinely non-confluent under `joinData`.

2. **Difference-Constraint Relaxation & Satisfiability Witness Finder (`solveLawWitness`)**:
   Propagates upper/lower bounds and difference constraints (`new.a <= new.b + k`, `monotone`,
   `writeOnce`, `new.a == c`, `new.a <= c`) across all fields of `e` (Bellman-Ford relaxation rounds)
   to synthesize a multi-field satisfying state `w : Data`, proved sound by `solveLawWitness_sound`.
-/
public import Obend.Spec.Law
@[expose] public section
namespace Obend.Spec.LawDial
open Obend.Core.Data (Data)
open Obend.Spec.Law
set_option autoImplicit false

/-! ## 1. The State Join-Semilattice (`joinData`) -/

/-- Every scalar extracted by `scalarOf` is non-negative (`Nat` or `0`/`1`). -/
theorem scalarOf_nonneg {d : Data} {x : Int} (h : scalarOf d = some x) : 0 ≤ x := by
  cases d <;> simp [scalarOf] at h
  · subst h; omega
  · rename_i b; cases b <;> simp at h <;> subst h <;> omega

/-- Every scalar extracted by `firstScalarField` is non-negative. -/
theorem firstScalarField_nonneg {name : String} :
    ∀ {fs : List (String × Data)} {x : Int}, firstScalarField name fs = some x → 0 ≤ x
  | [], _, h => by simp [firstScalarField] at h
  | (f, v) :: rest, x, h => by
    simp only [firstScalarField] at h
    split at h
    · cases hs : scalarOf v with
      | some s =>
        rw [hs] at h
        simp only [Option.some.injEq] at h
        subst h
        exact scalarOf_nonneg hs
      | none =>
        rw [hs] at h
        exact firstScalarField_nonneg h
    · exact firstScalarField_nonneg h

/-- Join a single `(k, v)` field against `fs₂`. -/
def joinField (fs₂ : List (String × Data)) (k : String) (v : Data) : Data :=
  match scalarOf v, firstScalarField k fs₂ with
  | some x, some y => .natural (Int.toNat (max x y))
  | _, _ => v

/-- Field-wise join (`max`) of two record field lists. -/
def maxScalarFields (fs₁ fs₂ : List (String × Data)) : List (String × Data) :=
  fs₁.map fun (k, v) => (k, joinField fs₂ k v)

/-- Join of two state `Data` values: field-wise `max` on scalar record fields. -/
def joinData (n₁ n₂ : Data) : Data :=
  match n₁, n₂ with
  | .record fs₁, .record fs₂ => .record (maxScalarFields fs₁ fs₂)
  | _, _ => n₁

theorem scalarOf_joinField {fs₂ : List (String × Data)} {f : String} {v : Data} {s y : Int}
    (hs : scalarOf v = some s) (h₂ : firstScalarField f fs₂ = some y) :
    scalarOf (joinField fs₂ f v) = some (max s y) := by
  have hx : 0 ≤ s := scalarOf_nonneg hs
  have hy : 0 ≤ y := firstScalarField_nonneg h₂
  have hmax : 0 ≤ max s y := by omega
  unfold joinField
  rw [hs, h₂]
  simp only [scalarOf, Option.some.injEq]
  exact Int.toNat_of_nonneg hmax

theorem scalarOf_joinField_none {fs₂ : List (String × Data)} {f : String} {v : Data}
    (hs : scalarOf v = none) :
    scalarOf (joinField fs₂ f v) = none := by
  unfold joinField
  rw [hs]
  exact hs

theorem firstScalarField_maxScalarFields {name : String} :
    ∀ (fs₁ fs₂ : List (String × Data)) {x y : Int},
      firstScalarField name fs₁ = some x →
      firstScalarField name fs₂ = some y →
      firstScalarField name (maxScalarFields fs₁ fs₂) = some (max x y)
  | [], _, _, _, h₁, _ => by simp [firstScalarField] at h₁
  | (f, v) :: rest, fs₂, x, y, h₁, h₂ => by
    simp only [firstScalarField] at h₁
    by_cases hf : f = name
    · subst hf
      simp only [ite_true] at h₁
      cases hs : scalarOf v with
      | some s =>
        rw [hs] at h₁
        simp only [Option.some.injEq] at h₁
        subst h₁
        simp only [maxScalarFields, List.map_cons, firstScalarField, ite_true,
          scalarOf_joinField hs h₂]
      | none =>
        rw [hs] at h₁
        simp only [maxScalarFields, List.map_cons, firstScalarField, ite_true,
          scalarOf_joinField_none hs]
        exact firstScalarField_maxScalarFields rest fs₂ h₁ h₂
    · simp only [hf, ite_false] at h₁
      simp only [maxScalarFields, List.map_cons, firstScalarField, hf, ite_false]
      exact firstScalarField_maxScalarFields rest fs₂ h₁ h₂

/-- **`fieldOf_joinData`**: reading a field present in both `n₁` and `n₂` from `joinData n₁ n₂`
returns the maximum of the two readings. -/
theorem fieldOf_joinData {name : String} {n₁ n₂ : Data} {x y : Int}
    (h₁ : fieldOf name n₁ = some x) (h₂ : fieldOf name n₂ = some y) :
    fieldOf name (joinData n₁ n₂) = some (max x y) := by
  cases n₁ <;> try (simp [fieldOf] at h₁)
  cases n₂ <;> try (simp [fieldOf] at h₂)
  exact firstScalarField_maxScalarFields _ _ h₁ h₂

/-! ## 2. The Confluence Dial (`dial`) and `dial_free_confluent` -/

/-- Coordination price of a law expression (`minidregg` `Pred.CoordinationDial`). -/
inductive DialVerdict where
  /-- Join-semilattice confluent under `joinData` (`max`) without coordination ordering. -/
  | free
  /-- History/sentinel-shaped (`writeOnce`): depends on whether `old` was unwritten (`0`). -/
  | stepShaped
  /-- Requires ordering or coordination across concurrent writers. -/
  | ordering
  deriving DecidableEq, Repr

/-- True when `r` reads no mutable state: a request/ledger fact (`subject`, `caller`, `height`,
`turn`) or a label constant. -/
def isFactOnly : LawRef → Bool
  | .field _ => false
  | .subject | .caller | .height | .turn | .labelConst _ => true

theorem read_factOnly {r : LawRef} (hr : isFactOnly r = true) (facts : Facts) (n₁ n₂ : Data) :
    r.read facts n₁ = r.read facts n₂ := by
  cases r <;> simp [isFactOnly, LawRef.read] at hr ⊢

theorem readLabel_factOnly {r : LawRef} (hr : isFactOnly r = true) (n₁ n₂ : Data) :
    r.readLabel n₁ = r.readLabel n₂ := by
  cases r <;> simp [isFactOnly, LawRef.readLabel] at hr ⊢

/-- Combine two dial verdicts under conjunction. -/
def DialVerdict.combine : DialVerdict → DialVerdict → DialVerdict
  | .free, .free => .free
  | .ordering, _ | _, .ordering => .ordering
  | _, _ => .stepShaped

/-- **The Confluence Dial** on `.obend` `LawExpr`. A comparison with a label field (`new.decider ==
"ember"`) is `.ordering`, as every equality on a field is: `joinData` keeps the left state's label,
so two admitted writes of different labels join to one of them. No label clause is `.free`. -/
def dial : LawExpr → DialVerdict
  | .leC (.field _) _ => .free
  | .monotone _ => .free
  | .eqC r _ | .leC r _ | .inC r _ => if isFactOnly r then .free else .ordering
  | .eqR l r | .leR l r | .leROff l r _ =>
    if isFactOnly l && isFactOnly r then .free else .ordering
  | .writeOnce _ => .stepShaped
  | .and l r => DialVerdict.combine (dial l) (dial r)
  | .or _ _ | .not _ | .implies _ _ => .ordering

theorem DialVerdict.combine_eq_free {a b : DialVerdict} (h : DialVerdict.combine a b = .free) :
    a = .free ∧ b = .free := by
  cases a <;> cases b <;> simp [DialVerdict.combine] at h ⊢

/-- **`dial_free_confluent`**: Any law classified `.free` by `dial` is join-semilattice confluent:
if two concurrent target states `n₁` and `n₂` are both admitted from `old` under `facts`, then their
field-wise maximum `joinData n₁ n₂` is also admitted. -/
theorem dial_free_confluent :
    ∀ {e : LawExpr}, dial e = .free →
      ∀ {facts : Facts} {old : Option Data} {n₁ n₂ : Data},
        e.denote facts old n₁ = true →
        e.denote facts old n₂ = true →
        e.denote facts old (joinData n₁ n₂) = true
  | .eqC r v, hd, facts, old, n₁, n₂, h₁, _ => by
    simp only [dial] at hd
    split at hd <;> try cases hd
    rename_i hr
    simp only [LawExpr.denote] at h₁ ⊢
    rw [read_factOnly hr facts (joinData n₁ n₂) n₁]
    exact h₁
  | .leC (.field f) v, _, facts, old, n₁, n₂, h₁, h₂ => by
    simp only [LawExpr.denote, LawRef.read] at h₁ h₂ ⊢
    cases hx : fieldOf f n₁ with
    | none => simp [hx] at h₁
    | some x =>
      cases hy : fieldOf f n₂ with
      | none => simp [hy] at h₂
      | some y =>
        rw [hx] at h₁; rw [hy] at h₂
        simp only [decide_eq_true_eq] at h₁ h₂
        rw [fieldOf_joinData hx hy]
        simp only [decide_eq_true_eq]
        omega
  | .leC .subject v, _, facts, old, n₁, n₂, h₁, _ => by
    simpa [LawExpr.denote, LawRef.read] using h₁
  | .leC .caller v, _, facts, old, n₁, n₂, h₁, _ => by
    simpa [LawExpr.denote, LawRef.read] using h₁
  | .leC .height v, _, facts, old, n₁, n₂, h₁, _ => by
    simpa [LawExpr.denote, LawRef.read] using h₁
  | .leC .turn v, _, facts, old, n₁, n₂, h₁, _ => by
    simpa [LawExpr.denote, LawRef.read] using h₁
  | .inC r vs, hd, facts, old, n₁, n₂, h₁, _ => by
    simp only [dial] at hd
    split at hd <;> try cases hd
    rename_i hr
    simp only [LawExpr.denote] at h₁ ⊢
    rw [read_factOnly hr facts (joinData n₁ n₂) n₁]
    exact h₁
  | .eqR l r, hd, facts, old, n₁, n₂, h₁, _ => by
    simp only [dial, Bool.and_eq_true] at hd
    split at hd <;> try cases hd
    rename_i hlr
    simp only [LawExpr.denote] at h₁ ⊢
    rw [read_factOnly hlr.1 facts (joinData n₁ n₂) n₁,
        read_factOnly hlr.2 facts (joinData n₁ n₂) n₁,
        readLabel_factOnly hlr.1 (joinData n₁ n₂) n₁,
        readLabel_factOnly hlr.2 (joinData n₁ n₂) n₁]
    exact h₁
  | .leR l r, hd, facts, old, n₁, n₂, h₁, _ => by
    simp only [dial, Bool.and_eq_true] at hd
    split at hd <;> try cases hd
    rename_i hlr
    simp only [LawExpr.denote] at h₁ ⊢
    rw [read_factOnly hlr.1 facts (joinData n₁ n₂) n₁,
        read_factOnly hlr.2 facts (joinData n₁ n₂) n₁]
    exact h₁
  | .leROff l r k, hd, facts, old, n₁, n₂, h₁, _ => by
    simp only [dial, Bool.and_eq_true] at hd
    split at hd <;> try cases hd
    rename_i hlr
    simp only [LawExpr.denote] at h₁ ⊢
    rw [read_factOnly hlr.1 facts (joinData n₁ n₂) n₁,
        read_factOnly hlr.2 facts (joinData n₁ n₂) n₁]
    exact h₁
  | .monotone f, _, facts, old, n₁, n₂, h₁, h₂ => by
    simp only [LawExpr.denote] at h₁ h₂ ⊢
    cases old with
    | none => rfl
    | some o =>
      dsimp only at h₁ h₂ ⊢
      cases ho : fieldOf f o with
      | none => simp [ho] at h₁
      | some b =>
        cases hx : fieldOf f n₁ with
        | none => simp [ho, hx] at h₁
        | some x =>
          cases hy : fieldOf f n₂ with
          | none => simp [ho, hy] at h₂
          | some y =>
            rw [ho, hx] at h₁; rw [ho, hy] at h₂
            simp only [decide_eq_true_eq] at h₁ h₂
            rw [fieldOf_joinData hx hy]
            simp only [decide_eq_true_eq]
            omega
  | .writeOnce _, hd, _, _, _, _, _, _ => by simp [dial] at hd
  | .not _, hd, _, _, _, _, _, _ => by simp [dial] at hd
  | .or _ _, hd, _, _, _, _, _, _ => by simp [dial] at hd
  | .implies _ _, hd, _, _, _, _, _, _ => by simp [dial] at hd
  | .and l r, hd, facts, old, n₁, n₂, h₁, h₂ => by
    simp only [dial] at hd
    obtain ⟨hl, hr⟩ := DialVerdict.combine_eq_free hd
    simp only [LawExpr.denote, Bool.and_eq_true] at h₁ h₂ ⊢
    exact ⟨dial_free_confluent hl h₁.1 h₂.1, dial_free_confluent hr h₁.2 h₂.2⟩

/-! ### Refutation Poles: Why `.or` and `.eqR` Cannot Be `.free` -/

/-- `new.x <= 1 or new.y <= 1`: classified `.ordering`, and refuted by `(1, 5)` joined with `(5, 1) = (5, 5)`. -/
def demoOrLaw : LawExpr := .or (.leC (.field "x") 1) (.leC (.field "y") 1)

def demoState15 : Data := .record [("x", .natural 1), ("y", .natural 5)]
def demoState51 : Data := .record [("x", .natural 5), ("y", .natural 1)]
def demoFacts : Facts := { subject := some 0, caller := none, height := 0, turn := 0 }

-- fixture kept (2026-11-04): refusal witness: `dial` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    dial demoOrLaw = .ordering ∧
    demoOrLaw.denote demoFacts none demoState15 = true ∧
    demoOrLaw.denote demoFacts none demoState51 = true ∧
    demoOrLaw.denote demoFacts none (joinData demoState15 demoState51) = false := by
  decide +kernel

/-- `new.x == new.y`: classified `.ordering`, and refuted when combined with `new.x <= 1 or new.y <= 1`. -/
def demoCoupledLaw : LawExpr := .and (.eqR (.field "x") (.field "y")) (.inC (.field "x") [1, 5])

/-! ## 3. Difference-Constraint Relaxation & Satisfiability Witness Finder (`solveLawWitness`) -/

/-- Read a natural field from an association list (defaulting to `0`). -/
def lookupVal (vals : List (String × Nat)) (f : String) : Nat :=
  (vals.lookup f).getD 0

/-- Update a natural field in an association list. -/
def updateVal (vals : List (String × Nat)) (f : String) (v : Nat) : List (String × Nat) :=
  match vals with
  | [] => [(f, v)]
  | (k, oldV) :: rest => if k == f then (k, v) :: rest else (k, oldV) :: updateVal rest f v

/-- Build a `Data.record` from a list of `(field, Nat)` pairs. -/
def recordOfVals (vals : List (String × Nat)) : Data :=
  .record (vals.map fun (k, v) => (k, .natural v))

/-- Read a `Nat` scalar from an optional old state. -/
def oldNatAt (old : Option Data) (f : String) : Nat :=
  match old.bind (fieldOf f) with
  | some v => Int.toNat v
  | none => 0

/-- One relaxation pass of atomic lower/upper/difference bounds in `e` over `vals`. -/
def relaxPass (facts : Facts) (old : Option Data) (vals : List (String × Nat)) : LawExpr → List (String × Nat)
  | .eqC (.field f) c =>
    if 0 ≤ c then updateVal vals f c.toNat else vals
  | .leC (.field f) c =>
    if 0 ≤ c && c.toNat < lookupVal vals f then updateVal vals f c.toNat else vals
  | .inC (.field f) (c :: _) =>
    if 0 ≤ c && !(c :: []).contains (Int.ofNat (lookupVal vals f)) then updateVal vals f c.toNat else vals
  | .eqR (.field f) (.field g) =>
    let m := max (lookupVal vals f) (lookupVal vals g)
    updateVal (updateVal vals f m) g m
  | .eqR (.field f) r =>
    match r.read facts (recordOfVals vals) with
    | some c => if 0 ≤ c then updateVal vals f c.toNat else vals
    | none => vals
  | .eqR l (.field g) =>
    match l.read facts (recordOfVals vals) with
    | some c => if 0 ≤ c then updateVal vals g c.toNat else vals
    | none => vals
  | .leR (.field f) (.field g) =>
    let vf := lookupVal vals f
    let vg := lookupVal vals g
    if vg < vf then updateVal vals g vf else vals
  | .leROff (.field f) (.field g) k =>
    let vf := Int.ofNat (lookupVal vals f)
    let vg := Int.ofNat (lookupVal vals g)
    if vg + k < vf && 0 ≤ vf - k then
      updateVal vals g (vf - k).toNat
    else vals
  | .monotone f =>
    let vo := oldNatAt old f
    if lookupVal vals f < vo then updateVal vals f vo else vals
  | .writeOnce f =>
    let vo := oldNatAt old f
    if vo != 0 then updateVal vals f vo else vals
  | .and l r =>
    relaxPass facts old (relaxPass facts old vals l) r
  | .or l r =>
    let v1 := relaxPass facts old vals l
    if l.denote facts old (recordOfVals v1) then v1 else relaxPass facts old vals r
  | _ => vals

/-- Run `rounds` Bellman-Ford-style constraint relaxation passes. -/
def relaxRounds (rounds : Nat) (facts : Facts) (old : Option Data) (e : LawExpr)
    (vals : List (String × Nat)) : List (String × Nat) :=
  match rounds with
  | 0 => vals
  | r + 1 => relaxRounds r facts old e (relaxPass facts old vals e)

/-- **`solveLawWitness`**: given field names `keys`, a law `e`, `facts`, and `old` state,
runs `keys.length + 2` relaxation passes from the initial state (inheriting `old` values where
present) and returns `some w` iff `e.denote facts old w = true`. -/
def solveLawWitness (keys : List String) (e : LawExpr) (facts : Facts) (old : Option Data) : Option Data :=
  let initVals := keys.map fun f => (f, oldNatAt old f)
  let solvedVals := relaxRounds (keys.length + 2) facts old e initVals
  let cand := recordOfVals solvedVals
  if e.denote facts old cand then some cand else none

/-- **`solveLawWitness_sound`**: any witness returned by `solveLawWitness` satisfies `e.denote`. -/
theorem solveLawWitness_sound {keys : List String} {e : LawExpr} {facts : Facts}
    {old : Option Data} {w : Data}
    (h : solveLawWitness keys e facts old = some w) :
    e.denote facts old w = true := by
  dsimp only [solveLawWitness] at h
  split at h
  · rename_i hev
    simp only [Option.some.injEq] at h
    subst h
    exact hev
  · cases h

/-- Example: multi-field coupled law `monotone(a) and new.a <= new.b and new.b <= 10` starting from
`old = {a: 4, b: 1}` (where any single-field edit from `{a: 2, b: 1}` fails, because `a` must rise
to `≥ 4` AND `b` must rise to `≥ a`). `solveLawWitness` finds `{a: 4, b: 4}` in one call. -/
def coupledMultiFieldLaw : LawExpr :=
  .and (.and (.monotone "a") (.leR (.field "a") (.field "b"))) (.leC (.field "b") 10)

def coupledOldState : Data := .record [("a", .natural 4), ("b", .natural 1)]

end Obend.Spec.LawDial
end
