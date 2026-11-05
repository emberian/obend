module
/-
# Obend.Run.HyperLaw — G5 Effect Laws: Design C (2-Trace HyperLaws) & Design D (Oracle7 Modal Equilibrium)

Implements `G5` Effect Laws Designs C and D from `review/DECISIONS-LEDGER.md` and
`ASTRA-EFFECT-LAWS-20261031.md` (§4–§5):

1. **Design C (`HyperLaw2` — `k=2` Universal Safety Hyperproperties & Observational Non-Interference)**:
   - A single-trace predicate (`Spec.Legal` or `Fold.Admission`) cannot express relational
     information-flow laws such as observational non-interference ("varying high-security inputs
     does not alter low-security observations across shared/world execution steps").
   - `LowView World Obs` projects the low-observable state (`lowEquiv : LowView World Obs → World → World → Prop`),
     lifts directly to `Obend.Run.Shared.Ledger` records (`LowView.ofSharedLedger`), and checks
     universal 2-trace relational safety via `checkHyperLaw2NonInterference` with proved soundness
     `checkHyperLaw2NonInterference_sound` and a `#tooth` mutation witness refusing a leaking trace pair.

2. **Design D (`Oracle7` — Gelfond-Lifschitz Reduct Modal `□` Epistemic Equilibrium Judge)**:
   - Stratified negation (`Law.Stratified`) forbids recursive cycles through negation (`¬`).
     Unstratified epistemic rules (`head ← posBody ∧ ¬□negBody`, e.g., default/justification rules
     in policy and epistemic equilibrium semantics) are judged via the Gelfond-Lifschitz (GL) reduct:
     given a candidate epistemic belief set `candidate : FactSet`, `glReduct prog candidate`
     evaluates all modal negative literals `¬□b` against `candidate`, yielding a positive Horn
     program whose least Herbrand model (`leastModelFuel`) must equal `candidate` up to set
     equivalence (`checkOracle7Equilibrium`).
   - Instantiates `oracle7Judge : Obend.Judge ModalProgram FactSet` (and registered format
     `oracle7Format : Obend.Judge.Format`) with proved `sound`, `mono`, `complete`, and a `#tooth`
     refusing the unstable self-defeating modal rule `p ← ¬□p` under both `[]` and `["p"]`.
-/
public import Obend.Run.Shared
public import Obend.Judge.Class
public import Obend.Tactic.Tooth
public section

namespace Obend.Run.HyperLaw

set_option autoImplicit false

/-! ## Part I — Design C (`HyperLaw2`): `k=2` Relational Safety Hyperproperties & Non-Interference -/

/-- A low-security observational projection from world states `World` to observations `Obs`. -/
structure LowView (World Obs : Type) where
  observe : World → Obs

/-- Two world states are observationally low-equivalent when their low projections agree. -/
def lowEquiv {World Obs : Type} (V : LowView World Obs) (w₁ w₂ : World) : Prop :=
  V.observe w₁ = V.observe w₂

/-- Decidable check for observational low-equivalence. -/
@[expose] def checkLowEquiv {World Obs : Type} [DecidableEq Obs]
    (V : LowView World Obs) (w₁ w₂ : World) : Bool :=
  decide (V.observe w₁ = V.observe w₂)

theorem checkLowEquiv_sound {World Obs : Type} [DecidableEq Obs]
    {V : LowView World Obs} {w₁ w₂ : World}
    (h : checkLowEquiv V w₁ w₂ = true) :
    lowEquiv V w₁ w₂ := by
  unfold checkLowEquiv lowEquiv at *
  exact of_decide_eq_true h

/-- Lift a raw-world `LowView` to a shared ledger record (`Obend.Run.Shared.Ledger`), observing
    both the low projection of the raw world and the public sequence of committed grants. -/
@[expose] def LowView.ofSharedLedger {ι W Tok Obs : Type}
    (L : Obend.Run.Shared.Ledger ι W Tok) (rawView : LowView W Obs) :
    LowView L.Rec (Obs × List (Obend.Run.Shared.Grant ι Tok)) where
  observe d := (rawView.observe (L.raw d), L.grants d)

/-- Per-step low-equivalence guard (a `#tooth` mutation target) used across a 2-trace execution. -/
@[expose] def checkHyperLaw2Step {World Obs : Type} [DecidableEq Obs]
    (V : LowView World Obs) (p : World × World) : Bool :=
  checkLowEquiv V p.1 p.2

/-- Declarative `k=2` non-interference hyperproperty over a paired 2-trace execution
    `trace : List (World × World)`: if the initial states of the two traces are low-equivalent,
    then every subsequent state pair along the paired execution must remain low-equivalent. -/
def HyperLaw2NonInterference {World Obs : Type}
    (V : LowView World Obs) (trace : List (World × World)) : Prop :=
  match trace with
  | [] => True
  | hd :: rest =>
    lowEquiv V hd.1 hd.2 → ∀ p ∈ rest, lowEquiv V p.1 p.2

/-- Total boolean checker for the `k=2` relational non-interference hyperproperty. -/
@[expose] def checkHyperLaw2NonInterference {World Obs : Type} [DecidableEq Obs]
    (V : LowView World Obs) (trace : List (World × World)) : Bool :=
  match trace with
  | [] => true
  | hd :: rest =>
    if checkLowEquiv V hd.1 hd.2 then
      rest.all (checkHyperLaw2Step V)
    else
      true

/-- Soundness of `checkHyperLaw2NonInterference`: when the checker returns `true`, the 2-trace
    execution satisfies `HyperLaw2NonInterference`. -/
theorem checkHyperLaw2NonInterference_sound {World Obs : Type} [DecidableEq Obs]
    {V : LowView World Obs} {trace : List (World × World)}
    (hok : checkHyperLaw2NonInterference V trace = true) :
    HyperLaw2NonInterference V trace := by
  cases trace with
  | nil => trivial
  | cons hd tl =>
    change (if checkLowEquiv V hd.1 hd.2 = true then tl.all (checkHyperLaw2Step V) else true) = true at hok
    intro hInit p hp
    have hInitBool : checkLowEquiv V hd.1 hd.2 = true := decide_eq_true hInit
    simp only [hInitBool, ite_true] at hok
    have hAll := List.all_eq_true.mp hok p hp
    exact checkLowEquiv_sound hAll

/-- Completeness of `checkHyperLaw2NonInterference` on finite 2-traces. -/
theorem checkHyperLaw2NonInterference_complete {World Obs : Type} [DecidableEq Obs]
    {V : LowView World Obs} {trace : List (World × World)}
    (hNI : HyperLaw2NonInterference V trace) :
    checkHyperLaw2NonInterference V trace = true := by
  cases trace with
  | nil => rfl
  | cons hd tl =>
    change (if checkLowEquiv V hd.1 hd.2 = true then tl.all (checkHyperLaw2Step V) else true) = true
    by_cases hInit : checkLowEquiv V hd.1 hd.2 = true
    · simp only [hInit, ite_true]
      apply List.all_eq_true.mpr
      intro p hp
      have hLow : lowEquiv V p.1 p.2 := hNI (checkLowEquiv_sound hInit) p hp
      exact decide_eq_true hLow
    · have hFalse : checkLowEquiv V hd.1 hd.2 = false := Bool.eq_false_iff.mpr hInit
      rw [hFalse]
      rfl

/-! ### Concrete 2-Trace Non-Interference Fixture & `#tooth` Witness -/

/-- A concrete two-level security world state with a public `lowOut` channel and secret `highIn`. -/
structure SecWorld where
  lowOut : Nat
  highIn : Nat
  deriving DecidableEq, Repr

/-- The low observer sees only `lowOut`, never `highIn`. -/
@[expose] def secLowView : LowView SecWorld Nat where
  observe w := w.lowOut

/-- A safe 2-trace where `highIn` differs (`0` vs `1`) but `lowOut` evolves identically (`10 → 11`). -/
@[expose] def safeTracePair : List (SecWorld × SecWorld) :=
  [(⟨10, 0⟩, ⟨10, 1⟩), (⟨11, 0⟩, ⟨11, 1⟩)]

/-- A leaking 2-trace where `highIn` (`0` vs `1`) flows into `lowOut` at step 1 (`10 → 0` vs `10 → 1`). -/
@[expose] def leakingTracePair : List (SecWorld × SecWorld) :=
  [(⟨10, 0⟩, ⟨10, 1⟩), (⟨0, 0⟩, ⟨1, 1⟩)]

example :
    checkHyperLaw2NonInterference secLowView safeTracePair = true := rfl

theorem leaking_trace_refused :
    checkHyperLaw2NonInterference secLowView leakingTracePair = false := rfl

-- Mutating the per-step low-equivalence guard to ignore leaks causes the leaking trace to pass.
#tooth leaking_trace_refused by mutation checkHyperLaw2Step :=
  fun {_ _} [_] _ _ => true


/-! ## Part II — Design D (`Oracle7`): Gelfond-Lifschitz Modal `□` Epistemic Equilibrium Judge -/

/-- A ground epistemic atom name. -/
abbrev Atom := String

/-- A finite set of ground epistemic atoms. -/
abbrev FactSet := List Atom

/-- An unstratified modal/epistemic rule `head ← posBody ∧ ¬□negBody`.
    Each atom `b ∈ posBody` must be derivable in the current world, while each atom
    `n ∈ negBody` represents a modal negative assumption `¬□n` tested against the candidate
    epistemic equilibrium. -/
structure ModalRule where
  head : Atom
  posBody : List Atom
  negBody : List Atom
  deriving DecidableEq, Repr

/-- A finite modal epistemic logic program. -/
abbrev ModalProgram := List ModalRule

/-- A positive Horn rule produced after eliminating modal negative literals via the
    Gelfond-Lifschitz reduct. -/
structure PosRule where
  head : Atom
  posBody : List Atom
  deriving DecidableEq, Repr

/-- Whether all atoms in `xs` belong to `facts`. -/
@[expose] def allIn (xs : List Atom) (facts : FactSet) : Bool :=
  xs.all (fun a => facts.contains a)

/-- Whether no atom in `xs` belongs to `facts` (used for modal `¬□` preconditions). -/
@[expose] def noneIn (xs : List Atom) (facts : FactSet) : Bool :=
  xs.all (fun a => !facts.contains a)

/-- Set inclusion `xs ⊆ ys` on `FactSet`. -/
@[expose] def factSetSubset (xs ys : FactSet) : Bool :=
  allIn xs ys

/-- Extensional set equivalence on `FactSet` (a `#tooth` mutation target):
    every derived atom is in the candidate and every candidate atom is derived. -/
@[expose] def checkFactSetEquiv (derived candidate : FactSet) : Bool :=
  factSetSubset derived candidate && factSetSubset candidate derived

/-- **Gelfond-Lifschitz Reduct** (`glReduct`): given a modal program `prog` and a candidate
    epistemic belief set `candidate`, drop every rule whose `negBody` intersects `candidate`
    and strip `negBody` from the remaining rules to obtain a positive Horn program. -/
@[expose] def glReduct (prog : ModalProgram) (candidate : FactSet) : List PosRule :=
  prog.filterMap fun r =>
    if noneIn r.negBody candidate then
      some ⟨r.head, r.posBody⟩
    else
      none

/-- One monotone immediate-consequence step `T_P` of a positive Horn program `reduct` over `acc`. -/
@[expose] def stepPosReduct (reduct : List PosRule) (acc : FactSet) : FactSet :=
  reduct.foldl (fun cur r =>
    if allIn r.posBody acc && !cur.contains r.head then
      cur ++ [r.head]
    else
      cur) acc

/-- Fuel-bounded least Herbrand model computation for a positive Horn reduct. -/
@[expose] def leastModelFuel : Nat → List PosRule → FactSet → FactSet
  | 0, _, acc => acc
  | fuel + 1, reduct, acc =>
    let next := stepPosReduct reduct acc
    if factSetSubset next acc then
      acc
    else
      leastModelFuel fuel reduct next

/-- Canonical fuel bound (`prog.length + 1`) sufficient to saturate any positive reduct of `prog`. -/
@[expose] def canonicalFuel (prog : ModalProgram) : Nat :=
  prog.length + 1

/-- Declarative stable epistemic equilibrium (`IsStableEquilibrium`): a candidate `FactSet` equals
    (up to extensional set equivalence) the least Herbrand model of its Gelfond-Lifschitz reduct
    `glReduct prog candidate`, and that least model is closed under the reduct's rules. -/
def IsStableEquilibrium (prog : ModalProgram) (candidate : FactSet) : Prop :=
  let reduct := glReduct prog candidate
  let least := leastModelFuel (canonicalFuel prog) reduct []
  checkFactSetEquiv least candidate = true ∧
    factSetSubset (stepPosReduct reduct least) least = true

/-- Refusal clauses for the `Oracle7` modal equilibrium judge. -/
inductive Oracle7Clause where
  /-- The candidate fact set does not match the least model of its Gelfond-Lifschitz reduct. -/
  | unstableEquilibrium (leastModel : FactSet) (candidate : FactSet)
  /-- The positive reduct did not close within the canonical fuel bound. -/
  | reductNotClosed (leastModel : FactSet)
  deriving DecidableEq, Repr

/-- Total deterministic checker for `Oracle7` modal epistemic equilibrium (`G5` Design D). -/
@[expose] def checkOracle7Equilibrium (_r : Nat) (prog : ModalProgram) (candidate : FactSet) :
    Judge.Verdict Oracle7Clause :=
  let reduct := glReduct prog candidate
  let least := leastModelFuel (canonicalFuel prog) reduct []
  if _hEq : checkFactSetEquiv least candidate = true then
    if _hClosed : factSetSubset (stepPosReduct reduct least) least = true then
      .ok
    else
      .refused (.reductNotClosed least) []
  else
    .refused (.unstableEquilibrium least candidate) []

/-- Soundness of `checkOracle7Equilibrium`: `.ok` establishes `IsStableEquilibrium prog candidate`. -/
theorem checkOracle7Equilibrium_sound {r : Nat} {prog : ModalProgram} {candidate : FactSet}
    (hok : checkOracle7Equilibrium r prog candidate = .ok) :
    IsStableEquilibrium prog candidate := by
  unfold checkOracle7Equilibrium at hok
  dsimp only at hok
  split at hok
  · rename_i hEq
    split at hok
    · rename_i hClosed
      exact ⟨hEq, hClosed⟩
    · cases hok
  · cases hok

/-- Completeness of `checkOracle7Equilibrium`: any `candidate` satisfying `IsStableEquilibrium`
    is accepted at grade `0` (and every higher grade). -/
theorem checkOracle7Equilibrium_complete {prog : ModalProgram} {candidate : FactSet}
    (hEqm : IsStableEquilibrium prog candidate) :
    checkOracle7Equilibrium 0 prog candidate = .ok := by
  rcases hEqm with ⟨hEq, hClosed⟩
  unfold checkOracle7Equilibrium
  dsimp only
  simp only [hEq, hClosed, dite_true]

/-- Monotonicity of `checkOracle7Equilibrium` across grades. -/
theorem checkOracle7Equilibrium_mono {r r' : Nat} {prog : ModalProgram} {candidate : FactSet}
    (_hle : r ≤ r') (_hdec : checkOracle7Equilibrium r prog candidate ≠ .uncovered) :
    checkOracle7Equilibrium r' prog candidate = checkOracle7Equilibrium r prog candidate :=
  rfl

/-- **`oracle7Judge`**: `Obend.Judge` instance for Gelfond-Lifschitz modal `□` epistemic equilibrium. -/
@[expose, instance_reducible] def oracle7Judge : Obend.Judge ModalProgram FactSet where
  Clause := Oracle7Clause
  Meaning := IsStableEquilibrium
  check := checkOracle7Equilibrium
  sound := checkOracle7Equilibrium_sound
  refutes _ := false
  refuted _ h := by cases h
  Fragment _ := True
  complete _ := by
    rintro ⟨cand, hEqm⟩
    exact ⟨cand, 0, checkOracle7Equilibrium_complete hEqm⟩
  mono := checkOracle7Equilibrium_mono

instance : Obend.Judge ModalProgram FactSet := oracle7Judge

/-! ### Self-Defeating Modal Fixture (`p ← ¬□p`), Stratified Default Fixture & `#tooth` Witness -/

/-- The classic self-defeating unstratified modal program `p ← ¬□p`:
    - If `candidate = []`, `¬□p` holds so the GL reduct is `p ← ⊤` with least model `["p"] ≠ []`.
    - If `candidate = ["p"]`, `¬□p` fails so the GL reduct is empty with least model `[] ≠ ["p"]`.
    Hence `selfDefeatingModalProg` has no stable equilibrium and must be refused on both candidates. -/
@[expose] def selfDefeatingModalProg : ModalProgram :=
  [⟨"p", [], ["p"]⟩]

/-- A well-founded default modal program: `fly ← bird ∧ ¬□abnormal`, `bird ← ⊤`.
    Its unique stable epistemic equilibrium is `["bird", "fly"]`. -/
@[expose] def defaultBirdProg : ModalProgram :=
  [⟨"bird", [], []⟩, ⟨"fly", ["bird"], ["abnormal"]⟩]

example :
    checkOracle7Equilibrium 1 defaultBirdProg ["bird", "fly"] = .ok := rfl

theorem self_defeating_modal_refused_on_p :
    checkOracle7Equilibrium 1 selfDefeatingModalProg ["p"] =
      .refused (.unstableEquilibrium [] ["p"]) [] := rfl

theorem self_defeating_modal_refused_on_empty :
    checkOracle7Equilibrium 1 selfDefeatingModalProg [] =
      .refused (.unstableEquilibrium ["p"] []) [] := rfl

-- Mutating the fixed-point equivalence check to `true` causes the unstable self-defeating
-- candidate `["p"]` for `p ← ¬□p` to be falsely accepted as `.ok`.
#tooth self_defeating_modal_refused_on_p by mutation checkFactSetEquiv :=
  fun _ _ => true

/-- Registered `Obend.Judge.Format` for `oracle7-gl-equilibrium` v`1`. -/
@[expose] def oracle7Format : Obend.Judge.Format where
  name := "oracle7-gl-equilibrium"
  version := "1"
  Obj := ModalProgram
  Cert := FactSet
  judge := oracle7Judge
  decodeObj s :=
    if s == "self-defeating" then .ok selfDefeatingModalProg
    else if s == "default-bird" then .ok defaultBirdProg
    else .error s!"unknown modal program wire id: {s}"
  decodeCert s :=
    if s == "" then .ok []
    else .ok (s.splitOn "," |>.map (·.trimAscii.toString))
  trust := .kernel
  regime := .decidable
  bad := (selfDefeatingModalProg, ["p"])
  badGrade := 1
  bad_refused := ⟨Oracle7Clause.unstableEquilibrium [] ["p"], [], rfl⟩

end Obend.Run.HyperLaw
end
