module
/-
# Obend.Law.Fold — the law judge over a log of writes, as an audited fold read at consensus time

The second instance of `Obend.Fold.Admission` (`Legal` is the first, `Obend.Run.Fold`), to show the
structure is not shaped around `Legal`. The world component is the ledger's CONSENSUS
(`Obend.Law.Consensus`: the height); the accumulator's rest is the object's current value. A row is
a write `(new, submission)`: the submission is sealed at the world's consensus (`sealAt`: the
request's height is the ledger's; a claim of a height the ledger has not reached is refused
`future`), and the sealed request is judged by the machine's verdict on the law (`Obend.Law.judge`)
from the current value; an accepted write makes `new` the current value. The one world-move row is
`tick c`, the ledger reaching consensus `c` (never backwards).

A write reads one fact: the ledger's height (`HeightIs`). So a receipt of a write opens the height it
was judged at, and `receipt_sufficient` is not trivial: a stranger re-judges the write at any world
agreeing with that opening.

- `write_reads_height`: the request a write is judged with carries the world's height.
- `write_claim_irrelevant`: two writes whose submissions differ only in the height they claim, both
  accepted, reach the same value.
- `write_future_refused`: a submission claiming a height the ledger has not reached is refused,
  naming the claim and the ledger's height, whatever the law.
-/
public import Obend.Fold
public import Obend.Law.Machine
@[expose] public section

namespace Obend.Law

open Obend.Core.Term (Term)
open Obend.Core.Data (Data Budget)
open Obend.Core.Machine (State Limits)

/-- Why a write was refused: the law's reason, no verdict within the limits, a claim from the future,
or a tick backwards. -/
inductive WriteRefusal where
  | refused (why : String)
  | noVerdict
  | future (claimed current : Nat)
  | heightBack (current proposed : Nat)
  deriving DecidableEq, Repr

/-- The one fact a write reads: the ledger's height is `n`. -/
structure HeightIs where
  n : Nat
  deriving DecidableEq, Repr

/-- A row of the law's fold. -/
inductive LawRow where
  /-- write `new` under the submission -/
  | write (new : Data) (sub : Submission)
  /-- the ledger reaches consensus `c` -/
  | tick (c : Consensus)

/-- One write of a sealed request, judged at the current value. -/
def judgeWrite (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term) (old new rq : Data) :
    Except WriteRefusal Data :=
  match judge policy limits budget law old new rq with
  | some .ok => .ok new
  | some (.refused why) => .error (.refused why)
  | none => .error .noVerdict

/-- One row, at the ledger's consensus `c` and the current value. -/
def lawStep (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term) (a : Consensus × Data) :
    LawRow → Except WriteRefusal (Consensus × Data)
  | .write new sub =>
    match sealAt a.1 sub with
    | .error (.futureHeight h c) => .error (.future h c)
    | .ok rq => (judgeWrite policy limits budget law a.2 new rq).map fun d => (a.1, d)
  | .tick c => if a.1.height ≤ c.height then .ok (c, a.2) else .error (.heightBack a.1.height c.height)

/-- **The law judge as an audited fold** over writes, read at the ledger's consensus. -/
def lawAdmission (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term) :
    Obend.Fold.Admission Consensus Data LawRow HeightIs WriteRefusal where
  step := lawStep policy limits budget law
  reads a
    | .write .. => [⟨a.1.height⟩]
    | .tick _ => []
  look c f := c.height == f.n
  moves
    | .write .. => false
    | .tick _ => true
  observe := .tick
  allowed c c' := decide (c.height ≤ c'.height)
  keeps_world a r b hm h := by
    cases r with
    | tick c => cases hm
    | write new sub =>
      simp only [lawStep] at h
      split at h
      · cases h
      · rename_i rq _
        cases hj : judgeWrite policy limits budget law a.2 new rq with
        | error e => rw [hj] at h; cases h
        | ok d => rw [hj] at h; cases h; rfl
  step_of_reads a w' r hm hr := by
    cases r with
    | tick c => cases hm
    | write new sub =>
      have h := hr ⟨a.1.height⟩ (by simp)
      simp only [beq_self_eq_true, beq_iff_eq] at h
      rcases a with ⟨⟨n⟩, d⟩
      rcases w' with ⟨n'⟩
      have h' : n' = n := by simpa using h.symm
      subst h'
      simp only [lawStep]
      split
      · rfl
      · rename_i rq _
        cases judgeWrite policy limits budget law d new rq <;> rfl
  observe_ok w w' l ha := by
    simp only [decide_eq_true_eq] at ha
    simp [lawStep, ha]

/-- **A write is judged with the ledger's height**: when it is accepted, the request the law judged
is the submission sealed at the world's consensus, whose `height` is the ledger's. -/
theorem write_reads_height {policy : State → Bool} {limits : Limits} {budget : Budget} {law : Term}
    {a : Consensus × Data} {new : Data} {sub : Submission} {b : Consensus × Data}
    (h : lawStep policy limits budget law a (.write new sub) = .ok b) :
    ∃ rq, sealAt a.1 sub = .ok rq ∧ rq.field "height" = some (.natural a.1.height) ∧
      judgeWrite policy limits budget law a.2 new rq = .ok b.2 := by
  simp only [lawStep] at h
  split at h
  · cases h
  · rename_i rq hs
    refine ⟨rq, hs, seal_height hs, ?_⟩
    cases hj : judgeWrite policy limits budget law a.2 new rq with
    | error e => rw [hj] at h; cases h
    | ok d => rw [hj] at h; cases h; rfl

/-- **The claimed height is irrelevant**: two writes whose submissions differ only in the height they
claim, both accepted, reach the same value. -/
theorem write_claim_irrelevant {policy : State → Bool} {limits : Limits} {budget : Budget} {law : Term}
    {a : Consensus × Data} {new : Data} {sub : Submission} {h h' : Option Nat} {b b' : Consensus × Data}
    (hb : lawStep policy limits budget law a (.write new { sub with seen := h }) = .ok b)
    (hb' : lawStep policy limits budget law a (.write new { sub with seen := h' }) = .ok b') : b = b' := by
  obtain ⟨rq, hs, _, hj⟩ := write_reads_height hb
  obtain ⟨rq', hs', _, hj'⟩ := write_reads_height hb'
  have := seal_claim_irrelevant hs hs'
  subst this
  have h1 : b.1 = a.1 := by
    simp only [lawStep, hs] at hb
    obtain ⟨d, _, rfl⟩ : ∃ d, judgeWrite policy limits budget law a.2 new rq = .ok d ∧ (a.1, d) = b := by
      cases hj2 : judgeWrite policy limits budget law a.2 new rq with
      | error e => rw [hj2] at hb; cases hb
      | ok d => rw [hj2] at hb; cases hb; exact ⟨d, rfl, rfl⟩
    rfl
  have h1' : b'.1 = a.1 := by
    simp only [lawStep, hs'] at hb'
    obtain ⟨d, _, rfl⟩ : ∃ d, judgeWrite policy limits budget law a.2 new rq = .ok d ∧ (a.1, d) = b' := by
      cases hj2 : judgeWrite policy limits budget law a.2 new rq with
      | error e => rw [hj2] at hb'; cases hb'
      | ok d => rw [hj2] at hb'; cases hb'; exact ⟨d, rfl, rfl⟩
    rfl
  have h2 : b.2 = b'.2 := Except.ok.inj (hj.symm.trans hj')
  exact Prod.ext (h1.trans h1'.symm) h2

/-- **A claim from the future is refused**, naming the claim and the ledger's height, before any
law runs. -/
theorem write_future_refused (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term)
    (a : Consensus × Data) (new : Data) {sub : Submission} {h : Nat} (hs : sub.seen = some h)
    (hlt : a.1.height < h) :
    lawStep policy limits budget law a (.write new sub) = .error (.future h a.1.height) := by
  simp only [lawStep, seal_future hs hlt]

/-- The fold accepts a log of writes exactly when each, sealed at the ledger's consensus, is judged
`ok` from the value the previous ones left. -/
theorem lawAdmission_run_cons (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term)
    (c : Consensus) (old new : Data) (sub : Submission) (rest : List LawRow) :
    (lawAdmission policy limits budget law).run (c, old) (.write new sub :: rest) =
      match sealAt c sub with
      | .error (.futureHeight h c') => .error (.future h c')
      | .ok rq =>
        match judge policy limits budget law old new rq with
        | some .ok => (lawAdmission policy limits budget law).run (c, new) rest
        | some (.refused why) => .error (.refused why)
        | none => .error .noVerdict := by
  simp only [Obend.Fold.Admission.run, List.foldlM_cons, lawAdmission, lawStep]
  split
  · rfl
  · simp only [judgeWrite]; split <;> rfl

end Obend.Law

end
