module
/-
# Obend.Logic.Ground — the ground judge: a claim run at listed data

`review/PROGRAM-LOGIC-20261101.md` §3, §5.2. The twin of the law probe (`Judge.Instances.lawProbe`):
the claim applied to one data instance is run by the reference stepper (`Law.run`, with the grade
as its fuel: `run_mono`, the stepper is deterministic, makes the grade monotone, and keeps the
checker's body visible to the kernel so a ground run is a `decide +kernel` fact), and the
Boolean it reaches is read back. `true` is the total judgment `Holds` at that instance
(`ground_sound`); `false` REFUTES: the claim does not hold at that instance, so no certificate of
any regime proves it for all data (`ground_refutes`). Running out of fuel is `uncovered`, not
`false`.
-/
public import Obend.Logic.Claim
public import Obend.Judge.Class
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
set_option autoImplicit false

/-- A closed claim at one data instance. -/
structure ClaimProblem where
  claim : Term
  args : List Data

/-- The run of the claim at the instance. -/
def ClaimProblem.term (p : ClaimProblem) : Term := apps p.claim (p.args.map Data.term)

/-- A Boolean read back from a run. -/
def readBool : Option Term → Option Bool
  | some (.boolean b) => some b
  | _ => none

/-- The Boolean the run reaches within `fuel` steps. -/
def groundAt (p : ClaimProblem) (fuel : Nat) : Option Bool := readBool (Obend.Law.run fuel p.term)

theorem groundAt_eval {p : ClaimProblem} {fuel : Nat} {b : Bool} (h : groundAt p fuel = some b) :
    Evaluates p.term (.boolean b) := by
  unfold groundAt readBool at h
  split at h
  · cases h; exact Obend.Law.run_sound fuel (by assumption)
  · cases h

inductive GroundClause where
  /-- the claim ran to `false` at this instance -/
  | falseAt
  deriving DecidableEq, Repr

def groundCheck (k : Nat) (p : ClaimProblem) (_ : Unit) : Judge.Verdict GroundClause :=
  match groundAt p k with
  | some true => .ok
  | some false => .refused .falseAt []
  | none => .uncovered

/-- More fuel never changes a run that finished. -/
theorem run_mono : ∀ (fuel : Nat) {t v : Term}, Obend.Law.run fuel t = some v → Obend.Law.run (fuel + 1) t = some v
  | 0, t, v, h => by
    simp only [Obend.Law.run] at h ⊢
    split at h
    · rename_i hv; simp [hv, h]
    · cases h
  | fuel + 1, t, v, h => by
    rw [Obend.Law.run] at h ⊢
    split at h
    · rename_i hv; simp [hv, h]
    · rename_i hv
      simp only [hv, Bool.false_eq_true, ite_false]
      split at h
      · exact run_mono fuel h
      · cases h

theorem run_mono_le {fuel fuel' : Nat} {t v : Term} (le : fuel ≤ fuel') (h : Obend.Law.run fuel t = some v) :
    Obend.Law.run fuel' t = some v := by
  induction le with
  | refl => exact h
  | step _ ih => exact run_mono _ ih

theorem groundAt_mono {p : ClaimProblem} {k k' : Nat} {b : Bool} (le : k ≤ k') (h : groundAt p k = some b) :
    groundAt p k' = some b := by
  unfold groundAt readBool at h ⊢
  split at h
  · rename_i v hv
    cases h
    rw [run_mono_le le hv]
  · cases h

/-- **`ground_sound`**: an accepted ground run is the total judgment at its instance. -/
theorem ground_sound {k : Nat} {p : ClaimProblem} (h : groundCheck k p () = .ok) : Holds p.claim p.args := by
  unfold groundCheck at h
  split at h
  · rename_i hd; exact groundAt_eval hd
  · cases h
  · cases h

/-- **`ground_refutes`**: a run to `false` refutes the claim at its instance. -/
theorem ground_refutes {k : Nat} {p : ClaimProblem} {path : List Nat}
    (h : groundCheck k p () = .refused .falseAt path) : ¬ Holds p.claim p.args := by
  unfold groundCheck at h
  split at h
  · cases h
  · rename_i hd
    intro ht
    have := evaluates_unique (groundAt_eval hd) ht
    cases this
  · cases h

/-- **The ground judge.** -/
instance ground : Judge ClaimProblem Unit where
  Clause := GroundClause
  Meaning p _ := Holds p.claim p.args
  check := groundCheck
  sound := by intro k p _ h; exact ground_sound h
  refutes _ := true
  refuted := by
    intro k p _ c path h _ _
    cases c
    exact ground_refutes h
  Fragment p := ∃ fuel, groundAt p fuel = some true
  complete := by
    rintro p ⟨fuel, hf⟩ _
    exact ⟨(), fuel, by simp [groundCheck, hf]⟩
  mono := by
    intro k k' p _ le hne
    unfold groundCheck at hne ⊢
    cases hd : groundAt p k with
    | none => rw [hd] at hne; exact absurd rfl hne
    | some v => rw [groundAt_mono le hd]

end Obend.Logic
end
