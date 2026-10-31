module
/- What a usage count may be read as (lane C2, item 4, 2026-11-01).

The join `joinUses` (pointwise `max`) is the same rule at every quantity. This module settles what the
count it produces means, and why `unrestricted` stays `max`:

* **All-path usage.** The count is `occurrences`, a function of the term (`uses_determined`); at a
  join it is the largest count of the branches a step may select (`join_count_is_max_of_paths`); along
  any reduction of a checked term it bounds the count of every reduct at every position that is not
  `unrestricted` (`count_bounds_every_path`), and is exact at `linear` ones.
* **Only its support is read at `unrestricted`.** Every consumer of a usage vector (`safeUses`,
  `linearFree`, `reusableCaptures`) gives the same answer on two vectors that agree at tracked
  positions and have the same zeros at `unrestricted` ones (`consumers_read_support`), and `max` and
  `+` have the same zeros (`join_add_same_zeros`): replacing `max` by `+` at `unrestricted` changes
  no judgment. At `affine` positions `+` would refuse a program that uses its hypothesis at most once
  on every path (`affine_join_needs_max`), so one rule, `max`, serves every quantity.
* **Never demand, never cost.** At an `unrestricted` hypothesis the count grows along a reduction
  (`count_not_demand_bound`), is positive for a hypothesis no reduction demands
  (`count_not_consumption`), and is equal for two terms of which one steps and one is stuck
  (`count_not_cost`). -/
public import Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Check

namespace Obend.Core.Proofs.JoinReading
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation Obend.Core.Proofs.SubjectReduction
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences uses_determined)
set_option autoImplicit false

/-! ### All-path usage -/

/-- At a join on a decided condition, the count is the larger of the counts of the two terms the
join may step to (`ifTrue`, `ifFalse`): the count is taken over every path, not the one taken. -/
public theorem join_count_is_max_of_paths (n : Nat) (cond : Bool) (whenTrue whenFalse : Term) (j : Nat) :
    (occurrences n (.ifBool (.boolean cond) whenTrue whenFalse)).getD j 0 =
      max ((occurrences n whenTrue).getD j 0) ((occurrences n whenFalse).getD j 0) ∧
    Step (.ifBool (.boolean cond) whenTrue whenFalse) (if cond then whenTrue else whenFalse) := by
  refine ⟨?_, ?_⟩
  · have lt := occurrences_length n whenTrue
    have lf := occurrences_length n whenFalse
    simp only [occurrences]
    rw [getD_addUses (by simp [joinUses, lt, lf]), getD_replicate_zero, Nat.zero_add,
      getD_joinUses (lt.trans lf.symm)]
  · cases cond
    · exact .ifFalse _ _
    · exact .ifTrue _ _

/-- **The count bounds every path.** Along any reduction of a term that checks (valid context,
within budget), the count of every reduct at every hypothesis that is not `unrestricted` is at most
the initial count (and equal at `linear` ones: `steps_conserve_linear'`). -/
public theorem count_bounds_every_path {a : Assumptions} {Γ : Context} {t t' : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) (valid : validContext a.shareableVariables Γ = true)
    (safe : safeUses Γ u = true) (steps : Steps t t') :
    Below Γ (occurrences Γ.length t') u := by
  induction steps generalizing T u with
  | refl => rw [← uses_determined typed]; exact fun _ _ _ _ => Nat.le_refl _
  | next step rest ih =>
    obtain ⟨T1, u1, h1, s1, b1, _, _⟩ := step_preserves_typing typed valid safe step
    exact below_trans (ih h1 s1) b1

/-! ### Only the support is read at `unrestricted` -/

/-- Two usage vectors that agree at every tracked position and have the same zeros at every
`unrestricted` one. -/
@[expose] public def SameReading (Γ : Context) (x y : Uses) : Prop :=
  x.length = Γ.length ∧ y.length = Γ.length ∧ ∀ j b, Γ[j]? = some b →
    (b.quantity = .unrestricted → (x.getD j 0 = 0 ↔ y.getD j 0 = 0)) ∧
    (b.quantity ≠ .unrestricted → x.getD j 0 = y.getD j 0)

/-- **Every consumer reads only the support at `unrestricted`.** -/
public theorem consumers_read_support {V : List Nat} {Γ : Context} {x y : Uses} (h : SameReading Γ x y) :
    safeUses Γ x = safeUses Γ y ∧ linearFree Γ x = linearFree Γ y ∧
      reusableCaptures V Γ x = reusableCaptures V Γ y := by
  obtain ⟨lx, ly, H⟩ := h
  refine ⟨Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_⟩
  · rw [safeUses_iff, safeUses_iff]
    refine ⟨fun ⟨_, s⟩ => ⟨ly, fun j b hb => ?_⟩, fun ⟨_, s⟩ => ⟨lx, fun j b hb => ?_⟩⟩
    all_goals
      have := s j b hb
      by_cases q : b.quantity = .unrestricted
      · rw [q] at this ⊢; rfl
      · first | rw [← (H j b hb).2 q]; exact this | rw [(H j b hb).2 q]; exact this
  · rw [linearFree_iff lx, linearFree_iff ly]
    refine ⟨fun s j b hb => ?_, fun s j b hb => ?_⟩
    all_goals
      by_cases q : b.quantity = .linear
      · have qu : b.quantity ≠ .unrestricted := by rw [q]; decide
        have e := (H j b hb).2 qu
        rcases s j b hb with z | n
        · first | (left; rw [← e]; exact z) | (left; rw [e]; exact z)
        · exact absurd q n
      · exact .inr q
  · rw [captures_iff, captures_iff]
    refine ⟨fun ⟨_, s⟩ => ⟨ly, fun j b hb => ?_⟩, fun ⟨_, s⟩ => ⟨lx, fun j b hb => ?_⟩⟩
    all_goals
      rcases s j b hb with z | r
      · by_cases q : b.quantity = .unrestricted
        · left; first | exact ((H j b hb).1 q).mp z | exact ((H j b hb).1 q).mpr z
        · left; first | (rw [← (H j b hb).2 q]; exact z) | (rw [(H j b hb).2 q]; exact z)
      · exact .inr r

/-- `max` and `+` have the same zeros: at `unrestricted` positions the two joins read alike. -/
public theorem join_add_same_zeros {x y : Uses} (h : x.length = y.length) (j : Nat) :
    (joinUses x y).getD j 0 = 0 ↔ (addUses x y).getD j 0 = 0 := by
  rw [getD_joinUses h, getD_addUses h]; omega

/-- At `affine` positions the join must be `max`: a hypothesis used once on each branch is used at
most once, and `+` would count it twice and refuse it. -/
public theorem affine_join_needs_max :
    safeUses [⟨.natural, .affine⟩] (occurrences 1 (.ifBool (.boolean true) (.bound 0) (.bound 0))) = true ∧
    safeUses [⟨.natural, .affine⟩]
      (addUses (occurrences 1 (.boolean true)) (addUses (occurrences 1 (.bound 0)) (occurrences 1 (.bound 0)))) =
        false := by decide

/-! ### Never demand, never cost -/

/-- `(λ(y : unrestricted ℕ). y + y) h` in `h : unrestricted ℕ`. -/
@[expose] public def doubling : Term := .app (.lam (.binary .add (.bound 0) (.bound 0))) (.bound 0)
@[expose] public def doublingAnnotation : LambdaAnnotation := ⟨.natural, .natural, .unrestricted, .reusable⟩
@[expose] public def unrestrictedNat : Context := [⟨.natural, .unrestricted⟩]

theorem doubling_typed :
    PartialTyping {} unrestrictedNat doubling .natural [1] := by
  have body := PartialTyping.binary (assumptions := {})
    (context := ⟨doublingAnnotation.domain, doublingAnnotation.parameter⟩ :: unrestrictedNat)
    (primitive := .add) (input := .natural) (output := .natural) rfl
    (.bound (index := 0) (binding := ⟨.natural, .unrestricted⟩) rfl)
    (.bound (index := 0) (binding := ⟨.natural, .unrestricted⟩) rfl)
  have lam := PartialTyping.lambda (annotation := doublingAnnotation) body (by decide) (by decide)
    (by decide) (by decide)
  exact PartialTyping.application lam (.bound (index := 0) (context := unrestrictedNat)
    (binding := ⟨.natural, .unrestricted⟩) rfl) rfl rfl
    (by decide)

/-- **The count is not a demand bound.** At an `unrestricted` hypothesis, a checked term counting it
once steps to one counting it twice: the count bounds no number of demands along a run. -/
public theorem count_not_demand_bound :
    PartialTyping {} unrestrictedNat doubling .natural [1] ∧
      Step doubling (.binary .add (.bound 0) (.bound 0)) ∧
      (occurrences 1 doubling).getD 0 0 = 1 ∧
      (occurrences 1 (.binary .add (.bound 0) (.bound 0))).getD 0 0 = 2 := by
  refine ⟨doubling_typed, ?_, by decide, by decide⟩
  have := Step.beta (.binary .add (.bound 0) (.bound 0)) (.bound 0)
  simpa [doubling, instantiate, Term.substitute] using this

/-- **The count is not consumption.** A hypothesis counted once is demanded by no step: the join's
untaken branch holds it, and the run discards it. -/
public theorem count_not_consumption :
    (occurrences 1 (.ifBool (.boolean true) (.nat 0) (.bound 0))).getD 0 0 = 1 ∧
      Step (.ifBool (.boolean true) (.nat 0) (.bound 0)) (.nat 0) ∧
      (occurrences 1 (.nat 0)).getD 0 0 = 0 ∧ ∀ t', ¬ Step (.nat 0) t' :=
  ⟨by decide, .ifTrue _ _, by decide, fun _ s => value_no_step (.natural 0) s⟩

/-- **The count is not cost.** Two terms with the same count, of which one takes a step and the
other takes none. -/
public theorem count_not_cost :
    occurrences 1 (.app (.lam (.bound 0)) (.bound 0)) = occurrences 1 (.bound 0) ∧
      Step (.app (.lam (.bound 0)) (.bound 0)) (.bound 0) ∧ ∀ t', ¬ Step (.bound 0) t' :=
  ⟨by decide, by simpa [instantiate, Term.substitute] using Step.beta (.bound 0) (.bound 0),
    fun _ s => by cases s⟩

end Obend.Core.Proofs.JoinReading
