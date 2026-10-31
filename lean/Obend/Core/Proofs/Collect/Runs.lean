module
/- Bounded runs, resumption and composition. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Collect.Lockstep
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

/-! ## Bounded runs, resumption and composition -/

/-- Outcomes agree under the renaming: same constructor, same reason, renamed payload,
related retained states. -/
@[expose] public def OutcomeRel (f : Nat → Nat) (D : Nat → Prop) : Outcome → Outcome → Prop
  | .finished value s, .finished value' t =>
    value' = renameValue f value ∧ AllIn D (valueAddresses value) ∧ Related f D s t
  | .suspended reason s, .suspended reason' t => reason' = reason ∧ Related f D s t
  | .divergent address s, .divergent address' t => address' = f address ∧ Related f D s t
  | .refused reason s, .refused reason' t => reason' = reason ∧ Related f D s t
  | .yielded plan s, .yielded plan' t => plan' = f plan ∧ Related f D s t
  | _, _ => False

/-- The one outcome a collected state may improve on: running out of heap. -/
@[expose] public def ranOutOfHeap : Outcome → Bool
  | .suspended .capacity _ => true
  | _ => false

public theorem Related.stack_length {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t) :
    t.stack.length = s.stack.length := by
  rw [related.stack, List.length_map]

/-- The gap between the two heap ends is fixed by the renaming: every pair related by
`f` has the same gap (allocation is lockstep). -/
public theorem Related.gap {f : Nat → Nat} {D : Nat → Prop} {s t s' t' : State} (one : Related f D s t)
    (two : Related f D s' t') : s.heap.size - t.heap.size = s'.heap.size - t'.heap.size := by
  have a := (one.heap.beyond (s.heap.size + s'.heap.size) (by omega)).2
  have b := (two.heap.beyond (s.heap.size + s'.heap.size) (by omega)).2
  have c := one.heap.size_le
  have d := two.heap.size_le
  omega

public theorem runBounded_zero_related {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t)
    (limits limits' : Limits) : OutcomeRel f D (runBounded limits 0 s) (runBounded limits' 0 t) := by
  have controlEq := related.control
  cases control : s.control <;> rw [control] at controlEq <;>
    simp only [runBounded, control, controlEq, renameControl, OutcomeRel, true_and] <;>
    first
      | exact related
      | exact ⟨by have inside := related.controlIn; rw [control] at inside; exact inside, related⟩

/-- An active control is the only one `step` advances. -/
@[expose] public def active : Control → Bool
  | .evaluate _ _ | .enter _ | .returned _ => true
  | _ => false

public theorem runBounded_succ_active {limits : Limits} {ticks : Nat} {s : State} (isActive : active s.control = true) :
    runBounded limits (ticks + 1) s =
      if (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack then
        runBounded limits ticks (stepRaw s) else .suspended .capacity s := by
  have stepEq : step limits s =
      if (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack then
        .suspended .ticks (stepRaw s) else .suspended .capacity s := by
    cases control : s.control <;> rw [control] at isActive <;> simp [active] at isActive <;>
      simp [step, control]
  simp only [runBounded, stepEq]
  by_cases fits : (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack <;>
    simp [fits]

public theorem runBounded_succ_inactive {limits : Limits} {ticks : Nat} {s : State} (inactive : active s.control = false) :
    runBounded limits (ticks + 1) s = runBounded limits 0 s := by
  cases control : s.control <;> rw [control] at inactive <;> simp [active] at inactive <;>
    simp [runBounded, step, control]

public theorem active_rename (f : Nat → Nat) (control : Control) :
    active (renameControl f control) = active control := by
  cases control <;> rfl

/-- `limits'` gives the related state `t` at least the room `limits` gives `s`: a heap
limit short by at most the gap between the two heaps (the cells collection freed), and
no smaller a stack limit. The gap is the same for every pair one renaming relates
(`Related.gap`), so the room is too (`RoomFor.shift`). Two instances: the same limits
(`RoomFor.same`), and limits counted from each state's own heap end
(`collect_resume_segment`'s use in `Kernel.ObjectiveResumeContract`). -/
public structure RoomFor (limits limits' : Limits) (s t : State) : Prop where
  heap : limits.heap ≤ limits'.heap + (s.heap.size - t.heap.size)
  stack : limits.stack ≤ limits'.stack

public theorem RoomFor.same (limits : Limits) (s t : State) : RoomFor limits limits s t :=
  ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

public theorem RoomFor.shift {f : Nat → Nat} {D : Nat → Prop} {limits limits' : Limits} {s t s' t' : State}
    (one : Related f D s t) (two : Related f D s' t') (room : RoomFor limits limits' s t) :
    RoomFor limits limits' s' t' :=
  ⟨by rw [← one.gap two]; exact room.heap, room.stack⟩

/-- `RoomFor`'s refuting pole: one more cell of limit than the related side gets, with no gap
to cover it (its satisfying pole is `RoomFor.same`). -/
theorem not_roomFor_short : ¬ RoomFor ⟨1, 0⟩ ⟨0, 0⟩ (initial (.nat 0)) (initial (.nat 0)) := by
  intro room
  have := room.heap
  simp [initial] at this

/-- **Bounded runs agree**, except where the original ran out of heap, for any limits that
give the related state at least the original's room (`RoomFor`: the collected state, whose
heap is no larger, may go further). -/
public theorem related_runBounded {f : Nat → Nat} {D : Nat → Prop} (limits limits' : Limits) :
    ∀ (ticks : Nat) (s t : State), Related f D s t → RoomFor limits limits' s t →
      ranOutOfHeap (runBounded limits ticks s) = false →
      OutcomeRel f D (runBounded limits ticks s) (runBounded limits' ticks t) := by
  intro ticks
  induction ticks with
  | zero => intro s t related _ _; exact runBounded_zero_related related limits limits'
  | succ ticks ih =>
    intro s t related room notCapacity
    have activeT : active t.control = active s.control := by rw [related.control, active_rename]
    cases isActive : active s.control with
    | false =>
      rw [runBounded_succ_inactive isActive, runBounded_succ_inactive (by rw [activeT, isActive])]
      exact runBounded_zero_related related limits limits'
    | true =>
      have next := related_stepRaw related
      have gap := related.gap next
      have nextLe := next.heap.size_le
      have heapRoom := room.heap
      rw [runBounded_succ_active isActive] at notCapacity ⊢
      rw [runBounded_succ_active (by rw [activeT, isActive])]
      by_cases fits : (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack
      · have fitsT : (stepRaw t).heap.size ≤ limits'.heap ∧ (stepRaw t).stack.length ≤ limits'.stack :=
          ⟨by have := fits.1; omega, by rw [next.stack_length]; exact Nat.le_trans fits.2 room.stack⟩
        rw [if_pos fits] at notCapacity ⊢
        rw [if_pos fitsT]
        exact ih _ _ next (room.shift related next) notCapacity
      · rw [if_neg fits] at notCapacity
        simp [ranOutOfHeap] at notCapacity

/-- **Exact agreement.** Given back the heap it freed (the gap `s.heap.size - t.heap.size`),
the collected run takes exactly the original's transitions, capacity suspensions included. -/
public theorem related_runBounded_exact {f : Nat → Nat} {D : Nat → Prop} (limits : Limits) :
    ∀ (ticks : Nat) (s t : State), Related f D s t → s.heap.size ≤ limits.heap →
      OutcomeRel f D (runBounded limits ticks s)
        (runBounded ⟨limits.heap - (s.heap.size - t.heap.size), limits.stack⟩ ticks t) := by
  intro ticks
  induction ticks with
  | zero => intro s t related _; exact runBounded_zero_related related _ _
  | succ ticks ih =>
    intro s t related fitsNow
    have activeT : active t.control = active s.control := by rw [related.control, active_rename]
    cases isActive : active s.control with
    | false =>
      rw [runBounded_succ_inactive isActive, runBounded_succ_inactive (by rw [activeT, isActive])]
      exact runBounded_zero_related related _ _
    | true =>
      have next := related_stepRaw related
      have gap := related.gap next
      have sizeLe := related.heap.size_le
      have nextLe := next.heap.size_le
      rw [runBounded_succ_active isActive, runBounded_succ_active (by rw [activeT, isActive])]
      by_cases fits : (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack
      · have fitsT : (stepRaw t).heap.size ≤ limits.heap - (s.heap.size - t.heap.size) ∧
            (stepRaw t).stack.length ≤ limits.stack := ⟨by omega, by rw [next.stack_length]; exact fits.2⟩
        rw [if_pos fits, if_pos fitsT]
        have := ih _ _ next fits.1
        rwa [← gap] at this
      · have notT : ¬ ((stepRaw t).heap.size ≤ limits.heap - (s.heap.size - t.heap.size) ∧
            (stepRaw t).stack.length ≤ limits.stack) := by
          intro fitsT; apply fits
          exact ⟨by omega, by rw [← next.stack_length]; exact fitsT.2⟩
        rw [if_neg fits, if_neg notT]
        exact ⟨rfl, related⟩

/-- **Resumption agrees**, with any response term (a response captures no address). -/
public theorem related_resume {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t)
    (response : Term) {s' : State} (resumed : resume response s = some s') :
    ∃ t', resume response t = some t' ∧ Related f D s' t' := by
  obtain ⟨plan, yielded⟩ := resume_requires_yield response s (by rw [resumed]; rfl)
  have controlT : t.control = .yielded (f plan) := by rw [related.control, yielded]; rfl
  simp only [resume, yielded] at resumed
  cases resumed
  refine ⟨{t with control := .evaluate response []}, by simp [resume, controlT], ?_⟩
  exact ⟨related.heap, allIn_nil D, rfl, related.stackIn, related.stack⟩

end Obend.Core.Collect
