module
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Graph
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 theorem push_nonEvaluating_backward {heap : Array Cell} {cell : Cell} {address : Address} {origin : Closure}
    (notEvaluating : ∀ source, cell ≠ .evaluating source)
    (found : (heap.push cell)[address]? = some (.evaluating origin)) :
    heap[address]? = some (.evaluating origin) := by
  by_cases same : address = heap.size
  · subst address
    simp at found
    exact False.elim (notEvaluating origin found)
  · simpa [Array.getElem?_push,same] using found

 theorem allocateFields_evaluating_backward {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} {address : Address} {origin : Closure}
    (found : (allocateFields heap environment fields).1[address]? = some (.evaluating origin)) :
    heap[address]? = some (.evaluating origin) := by
  induction fields generalizing heap with
  | nil => exact found
  | cons field fields ih =>
      rw [allocateFields_cons] at found
      exact push_nonEvaluating_backward (by intro source; cases source; simp) (ih found)

 theorem set_nonEvaluating_backward {heap : Array Cell} {target address : Address} {cell : Cell} {origin : Closure}
    (notEvaluating : ∀ source, cell ≠ .evaluating source)
    (found : (heap.set! target cell)[address]? = some (.evaluating origin)) :
    heap[address]? = some (.evaluating origin) := by
  by_cases allocated : target < heap.size
  · by_cases same : address = target
    · subst address
      simp [Array.set!,allocated] at found
      exact False.elim (notEvaluating origin found)
    · simpa [Array.set!,allocated,same,Ne.symm same] using found
  · simpa [Array.set!,Array.setIfInBounds,allocated] using found

/-- An evaluating phase can only survive from an existing evaluating cell or
be created by entering that exact suspended address. All actual allocations,
including tied Fix and cached predecessor allocation, are covered. -/
 public theorem stepRaw_evaluating_birth {state : State} {address : Address} {origin : Closure}
    (found : (stepRaw state).heap[address]? = some (.evaluating origin)) :
    state.heap[address]? = some (.evaluating origin) ∨
      (state.control = .enter address ∧ state.heap[address]? = some (.suspended origin)) := by
  cases current : state.control with
  | complete value | refused reason | blackhole target | yielded _ => exact Or.inl (by simpa [stepRaw,current] using found)
  | enter target =>
      cases prior : state.heap[target]? with
      | none => exact Or.inl (by simpa [stepRaw,current,prior] using found)
      | some cell =>
          cases cell with
          | evaluating old | cached old value => exact Or.inl (by simpa [stepRaw,current,prior] using found)
          | suspended old =>
              have changed : (state.heap.set! target (.evaluating old))[address]? = some (.evaluating origin) := by
                simpa [stepRaw,current,prior] using found
              by_cases same : address = target
              · subst address
                have allocated := (Array.getElem?_eq_some_iff.mp prior).1
                simp [Array.set!,allocated] at changed
                subst old
                exact Or.inr ⟨rfl,prior⟩
              · exact Or.inl (by simpa [Array.set!,same,Ne.symm same] using changed)
  | evaluate term environment =>
      cases term <;> simp only [stepRaw,current] at found
      all_goals repeat' first | split at found
      all_goals first
        | exact Or.inl found
        | exact Or.inl (allocateFields_evaluating_backward found)
        | exact Or.inl (push_nonEvaluating_backward (by intro source; simp) found)
        | exact Or.inl (push_nonEvaluating_backward (by intro source; simp)
            (push_nonEvaluating_backward (by intro source; simp) found))
  | returned value =>
      cases frames : state.stack with
      | nil => exact Or.inl (by simpa [stepRaw,current,frames] using found)
      | cons frame rest =>
          cases frame <;> cases value <;> simp only [stepRaw,current,frames] at found
          all_goals repeat' first | split at found
          all_goals first
            | exact Or.inl found
            | exact Or.inl (allocateFields_evaluating_backward found)
            | exact Or.inl (push_nonEvaluating_backward (by intro source; simp) found)
            | exact Or.inl (set_nonEvaluating_backward (by intro source; simp) found)

/-- Every reachable evaluating cell has a real entry witness at its permanent
address and source origin. This rules out the unearned phase in the named
GraphRepresents/Born counterexample, independently of source termination. -/
 theorem reachable_evaluating_started {source : Term} {state : State} {address : Address} {origin : Closure}
    (reachable : Reachable (initial source) state)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ entered : State, Reachable (initial source) entered ∧ entered.control = .enter address ∧
      entered.heap[address]? = some (.suspended origin) := by
  induction reachable with
  | start => simp [initial] at found
  | next reachable ih =>
      rcases stepRaw_evaluating_birth found with existing | ⟨entered,suspended⟩
      · exact ih existing
      · exact ⟨_,reachable,entered,suspended⟩

 theorem evaluatingSegment_reachable {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) : Reachable (stepRaw entered) state := by
  induction segment with
  | start _ _ => exact .start
  | next segment found ih => exact .next ih

 theorem evaluatingSegment_cell {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) : state.heap[address]? = some (.evaluating origin) := by
  cases segment with
  | start enter suspended =>
      have allocated := (Array.getElem?_eq_some_iff.mp suspended).1
      simp only [stepRaw,enter,suspended]
      simp [Array.set!,allocated]
  | next segment found => exact found

/-- Extract the genuine local source segment for an update anywhere in the
continuation. Inner updates retain their own local provenance while erasing
administrative boundaries from the demanded context. -/
 public theorem stackRealizes_update_segment {meaning : AddressMeaning} {root focus : Term}
    {before after : List Frame} {address : Address}
    (realizes : StackRealizes meaning root focus (before ++ .update address::after)) :
    Steps (meaning address) (stackMeaning meaning before focus) := by
  induction before generalizing focus with
  | nil => exact realizes.1
  | cons frame before ih =>
      cases frame with
      | update other =>
          have head : Steps (meaning other) focus := realizes.1
          have rest := ih realizes.2
          exact sourceSteps_trans rest (sourceSteps_stack meaning before head)
      | argument _ _ | field _ | reflect | metadata | project | extend _ _
      | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          exact ih realizes

/-- Every active update bounds the current demanded source budget, derived
from its local continuation segment. This theorem allows intervening sharing
updates and arbitrary source contexts, rather than assuming an execution
oracle for the heap. -/
 public theorem graphBy_pending_budget {meaning : AddressMeaning} {state : State} {source nameValue focus : Term}
    {address : Address} {before after : List Frame} {nameCost : Nat}
    (represented : GraphRepresentsBy meaning state source)
    (head : state.stack = before ++ .update address::after)
    (current : controlMeaning meaning state.control = some focus)
    (demand : SourceDerivation (meaning address) nameValue nameCost) :
    ∃ focusValue focusCost, SourceDerivation focus focusValue focusCost ∧ focusCost ≤ nameCost := by
  obtain ⟨_,_,_,_,_,other,control,stack⟩ := represented
  have aligned : other = focus := Option.some.inj (control.symm.trans current)
  subst other
  have segment := stackRealizes_update_segment (head ▸ stack)
  obtain ⟨contextCost,context,contextLe⟩ := sourceSteps_derivation_tail segment demand
  obtain ⟨value,cost,focusDemand,le⟩ := stack_derivation_demand context
  exact ⟨value,cost,focusDemand,Nat.le_trans le contextLe⟩

end Obend.Core.Proofs.Adequacy
