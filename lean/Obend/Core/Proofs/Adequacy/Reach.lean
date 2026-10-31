module
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Birth
public import Obend.Core.Proofs.Adequacy.Run
public import Obend.Core.Proofs.Adequacy.StepRaw
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

/-- Finite actual traces construct coherent name assignments. Already allocated
source identities survive every prefix, including cached structured values;
only freshly allocated addresses acquire names. -/
 public theorem rawRun_graphBy_names {meaning : AddressMeaning} {state : State} {source : Term} {ticks : Nat}
    (represented : GraphRepresentsBy meaning state source)
    (successful : ResultControl (rawRun ticks state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (rawRun ticks state) source := by
  induction ticks generalizing state meaning with
  | zero => exact ⟨meaning,(fun _ _ => rfl),represented⟩
  | succ ticks ih =>
      have nextSuccessful : ResultControl (stepRaw state).control := rawRun_resultControl successful
      obtain ⟨middle,first,nextRepresented⟩ := graph_stepRaw_names represented nextSuccessful
      obtain ⟨next,rest,finalRepresented⟩ := ih nextRepresented successful
      refine ⟨next,?_,finalRepresented⟩
      intro address allocated
      exact (first address allocated).trans
        (rest address (Nat.lt_of_lt_of_le allocated (stepRaw_preservesOrigins state).1))

 public theorem rawRun_named_graph {source : Term} (closed : Scoped 0 source) (ticks : Nat)
    (successful : ResultControl (rawRun ticks (initial source)).control) :
    ∃ meaning : AddressMeaning, GraphRepresentsBy meaning (rawRun ticks (initial source)) source := by
  obtain ⟨meaning,_,represented⟩ := rawRun_graphBy_names (graphBy_initializes closed) successful
  exact ⟨meaning,represented⟩

/-- Every actual reachable evaluating phase comes with an uninterrupted real
machine interval from its precise suspended closure entry. Combined with the
coherent assignment theorem, this is the phase-provenance input for proving
active-update budgets and excluding blackholes in terminating source runs. -/
 theorem reachable_evaluating_segment {source : Term} {state : State} {address : Address} {origin : Closure}
    (reachable : Reachable (initial source) state)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ entered : State, Reachable (initial source) entered ∧ entered.control = .enter address ∧
      entered.heap[address]? = some (.suspended origin) ∧ EvaluatingSegment address origin entered state := by
  induction reachable with
  | start => simp [initial] at found
  | next reachable ih =>
      rcases stepRaw_evaluating_birth found with existing | ⟨entered,suspended⟩
      · obtain ⟨entry,earlier,enter,old,segment⟩ := ih existing
        exact ⟨entry,earlier,enter,old,.next segment found⟩
      · exact ⟨_,reachable,entered,suspended,.start entered suspended⟩

 theorem reachable_graphBy_names {start state : State} {source : Term} {meaning : AddressMeaning}
    (represented : GraphRepresentsBy meaning start source) (reachable : Reachable start state)
    (successful : ResultControl state.control) :
    ∃ next : AddressMeaning, SourceNamesAgree start meaning next ∧ GraphRepresentsBy next state source := by
  induction reachable with
  | start => exact ⟨meaning,(fun _ _ => rfl),represented⟩
  | @next before reachable ih =>
      have priorSuccessful : ResultControl before.control := rawRun_resultControl (ticks := 1) successful
      obtain ⟨middle,first,prior⟩ := ih priorSuccessful
      obtain ⟨next,last,current⟩ := graph_stepRaw_names prior successful
      refine ⟨next,?_,current⟩
      intro address allocated
      exact (first address allocated).trans
        (last address (Nat.lt_of_lt_of_le allocated (reachable_preservesOrigins reachable).1))

/-- Whole-source termination supplies a finite independent budget for EVERY
actual evaluating interval's entered source name and retained lexical origin.
The origin cost is bounded by its name cost, and is strictly smaller for tied
Fix; ordinary aliases instead capture only older addresses. The concrete
interval witness is derived from reachability, including faulty endpoints. -/
 theorem reachable_evaluating_budget {source result : Term} {state : State} {address : Address} {origin : Closure}
    (closed : Scoped 0 source) (terminates : Evaluates source result)
    (reachable : Reachable (initial source) state)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ (entered : State) (meaning : AddressMeaning) (value : Term) (nameCost originCost : Nat),
      Reachable (initial source) entered ∧ entered.control = .enter address ∧
      entered.heap[address]? = some (.suspended origin) ∧ EvaluatingSegment address origin entered state ∧
      GraphRepresentsBy meaning entered source ∧ SourceDerivation (meaning address) value nameCost ∧
      SourceDerivation (closeOrigin meaning origin) value originCost ∧ originCost ≤ nameCost ∧
      (EnvironmentValid address origin.environment ∨ originCost < nameCost) := by
  obtain ⟨entered,earlier,enter,suspended,segment⟩ := reachable_evaluating_segment reachable found
  have successful : ResultControl entered.control := by simp [enter,ResultControl]
  obtain ⟨meaning,_,represented⟩ := reachable_graphBy_names (graphBy_initializes closed) earlier successful
  have snapshot := represented
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp only [enter,controlMeaning,Option.some.injEq] at control
  subst focus
  obtain ⟨wholeCost,whole⟩ := source_evaluates_derivation
    (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
  obtain ⟨value,nameCost,demand,_⟩ := stack_derivation_demand whole
  have originSteps := (heap address _ suspended).1
  obtain ⟨originCost,originDemand,le⟩ := sourceSteps_derivation_tail originSteps demand
  have born := reachable_originsBorn closed earlier address _ suspended
  have descent : EnvironmentValid address origin.environment ∨ originCost < nameCost := by
    rcases originBorn_demand_descent born originSteps demand with captures | ⟨smaller,tail,less⟩
    · exact Or.inl captures
    · have aligned := sourceDerivation_cost_unique tail originDemand
      exact Or.inr (aligned ▸ less)
  exact ⟨entered,meaning,value,nameCost,originCost,earlier,enter,suspended,segment,snapshot,demand,originDemand,le,descent⟩

 theorem evaluatingSegment_from_entry {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) : Reachable entered state := by
  induction segment with
  | start _ _ => exact .next .start
  | next segment found ih => exact .next ih

/-- The source budget earned at suspended entry survives in the coherent
assignment at the CURRENT evaluating phase. Captured origins and the same
address name retain their exact source term while other allocations occur. -/
 theorem reachable_evaluating_current_budget {source result : Term} {state : State} {address : Address} {origin : Closure}
    (closed : Scoped 0 source) (terminates : Evaluates source result)
    (reachable : Reachable (initial source) state) (successful : ResultControl state.control)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ (meaning : AddressMeaning) (value : Term) (nameCost originCost : Nat),
      GraphRepresentsBy meaning state source ∧ SourceDerivation (meaning address) value nameCost ∧
      SourceDerivation (closeOrigin meaning origin) value originCost ∧ originCost ≤ nameCost ∧
      (EnvironmentValid address origin.environment ∨ originCost < nameCost) := by
  obtain ⟨entered,priorMeaning,value,nameCost,originCost,earlier,enter,suspended,segment,prior,demand,originDemand,le,descent⟩ :=
    reachable_evaluating_budget closed terminates reachable found
  obtain ⟨meaning,same,current⟩ := reachable_graphBy_names prior (evaluatingSegment_from_entry segment) successful
  have allocated := (Array.getElem?_eq_some_iff.mp suspended).1
  have originValid : ClosureValid entered.heap.size origin := prior.1.1 address _ suspended
  have sourceEq : closeOrigin priorMeaning origin = closeOrigin meaning origin :=
    closeTerm_meaning_congr originValid.2 originValid.1 same
  refine ⟨meaning,value,nameCost,originCost,current,?_,?_,le,descent⟩
  · simpa only [←same address allocated] using demand
  · simpa only [←sourceEq] using originDemand

end Obend.Core.Proofs.Adequacy
