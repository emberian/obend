module
/- Demand safety: budgets, and per-transition safety. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Birth
public import Obend.Core.Proofs.Adequacy.CasesControl
public import Obend.Core.Proofs.Adequacy.CasesEval
public import Obend.Core.Proofs.Adequacy.CasesReturn
public import Obend.Core.Proofs.Adequacy.Run
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 theorem captureCap_le {environment : Environment} {cap : Nat}
    (captures : EnvironmentValid cap environment) : captureCap environment ≤ cap := by
  induction environment with
  | nil => exact Nat.zero_le _
  | cons address rest ih =>
      apply Nat.max_le.mpr
      exact ⟨Nat.succ_le_of_lt (captures address (List.mem_cons_self ..)),
        ih (fun reference member => captures reference (List.mem_cons_of_mem _ member))⟩

 theorem captureCap_valid (environment : Environment) : EnvironmentValid (captureCap environment) environment := by
  induction environment with
  | nil => simp [EnvironmentValid]
  | cons address rest ih =>
      intro reference member
      rcases List.mem_cons.mp member with equal | old
      · subst reference
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih reference old) (Nat.le_max_right _ _)

 public theorem initial_demandSafety (source : Term) (meaning : AddressMeaning) : DemandSafety meaning (initial source) := by
  intro address origin found
  simp [initial] at found

 public theorem demandSafety_returned {meaning : AddressMeaning} {state : State} {value : RuntimeValue}
    (returned : state.control = .returned value) : DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have positive := sourceDerivation_cost_positive nameDemand
  simp only [budgetFocus,returned,controlMeaning,Option.some.injEq] at current
  subst focus
  obtain ⟨_,rfl⟩ := sourceDerivation_value_inv (valueMeaning_value meaning value) focusDemand
  by_cases greater : 1 < nameCost
  · exact Or.inl greater
  · right
    refine ⟨by omega,?_⟩
    simp [budgetCap,returned]

 public theorem demandSafety_forbids_finite_reentry {meaning : AddressMeaning} {state : State} {address : Address} {origin : Closure}
    {value : Term} {cost : Nat} (safe : DemandSafety meaning state)
    (enter : state.control = .enter address) (busy : state.heap[address]? = some (.evaluating origin))
    (demand : SourceDerivation (meaning address) value cost) : False := by
  have focus : budgetFocus meaning state = some (meaning address) := by simp [budgetFocus,enter,busy]
  rcases safe address origin busy value cost demand (meaning address) focus value cost demand with less | ⟨equal,cap⟩
  · exact Nat.lt_irrefl _ less
  · have impossible : address+1 ≤ address := by simpa only [budgetCap,enter,busy] using cap
    exact Nat.not_succ_le_self _ impossible

/-- The real suspended→evaluating transition preserves active demand safety
and registers the newly active update with its source-origin budget. This
is general heap/closure preservation, including actual tied Fix origins. -/
 theorem stepRaw_demandSafety_enter_suspended {meaning : AddressMeaning} {state : State}
    {address : Address} {origin : Closure} (safe : DemandSafety meaning state)
    (heap : HeapRealizes meaning state.heap) (born : HeapOriginsBorn state.heap)
    (enter : state.control = .enter address) (suspended : state.heap[address]? = some (.suspended origin)) :
    DemandSafety meaning (stepRaw state) := by
  intro other old found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have focusEq : focus = closeOrigin meaning origin := by
    simpa only [budgetFocus,stepRaw,enter,suspended,controlMeaning,Option.some.injEq,closeOrigin] using current.symm
  subst focus
  have oldFocus : budgetFocus meaning state = some (closeOrigin meaning origin) := by simp [budgetFocus,enter,suspended]
  have capEq : budgetCap (stepRaw state) = budgetCap state := by simp [budgetCap,stepRaw,enter,suspended]
  rcases stepRaw_evaluating_birth found with prior | ⟨entered,oldSuspended⟩
  · have previous := safe other old prior nameValue nameCost nameDemand _ oldFocus focusValue focusCost focusDemand
    simpa only [capEq] using previous
  · have addressEq : other = address := by rw [enter] at entered; exact (Control.enter.inj entered).symm
    subst other
    have originEq : old = origin := Cell.suspended.inj (Option.some.inj (oldSuspended.symm.trans suspended))
    subst old
    have originSteps := (heap address _ suspended).1
    have originBorn := born address _ suspended
    rcases originBorn_demand_descent originBorn originSteps nameDemand with captures | ⟨smaller,tail,less⟩
    · obtain ⟨smaller,tail,le⟩ := sourceSteps_derivation_tail originSteps nameDemand
      have aligned := sourceDerivation_cost_unique focusDemand tail
      have budgetLe : focusCost ≤ nameCost := aligned.symm ▸ le
      by_cases strict : focusCost < nameCost
      · exact Or.inl strict
      · right
        refine ⟨by omega,?_⟩
        simpa [budgetCap,stepRaw,enter,suspended,cellOrigin] using captureCap_le captures
    · have aligned := sourceDerivation_cost_unique tail focusDemand
      exact Or.inl (aligned ▸ less)

 public theorem budgetFocus_enter_steps {meaning : AddressMeaning} {state : State} {address : Address} {focus : Term}
    (heap : HeapRealizes meaning state.heap) (enter : state.control = .enter address)
    (current : budgetFocus meaning state = some focus) : Steps (meaning address) focus := by
  cases found : state.heap[address]? with
  | none => simp [budgetFocus,enter,found] at current; subst focus; exact .refl _
  | some cell =>
      cases cell with
      | evaluating origin => simp [budgetFocus,enter,found] at current; subst focus; exact .refl _
      | suspended origin =>
          simp [budgetFocus,enter,found] at current
          subst focus
          exact (heap address _ found).1
      | cached origin value =>
          simp [budgetFocus,enter,found] at current
          subst focus
          exact (heap address _ found).2.1

 theorem budgetCap_enter_bound {state : State} {address : Address}
    (born : HeapOriginsBorn state.heap) (enter : state.control = .enter address) : budgetCap state ≤ address+1 := by
  cases found : state.heap[address]? with
  | none => simp [budgetCap,enter,found]
  | some cell =>
      cases cell with
      | evaluating origin | cached origin value => simp [budgetCap,enter,found]
      | suspended origin =>
          simpa only [budgetCap,enter,found,cellOrigin] using captureCap_le (originBorn_capture_bound (born address _ found))

/-- Bare lexical lookup preserves active source/capture safety. Suspended and
cached phases reduce source budget; every origin's cap is bounded by the
looked-up address, itself retained by the current environment. -/
 theorem stepRaw_demandSafety_bound {meaning : AddressMeaning} {state : State}
    {environment : Environment} {index address : Nat} (safe : DemandSafety meaning state)
    (heap : HeapRealizes meaning state.heap) (born : HeapOriginsBorn state.heap)
    (evaluate : state.control = .evaluate (.bound index) environment)
    (lookup : environment[index]? = some address) : DemandSafety meaning (stepRaw state) := by
  have nextEnter : (stepRaw state).control = .enter address := by simp [stepRaw,evaluate,lookup]
  have nextHeap : HeapRealizes meaning (stepRaw state).heap := by simpa [stepRaw,evaluate,lookup] using heap
  have nextBorn : HeapOriginsBorn (stepRaw state).heap := by simpa [stepRaw,evaluate,lookup] using born
  have closes : closeTerm meaning environment (.bound index) = meaning address := by
    cases environment with
    | nil => simp at lookup
    | cons reference references => simp [closeTerm,Term.substitute,environmentSubstitution,lookup]
  have oldFocus : budgetFocus meaning state = some (meaning address) := by simp [budgetFocus,evaluate,controlMeaning,closes]
  have capLe : budgetCap (stepRaw state) ≤ budgetCap state := by
    have addressCap : address+1 ≤ captureCap environment :=
      Nat.succ_le_of_lt (captureCap_valid environment address (List.mem_of_getElem? lookup))
    calc
      budgetCap (stepRaw state) ≤ address+1 := budgetCap_enter_bound nextBorn nextEnter
      _ ≤ captureCap environment := addressCap
      _ = budgetCap state := by simp [budgetCap,evaluate]
  intro other origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have oldFound : state.heap[other]? = some (.evaluating origin) := by simpa [stepRaw,evaluate,lookup] using found
  have enters := budgetFocus_enter_steps nextHeap nextEnter current
  have evaluated : Evaluates (meaning address) focusValue :=
    ⟨sourceSteps_trans enters (sourceDerivation_evaluates focusDemand).1,(sourceDerivation_evaluates focusDemand).2⟩
  obtain ⟨priorCost,priorDemand⟩ := source_evaluates_derivation evaluated
  obtain ⟨smaller,tail,le⟩ := sourceSteps_derivation_tail enters priorDemand
  have aligned := sourceDerivation_cost_unique focusDemand tail
  have budgetLe : focusCost ≤ priorCost := aligned.symm ▸ le
  rcases safe other origin oldFound nameValue nameCost nameDemand _ oldFocus focusValue priorCost priorDemand with less | ⟨equal,cap⟩
  · exact Or.inl (Nat.lt_of_le_of_lt budgetLe less)
  · by_cases strict : focusCost < nameCost
    · exact Or.inl strict
    · right
      exact ⟨by omega,Nat.le_trans capLe cap⟩

 theorem demandSafety_terminal {meaning : AddressMeaning} {state : State}
    (terminal : (∃ reason, state.control = .refused reason) ∨ (∃ address, state.control = .blackhole address)) :
    DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  rcases terminal with ⟨reason,refused⟩ | ⟨target,blackhole⟩
  · simp [budgetFocus,refused,controlMeaning] at current
  · simp [budgetFocus,blackhole,controlMeaning] at current

/-- EVERY actual administrative transition preserves active demand safety.
Explicit terminal faults remain classified; source termination plus earned
finite update budgets is used separately to exclude evaluating re-entry. -/
 public theorem stepRaw_demandSafety_administrative {meaning : AddressMeaning} {state : State}
    (safe : DemandSafety meaning state) (heap : HeapRealizes meaning state.heap)
    (born : HeapOriginsBorn state.heap) (administrative : DemandAdministrative state) :
    DemandSafety meaning (stepRaw state) := by
  cases current : state.control with
  | enter address =>
      cases found : state.heap[address]? with
      | none => exact demandSafety_terminal (Or.inl ⟨.missingCell,by simp [stepRaw,current,found]⟩)
      | some cell =>
          cases cell with
          | suspended origin => exact stepRaw_demandSafety_enter_suspended safe heap born current found
          | cached origin value => exact demandSafety_returned (value := value) (by simp [stepRaw,current,found])
          | evaluating origin => exact demandSafety_terminal (Or.inr ⟨address,by simp [stepRaw,current,found]⟩)
  | evaluate term environment =>
      cases term <;> try simp [DemandAdministrative,current] at administrative
      case bound index =>
        cases lookup : environment[index]? with
        | none => exact demandSafety_terminal (Or.inl ⟨.unbound,by simp [stepRaw,current,lookup]⟩)
        | some address => exact stepRaw_demandSafety_bound safe heap born current lookup
  | returned value | complete value | refused reason | blackhole address | yielded _ => simp [DemandAdministrative,current] at administrative

 theorem frame_derivation_demand_strict {meaning : AddressMeaning} {frame : Frame} {focus result : Term} {cost : Nat}
    (ordinary : ∀ address, frame ≠ .update address)
    (derivation : SourceDerivation (frameMeaning meaning frame focus) result cost) :
    ∃ value demandCost, SourceDerivation focus value demandCost ∧ demandCost < cost := by
  cases frame with
  | update address => exact False.elim (ordinary address rfl)
  | argument term environment =>
      cases derivation with
      | value value => cases value
      | applicationLambda first second => exact ⟨_,_,first,by omega⟩
      | applicationSpecification first second => exact ⟨_,_,first,by omega⟩
  | field name =>
      cases derivation with
      | value value => cases value
      | field first found second => exact ⟨_,_,first,by omega⟩
  | reflect =>
      cases derivation with
      | value value => cases value
      | reflect first second => exact ⟨_,_,first,by omega⟩
  | metadata =>
      cases derivation with
      | value value => cases value
      | metadata first second => exact ⟨_,_,first,by omega⟩
  | project =>
      cases derivation with
      | value value => cases value
      | project first second => exact ⟨_,_,first,by omega⟩
  | extend fields environment =>
      cases derivation with
      | value value => cases value
      | extend first => exact ⟨_,_,first,by omega⟩
  | condition zero body environment =>
      cases derivation with
      | value value => cases value
      | zero first second => exact ⟨_,_,first,by omega⟩
      | successor first second => exact ⟨_,_,first,by omega⟩
  | binaryLeft primitive right environment =>
      cases derivation with
      | value value => cases value
      | binary first second found => exact ⟨_,_,first,by omega⟩
  | binaryRight primitive left =>
      cases derivation with
      | value value => cases value
      | binary first second found => exact ⟨_,_,second,by omega⟩
  | case arms environment =>
      cases derivation with
      | value value => cases value
      | case first found second => exact ⟨_,_,first,by omega⟩
  | ifBool whenTrue whenFalse environment =>
      cases derivation with
      | value value => cases value
      | ifTrue first second => exact ⟨_,_,first,by omega⟩
      | ifFalse first second => exact ⟨_,_,first,by omega⟩

 theorem stackUpdates_member_split {stack : List Frame} {address : Address}
    (member : address ∈ stackUpdates stack) :
    ∃ before after, stack = before ++ .update address::after := by
  induction stack with
  | nil => simp [stackUpdates] at member
  | cons frame rest ih =>
      by_cases update : ∃ other, frame = .update other
      · obtain ⟨other,eq⟩ := update
        subst frame
        rcases List.mem_cons.mp member with same | later
        · subst address; exact ⟨[],rest,rfl⟩
        · obtain ⟨before,after,eq⟩ := ih later
          exact ⟨.update other::before,after,by simp [eq]⟩
      · have later : address ∈ stackUpdates rest := by
          cases frame <;> simp_all [stackUpdates]
        obtain ⟨before,after,eq⟩ := ih later
        exact ⟨frame::before,after,by simp [eq]⟩

 public theorem budgetFocus_control_steps {meaning : AddressMeaning} {state : State} {before focus : Term}
    (heap : HeapRealizes meaning state.heap)
    (control : controlMeaning meaning state.control = some before)
    (current : budgetFocus meaning state = some focus) : Steps before focus := by
  cases actual : state.control with
  | enter address =>
      simp only [actual,controlMeaning,Option.some.injEq] at control
      subst before
      exact budgetFocus_enter_steps heap actual current
  | evaluate term environment | returned value | complete value | refused reason | blackhole address | yielded _ =>
      have aligned : before = focus := by
        apply Option.some.inj
        exact control.symm.trans (by simpa only [budgetFocus,actual] using current)
      subst focus
      exact .refl _

/-- Any actual graph with a demanding continuation at its head is safe: the
head's child consumes strictly less budget than every enclosing active update.
This is a general semantic consequence for all eight lazy demand contexts. -/
 public theorem graphBy_nonUpdate_head_demandSafety {meaning : AddressMeaning} {state : State} {source : Term}
    {frame : Frame} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (head : state.stack = frame::rest) (ordinary : ∀ address, frame ≠ .update address) : DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have busy := represented.2.1
  have member := busy.2 address |>.mpr ⟨origin,found⟩
  have restMember : address ∈ stackUpdates rest := by
    rw [head] at member
    cases frame <;> try exact member
    case update other => exact False.elim (ordinary other rfl)
  obtain ⟨before,after,split⟩ := stackUpdates_member_split restMember
  obtain ⟨_,_,_,_,heap,oldFocus,control,stack⟩ := represented
  have localHead : state.stack = (frame::before) ++ .update address::after := by simp [head,split]
  have segment := stackRealizes_update_segment (localHead ▸ stack)
  obtain ⟨contextCost,context,contextLe⟩ := sourceSteps_derivation_tail segment nameDemand
  obtain ⟨middle,middleCost,middleDerivation,middleLe⟩ := stack_derivation_demand (stack := before) context
  obtain ⟨child,childCost,childDerivation,childLt⟩ := frame_derivation_demand_strict ordinary middleDerivation
  have focused := budgetFocus_control_steps heap control current
  obtain ⟨actualCost,actualDerivation,actualLe⟩ := sourceSteps_derivation_tail focused childDerivation
  have aligned := sourceDerivation_cost_unique focusDemand actualDerivation
  have below : actualCost < nameCost :=
    Nat.lt_of_le_of_lt actualLe (Nat.lt_of_lt_of_le childLt (Nat.le_trans middleLe contextLe))
  exact Or.inl (aligned.symm ▸ below)

/-- General application/object/field/extension/condition/primitive demand
dispatch constructs the actual next named graph AND active-update safety.
No finite-source or evaluator oracle is a premise. -/
 public theorem graph_evaluate_context_safety {meaning : AddressMeaning} {state : State} {source hole : Term}
    {context : DemandContext} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current⟩ := graph_evaluate_context_names represented evaluate
  refine ⟨next,same,current,?_⟩
  apply graphBy_nonUpdate_head_demandSafety current
    (frame := context.frame environment) (rest := state.stack)
  · simp only [demandContext_dispatch evaluate]
  · intro address
    cases context <;> simp [DemandContext.frame]


/-- A genuine source reduction after an actual continuation prefix makes the
next demand strictly smaller than every surviving active update. Allocation
may change future names; the actual old heap prefix retains its assignment. -/
 theorem graphBy_semantic_reduction_demandSafety {meaning next : AddressMeaning}
    {state : State} {source before after : Term} {consumed : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (same : SourceNamesAgree state meaning next)
    (representedNext : GraphRepresentsBy next (stepRaw state) source)
    (noEnter : ∀ address, state.control ≠ .enter address)
    (head : state.stack = consumed ++ (stepRaw state).stack)
    (oldControl : controlMeaning meaning state.control = some before)
    (newControl : controlMeaning next (stepRaw state).control = some after)
    (reduce : Step (stackMeaning meaning consumed before) after) :
    DemandSafety next (stepRaw state) := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have oldFound : state.heap[address]? = some (.evaluating origin) := by
    rcases stepRaw_evaluating_birth found with old | ⟨entered,_⟩
    · exact old
    · exact False.elim (noEnter address entered)
  have oldDemand : SourceDerivation (meaning address) nameValue nameCost := by
    rw [same address (Array.getElem?_eq_some_iff.mp oldFound).1]
    exact nameDemand
  have busy := representedNext.2.1
  have member := busy.2 address |>.mpr ⟨origin,found⟩
  obtain ⟨frames,rest,split⟩ := stackUpdates_member_split member
  have oldHead : state.stack = (consumed ++ frames) ++ .update address::rest := by
    rw [head,split,List.append_assoc]
  obtain ⟨_,_,_,_,_,oldFocus,control,stack⟩ := represented
  have aligned : oldFocus = before := Option.some.inj (control.symm.trans oldControl)
  subst oldFocus
  have segment := stackRealizes_update_segment (oldHead ▸ stack)
  have contextEq : stackMeaning meaning (consumed ++ frames) before =
      stackMeaning meaning frames (stackMeaning meaning consumed before) := by
    simp [stackMeaning,List.foldl_append]
  rw [contextEq] at segment
  obtain ⟨contextCost,context,contextLe⟩ := sourceSteps_derivation_tail segment oldDemand
  obtain ⟨middle,middleCost,middleDerivation,middleLe⟩ := stack_derivation_demand (stack := frames) context
  obtain ⟨childCost,childDerivation,childLt⟩ := sourceStep_derivation_tail reduce middleDerivation
  have focused := budgetFocus_control_steps representedNext.2.2.2.2.1 newControl current
  obtain ⟨actualCost,actualDerivation,actualLe⟩ := sourceSteps_derivation_tail focused childDerivation
  have costEq := sourceDerivation_cost_unique focusDemand actualDerivation
  have below : actualCost < nameCost :=
    Nat.lt_of_le_of_lt actualLe (Nat.lt_of_lt_of_le childLt (Nat.le_trans middleLe contextLe))
  exact Or.inl (costEq.symm ▸ below)

 public theorem graph_object_access_safety {meaning : AddressMeaning} {state : State} {source : Term}
    {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,consumed,before,after,oldControl,newControl,split,reduce⟩ :=
    graph_object_access_execution represented returned head
  refine ⟨next,same,current,?_⟩
  exact graphBy_semantic_reduction_demandSafety represented same current
    (by intro address; simp [returned]) split oldControl newControl reduce


 public theorem graph_execution_demandSafety {meaning next : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (same : SourceNamesAgree state meaning next)
    (current : GraphRepresentsBy next (stepRaw state) source)
    (noEnter : ∀ address, state.control ≠ .enter address)
    (dispatch : SourceDispatch meaning next state) : DemandSafety next (stepRaw state) := by
  obtain ⟨consumed,before,after,oldControl,newControl,split,reduce⟩ := dispatch
  exact graphBy_semantic_reduction_demandSafety represented same current noEnter split oldControl newControl reduce

 public theorem graph_evaluate_mix_safety {meaning : AddressMeaning} {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_evaluate_mix_execution represented evaluate
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [evaluate]) dispatch⟩

 public theorem graph_evaluate_done_safety {meaning : AddressMeaning} {state : State} {source value : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.done value) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_evaluate_done_execution represented evaluate
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [evaluate]) dispatch⟩

 public theorem graph_closure_call_safety {meaning : AddressMeaning} {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_closure_call_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 public theorem graph_condition_zero_safety {meaning : AddressMeaning} {state : State} {source zero body : Term}
    {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_condition_zero_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 public theorem graph_condition_successor_safety {meaning : AddressMeaning} {state : State} {source zero body : Term}
    {environment : Environment} {rest : List Frame} {number : Nat}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_condition_successor_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 public theorem graph_field_return_safety {meaning : AddressMeaning} {state : State} {source : Term}
    {fields : List (String × Address)} {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_field_return_execution represented returned head found
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

/-- A tied thunk's actual source origin contains its own permanent source name
properly. Entering that origin therefore strictly reduces every finite pending
update budget, even though the heap graph itself is cyclic. -/
 theorem graphBy_enter_tied_demandSafety {meaning : AddressMeaning} {state : State} {source spec inherited : Term}
    {address : Address} {captured : Environment}
    (represented : GraphRepresentsBy meaning state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.suspended
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩)) :
    DemandSafety meaning state := by
  intro other origin busyFound nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have focusEq : focus = closeOrigin meaning
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩ := by
    simpa [budgetFocus,enter,found] using current.symm
  subst focus
  have member := represented.2.1.2 other |>.mpr ⟨origin,busyFound⟩
  obtain ⟨before,after,split⟩ := stackUpdates_member_split member
  have fixed : controlMeaning meaning state.control = some (meaning address) := by simp [controlMeaning,enter]
  obtain ⟨result,cost,demand,le⟩ := graphBy_pending_budget represented split fixed nameDemand
  have heap := represented.2.2.2.2.1
  have sourceOrigin := (heap address _ found).1
  have proper := tiedOrigin_name_proper meaning address spec inherited captured
  have different : meaning address ≠ closeOrigin meaning
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩ := by
    intro equal; rw [equal] at proper; exact Nat.lt_irrefl _ proper
  obtain ⟨smaller,tail,less⟩ := sourceSteps_derivation_strict sourceOrigin different demand
  have aligned := sourceDerivation_cost_unique focusDemand tail
  exact Or.inl (aligned.symm ▸ Nat.lt_of_lt_of_le less le)

 public theorem graph_evaluate_fix_safety {meaning : AddressMeaning} {state : State} {source spec inherited : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current⟩ := graph_evaluate_fix_names represented evaluate
  refine ⟨next,same,current,?_⟩
  apply graphBy_enter_tied_demandSafety current
    (address := state.heap.size) (spec := spec) (inherited := inherited) (captured := environment)
  · simp [stepRaw,evaluate]
  · simp [stepRaw,evaluate]


 theorem budgetFocus_meaning_congr {meaning next : AddressMeaning} {state : State}
    (lexical : LexicalInvariant state) (same : ∀ address, address < state.heap.size → meaning address = next address) :
    budgetFocus meaning state = budgetFocus next state := by
  cases control : state.control with
  | evaluate term environment =>
      have valid : ClosureValid state.heap.size ⟨term,environment⟩ := by simpa [control,ControlValid] using lexical.2.1
      simp only [budgetFocus,control,controlMeaning,closeTerm_meaning_congr valid.2 valid.1 same]
  | returned value | complete value =>
      have valid : RuntimeValueValid state.heap.size value := by simpa [control,ControlValid] using lexical.2.1
      simp only [budgetFocus,control,controlMeaning,valueMeaning_congr valid same]
  | refused reason | blackhole address => simp [budgetFocus,control,controlMeaning]
  | yielded plan =>
      have allocated : plan < state.heap.size := by simpa [control,ControlValid] using lexical.2.1
      simp only [budgetFocus,control,controlMeaning,same plan allocated]
  | enter address =>
      have allocated : address < state.heap.size := by simpa [control,ControlValid] using lexical.2.1
      cases found : state.heap[address]? with
      | none => simp [budgetFocus,control,found,same address allocated]
      | some cell =>
          have valid := lexical.1 address cell found
          cases cell with
          | suspended origin =>
              simp only [CellValid] at valid
              simp only [budgetFocus,control,found,closeOrigin,closeTerm_meaning_congr valid.2 valid.1 same]
          | cached origin value =>
              simp only [CellValid] at valid
              simp only [budgetFocus,control,found,valueMeaning_congr valid.2 same]
          | evaluating origin => simp [budgetFocus,control,found,same address allocated]

 public theorem demandSafety_meaning_congr {meaning next : AddressMeaning} {state : State}
    (lexical : LexicalInvariant state) (same : ∀ address, address < state.heap.size → meaning address = next address)
    (safe : DemandSafety meaning state) : DemandSafety next state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have oldDemand : SourceDerivation (meaning address) nameValue nameCost := by
    rw [same address (Array.getElem?_eq_some_iff.mp found).1]; exact nameDemand
  have oldFocus : budgetFocus meaning state = some focus := (budgetFocus_meaning_congr lexical same).trans current
  exact safe address origin found nameValue nameCost oldDemand focus oldFocus focusValue focusCost focusDemand


 public theorem demandSafety_complete {meaning : AddressMeaning} {state : State} {value : RuntimeValue}
    (complete : state.control = .complete value) : DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have positive := sourceDerivation_cost_positive nameDemand
  simp only [budgetFocus,complete,controlMeaning,Option.some.injEq] at current
  subst focus
  obtain ⟨_,rfl⟩ := sourceDerivation_value_inv (valueMeaning_value meaning value) focusDemand
  by_cases greater : 1 < nameCost
  · exact Or.inl greater
  · right; refine ⟨by omega,?_⟩; simp [budgetCap,complete]

end Obend.Core.Proofs.Adequacy
