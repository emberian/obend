module
/- Terminating runs: result control, retained prefixes, finish or suspend. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.SafetyRaw
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

/-- A finite independent derivation of the demanded returned-value context
forces every real frame dispatch to have the required operand/field. This
uses source semantics, without a separate typed-source restriction. -/
 public theorem closeTerm_lam_form (meaning : AddressMeaning) (environment : Environment) (body : Term) :
    closeTerm meaning environment (.lam body) = .lam
      (match environment with
        | [] => body
        | _::_ => body.substitute (liftSubstitution (environmentSubstitution meaning environment))) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem frame_derivation_return_progress {meaning : AddressMeaning} {state : State} {frame : Frame}
    {rest : List Frame} {returnedValue : RuntimeValue} {result : Term} {cost : Nat}
    (busy : BusyInvariant state) (returned : state.control = .returned returnedValue)
    (head : state.stack = frame::rest)
    (derivation : SourceDerivation (frameMeaning meaning frame (valueMeaning meaning returnedValue)) result cost) :
    ResultControl (stepRaw state).control := by
  cases frame with
  | update address =>
      obtain ⟨origin,found⟩ := busy_update_exists busy head
      simp [stepRaw,returned,head,found,ResultControl]
  | argument argument environment =>
      cases derivation with
      | value value => cases value
      | applicationLambda first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
      | applicationSpecification first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | reflect =>
      cases derivation with
      | value value => cases value
      | reflect first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | metadata =>
      cases derivation with
      | value value => cases value
      | metadata first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | project =>
      cases derivation with
      | value value => cases value
      | project first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | field name =>
      cases derivation with
      | value value => cases value
      | @field target body result fields name targetCost resultCost first selected second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case record addresses =>
            subst fields
            cases found : addresses.find? (fun field => field.1 == name) with
            | none => simp [List.find?_map,Function.comp_def,found] at selected
            | some field => obtain ⟨key,address⟩ := field; simp [stepRaw,returned,head,found,ResultControl]
  | extend fields environment =>
      cases derivation with
      | value value => cases value
      | extend first =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | condition zero body environment =>
      cases derivation with
      | value value => cases value
      | zero first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case natural number => subst number; simp [stepRaw,returned,head,ResultControl]
      | successor first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case natural number => subst number; simp [stepRaw,returned,head,ResultControl]
  | binaryLeft primitive right environment => simp [stepRaw,returned,head,ResultControl]
  | binaryRight primitive left =>
      cases derivation with
      | value value => cases value
      | binary first second found =>
          have leftEq := (sourceDerivation_value_inv (valueMeaning_value meaning left) first).1
          have rightEq := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) second).1
          rw [leftEq,rightEq] at found
          cases primitive <;> cases left <;> cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form,primitiveResult] at found
          all_goals simp [stepRaw,returned,head,valueTerm,primitiveResult,scalarValue,ResultControl]
  | case arms environment =>
      cases derivation with
      | value value => cases value
      | @case scrutinee payload body result closedArms tag scrutineeCost resultCost first selected second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case variant label address =>
            obtain ⟨rfl,-⟩ := same
            cases found : arms.find? (fun arm => arm.1 == tag) with
            | none => rw [find_map_arms,found] at selected; simp at selected
            | some arm => obtain ⟨key,armBody⟩ := arm; simp [stepRaw,returned,head,found,ResultControl]
  | ifBool whenTrue whenFalse environment =>
      cases derivation with
      | value value => cases value
      | ifTrue first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case boolean value => subst value; simp [stepRaw,returned,head,ResultControl]
      | ifFalse first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case boolean value => subst value; simp [stepRaw,returned,head,ResultControl]


/-- Independent source termination supplies the exact demanded frame operand
and selected field, while earned Safety excludes busy re-entry. Thus every
actual next raw control is running/finished, with no typed-domain premise. -/
 theorem graphBy_terminating_next_result {meaning : AddressMeaning} {state : State} {source result : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (terminates : Evaluates source result) : ResultControl (stepRaw state).control := by
  cases control : state.control with
  | refused reason | blackhole address =>
      obtain ⟨_,_,_,_,_,focus,current,_⟩ := represented
      simp [control,controlMeaning] at current
  | yielded plan =>
      -- A terminating source never yields: the focus would be a stuck perform.
      exfalso
      obtain ⟨_,_,_,_,_,focus,current,stack⟩ := represented
      simp only [control,controlMeaning,Option.some.injEq] at current
      subst focus
      obtain ⟨cost,whole⟩ := source_evaluates_derivation (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
      obtain ⟨_,_,demand,_⟩ := stack_derivation_demand whole
      cases demand with
      | value isValue => cases isValue
  | complete value => simp [stepRaw,control,ResultControl]
  | enter address =>
      cases found : state.heap[address]? with
      | none =>
          have noMissing := stepRaw_no_missingCell represented.1 (by simp [control])
          simp [stepRaw,control,found] at noMissing
      | some cell =>
          cases cell with
          | evaluating origin => exact False.elim (graphBy_terminating_reentry_impossible represented safe terminates control found)
          | suspended origin | cached origin value => simp [stepRaw,control,found,ResultControl]
  | evaluate term environment =>
      cases term <;> try simp [stepRaw,control,ResultControl]
      case hole n payload =>
        obtain ⟨_,_,_,_,_,focus,current,stack⟩ := represented
        have aligned : focus = closeTerm meaning environment (.hole n payload) := by
          simpa [controlMeaning,control] using current.symm
        subst focus
        obtain ⟨cost,whole⟩ := source_evaluates_derivation
          (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
        obtain ⟨_,_,demand,_⟩ := stack_derivation_demand whole
        cases environment <;> simp only [closeTerm,Term.substitute] at demand
        all_goals exact False.elim (sourceDerivation_hole_false demand)
      case perform plan =>
        -- A terminating source never demands a perform: it has no derivation.
        exfalso
        obtain ⟨_,_,_,_,_,focus,current,stack⟩ := represented
        have aligned : focus = closeTerm meaning environment (.perform plan) := by
          simpa [controlMeaning,control] using current.symm
        subst focus
        obtain ⟨cost,whole⟩ := source_evaluates_derivation (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
        obtain ⟨_,_,demand,_⟩ := stack_derivation_demand whole
        rw [closeTerm_perform] at demand
        cases demand with
        | value isValue => cases isValue
      case bound index =>
        cases found : environment[index]? with
        | none =>
            have noUnbound := stepRaw_no_unbound represented.1 (by simp [control])
            simp [stepRaw,control,found] at noUnbound
        | some address => simp [stepRaw,control,found,ResultControl]
  | returned value =>
      cases head : state.stack with
      | nil => simp [stepRaw,control,head,ResultControl]
      | cons frame rest =>
          obtain ⟨_,busy,_,_,_,focus,current,stack⟩ := represented
          have aligned : focus = valueMeaning meaning value := by simpa [controlMeaning,control] using current.symm
          subst focus
          have residual := sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates
          obtain ⟨cost,whole⟩ := source_evaluates_derivation residual
          have framed : SourceDerivation
              (stackMeaning meaning rest (frameMeaning meaning frame (valueMeaning meaning value))) result cost := by
            simpa only [head,stackMeaning,List.foldl_cons] using whole
          obtain ⟨middle,middleCost,demand,_⟩ := stack_derivation_demand framed
          exact frame_derivation_return_progress busy control head demand

 theorem rawRun_terminating_graphSafety {meaning : AddressMeaning} {state : State} {source result : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (terminates : Evaluates source result) (ticks : Nat) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (rawRun ticks state) source ∧ DemandSafety next (rawRun ticks state) := by
  induction ticks generalizing state meaning with
  | zero => exact ⟨meaning,represented,safe⟩
  | succ ticks ih =>
      have successful := graphBy_terminating_next_result represented safe terminates
      obtain ⟨next,_,current,nextSafe⟩ := graph_stepRaw_safety_names represented safe born successful
      exact ih current nextSafe (stepRaw_originsBorn represented.1 born)

/-- Every finite prefix of the actual executor remains running/finished for
EVERY independently terminating closed source. All refusals and blackholes
are excluded from these actual traces; finite completion is still separate. -/
 public theorem rawRun_terminating_resultControl {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (ticks : Nat) :
    ResultControl (rawRun ticks (initial source)).control := by
  obtain ⟨meaning,represented,safe⟩ := rawRun_terminating_graphSafety (graphBy_initializes closed)
    (initial_demandSafety source _) (initial_originsBorn source) terminates ticks
  obtain ⟨_,_,_,_,_,focus,control,stack⟩ := represented
  cases actual : (rawRun ticks (initial source)).control <;> try trivial
  all_goals first
    | (simp [actual,controlMeaning] at control; done)
    | (exfalso
       simp only [actual,controlMeaning,Option.some.injEq] at control
       subst focus
       obtain ⟨cost,whole⟩ := source_evaluates_derivation (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
       obtain ⟨_,_,demand,_⟩ := stack_derivation_demand whole
       cases demand with
       | value isValue => cases isValue)


/-- For arbitrary capacities, the bounded executor retains an exact actual
raw prefix; suspension can shorten its physical work, but cannot synthesize
or replace machine state. -/
 public theorem runBounded_retained_prefix (limits : Limits) (ticks : Nat) (state : State) :
    ∃ count, count ≤ ticks ∧ retainedState (runBounded limits ticks state) = rawRun count state := by
  induction ticks generalizing state with
  | zero =>
      refine ⟨0,Nat.le_refl _,?_⟩
      cases control : state.control <;> simp [runBounded,control,retainedState,rawRun]
  | succ ticks ih =>
      cases control : state.control with
      | complete value | refused reason | blackhole address | yielded _ =>
          refine ⟨0,Nat.zero_le _,?_⟩
          simp [runBounded,step,control,retainedState,rawRun]
      | evaluate term environment | enter address | returned value =>
          by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
          · have dispatched : step limits state = .suspended .ticks (stepRaw state) := by simp [step,control,fits]
            obtain ⟨count,bound,exactState⟩ := ih (stepRaw state)
            refine ⟨count+1,Nat.succ_le_succ bound,?_⟩
            simpa only [runBounded,dispatched,rawRun] using exactState
          · have suspended : step limits state = .suspended .capacity state := by simp [step,control,fits]
            refine ⟨0,Nat.zero_le _,?_⟩
            simp only [runBounded,suspended,retainedState,rawRun]

 theorem runBounded_terminating_retained_resultControl {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (limits : Limits) (ticks : Nat) :
    ResultControl (retainedState (runBounded limits ticks (initial source))).control := by
  obtain ⟨count,_,exactState⟩ := runBounded_retained_prefix limits ticks (initial source)
  rw [exactState]
  exact rawRun_terminating_resultControl closed terminates count

/-- Finite resource classification follows the actual source-derived raw
progress theorem. Any capacities/ticks yield a genuine finish or retained
suspension, never a semantic refusal or blackhole for a terminating source. -/
 theorem runBounded_only_finish_or_suspend (limits : Limits) (ticks : Nat) (state : State)
    (progress : ∀ count, ResultControl (rawRun count state).control) :
    (∃ value final, runBounded limits ticks state = .finished value final) ∨
      (∃ reason retained, runBounded limits ticks state = .suspended reason retained) := by
  induction ticks generalizing state with
  | zero =>
      have current := progress 0
      cases control : state.control with
      | refused reason | blackhole address | yielded _ => simp [rawRun,control,ResultControl] at current
      | complete value => exact Or.inl ⟨value,state,by simp [runBounded,control]⟩
      | evaluate term environment | enter address | returned value =>
          exact Or.inr ⟨.ticks,state,by simp [runBounded,control]⟩
  | succ ticks ih =>
      have current := progress 0
      cases control : state.control with
      | refused reason | blackhole address | yielded _ => simp [rawRun,control,ResultControl] at current
      | complete value => exact Or.inl ⟨value,state,by simp [runBounded,step,control]⟩
      | evaluate term environment | enter address | returned value =>
          by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
          · have dispatched : step limits state = .suspended .ticks (stepRaw state) := by simp [step,control,fits]
            have nextProgress : ∀ count, ResultControl (rawRun count (stepRaw state)).control := fun count => progress (count+1)
            simpa only [runBounded,dispatched] using ih (stepRaw state) nextProgress
          · have suspended : step limits state = .suspended .capacity state := by simp [step,control,fits]
            exact Or.inr ⟨.capacity,state,by simp only [runBounded,suspended]⟩

 theorem runBounded_terminating_finish_or_suspend {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (limits : Limits) (ticks : Nat) :
    (∃ value final, runBounded limits ticks (initial source) = .finished value final) ∨
      (∃ reason retained, runBounded limits ticks (initial source) = .suspended reason retained) :=
  runBounded_only_finish_or_suspend limits ticks (initial source) (rawRun_terminating_resultControl closed terminates)

/-! Non-vacuity of the r11 source-only premises. Every new r11 theorem whose
premises are `Scoped 0 source` and `Evaluates source result` is instantiated
below at a closed Fix program that genuinely evaluates. The internal graph
lemmas (GraphRepresentsBy / DemandSafety / HeapOriginsBorn premises) are
discharged on actual traces by `rawRun_terminating_graphSafety` from
`graphBy_initializes`, `initial_demandSafety` and `initial_originsBorn`. -/

theorem lazyFixedSource_closed : Scoped 0 lazyFixedSource :=
  .fix (.lam (.lam (.lam (.bound (by decide))))) (.natural 7)

theorem lazyFixedSource_evaluates : Evaluates lazyFixedSource (.lam (.bound 0)) :=
  lazy_fixed_function

theorem lazyFixedSource_resultControl (ticks : Nat) :
    ResultControl (rawRun ticks (initial lazyFixedSource)).control :=
  rawRun_terminating_resultControl lazyFixedSource_closed lazyFixedSource_evaluates ticks

theorem lazyFixedSource_finish_or_suspend (limits : Limits) (ticks : Nat) :
    (∃ value final, runBounded limits ticks (initial lazyFixedSource) = .finished value final) ∨
      (∃ reason retained, runBounded limits ticks (initial lazyFixedSource) = .suspended reason retained) :=
  runBounded_terminating_finish_or_suspend lazyFixedSource_closed lazyFixedSource_evaluates limits ticks

end Obend.Core.Proofs.Adequacy
