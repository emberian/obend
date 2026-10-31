module
/- Demand safety of every raw transition; terminating runs never re-enter a blackhole. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Safety
public import Obend.Core.Proofs.Adequacy.StepRaw
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 theorem graph_next_returned_safety {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (returned : ∃ value, (stepRaw state).control = .returned value) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨value,returned⟩ := returned
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  exact ⟨next,same,current,demandSafety_returned returned⟩

 theorem graph_next_complete_safety {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (complete : ∃ value, (stepRaw state).control = .complete value) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨value,complete⟩ := complete
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  exact ⟨next,same,current,demandSafety_complete complete⟩

 theorem graph_next_ordinary_safety {meaning : AddressMeaning} {state : State} {source : Term} {frame : Frame} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (head : (stepRaw state).stack = frame::rest) (ordinary : ∀ address, frame ≠ .update address) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  exact ⟨next,same,current,graphBy_nonUpdate_head_demandSafety current head ordinary⟩

 theorem graph_administrative_safety {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (successful : ResultControl (stepRaw state).control)
    (administrative : DemandAdministrative state) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  have unchanged : (stepRaw state).heap.size = state.heap.size := by
    cases control : state.control with
    | enter address =>
        cases found : state.heap[address]? with
        | none => simp [stepRaw,control,found]
        | some cell => cases cell <;> simp [stepRaw,control,found]
    | evaluate term environment =>
        cases term <;> try simp [DemandAdministrative,control] at administrative
        case bound index =>
          cases found : environment[index]? <;> simp [stepRaw,control,found]
    | returned value | complete value | refused reason | blackhole address | yielded _ => simp [DemandAdministrative,control] at administrative
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  have agreement : ∀ address, address < (stepRaw state).heap.size → meaning address = next address := by
    intro address allocated; rw [unchanged] at allocated; exact same address allocated
  exact ⟨next,same,current,demandSafety_meaning_congr current.1 agreement
    (stepRaw_demandSafety_administrative safe represented.2.2.2.2.1 born administrative)⟩

/-- Every running/finished actual raw transition preserves the named graph
and active finite-demand safety, including cyclic Fix allocation and sharing.
Fault exclusion is a separate source-termination consequence. -/
 theorem graph_case_return_safety {meaning : AddressMeaning} {state : State} {source body : Term}
    {arms : List (String × Term)} {environment : Environment} {tag key : String} {payload : Address}
    {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.variant tag payload))
    (head : state.stack = .case arms environment::rest)
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_case_return_execution represented returned head found
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 theorem graph_ifBool_return_safety {meaning : AddressMeaning} {state : State} {source whenTrue whenFalse : Term}
    {environment : Environment} {rest : List Frame} {value : Bool} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.boolean value))
    (head : state.stack = .ifBool whenTrue whenFalse environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_ifBool_return_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 public theorem graph_stepRaw_safety_names {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (successful : ResultControl (stepRaw state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  cases control : state.control with
  | complete value => exact graph_next_complete_safety represented successful (by simp [stepRaw,control])
  | refused reason | blackhole address | yielded _ =>
      simp [stepRaw,control,ResultControl] at successful
  | enter address =>
      cases found : state.heap[address]? with
      | none => simp [stepRaw,control,found,ResultControl] at successful
      | some cell =>
          cases cell with
          | suspended origin => exact graph_administrative_safety represented safe born successful (by simp [DemandAdministrative,control])
          | cached origin value => exact graph_next_returned_safety represented successful (by simp [stepRaw,control,found])
          | evaluating origin => simp [stepRaw,control,found,ResultControl] at successful
  | evaluate term environment =>
      cases term with
      | hole n payload => obend_cases payload with [stepRaw, control, ResultControl]
      | bound index =>
          cases found : environment[index]? with
          | none => simp [stepRaw,control,found,ResultControl] at successful
          | some address => exact graph_administrative_safety represented safe born successful (by simp [DemandAdministrative,control])
      | lam body => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | nat number => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | boolean value => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | label name => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | app function argument => exact graph_evaluate_context_safety (context := .argument argument) represented control
      | mix lower upper => exact graph_evaluate_mix_safety represented control
      | fix spec inherited => exact graph_evaluate_fix_safety represented control
      | specification descriptor extension => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | prototype spec target => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | record fields => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | reflect term => exact graph_evaluate_context_safety (context := .reflect) represented control
      | metadata term => exact graph_evaluate_context_safety (context := .metadata) represented control
      | project term => exact graph_evaluate_context_safety (context := .project) represented control
      | get target name => exact graph_evaluate_context_safety (context := .field name) represented control
      | extend inherited fields => exact graph_evaluate_context_safety (context := .extend fields) represented control
      | ifZero value zero body => exact graph_evaluate_context_safety (context := .condition zero body) represented control
      | binary primitive left right => exact graph_evaluate_context_safety (context := .binary primitive right) represented control
      | inject tag payload => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | case scrutinee arms => exact graph_evaluate_context_safety (context := .case arms) represented control
      | ifBool condition whenTrue whenFalse =>
          exact graph_evaluate_context_safety (context := .ifBool whenTrue whenFalse) represented control
      | perform plan =>
          cases shared : forcingShared state.stack <;> simp [stepRaw,control,shared,ResultControl] at successful
      | done value => exact graph_evaluate_done_safety represented control
  | returned value =>
      cases frames : state.stack with
      | nil => exact graph_next_complete_safety represented successful (by simp [stepRaw,control,frames])
      | cons frame rest =>
          cases frame with
          | update address => 
              obtain ⟨origin,found⟩ := busy_update_exists represented.2.1 frames
              exact graph_next_returned_safety represented successful (by simp [stepRaw,control,frames,found])
          | argument argument environment =>
              cases value with
              | closure body captured => exact graph_closure_call_safety represented control frames
              | specification descriptor extension =>
                  exact graph_next_ordinary_safety represented successful
                    (frame := .argument argument environment) (rest := rest)
                    (by simp [stepRaw,control,frames]) (by intro address; simp)
              | natural _ | boolean _ | label _ | record _ | prototype _ _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | reflect =>
              cases value with
              | prototype spec target => exact graph_object_access_safety (access := .reflect) represented control frames
              | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | metadata =>
              cases value with
              | specification descriptor extension => exact graph_object_access_safety (access := .metadata) represented control frames
              | closure _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | project =>
              cases value with
              | prototype spec target => exact graph_object_access_safety (access := .project) represented control frames
              | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | field name =>
              cases value with
              | record fields =>
                  cases found : fields.find? (fun field => field.1 == name) with
                  | none => simp [stepRaw,control,frames,found,ResultControl] at successful
                  | some field =>
                      obtain ⟨key,address⟩ := field
                      exact graph_field_return_safety represented control frames found
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | extend fields environment =>
              cases value with
              | record inherited => exact graph_next_returned_safety represented successful (by simp [stepRaw,control,frames])
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | condition zero body environment =>
              cases value with
              | natural number =>
                  cases number with
                  | zero => exact graph_condition_zero_safety represented control frames
                  | succ number => exact graph_condition_successor_safety represented control frames
              | closure _ _ | specification _ _ | prototype _ _ | record _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | binaryLeft primitive right environment =>
              exact graph_next_ordinary_safety represented successful
                (frame := .binaryRight primitive value) (rest := rest)
                (by simp [stepRaw,control,frames]) (by intro address; simp)
          | binaryRight primitive left =>
              cases dispatch : (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
              | none => simp [stepRaw,control,frames,dispatch,ResultControl] at successful
              | some result =>
                  cases scalar : scalarValue result with
                  | none => simp [stepRaw,control,frames,dispatch,scalar,ResultControl] at successful
                  | some next => exact graph_next_returned_safety represented successful (by simp [stepRaw,control,frames,dispatch,scalar])
          | case arms environment =>
              cases value with
              | variant tag payload =>
                  cases found : arms.find? (fun arm => arm.1 == tag) with
                  | none => simp [stepRaw,control,frames,found,ResultControl] at successful
                  | some arm =>
                      obtain ⟨key,body⟩ := arm
                      exact graph_case_return_safety represented control frames found
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | ifBool whenTrue whenFalse environment =>
              cases value with
              | boolean value => exact graph_ifBool_return_safety represented control frames
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful



 theorem rawRun_graphBy_safety_names {meaning : AddressMeaning} {state : State} {source : Term} {ticks : Nat}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (successful : ResultControl (rawRun ticks state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (rawRun ticks state) source ∧ DemandSafety next (rawRun ticks state) := by
  induction ticks generalizing state meaning with
  | zero => exact ⟨meaning,(fun _ _ => rfl),represented,safe⟩
  | succ ticks ih =>
      have nextSuccessful : ResultControl (stepRaw state).control := rawRun_resultControl successful
      obtain ⟨middle,first,nextRepresented,nextSafe⟩ := graph_stepRaw_safety_names represented safe born nextSuccessful
      have nextBorn := stepRaw_originsBorn represented.1 born
      obtain ⟨next,rest,finalRepresented,finalSafe⟩ := ih nextRepresented nextSafe nextBorn successful
      refine ⟨next,?_,finalRepresented,finalSafe⟩
      intro address allocated
      exact (first address allocated).trans
        (rest address (Nat.lt_of_lt_of_le allocated (stepRaw_preservesOrigins state).1))

/-- Closed source initialization earns the active-update invariant for every
actual running/finished prefix. No heap representation or safety oracle is a
premise, and undemanded divergent fields remain permitted. -/
 theorem rawRun_closed_demandSafety {source : Term} (closed : Scoped 0 source) (ticks : Nat)
    (successful : ResultControl (rawRun ticks (initial source)).control) :
    ∃ meaning : AddressMeaning, GraphRepresentsBy meaning (rawRun ticks (initial source)) source ∧
      DemandSafety meaning (rawRun ticks (initial source)) := by
  obtain ⟨meaning,_,current,safe⟩ := rawRun_graphBy_safety_names (graphBy_initializes closed)
    (initial_demandSafety source _) (initial_originsBorn source) successful
  exact ⟨meaning,current,safe⟩

 theorem graphBy_terminating_control_budget {meaning : AddressMeaning} {state : State} {source result focus : Term}
    (represented : GraphRepresentsBy meaning state source) (terminates : Evaluates source result)
    (control : controlMeaning meaning state.control = some focus) :
    ∃ value cost, SourceDerivation focus value cost := by
  obtain ⟨_,_,_,_,_,before,actual,stack⟩ := represented
  have aligned : before = focus := Option.some.inj (actual.symm.trans control)
  subst before
  have residual := sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates
  obtain ⟨cost,whole⟩ := source_evaluates_derivation residual
  obtain ⟨value,demandCost,demand,_⟩ := stack_derivation_demand whole
  exact ⟨value,demandCost,demand⟩

 public theorem graphBy_terminating_reentry_impossible {meaning : AddressMeaning} {state : State} {source result : Term}
    {address : Address} {origin : Closure} (represented : GraphRepresentsBy meaning state source)
    (safe : DemandSafety meaning state) (terminates : Evaluates source result)
    (enter : state.control = .enter address) (busy : state.heap[address]? = some (.evaluating origin)) : False := by
  obtain ⟨value,cost,demand⟩ := graphBy_terminating_control_budget represented terminates
    (show controlMeaning meaning state.control = some (meaning address) by simp [controlMeaning,enter])
  exact demandSafety_forbids_finite_reentry safe enter busy demand

/-- A terminating independent closed source cannot re-enter any actually
busy thunk at any running prefix of the real graph executor, including tied
Fix. The named graph and safety proof are constructed by the actual trace. -/
 theorem rawRun_terminating_reentry_impossible {source result : Term} {ticks : Nat}
    {address : Address} {origin : Closure} (closed : Scoped 0 source) (terminates : Evaluates source result)
    (enter : (rawRun ticks (initial source)).control = .enter address)
    (busy : (rawRun ticks (initial source)).heap[address]? = some (.evaluating origin)) : False := by
  have successful : ResultControl (rawRun ticks (initial source)).control := by simp [ResultControl,enter]
  obtain ⟨meaning,represented,safe⟩ := rawRun_closed_demandSafety closed ticks successful
  exact graphBy_terminating_reentry_impossible represented safe terminates enter busy


 theorem reachable_closed_demandSafety {source : Term} {state : State} (closed : Scoped 0 source)
    (reachable : Reachable (initial source) state) (successful : ResultControl state.control) :
    ∃ meaning : AddressMeaning, GraphRepresentsBy meaning state source ∧ DemandSafety meaning state := by
  induction reachable with
  | start => exact ⟨_,graphBy_initializes closed,initial_demandSafety source _⟩
  | @next before path ih =>
      have priorSuccessful : ResultControl before.control := rawRun_resultControl (ticks := 1) successful
      obtain ⟨meaning,represented,safe⟩ := ih priorSuccessful
      obtain ⟨next,_,current,nextSafe⟩ := graph_stepRaw_safety_names represented safe
        (reachable_originsBorn closed path) successful
      exact ⟨next,current,nextSafe⟩

 theorem stepRaw_blackhole_origin {state : State} {address : Address}
    (hole : (stepRaw state).control = .blackhole address) :
    state.control = .blackhole address ∨
      (state.control = .enter address ∧ ∃ origin, state.heap[address]? = some (.evaluating origin)) := by
  unfold stepRaw at hole
  split at hole <;> repeat' first | split at hole
  all_goals simp_all

/-- General terminating closed-source consequence for EVERY reachable state:
the actual graph executor never produces a blackhole. This says nothing about
classifying blackholes for arbitrary diverging source computations. -/
 theorem reachable_terminating_no_blackhole {source result : Term} {state : State}
    (closed : Scoped 0 source) (terminates : Evaluates source result)
    (reachable : Reachable (initial source) state) : ∀ address, state.control ≠ .blackhole address := by
  induction reachable with
  | start => intro address; simp [initial]
  | @next before path ih =>
      intro address hole
      rcases stepRaw_blackhole_origin hole with prior | ⟨enter,origin,found⟩
      · exact ih address prior
      · have successful : ResultControl before.control := by simp [ResultControl,enter]
        obtain ⟨meaning,represented,safe⟩ := reachable_closed_demandSafety closed path successful
        exact graphBy_terminating_reentry_impossible represented safe terminates enter found

 theorem rawRun_terminating_no_blackhole {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (ticks : Nat) :
    ∀ address, (rawRun ticks (initial source)).control ≠ .blackhole address :=
  reachable_terminating_no_blackhole closed terminates (rawRun_reachable .start ticks)

end Obend.Core.Proofs.Adequacy
