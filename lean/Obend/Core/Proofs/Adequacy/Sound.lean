module
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Run
public import Obend.Core.Proofs.Adequacy.StepRaw
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

/-- A normally terminating trace never traverses an absorbing fault or
blackhole. This derives the per-step successful classification from the
actual final control, instead of assuming coverage along the trace. -/
 public theorem rawRun_graph {ticks : Nat} {state : State} {source : Term}
    (represented : GraphRepresents state source)
    (successful : ResultControl (rawRun ticks state).control) : GraphRepresents (rawRun ticks state) source := by
  induction ticks generalizing state with
  | zero => exact represented
  | succ ticks ih =>
      have nextSuccessful : ResultControl (stepRaw state).control := rawRun_resultControl successful
      exact ih (graph_stepRaw represented nextSuccessful) successful

/-- Independent source termination gives finite actual administrative progress
at EVERY running/finished raw prefix of the closed program. This is a concrete
executor theorem with no caller-supplied graph representation or acyclicity.
Its endpoint still explicitly allows a fault/blackhole; full completeness must
exclude those endpoints and compose demands through semantic constructors. -/
 theorem rawRun_terminating_administration {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (ticks : Nat)
    (successful : ResultControl (rawRun ticks (initial source)).control) :
    DemandAdministrationHalts (rawRun ticks (initial source)) := by
  exact graph_terminating_administration (rawRun_graph (graph_initializes closed) successful)
    (reachable_originsBorn closed (rawRun_reachable .start ticks)) terminates

 theorem rawRun_natural_sound {ticks : Nat} {source : Term} {number : Nat}
    (closed : Scoped 0 source) (complete : (rawRun ticks (initial source)).control = .complete (.natural number)) :
    Evaluates source (.nat number) := by
  apply graph_complete_natural_sound (rawRun_graph (graph_initializes closed) ?_) complete
  simp only [complete,ResultControl]

 theorem rawRun_boolean_sound {ticks : Nat} {source : Term} {value : Bool}
    (closed : Scoped 0 source) (complete : (rawRun ticks (initial source)).control = .complete (.boolean value)) :
    Evaluates source (.boolean value) := by
  apply graph_complete_boolean_sound (rawRun_graph (graph_initializes closed) ?_) complete
  simp only [complete,ResultControl]

 theorem rawRun_label_sound {ticks : Nat} {source : Term} {name : String}
    (closed : Scoped 0 source) (complete : (rawRun ticks (initial source)).control = .complete (.label name)) :
    Evaluates source (.label name) := by
  apply graph_complete_label_sound (rawRun_graph (graph_initializes closed) ?_) complete
  simp only [complete,ResultControl]

/-- The actual finite-resource executor is sound at EVERY bound: a finished
result supplies its own successful-path classification. Tick/capacity
suspension and blackholes cannot be laundered into source evaluations. -/
 theorem runBounded_finished_graph {limits : Limits} {ticks : Nat} {state final : State}
    {source : Term} {value : RuntimeValue} (represented : GraphRepresents state source)
    (finished : runBounded limits ticks state = .finished value final) : GraphRepresents final source := by
  induction ticks generalizing state with
  | zero =>
      cases control : state.control <;> simp only [runBounded,control] at finished
      all_goals try contradiction
      cases finished
      exact represented
  | succ ticks ih =>
      cases stepped : step limits state with
      | finished value next =>
          have eq : next = state := by
            cases control : state.control <;> simp only [step,control] at stepped
            all_goals try (split at stepped <;> contradiction)
            all_goals try contradiction
            cases stepped; rfl
          simp only [runBounded,stepped] at finished
          cases finished
          simpa only [eq] using represented
      | suspended reason next =>
          cases reason with
          | ticks =>
              have rest : runBounded limits ticks next = .finished value final := by simpa only [runBounded,stepped] using finished
              have raw := step_ticks_raw stepped
              have successful : ResultControl (stepRaw state).control := by
                simpa only [←raw] using runBounded_finished_resultControl rest
              exact ih (by simpa only [raw] using graph_stepRaw represented successful) rest
          | capacity => simp [runBounded,stepped] at finished
      | divergent address next | refused reason next | yielded _ next => simp [runBounded,stepped] at finished

 theorem runBounded_natural_sound {limits : Limits} {ticks : Nat} {source : Term} {number : Nat} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (.natural number) final) :
    Evaluates source (.nat number) :=
  graph_complete_natural_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

 theorem runBounded_boolean_sound {limits : Limits} {ticks : Nat} {source : Term} {value : Bool} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (.boolean value) final) :
    Evaluates source (.boolean value) :=
  graph_complete_boolean_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

 theorem runBounded_label_sound {limits : Limits} {ticks : Nat} {source : Term} {name : String} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (.label name) final) :
    Evaluates source (.label name) :=
  graph_complete_label_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

 theorem runBounded_value_sound {limits : Limits} {ticks : Nat} {source : Term} {value : RuntimeValue} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished value final) :
    ∃ meaning : AddressMeaning, MeaningsScoped final.heap.size meaning ∧ HeapRealizes meaning final.heap ∧
      Evaluates source (valueMeaning meaning value) :=
  graph_complete_value_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

 theorem runBounded_observation_sound {limits : Limits} {ticks : Nat} {source : Term} {result : Observation} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (observationRuntime result) final) :
    Evaluates source (observationTerm result) := by
  cases result with
  | natural _ => exact runBounded_natural_sound closed finished
  | boolean _ => exact runBounded_boolean_sound closed finished
  | label _ => exact runBounded_label_sound closed finished

 theorem runBounded_observes_sound {limits : Limits} {ticks : Nat} {source : Term} {result : Observation} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (observationRuntime result) final) :
    ∃ value, Evaluates source value ∧ Observes value result := by
  refine ⟨observationTerm result,runBounded_observation_sound closed finished,?_⟩
  cases result with
  | natural number => exact Observes.natural number
  | boolean value => exact Observes.boolean value
  | label name => exact Observes.label name

/-- Changing resources cannot change a normally returned ground observation.
This covers every closed partial program and observations of different kinds,
not only repeated numeric fixture runs. Suspension makes no result claim. -/
 theorem runBounded_resource_independent {source : Term} {firstLimits secondLimits : Limits}
    {firstTicks secondTicks : Nat} {first second : Observation} {firstState secondState : State}
    (closed : Scoped 0 source)
    (left : runBounded firstLimits firstTicks (initial source) = .finished (observationRuntime first) firstState)
    (right : runBounded secondLimits secondTicks (initial source) = .finished (observationRuntime second) secondState) :
    first = second := by
  have eq := source_evaluates_unique (runBounded_observation_sound closed left) (runBounded_observation_sound closed right)
  cases first <;> cases second <;> simp [observationTerm] at eq
  all_goals subst_vars; rfl

/-- The finite-resource wrapper realizes the source-derived administrative
progress segment at its concrete trace maxima. This promises progress past
pointer lookup, not normal completion of the entire program. -/
 theorem runBounded_terminating_administration {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (prefixTicks : Nat)
    (successful : ResultControl (rawRun prefixTicks (initial source)).control) :
    ∃ ticks limits, ¬ DemandAdministrative
      (retainedState (runBounded limits ticks (rawRun prefixTicks (initial source)))) := by
  obtain ⟨ticks,stop⟩ := rawRun_terminating_administration closed terminates prefixTicks successful
  refine ⟨ticks,traceLimits ticks (rawRun prefixTicks (initial source)),?_⟩
  simpa only [adequate_trace_execution] using stop

end Obend.Core.Proofs.Adequacy
