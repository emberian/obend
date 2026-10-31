module
/- Ground execution through the kernel's own extraction path is complete.

`execution_source_semantics` (`DataSoundness`) is the soundness half of the Plan output path: any
successful `executeWith` of a closed term extracts THE deep evaluation of the term. This file is
the completeness half for ground observations: a closed term that evaluates to a natural, a boolean
or a label is executed successfully by `execute` (the unrestricted policy) at the trace's own
limits and a budget that pays the observation's bytes, and the extracted Data is that observation.

* `execute_ground_complete`: `Scoped 0 term`, `Evaluates term (observationTerm o)` ⇒ some
  `execute limits budget term` succeeds with `observationData o`.
* `execute_ground_iff`: for every policy, a successful execution extracts `observationData o`
  exactly when the term evaluates to `observationTerm o`.

A structured result (a record, a sum) is read by the kernel only through a ground probe of it
(`Obend.Law.Machine`); deep completeness of `materializeWith` (re-entering field cells from a
settled heap) is not proved here. -/
public import Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Completeness
namespace Obend.Core.Proofs.GroundExecution
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
open Obend.Core.Proofs.Adequacy
open Obend.Core.Proofs.Completeness
open Obend.Core.Proofs.DataSoundness
open Obend.Core.Data
set_option autoImplicit false

/-- A ground observation, as extracted Data. -/
@[expose] public def observationData : Observation → Data
  | .natural n => .natural n
  | .boolean b => .boolean b
  | .label s => .label s

/-- The bytes `materializeWith` charges a ground value. -/
@[expose] public def materialBytes : Observation → Nat
  | .natural n => (toString n).utf8ByteSize + 2
  | .boolean _ => 2
  | .label s => s.utf8ByteSize + (toString s.utf8ByteSize).utf8ByteSize + 2

/-- A byte allowance that pays materialization and then the canonical encoding. -/
@[expose] public def groundBytes (o : Observation) : Nat :=
  materialBytes o + ((encoded 1 (observationData o)).getD []).length

/-- `limits` is at least `bound`, in heap and in stack. -/
@[expose] public def Covers (limits bound : Limits) : Prop :=
  bound.heap ≤ limits.heap ∧ bound.stack ≤ limits.stack

/-- More room and more ticks never change a finished run: a run that finished at `limits` within
`ticks` finishes the same at any limits that cover them, with any more ticks. -/
public theorem runBounded_finished_mono {limits limits' : Limits} (cover : Covers limits' limits) :
    ∀ {ticks ticks' : Nat} {state final : State} {value : RuntimeValue}, ticks ≤ ticks' →
      runBounded limits ticks state = .finished value final →
      runBounded limits' ticks' state = .finished value final := by
  intro ticks
  induction ticks with
  | zero =>
      intro ticks' state final value _ finished
      cases control : state.control <;> simp only [runBounded, control] at finished <;> try contradiction
      cases finished
      cases ticks' with
      | zero => simp [runBounded, control]
      | succ t => simp [runBounded, step, control]
  | succ ticks ih =>
      intro ticks' state final value le finished
      obtain ⟨t, rfl⟩ : ∃ t, ticks' = t + 1 := ⟨ticks' - 1, by omega⟩
      cases control : state.control with
      | complete v =>
          simp only [runBounded, step, control] at finished ⊢
          exact finished
      | refused _ | blackhole _ | yielded _ =>
          simp [runBounded, step, control] at finished
      | evaluate _ _ | enter _ | returned _ =>
          by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
          · have stepped : step limits state = .suspended .ticks (stepRaw state) := by simp [step, control, fits]
            have fits' : (stepRaw state).heap.size ≤ limits'.heap ∧ (stepRaw state).stack.length ≤ limits'.stack :=
              ⟨Nat.le_trans fits.1 cover.1, Nat.le_trans fits.2 cover.2⟩
            have stepped' : step limits' state = .suspended .ticks (stepRaw state) := by simp [step, control, fits']
            simp only [runBounded, stepped] at finished
            simp only [runBounded, stepped']
            exact ih (by omega) finished
          · have stepped : step limits state = .suspended .capacity state := by simp [step, control, fits]
            simp [runBounded, stepped] at finished

theorem materialize_ground (limits : Limits) (o : Observation) (budget : Budget) (state : State)
    (nodes : 1 ≤ budget.nodes) (bytes : materialBytes o ≤ budget.bytes) :
    ∃ r : Result, materializeWith (fun _ => true) limits budget.nodes budget (observationRuntime o) state =
      .ok r ∧ r.value = observationData o ∧ r.state = state := by
  obtain ⟨n, hn⟩ : ∃ n, budget.nodes = n + 1 := ⟨budget.nodes - 1, by omega⟩
  rw [hn]
  cases o with
  | natural k =>
      simp only [materialBytes] at bytes
      simp only [materializeWith, observationRuntime]
      rw [if_neg (by omega), if_neg (by omega)]
      exact ⟨_, rfl, rfl, rfl⟩
  | boolean b =>
      simp only [materialBytes] at bytes
      simp only [materializeWith, observationRuntime]
      rw [if_neg (by omega), if_neg (by omega)]
      exact ⟨_, rfl, rfl, rfl⟩
  | label s =>
      simp only [materialBytes] at bytes
      simp only [materializeWith, observationRuntime]
      rw [if_neg (by omega), if_neg (by omega)]
      exact ⟨_, rfl, rfl, rfl⟩

theorem encoded_ground (o : Observation) {depth : Nat} (h : 1 ≤ depth) :
    encoded depth (observationData o) = encoded 1 (observationData o) ∧
      ∃ bytes, encoded 1 (observationData o) = some bytes := by
  obtain ⟨n, rfl⟩ : ∃ n, depth = n + 1 := ⟨depth - 1, by omega⟩
  cases o <;> exact ⟨rfl, _, rfl⟩

/-- **Ground execution is complete, with enough resources.** A closed term that evaluates to a
ground observation has limits and a tick count past which `execute` succeeds, and every such
execution (at any limits covering them, any more ticks, one node and `groundBytes` bytes or more)
extracts exactly that observation. -/
public theorem execute_ground_complete {term : Term} {o : Observation} (closed : Scoped 0 term)
    (evaluates : Evaluates term (observationTerm o)) :
    ∃ (limits₀ : Limits) (ticks₀ : Nat), ∀ (limits : Limits) (budget : Budget),
      Covers limits limits₀ → ticks₀ ≤ budget.ticks → 1 ≤ budget.nodes → groundBytes o ≤ budget.bytes →
      ∃ e : Execution limits budget term, execute limits budget term = .ok e ∧
        e.extraction.result.value = observationData o := by
  have observes : Observes (observationTerm o) o := by cases o <;> constructor
  obtain ⟨count, final, finished⟩ := runBounded_finite_completion closed evaluates observes
  have graph := runBounded_finished_graph (graph_initializes closed) finished
  have complete := runBounded_finished_control finished
  have emptyStack : final.stack = [] := graph.2.2.1 _ complete
  refine ⟨traceLimits count (initial term), count, fun limits budget cover enough nodes bytes => ?_⟩
  have forced : (forceWith (fun _ => true) limits budget.ticks (initial term)).1 =
      .finished (observationRuntime o) final := by
    rw [forceWith_unrestricted]; exact runBounded_finished_mono cover enough finished
  obtain ⟨enc, encBytes⟩ := encoded_ground o nodes
  obtain ⟨bs, hbs⟩ := encBytes
  have hlen : bs.length ≤ budget.bytes := by
    have : bs.length ≤ groundBytes o := by simp only [groundBytes, hbs, Option.getD_some]; omega
    omega
  unfold execute executeWith
  split
  · rename_i value state ticks heq
    have h1 := congrArg Prod.fst heq
    rw [forced] at h1
    cases h1
    obtain ⟨r, hr, hval, _⟩ := materialize_ground limits o {budget with ticks := ticks} final nodes
      (by simp only [groundBytes] at bytes; show materialBytes o ≤ budget.bytes; omega)
    unfold extractWith
    split
    · rename_i failure hc
      exfalso
      simp only [completeWith, Bool.not_true, Bool.false_eq_true, if_false, complete, emptyStack,
        hr, bind, Except.bind, hval, enc, hbs] at hc
      rw [if_neg (by omega)] at hc
      cases hc
    · rename_i result hc
      refine ⟨_, rfl, ?_⟩
      simp only [completeWith, Bool.not_true, Bool.false_eq_true, if_false, complete, emptyStack,
        hr, bind, Except.bind, hval, enc, hbs] at hc
      rw [if_neg (by omega)] at hc
      cases hc
      exact hval
  all_goals
    rename_i heq
    have h1 := congrArg Prod.fst heq
    rw [forced] at h1
    cases h1

/-- **Ground execution, both ways.** For every policy, limits and budget, a successful execution of
a closed term extracts a ground observation's Data exactly when the term evaluates to it. -/
public theorem execution_ground_iff {policy : State → Bool} {limits : Limits} {budget : Budget} {term : Term}
    (closed : Scoped 0 term) (e : ExecutionWith policy limits budget term) (o : Observation) :
    e.extraction.result.value = observationData o ↔ Evaluates term (observationTerm o) := by
  have sem := (execution_source_semantics closed e).2
  constructor
  · intro h
    have deep := (sem (observationData o)).2 h.symm
    cases o with
    | natural n => cases deep with | natural ev => exact ev
    | boolean b => cases deep with | boolean ev => exact ev
    | label s => cases deep with | label ev => exact ev
  · intro ev
    refine ((sem (observationData o)).1 ?_).symm
    cases o with
    | natural n => exact .natural ev
    | boolean b => exact .boolean ev
    | label s => exact .label ev

end Obend.Core.Proofs.GroundExecution
