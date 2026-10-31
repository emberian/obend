module
/- `rawRun` and `runBounded`: traces, budgets, retained states. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Origins
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 public theorem originBorn_capture_bound {address : Address} {origin : Closure}
    (born : OriginBorn address origin) : EnvironmentValid (address+1) origin.environment := by
  rcases born with ordinary | ⟨spec,inherited,captured,environmentEq,captures,termEq⟩
  · intro reference member; exact Nat.lt_trans (ordinary reference member) (Nat.lt_succ_self _)
  · rw [environmentEq]
    intro reference member
    rcases List.mem_cons.mp member with equal | old
    · subst reference; exact Nat.lt_succ_self _
    · exact Nat.lt_trans (captures reference old) (Nat.lt_succ_self _)

/-- Actual administrative demand segments are finite by lexicographic descent
on independent source cost and lexical birth address. This allows real tied
Fix and sharing; it assumes neither an acyclic heap nor finite unfolding. -/
 theorem administrative_budget_halts (cost cap : Nat) : AdministrativeBudget cost cap := by
  induction cost using Nat.strongRecOn generalizing cap with
  | ind cost costIH =>
      induction cap using Nat.strongRecOn with
      | ind cap capIH =>
          have allEnters : ∀ (meaning : AddressMeaning) (state : State), HeapRealizes meaning state.heap → HeapOriginsBorn state.heap →
              ∀ (address : Address) (result : Term), state.control = .enter address → address+1 ≤ cap →
              SourceDerivation (meaning address) result cost → DemandAdministrationHalts state := by
            intro meaning state heap born address result enter addressCap derivation
            cases found : state.heap[address]? with
            | none => exact ⟨1,by simp [rawRun,stepRaw,enter,found,DemandAdministrative]⟩
            | some cell =>
                cases cell with
                | evaluating origin => exact ⟨1,by simp [rawRun,stepRaw,enter,found,DemandAdministrative]⟩
                | cached origin value => exact ⟨1,by simp [rawRun,stepRaw,enter,found,DemandAdministrative]⟩
                | suspended origin =>
                    have old := heap address _ found
                    have originBorn := born address _ found
                    have nextHeap : HeapRealizes meaning (stepRaw state).heap := by
                      simpa [stepRaw,enter,found] using heapRealizes_set heap (show CellRealizes meaning address (.evaluating origin) from old)
                    have nextBorn : HeapOriginsBorn (stepRaw state).heap := by
                      simpa [stepRaw,enter,found] using heapOriginsBorn_set born found (show cellOrigin (.evaluating origin) = cellOrigin (.suspended origin) from rfl)
                    have nextControl : (stepRaw state).control = .evaluate origin.term origin.environment := by simp [stepRaw,enter,found]
                    have halted : DemandAdministrationHalts (stepRaw state) := by
                      rcases originBorn_demand_descent originBorn old.1 derivation with captures | ⟨smaller,tail,less⟩
                      · obtain ⟨smaller,tail,le⟩ := sourceSteps_derivation_tail old.1 derivation
                        by_cases less : smaller < cost
                        · exact (costIH smaller less address meaning (stepRaw state) nextHeap nextBorn).2
                            origin.term origin.environment result nextControl captures tail
                        · have equal : smaller = cost := by omega
                          subst smaller
                          exact (capIH address (Nat.lt_of_lt_of_le (Nat.lt_succ_self address) addressCap) meaning (stepRaw state) nextHeap nextBorn).2
                            origin.term origin.environment result nextControl captures tail
                      · exact (costIH smaller less (address+1) meaning (stepRaw state) nextHeap nextBorn).2
                          origin.term origin.environment result nextControl (originBorn_capture_bound originBorn) tail
                    obtain ⟨ticks,stop⟩ := halted
                    exact ⟨ticks+1,stop⟩
          intro meaning state heap born
          refine ⟨allEnters meaning state heap born,?_⟩
          intro term environment result evaluate captures derivation
          by_cases isBound : ∃ index, term = .bound index
          · obtain ⟨index,rfl⟩ := isBound
            cases found : environment[index]? with
            | none => exact ⟨1,by simp [rawRun,stepRaw,evaluate,found,DemandAdministrative]⟩
            | some address =>
                have addressCap : address+1 ≤ cap := by
                  have less := captures address (List.mem_of_getElem? found)
                  exact Nat.succ_le_of_lt less
                have demand : SourceDerivation (meaning address) result cost := by
                  cases environment with
                  | nil => simp at found
                  | cons reference references =>
                      simpa [closeTerm,Term.substitute,environmentSubstitution,found] using derivation
                have nextHeap : HeapRealizes meaning (stepRaw state).heap := by simpa [stepRaw,evaluate,found] using heap
                have nextBorn : HeapOriginsBorn (stepRaw state).heap := by simpa [stepRaw,evaluate,found] using born
                have nextControl : (stepRaw state).control = .enter address := by simp [stepRaw,evaluate,found]
                obtain ⟨ticks,stop⟩ := allEnters meaning (stepRaw state) nextHeap nextBorn
                  address result nextControl addressCap demand
                exact ⟨ticks+1,stop⟩
          · refine ⟨0,?_⟩
            cases term <;> simp_all [rawRun,DemandAdministrative]

 theorem traceFits_mono {ticks : Nat} {state : State} {small large : Limits}
    (fits : TraceFits small ticks state) (heap : small.heap ≤ large.heap)
    (stack : small.stack ≤ large.stack) : TraceFits large ticks state := by
  induction ticks generalizing state with
  | zero => trivial
  | succ ticks ih =>
      exact ⟨Nat.le_trans fits.1 heap,Nat.le_trans fits.2.1 stack,ih fits.2.2⟩

 theorem traceFits_traceLimits (ticks : Nat) (state : State) :
    TraceFits (traceLimits ticks state) ticks state := by
  induction ticks generalizing state with
  | zero => trivial
  | succ ticks ih =>
      refine ⟨Nat.le_max_left _ _,Nat.le_max_left _ _,?_⟩
      exact traceFits_mono (ih (stepRaw state)) (Nat.le_max_right _ _) (Nat.le_max_right _ _)

 public theorem rawRun_absorbs {state : State} (ticks : Nat) (absorbs : stepRaw state = state) :
    rawRun ticks state = state := by
  induction ticks with
  | zero => rfl
  | succ ticks ih => simpa only [rawRun,absorbs] using ih

 public theorem rawRun_resultControl {ticks : Nat} {state : State}
    (successful : ResultControl (rawRun ticks state).control) : ResultControl state.control := by
  cases control : state.control with
  | evaluate _ _ | enter _ | returned _ | complete _ => trivial
  | refused reason | blackhole address | yielded _ =>
      have absorbing : stepRaw state = state := by simp [stepRaw,control]
      simp only [rawRun_absorbs ticks absorbing,control,ResultControl] at successful

 public theorem graph_terminating_administration {state : State} {source result : Term}
    (represented : GraphRepresents state source) (born : HeapOriginsBorn state.heap)
    (terminates : Evaluates source result) : DemandAdministrationHalts state := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  obtain ⟨wholeCost,whole⟩ := source_evaluates_derivation
    (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
  obtain ⟨value,cost,demand,_⟩ := stack_derivation_demand whole
  have valid := lexical.2.1
  cases current : state.control with
  | evaluate term environment =>
      simp only [current,controlMeaning,Option.some.injEq] at control
      subst focus
      have evalValid : ClosureValid state.heap.size ⟨term,environment⟩ := by
        simpa only [current,ControlValid] using valid
      exact (administrative_budget_halts cost state.heap.size meaning state heap born).2
        term environment value current evalValid.2 demand
  | enter address =>
      simp only [current,controlMeaning,Option.some.injEq] at control
      subst focus
      have allocated : address < state.heap.size := by simpa only [current,ControlValid] using valid
      exact (administrative_budget_halts cost state.heap.size meaning state heap born).1
        address value current (Nat.succ_le_of_lt allocated) demand
  | returned value | complete value | refused reason | blackhole address | yielded _ =>
      exact ⟨0,by simp [rawRun,DemandAdministrative,current]⟩

 public theorem rawRun_reachable {start state : State} (reachable : Reachable start state) (ticks : Nat) :
    Reachable start (rawRun ticks state) := by
  induction ticks generalizing state with
  | zero => exact reachable
  | succ ticks ih => exact ih (.next reachable)

/-- Phase provenance is genuinely required for completeness. Even the graph
relation plus birth-valid origins and a terminating source can be fabricated
with an unearned evaluating phase. Actual reachability must exclude this
state; treating GraphRepresents as a completeness oracle would be unsound. -/
 theorem represented_born_blackhole_counterexample :
    ∃ state : State, GraphRepresents state (.nat 0) ∧ HeapOriginsBorn state.heap ∧
      Evaluates (.nat 0) (.nat 0) ∧ (stepRaw state).control = .blackhole 0 := by
  let state : State := ⟨#[.evaluating ⟨.nat 0,[]⟩],.enter 0,[.update 0]⟩
  have singleton : ∀ address cell, state.heap[address]? = some cell →
      address = 0 ∧ cell = .evaluating ⟨.nat 0,[]⟩ := by
    intro address cell found
    have allocated := (Array.getElem?_eq_some_iff.mp found).1
    have addressEq : address = 0 := by change address < 1 at allocated; omega
    subst address
    exact ⟨rfl,by simpa [state] using found.symm⟩
  have lexical : LexicalInvariant state := by
    refine ⟨?_,by simp [state,ControlValid],?_⟩
    · intro address cell found
      obtain ⟨rfl,rfl⟩ := singleton address cell found
      exact ⟨.natural _,by simp [EnvironmentValid]⟩
    · intro frame member
      simp [state] at member
      subst frame
      simp [FrameValid,state]
  have busy : BusyInvariant state := by
    simp only [BusyInvariant,Busy,state,stackUpdates,List.nodup_cons,List.nodup_nil,List.not_mem_nil,true_and,not_false_eq_true]
    intro address
    cases address <;> simp
  have realized : HeapRealizes (fun _ => .nat 0) state.heap := by
    intro address cell found
    obtain ⟨rfl,rfl⟩ := singleton address cell found
    exact ⟨.refl _,trivial⟩
  refine ⟨state,⟨lexical,busy,?_,fun _ => .nat 0,?_,realized,.nat 0,rfl,?_⟩,?_,⟨.refl _,.natural _⟩,?_⟩
  · intro value complete; cases complete
  · intro address allocated; exact .natural _
  · exact ⟨.refl _,.refl _⟩
  · intro address cell found
    obtain ⟨rfl,rfl⟩ := singleton address cell found
    exact Or.inl (by simp [EnvironmentValid,cellOrigin])
  · simp [stepRaw,state]

 theorem step_finished_control {limits : Limits} {state final : State} {value : RuntimeValue}
    (finished : step limits state = .finished value final) : final.control = .complete value := by
  cases control : state.control <;> simp only [step,control] at finished
  all_goals try (split at finished <;> contradiction)
  all_goals try contradiction
  cases finished
  exact control

 public theorem step_ticks_raw {limits : Limits} {state next : State}
    (stepped : step limits state = .suspended .ticks next) : next = stepRaw state := by
  cases control : state.control <;> simp only [step,control] at stepped
  all_goals try contradiction
  all_goals split at stepped <;> simp_all

 public theorem runBounded_finished_control {limits : Limits} {ticks : Nat} {state final : State} {value : RuntimeValue}
    (finished : runBounded limits ticks state = .finished value final) : final.control = .complete value := by
  induction ticks generalizing state with
  | zero =>
      cases control : state.control <;> simp only [runBounded,control] at finished
      all_goals try contradiction
      cases finished
      exact control
  | succ ticks ih =>
      cases stepped : step limits state with
      | finished value next =>
          simp only [runBounded,stepped] at finished
          cases finished
          exact step_finished_control stepped
      | suspended reason next =>
          cases reason with
          | ticks => exact ih (by simpa only [runBounded,stepped] using finished)
          | capacity => simp [runBounded,stepped] at finished
      | divergent address next | refused reason next | yielded _ next => simp [runBounded,stepped] at finished

 public theorem runBounded_finished_resultControl {limits : Limits} {ticks : Nat} {state final : State} {value : RuntimeValue}
    (finished : runBounded limits ticks state = .finished value final) : ResultControl state.control := by
  cases control : state.control with
  | evaluate _ _ | enter _ | returned _ | complete _ => trivial
  | blackhole address | refused reason | yielded _ =>
      cases ticks <;> simp [runBounded,step,control] at finished

 theorem runBounded_retains_rawRun {limits : Limits} {ticks : Nat} {state : State}
    (fits : TraceFits limits ticks state) :
    retainedState (runBounded limits ticks state) = rawRun ticks state := by
  induction ticks generalizing state with
  | zero => cases control : state.control <;> simp [runBounded,rawRun,retainedState,control]
  | succ ticks ih =>
      have next := ih fits.2.2
      cases control : state.control
      all_goals first
        | have admitted : step limits state = .suspended .ticks (stepRaw state) := by
            simp [step,control,fits.1,fits.2.1]
          simpa only [runBounded,admitted,rawRun] using next
        | have absorbing : stepRaw state = state := by simp [stepRaw,control]
          simpa only [runBounded,step,control,retainedState] using
            (rawRun_absorbs (ticks+1) absorbing).symm

set_option linter.unnecessarySimpa false in
 theorem runBounded_complete_classifies {limits : Limits} {ticks : Nat} {state : State}
    {value : RuntimeValue}
    (complete : (retainedState (runBounded limits ticks state)).control = .complete value) :
    runBounded limits ticks state =
      .finished value (retainedState (runBounded limits ticks state)) := by
  induction ticks generalizing state with
  | zero => cases control : state.control <;> simp_all [runBounded,retainedState]
  | succ ticks ih =>
      cases control : state.control
      all_goals first
        | simpa [runBounded,step,control,retainedState] using complete
        | by_cases within : (stepRaw state).heap.size ≤ limits.heap ∧
              (stepRaw state).stack.length ≤ limits.stack
          · have admitted : step limits state = .suspended .ticks (stepRaw state) := by
              simp [step,control,within.1,within.2]
            simp only [runBounded,admitted] at complete ⊢
            exact ih complete
          · have capacity : step limits state = .suspended .capacity state := by
              simp [step,control,Bool.and_eq_true,within]
            simp only [runBounded,capacity,retainedState] at complete
            rw [control] at complete
            contradiction

 public theorem adequate_trace_execution (ticks : Nat) (state : State) :
    retainedState (runBounded (traceLimits ticks state) ticks state) = rawRun ticks state :=
  runBounded_retains_rawRun (traceFits_traceLimits ticks state)

 public theorem adequate_trace_completion {ticks : Nat} {state : State} {value : RuntimeValue}
    (complete : (rawRun ticks state).control = .complete value) :
    runBounded (traceLimits ticks state) ticks state = .finished value (rawRun ticks state) := by
  have retained := adequate_trace_execution ticks state
  have classified := runBounded_complete_classifies (retained ▸ complete)
  simpa only [retained] using classified

 theorem rawRun_lexicalInvariant {source : Term} (closed : Scoped 0 source) (ticks : Nat) :
    LexicalInvariant (rawRun ticks (initial source)) := by
  have general : ∀ ticks state, LexicalInvariant state → LexicalInvariant (rawRun ticks state) := by
    intro ticks
    induction ticks with
    | zero => intro state invariant; exact invariant
    | succ ticks ih => intro state invariant; exact ih _ (stepRaw_lexicalInvariant invariant)
  exact general ticks _ (initial_lexicalInvariant closed)

 theorem rawRun_preservesOrigins (ticks : Nat) (state : State) :
    PreservesOrigins state.heap (rawRun ticks state).heap := by
  induction ticks generalizing state with
  | zero => exact preservesOrigins_refl _
  | succ ticks ih => exact preservesOrigins_trans (stepRaw_preservesOrigins _) (ih _)

 theorem rawRun_preservesCached (ticks : Nat) (state : State) :
    PreservesCached state.heap (rawRun ticks state).heap := by
  induction ticks generalizing state with
  | zero => exact preservesCached_refl _
  | succ ticks ih => exact preservesCached_trans (stepRaw_preservesCached _) (ih _)

end Obend.Core.Proofs.Adequacy
