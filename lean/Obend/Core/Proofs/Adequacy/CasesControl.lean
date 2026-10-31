module
/- Name agreement and graph preservation for the control transitions (application to done). -/
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

 theorem graph_evaluate_application_names {meaning : AddressMeaning} {state : State} {source function argument : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.app function argument) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,evaluate] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment function,?_,?_⟩
  · simpa [stepRaw,evaluate] using names
  · simpa [stepRaw,evaluate] using heap
  · simp [stepRaw,evaluate,controlMeaning]
  · simpa [stepRaw,evaluate,StackRealizes,frameMeaning,closeTerm_app] using stack

 public theorem graph_binary_left_return_names {meaning : AddressMeaning} {state : State} {source right : Term} {primitive : Primitive}
    {environment : Environment} {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned value)
    (head : state.stack = .binaryLeft primitive right environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment right,?_,?_⟩
  · simpa [stepRaw,returned,head] using names
  · simpa [stepRaw,returned,head] using heap
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head,StackRealizes,frameMeaning] using stack

 public theorem graph_complete_return_names {meaning : AddressMeaning} {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned value)
    (empty : state.stack = []) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,returned,empty] using names
  · simpa [stepRaw,returned,empty] using heap
  · simp [stepRaw,returned,empty,controlMeaning]
  · simpa [stepRaw,returned,empty] using stack

 public theorem closeTerm_inject (meaning : AddressMeaning) (environment : Environment) (tag : String) (payload : Term) :
    closeTerm meaning environment (.inject tag payload) = .inject tag (closeTerm meaning environment payload) := by
  cases environment <;> simp [closeTerm,Term.substitute]

/-- Injection allocates exactly one lazy payload thunk; the returned variant
denotes the injected closed payload computation without forcing it. -/
 public theorem graph_evaluate_inject_names {meaning : AddressMeaning} {state : State} {source payload : Term}
    {tag : String} {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.inject tag payload) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.inject tag payload,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scope : Scoped environment.length payload := by simpa using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scope valid.2
  have sourceEq : valueMeaning one (.variant tag state.heap.size) =
      closeTerm meaning environment (.inject tag payload) := by
    simp [valueMeaning,oneFresh,closeTerm_inject]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 oneSame stack
  refine ⟨one,oneSame,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning one (.variant tag state.heap.size),?_,?_⟩
  · simpa [stepRaw,evaluate] using oneNames
  · simpa [stepRaw,evaluate] using oneHeap
  · simp [stepRaw,evaluate,controlMeaning]
  · rw [sourceEq]
    simpa [stepRaw,evaluate] using consumers

 public theorem find_map_arms (arms : List (String × Term)) (f : Term → Term) (tag : String) :
    (arms.map fun arm => (arm.1,f arm.2)).find? (fun arm => arm.1 == tag) =
      (arms.find? (fun arm => arm.1 == tag)).map (fun arm => (arm.1,f arm.2)) := by
  rw [List.find?_map]
  rfl

 theorem find_arm_label {arms : List (String × Term)} {tag key : String} {body : Term}
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) : key = tag := by
  have holds := List.find?_some found
  simpa using holds

/-- A returned variant selects its first matching arm. The binder is a fresh
indirection cell to the shared payload address, and the transition is exactly
independent source case-of-injection reduction. -/
 public theorem graph_case_return_execution {meaning : AddressMeaning} {state : State} {source body : Term}
    {arms : List (String × Term)} {environment : Environment} {tag key : String} {payload : Address}
    {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.variant tag payload))
    (head : state.stack = .case arms environment::rest)
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have keyEq := find_arm_label found
  subst keyEq
  have frameValid : FrameValid state.heap.size (.case arms environment) :=
    lexical.2.2 _ (head ▸ List.mem_cons_self ..)
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  have payloadValid : payload < state.heap.size := by
    simpa only [returned,ControlValid,RuntimeValueValid] using lexical.2.1
  have bodyScope : Scoped (environment.length+1) body :=
    frameValid.2 _ (List.mem_of_find?_eq_some found)
  have bindingCaptures : EnvironmentValid state.heap.size [payload] := by
    intro address member
    simp at member
    subst member
    exact payloadValid
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes (term := .bound 0) lexical.1 names heap (.bound (by simp)) bindingCaptures
  have freshEq : one state.heap.size = meaning payload := by
    rw [oneFresh]
    simp [closeTerm,Term.substitute,environmentSubstitution]
  let sigma := environmentSubstitution meaning environment
  let closedArms := arms.map fun arm => (arm.1,arm.2.substitute (liftSubstitution sigma))
  have closedFound : closedArms.find? (fun arm => arm.1 == key) =
      some (key,body.substitute (liftSubstitution sigma)) := by
    simp only [closedArms]
    rw [find_map_arms,found]
    rfl
  have reduce : Step (.case (.inject key (meaning payload)) closedArms)
      (closeTerm one (state.heap.size::environment) body) := by
    rw [←closeTerm_beta names frameValid.1 bodyScope (names payload payloadValid) oneSame freshEq]
    exact Step.caseInject _ _ _ _ closedFound
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source (.case (.inject key (meaning payload)) closedArms) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have consumers := stackRealizes_congr restValid oneSame before
  have advanced := stackRealizes_steps consumers (Steps.next reduce (Steps.refl _))
  refine ⟨one,oneSame,?_,?_⟩
  · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm one (state.heap.size::environment) body,?_,?_⟩
    · simpa [stepRaw,returned,head,found] using oneNames
    · simpa [stepRaw,returned,head,found] using oneHeap
    · simp [stepRaw,returned,head,found,controlMeaning]
    · simpa [stepRaw,returned,head,found] using advanced
  · refine ⟨[.case arms environment],.inject key (meaning payload),closeTerm one (state.heap.size::environment) body,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,found,controlMeaning]
    · simp [stepRaw,returned,head,found]
    · simpa [stackMeaning,frameMeaning] using reduce

 public theorem graph_case_return_names {meaning : AddressMeaning} {state : State} {source body : Term}
    {arms : List (String × Term)} {environment : Environment} {tag key : String} {payload : Address}
    {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.variant tag payload))
    (head : state.stack = .case arms environment::rest)
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_case_return_execution represented returned head found
  exact ⟨next,same,current⟩

/-- A returned Boolean selects exactly one branch; the other stays latent. -/
 public theorem graph_ifBool_return_execution {meaning : AddressMeaning} {state : State} {source whenTrue whenFalse : Term}
    {environment : Environment} {rest : List Frame} {value : Bool} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.boolean value))
    (head : state.stack = .ifBool whenTrue whenFalse environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source
      (.ifBool (.boolean value) (closeTerm meaning environment whenTrue) (closeTerm meaning environment whenFalse)) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  cases value with
  | true =>
    have advanced := stackRealizes_steps before (Steps.next (Step.ifTrue _ _) (Steps.refl _))
    refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
    · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
        stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment whenTrue,?_,?_⟩
      · simpa [stepRaw,returned,head] using names
      · simpa [stepRaw,returned,head] using heap
      · simp [stepRaw,returned,head,controlMeaning]
      · simpa [stepRaw,returned,head] using advanced
    · refine ⟨[.ifBool whenTrue whenFalse environment],.boolean true,closeTerm meaning environment whenTrue,?_,?_,?_,?_⟩
      · simp [controlMeaning,returned,valueMeaning]
      · simp [stepRaw,returned,head,controlMeaning]
      · simp [stepRaw,returned,head]
      · exact Step.ifTrue _ _
  | false =>
    have advanced := stackRealizes_steps before (Steps.next (Step.ifFalse _ _) (Steps.refl _))
    refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
    · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
        stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment whenFalse,?_,?_⟩
      · simpa [stepRaw,returned,head] using names
      · simpa [stepRaw,returned,head] using heap
      · simp [stepRaw,returned,head,controlMeaning]
      · simpa [stepRaw,returned,head] using advanced
    · refine ⟨[.ifBool whenTrue whenFalse environment],.boolean false,closeTerm meaning environment whenFalse,?_,?_,?_,?_⟩
      · simp [controlMeaning,returned,valueMeaning]
      · simp [stepRaw,returned,head,controlMeaning]
      · simp [stepRaw,returned,head]
      · exact Step.ifFalse _ _

 public theorem graph_ifBool_return_names {meaning : AddressMeaning} {state : State} {source whenTrue whenFalse : Term}
    {environment : Environment} {rest : List Frame} {value : Bool} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.boolean value))
    (head : state.stack = .ifBool whenTrue whenFalse environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_ifBool_return_execution represented returned head
  exact ⟨next,same,current⟩

 public theorem closeTerm_perform (meaning : AddressMeaning) (environment : Environment) (plan : Term) :
    closeTerm meaning environment (.perform plan) = .perform (closeTerm meaning environment plan) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem closeTerm_done (meaning : AddressMeaning) (environment : Environment) (value : Term) :
    closeTerm meaning environment (.done value) = .done (closeTerm meaning environment value) := by
  cases environment <;> simp [closeTerm,Term.substitute]

/-- A perform outside every shared cell allocates its plan as one lazy cell and
yields; the yielded control still means the same source redex `perform plan`,
so no source step is claimed or needed. -/
 public theorem graph_evaluate_perform_names {meaning : AddressMeaning} {state : State} {source plan : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.perform plan) environment)
    (direct : forcingShared state.stack = false) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.perform plan,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scope : Scoped environment.length plan := by simpa using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scope valid.2
  have sourceEq : Term.perform (one state.heap.size) = closeTerm meaning environment (.perform plan) := by
    simp [oneFresh,closeTerm_perform]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 oneSame stack
  refine ⟨one,oneSame,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,.perform (one state.heap.size),?_,?_⟩
  · simpa [stepRaw,evaluate,direct] using oneNames
  · simpa [stepRaw,evaluate,direct] using oneHeap
  · simp [stepRaw,evaluate,direct,controlMeaning]
  · rw [sourceEq]
    simpa [stepRaw,evaluate,direct] using consumers

/-- `done` is exactly the independent source reduction `done v → v`. -/
 public theorem graph_evaluate_done_execution {meaning : AddressMeaning} {state : State} {source value : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.done value) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have reduce : Step (closeTerm meaning environment (.done value)) (closeTerm meaning environment value) := by
    rw [closeTerm_done]; exact Step.done _
  simp [controlMeaning,evaluate] at control
  subst focus
  have advanced := stackRealizes_steps stack (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment value,?_,?_⟩
    · simpa [stepRaw,evaluate] using names
    · simpa [stepRaw,evaluate] using heap
    · simp [stepRaw,evaluate,controlMeaning]
    · simpa [stepRaw,evaluate] using advanced
  · refine ⟨[],closeTerm meaning environment (.done value),closeTerm meaning environment value,?_,?_,?_,?_⟩
    · simp [controlMeaning,evaluate]
    · simp [stepRaw,evaluate,controlMeaning]
    · simp [stepRaw,evaluate,controlMeaning]
    · exact reduce

 public theorem graph_evaluate_done_names {meaning : AddressMeaning} {state : State} {source value : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.done value) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_evaluate_done_execution represented evaluate
  exact ⟨next,same,current⟩

/-- Entering a source application installs the lexical argument continuation;
its semantic demand segment is the independently defined source application. -/
 theorem graph_evaluate_application {state : State} {source function argument : Term}
    {environment : Environment} (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.app function argument) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_application_names byNames evaluate
  exact graphBy_graph advanced

/-- Binary evaluation switches from the left demand to the right one without
forcing any captured arguments of the returned left value. -/
 public theorem graph_binary_left_return {state : State} {source right : Term} {primitive : Primitive}
    {environment : Environment} {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (head : state.stack = .binaryLeft primitive right environment::rest) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_binary_left_return_names byNames returned head
  exact graphBy_graph advanced

 public theorem graph_complete_return {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (empty : state.stack = []) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_complete_return_names byNames returned empty
  exact graphBy_graph advanced

end Obend.Core.Proofs.Adequacy
