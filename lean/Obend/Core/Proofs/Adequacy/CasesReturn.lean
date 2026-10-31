module
/- Name agreement and graph preservation for the returning transitions (fields to closure calls). -/
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

 public theorem graph_field_return_execution {meaning : AddressMeaning} {state : State} {source : Term} {fields : List (String × Address)}
    {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have keyEq : key = name := by simpa using List.find?_some found
  subst key
  have sourceFound : (fields.map fun field => (field.1,meaning field.2)).find? (fun field => field.1 == name) = some (name,meaning address) := by
    simp [List.find?_map,Function.comp_def,found]
  have reduce := Step.field _ name (meaning address) sourceFound
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source (.get (valueMeaning meaning (.record fields)) name) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,meaning address,?_,?_⟩
    · simpa [stepRaw,returned,head,found] using names
    · simpa [stepRaw,returned,head,found] using heap
    · simp [stepRaw,returned,head,found,controlMeaning]
    · simpa [stepRaw,returned,head,found] using advanced
  · refine ⟨[.field name],valueMeaning meaning (.record fields),meaning address,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning,found]
    · simp [stepRaw,returned,head,controlMeaning,found]
    · exact reduce

 public theorem graph_field_return_names {meaning : AddressMeaning} {state : State} {source : Term} {fields : List (String × Address)}
    {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_field_return_execution represented returned head found
  exact ⟨next,same,current⟩

 public theorem graph_evaluate_mix_execution {meaning : AddressMeaning} {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.mix lower upper,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length lower ∧ Scoped environment.length upper := by simpa using valid.1
  have reduce : Step (closeTerm meaning environment (.mix lower upper)) (closeTerm meaning environment (mixBody lower upper)) := by
    rw [closeTerm_mixBody names valid.2 scopes.1 scopes.2]
    have rule := Step.mix (closeTerm meaning environment lower) (closeTerm meaning environment upper)
    cases environment <;> simpa [closeTerm,Term.substitute] using rule
  simp [controlMeaning,evaluate] at control
  subst focus
  have advanced := stackRealizes_steps stack (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment (mixBody lower upper),?_,?_⟩
    · simpa [stepRaw,evaluate] using names
    · simpa [stepRaw,evaluate] using heap
    · simp [stepRaw,evaluate,controlMeaning]
    · simpa [stepRaw,evaluate] using advanced
  · refine ⟨[],closeTerm meaning environment (.mix lower upper),closeTerm meaning environment (mixBody lower upper),?_,?_,?_,?_⟩
    · simp [controlMeaning,evaluate]
    · simp [stepRaw,evaluate,controlMeaning]
    · simp [stepRaw,evaluate,controlMeaning]
    · exact reduce

 public theorem graph_evaluate_mix_names {meaning : AddressMeaning} {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_evaluate_mix_execution represented evaluate
  exact ⟨next,same,current⟩

 public theorem graph_condition_zero_execution {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source
      (.ifZero (.nat 0) (closeTerm meaning environment zero)
        (body.substitute (liftSubstitution (environmentSubstitution meaning environment)))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next (Step.zero _ _) (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment zero,?_,?_⟩
    · simpa [stepRaw,returned,head] using names
    · simpa [stepRaw,returned,head] using heap
    · simp [stepRaw,returned,head,controlMeaning]
    · simpa [stepRaw,returned,head] using advanced
  · refine ⟨[.condition zero body environment],.nat 0,closeTerm meaning environment zero,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · exact Step.zero _ _

 public theorem graph_condition_zero_names {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_condition_zero_execution represented returned head
  exact ⟨next,same,current⟩

 public theorem graph_condition_successor_execution {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment}
    {number : Nat} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have frameValid : FrameValid state.heap.size (.condition zero body environment) :=
    lexical.2.2 _ (head ▸ List.mem_cons_self ..)
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  let extended := extendMeaning meaning state.heap.size (.nat number)
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = .nat number := by simp [extended,extendMeaning]
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; rw [fresh]; exact .natural _
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newCell : CellRealizes extended state.heap.size (.cached ⟨.nat number,[]⟩ (.natural number)) := by
    simp only [CellRealizes,cellOrigin,closeOrigin,closeTerm,valueMeaning,fresh]
    exact ⟨Steps.refl _,Steps.refl _,Value.natural _⟩
  have newHeap := heapRealizes_push (heapRealizes_congr lexical.1 same heap) newCell
  have reduce : Step
      (.ifZero (.nat (number+1)) (closeTerm meaning environment zero)
        (body.substitute (liftSubstitution (environmentSubstitution meaning environment))))
      (closeTerm extended (state.heap.size::environment) body) := by
    rw [←closeTerm_beta names frameValid.1 frameValid.2.2 (Scoped.natural number) same fresh]
    exact Step.successor _ _ _
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source
      (.ifZero (.nat (number+1)) (closeTerm meaning environment zero)
        (body.substitute (liftSubstitution (environmentSubstitution meaning environment)))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have consumers := stackRealizes_congr restValid same before
  have advanced := stackRealizes_steps consumers (Steps.next reduce (Steps.refl _))
  refine ⟨extended,same,?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm extended (state.heap.size::environment) body,?_,?_⟩
    · simpa [stepRaw,returned,head] using newNames
    · simpa [stepRaw,returned,head] using newHeap
    · simp [stepRaw,returned,head,controlMeaning]
    · simpa [stepRaw,returned,head] using advanced
  · refine ⟨[.condition zero body environment],.nat (number+1),closeTerm extended (state.heap.size::environment) body,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · exact reduce

 public theorem graph_condition_successor_names {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment}
    {number : Nat} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_condition_successor_execution represented returned head
  exact ⟨next,same,current⟩

 public theorem graph_extend_record_names {meaning : AddressMeaning} {state : State} {source : Term} {inherited : List (String × Address)}
    {fields : List (String × Term)} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record inherited))
    (head : state.stack = .extend fields environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have validFrame : FrameValid state.heap.size (.extend fields environment) :=
    lexical.2.2 _ (head ▸ List.mem_cons_self ..)
  have validInherited : RuntimeValueValid state.heap.size (.record inherited) := by
    simpa only [returned,ControlValid] using lexical.2.1
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  obtain ⟨extended,newNames,newHeap,same,fieldsEq⟩ :=
    allocateFields_realizes lexical.1 names heap validFrame.1 validFrame.2
  let retained := inherited.filter (fun prior => !(fields.any fun field => field.1 == prior.1))
  let newValue := RuntimeValue.record ((allocateFields state.heap environment fields).2++retained)
  have inheritedEq : inherited.map (fun field => (field.1,extended field.2)) =
      inherited.map (fun field => (field.1,meaning field.2)) := by
    apply List.map_congr_left
    intro field member
    exact Prod.ext rfl (same _ (validInherited field member)).symm
  have denotes : valueMeaning extended newValue =
      .record (extendFields (inherited.map fun field => (field.1,meaning field.2))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) := by
    simp only [newValue,valueMeaning,List.map_append,fieldsEq,extendFields]
    congr 2
    have filtered := List.filter_map (f := fun field : String × Address => (field.1,extended field.2))
      (p := fun prior => !((fields.map fun field => (field.1,closeTerm meaning environment field.2)).any fun field => field.1 == prior.1))
      (l := inherited)
    simpa [retained,List.any_map,Function.comp_def,inheritedEq] using filtered.symm
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (.extend (valueMeaning meaning (.record inherited))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have consumers := stackRealizes_congr restValid same before
  have reduce : Step
      (.extend (valueMeaning meaning (.record inherited))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) (valueMeaning extended newValue) := by
    rw [denotes]
    exact Step.extendRecord _ _
  have advanced := stackRealizes_steps consumers (Steps.next reduce (Steps.refl _))
  refine ⟨extended,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning extended newValue,?_,?_⟩
  · simpa [stepRaw,returned,head] using newNames
  · simpa [stepRaw,returned,head] using newHeap
  · simp [stepRaw,returned,head,controlMeaning,newValue,retained]
  · simpa [stepRaw,returned,head] using advanced

 public theorem graph_evaluate_fix_names {meaning : AddressMeaning} {state : State} {source spec inherited : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.fix spec inherited,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length spec ∧ Scoped environment.length inherited := by
    simpa using valid.1
  let fixSource := closeTerm meaning environment (.fix spec inherited)
  let extended := extendMeaning meaning state.heap.size fixSource
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = fixSource := by simp [extended,extendMeaning]
  have closed : Scoped 0 fixSource := closeTerm_scoped names valid.2 valid.1
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; simpa only [fresh] using closed
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newHeap := heapRealizes_congr lexical.1 same heap
  let body := Term.app (Term.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)
  have originEq : closeTerm extended (state.heap.size::environment) body =
      .app (.app (closeTerm meaning environment spec) fixSource) (closeTerm meaning environment inherited) := by
    simp only [body,closeTerm_app,closeTerm_weaken valid.2 scopes.1 same,
      closeTerm_weaken valid.2 scopes.2 same]
    simp [closeTerm,Term.substitute,environmentSubstitution,fresh]
  have newCell : CellRealizes extended state.heap.size (.suspended ⟨body,state.heap.size::environment⟩) := by
    refine ⟨?_,True.intro⟩
    simp only [cellOrigin,closeOrigin,fresh,originEq]
    simpa only [fixSource,closeTerm_fix] using
      Steps.next (Step.fix (closeTerm meaning environment spec) (closeTerm meaning environment inherited)) (Steps.refl _)
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨extended,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,fixSource,?_,?_⟩
  · simpa [stepRaw,evaluate] using newNames
  · simpa [stepRaw,evaluate,body] using heapRealizes_push newHeap newCell
  · simp [stepRaw,evaluate,controlMeaning,fresh]
  · simpa [stepRaw,evaluate,fixSource] using consumers

 public theorem graph_closure_call_execution {meaning : AddressMeaning} {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have closureValid : RuntimeValueValid state.heap.size (.closure body captured) := by
    simpa only [returned,ControlValid] using lexical.2.1
  have argumentValid : ClosureValid state.heap.size ⟨argument,environment⟩ := by
    have hv := lexical.2.2 (.argument argument environment) (head ▸ List.mem_cons_self ..)
    exact hv
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  let argumentSource := closeTerm meaning environment argument
  let extended := extendMeaning meaning state.heap.size argumentSource
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = argumentSource := by simp [extended,extendMeaning]
  have argClosed : Scoped 0 argumentSource := closeTerm_scoped names argumentValid.2 argumentValid.1
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; simpa only [fresh] using argClosed
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newHeap := heapRealizes_congr lexical.1 same heap
  have newCell : CellRealizes extended state.heap.size (.suspended ⟨argument,environment⟩) := by
    refine ⟨?_,True.intro⟩
    have argSame := closeTerm_meaning_congr argumentValid.2 argumentValid.1 same
    simpa only [fresh,cellOrigin,closeOrigin,←argSame] using Steps.refl argumentSource
  have beta : Step (.app (valueMeaning meaning (.closure body captured)) argumentSource)
      (closeTerm extended (state.heap.size::captured) body) := by
    simp only [valueMeaning,closeTerm_lambda closureValid.1]
    rw [←closeTerm_beta names closureValid.2 closureValid.1 argClosed same fresh]
    exact Step.beta _ _
  simp [returned,controlMeaning] at control
  subst focus
  have consumers : StackRealizes meaning source
      (.app (valueMeaning meaning (.closure body captured)) argumentSource) rest := by
    simpa only [head,StackRealizes,frameMeaning,argumentSource] using stack
  have newConsumers := stackRealizes_congr restValid same consumers
  have advanced := stackRealizes_steps newConsumers (Steps.next beta (Steps.refl _))
  refine ⟨extended,same,?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,
      closeTerm extended (state.heap.size::captured) body,?_,?_⟩
    · simpa [stepRaw,returned,head] using newNames
    · simpa [stepRaw,returned,head] using heapRealizes_push newHeap newCell
    · simp [stepRaw,returned,head,controlMeaning]
    · simpa [stepRaw,returned,head] using advanced
  · refine ⟨[.argument argument environment],valueMeaning meaning (.closure body captured),closeTerm extended (state.heap.size::captured) body,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · exact beta

 public theorem graph_closure_call_names {meaning : AddressMeaning} {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_closure_call_execution represented returned head
  exact ⟨next,same,current⟩

 public theorem graph_field_return {state : State} {source : Term} {fields : List (String × Address)}
    {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_field_return_names byNames returned head found
  exact graphBy_graph advanced

 public theorem graph_evaluate_mix {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_mix_names byNames evaluate
  exact graphBy_graph advanced

 public theorem graph_condition_zero {state : State} {source zero body : Term} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_condition_zero_names byNames returned head
  exact graphBy_graph advanced

 public theorem graph_condition_successor {state : State} {source zero body : Term} {environment : Environment}
    {number : Nat} {rest : List Frame} (represented : GraphRepresents state source)
    (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_condition_successor_names byNames returned head
  exact graphBy_graph advanced

 public theorem graph_extend_record {state : State} {source : Term} {inherited : List (String × Address)}
    {fields : List (String × Term)} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.record inherited))
    (head : state.stack = .extend fields environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_extend_record_names byNames returned head
  exact graphBy_graph advanced

/-- Allocating any lexical Fix ties one stable address to the closed source
Fix and retains its one-step unfolding as the cell origin. This is a general
graph preservation theorem, including nonempty captured environments and
active surrounding update segments. -/
 public theorem graph_evaluate_fix {state : State} {source spec inherited : Term} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_fix_names byNames evaluate
  exact graphBy_graph advanced

/-- General lazy closure beta through the actual allocator. The newly suspended
argument has a closed source name, existing heap names retain their meanings,
and each local update segment advances by the independent source beta rule. -/
 public theorem graph_closure_call {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source)
    (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_closure_call_names byNames returned head
  exact graphBy_graph advanced

end Obend.Core.Proofs.Adequacy
