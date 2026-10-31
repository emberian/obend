module
/- Name agreement and graph preservation for the evaluating transitions (context to record). -/
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

 public theorem graph_evaluate_context_names {meaning : AddressMeaning} {state : State} {source hole : Term} {context : DemandContext} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have scope : Scoped environment.length (context.term hole) := by
    have valid := lexical.2.1
    rw [evaluate] at valid
    exact valid.1
  simp [controlMeaning,evaluate] at control
  subst focus
  have dispatched := demandContext_dispatch evaluate
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment hole,?_,?_⟩
  · simpa only [dispatched] using names
  · simpa only [dispatched] using heap
  · simp only [dispatched,controlMeaning]
  · rw [demandContext_closes context meaning environment hole scope] at stack
    cases context <;> simpa only [dispatched,DemandContext.frame,StackRealizes] using stack

 public theorem graph_evaluate_bound_names {meaning : AddressMeaning} {state : State} {source : Term} {environment : Environment} {index address : Nat}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.bound index) environment)
    (found : environment[index]? = some address) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have closes : closeTerm meaning environment (.bound index) = meaning address := by
    cases environment with
    | nil => simp at found
    | cons _ _ => simp [closeTerm,Term.substitute,environmentSubstitution,found]
  simp [controlMeaning,evaluate,closes] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,meaning address,?_,?_⟩
  · simpa [stepRaw,evaluate,found] using names
  · simpa [stepRaw,evaluate,found] using heap
  · simp [stepRaw,evaluate,found,controlMeaning]
  · simpa [stepRaw,evaluate,found] using stack

 public theorem graph_evaluate_immediate_names {meaning : AddressMeaning} {state : State} {source : Term} {immediate : ImmediateValue} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate immediate.term environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have denotes : valueMeaning meaning (immediate.runtime environment) = closeTerm meaning environment immediate.term := by
    cases immediate <;> cases environment <;> simp [ImmediateValue.term,ImmediateValue.runtime,valueMeaning,closeTerm,Term.substitute]
  simp [controlMeaning,evaluate] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning (immediate.runtime environment),?_,?_⟩
  · cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using names
  · cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using heap
  · cases immediate <;> simp [stepRaw,evaluate,ImmediateValue.term,ImmediateValue.runtime,controlMeaning]
  · rw [denotes]
    cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using stack

 public theorem graph_object_access_execution {meaning : AddressMeaning} {state : State} {source : Term} {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (frameMeaning meaning access.frame (valueMeaning meaning (access.value first second))) rest := by
    cases access <;> simpa [head,ObjectAccess.frame,StackRealizes] using stack
  have reduce : Step (frameMeaning meaning access.frame (valueMeaning meaning (access.value first second)))
      (meaning (access.address first second)) := by
    cases access with
    | reflect => exact Step.reflectPrototype _ _
    | metadata => exact Step.metadataSpecification _ _
    | project => exact Step.projectPrototype _ _
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,meaning (access.address first second),?_,?_⟩
    · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using names
    · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using heap
    · cases access <;> simp [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value,ObjectAccess.address,controlMeaning]
    · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using advanced
  · refine ⟨[access.frame],valueMeaning meaning (access.value first second),meaning (access.address first second),?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · cases access <;> simp [stepRaw,returned,head,controlMeaning,ObjectAccess.frame,ObjectAccess.value,ObjectAccess.address]
    · cases access <;> simp [stepRaw,returned,head,controlMeaning,ObjectAccess.frame,ObjectAccess.value,ObjectAccess.address]
    · exact reduce

 public theorem graph_object_access_names {meaning : AddressMeaning} {state : State} {source : Term} {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_object_access_execution represented returned head
  exact ⟨next,same,current⟩

 public theorem graph_specification_call_names {meaning : AddressMeaning} {state : State} {source argument : Term} {environment : Environment}
    {descriptor extension : Address} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.specification descriptor extension))
    (head : state.stack = .argument argument environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (.app (.specification (meaning descriptor) (meaning extension)) (closeTerm meaning environment argument)) rest := by
    simpa only [head,StackRealizes,frameMeaning,valueMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next (Step.applySpecification _ _ _) (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,meaning extension,?_,?_⟩
  · simpa [stepRaw,returned,head] using names
  · simpa [stepRaw,returned,head] using heap
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head,StackRealizes,frameMeaning] using advanced

 public theorem graph_primitive_return_names {meaning : AddressMeaning} {state : State} {source result : Term} {primitive : Primitive}
    {left right next : RuntimeValue} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned right)
    (head : state.stack = .binaryRight primitive left::rest)
    (dispatch : (valueTerm left).bind (fun l => (valueTerm right).bind (primitiveResult primitive l)) = some result)
    (scalar : scalarValue result = some next) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  obtain ⟨leftTerm,leftFound,rightResult⟩ := Option.bind_eq_some_iff.mp dispatch
  obtain ⟨rightTerm,rightFound,primitiveFound⟩ := Option.bind_eq_some_iff.mp rightResult
  have reduce : Step (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) (valueMeaning meaning next) := by
    have rule := Step.primitive primitive _ _ result (valueMeaning_value meaning left) (valueMeaning_value meaning right)
      (by simpa only [valueTerm_meaning leftFound meaning,valueTerm_meaning rightFound meaning] using primitiveFound)
    simpa only [scalarValue_meaning scalar meaning] using rule
  have before : StackRealizes meaning source (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning next,?_,?_⟩
  · simpa [stepRaw,returned,head,dispatch,scalar] using names
  · simpa [stepRaw,returned,head,dispatch,scalar] using heap
  · simp [stepRaw,returned,head,dispatch,scalar,controlMeaning]
  · simpa [stepRaw,returned,head,dispatch,scalar] using advanced

 public theorem graph_enter_suspended_names {meaning : AddressMeaning} {state : State} {source : Term} {address : Nat} {origin : Closure}
    (represented : GraphRepresentsBy meaning state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.suspended origin)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,enter] at control
  subst focus
  have oldCell := heap address _ found
  have newCell : CellRealizes meaning address (.evaluating origin) := oldCell
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    closeOrigin meaning origin,?_,?_⟩
  · simpa [stepRaw,enter,found] using names
  · simpa [stepRaw,enter,found] using heapRealizes_set heap newCell
  · simp [stepRaw,enter,found,controlMeaning,closeOrigin]
  · simpa [stepRaw,enter,found,StackRealizes,cellOrigin] using And.intro oldCell.1 stack

 public theorem graph_cache_update_names {meaning : AddressMeaning} {state : State} {source : Term} {address : Nat}
    {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned value)
    (update : state.stack = .update address::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  obtain ⟨origin,found⟩ := busy_update_exists busy update
  simp [controlMeaning,returned] at control
  subst focus
  have segments : StackRealizes meaning source (valueMeaning meaning value) (.update address::rest) :=
    update ▸ stack
  have cached := cachedCell_realizes heap found segments
  have consumers := stackRealizes_steps segments.2 segments.1
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,returned,update,found] using names
  · simpa [stepRaw,returned,update,found] using heapRealizes_set heap cached
  · simp [stepRaw,returned,update,found,controlMeaning]
  · simpa [stepRaw,returned,update,found] using consumers

 public theorem graph_enter_cached_names {meaning : AddressMeaning} {state : State} {source : Term} {address : Nat}
    {origin : Closure} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.cached origin value)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,enter] at control
  subst focus
  have cached := heap address _ found
  have consumed := stackRealizes_steps stack cached.2.1
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,enter,found] using names
  · simpa [stepRaw,enter,found] using heap
  · simp [stepRaw,enter,found,controlMeaning]
  · simpa [stepRaw,enter,found] using consumed

 public theorem graph_evaluate_pair_names {meaning : AddressMeaning} {state : State} {source first second : Term} {environment : Environment}
    {kind : PairObject} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (kind.term first second) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨kind.term first second,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length first ∧ Scoped environment.length second := by
    cases kind <;> simpa [PairObject.term] using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scopes.1 valid.2
  have oneValid := heapValid_push lexical.1
    (show CellValid (state.heap.size+1) (.suspended ⟨first,environment⟩) from
      ⟨scopes.1,environmentValid_mono valid.2 (Nat.le_succ _)⟩)
  have capturesOne : EnvironmentValid (state.heap.push (.suspended ⟨first,environment⟩)).size environment :=
    environmentValid_mono valid.2 (by simp)
  obtain ⟨two,twoNames,twoHeap,twoSame,twoFresh⟩ :=
    allocateClosure_realizes oneValid oneNames oneHeap scopes.2 capturesOne
  have same : ∀ address, address < state.heap.size → meaning address = two address := by
    intro address allocated
    exact (oneSame address allocated).trans (twoSame address (by simpa using Nat.lt_succ_of_lt allocated))
  have firstEq : two state.heap.size = closeTerm meaning environment first := by
    rw [←twoSame state.heap.size (by simp),oneFresh]
  have secondEq : two (state.heap.size+1) = closeTerm meaning environment second := by
    have closeEq := closeTerm_meaning_congr valid.2 scopes.2 oneSame
    simpa only [Array.size_push,←closeEq] using twoFresh
  have sourceEq : valueMeaning two (kind.value state.heap.size (state.heap.size+1)) =
      closeTerm meaning environment (kind.term first second) := by
    cases kind <;> cases environment <;> simp [PairObject.term,PairObject.value,valueMeaning,firstEq,secondEq,closeTerm,Term.substitute]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨two,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning two (kind.value state.heap.size (state.heap.size+1)),?_,?_⟩
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoNames
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoHeap
  · cases kind <;> simp [stepRaw,evaluate,PairObject.term,PairObject.value,controlMeaning]
  · rw [sourceEq]
    cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using consumers

 public theorem graph_evaluate_record_names {meaning : AddressMeaning} {state : State} {source : Term} {fields : List (String × Term)} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.record fields) environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.record fields,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : ∀ field ∈ fields, Scoped environment.length field.2 := by simpa using valid.1
  obtain ⟨extended,newNames,newHeap,same,fieldsEq⟩ := allocateFields_realizes lexical.1 names heap valid.2 scopes
  have denotes : valueMeaning extended (.record (allocateFields state.heap environment fields).2) =
      closeTerm meaning environment (.record fields) := by simp only [valueMeaning,fieldsEq,closeTerm_record]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨extended,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning extended (.record (allocateFields state.heap environment fields).2),?_,?_⟩
  · simpa [stepRaw,evaluate] using newNames
  · simpa [stepRaw,evaluate] using newHeap
  · simp [stepRaw,evaluate,controlMeaning]
  · rw [denotes]
    simpa [stepRaw,evaluate] using consumers

/-- Every demand-starting context advances through the real dispatcher,
including fields, reflection, extension, conditionals and binary operands. -/
 public theorem graph_evaluate_context {state : State} {source hole : Term} {context : DemandContext} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_context_names byNames evaluate
  exact graphBy_graph advanced

 public theorem graph_evaluate_bound {state : State} {source : Term} {environment : Environment} {index address : Nat}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.bound index) environment)
    (found : environment[index]? = some address) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_bound_names byNames evaluate found
  exact graphBy_graph advanced

 public theorem graph_evaluate_immediate {state : State} {source : Term} {immediate : ImmediateValue} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate immediate.term environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_immediate_names byNames evaluate
  exact graphBy_graph advanced

 public theorem graph_object_access {state : State} {source : Term} {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresents state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_object_access_names byNames returned head
  exact graphBy_graph advanced

 public theorem graph_specification_call {state : State} {source argument : Term} {environment : Environment}
    {descriptor extension : Address} {rest : List Frame} (represented : GraphRepresents state source)
    (returned : state.control = .returned (.specification descriptor extension))
    (head : state.stack = .argument argument environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_specification_call_names byNames returned head
  exact graphBy_graph advanced

/-- Every successful primitive dispatch performs the independent source
primitive step. The premises are the actual dispatch branches, rather than a
semantic oracle; all four primitives and all scalar results are covered. -/
 public theorem graph_primitive_return {state : State} {source result : Term} {primitive : Primitive}
    {left right next : RuntimeValue} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned right)
    (head : state.stack = .binaryRight primitive left::rest)
    (dispatch : (valueTerm left).bind (fun l => (valueTerm right).bind (primitiveResult primitive l)) = some result)
    (scalar : scalarValue result = some next) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_primitive_return_names byNames returned head dispatch scalar
  exact graphBy_graph advanced

/-- General suspended→evaluating transition preserves the complete graph
relation, installing local source provenance at its actual update frame. -/
 public theorem graph_enter_suspended {state : State} {source : Term} {address : Nat} {origin : Closure}
    (represented : GraphRepresents state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.suspended origin)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_enter_suspended_names byNames enter found
  exact graphBy_graph advanced

/-- General evaluating→cached transition preserves the graph relation, using
the LOCAL update-segment derivation to certify the cell and to advance its
consumers. Closure/record caches are covered, and cyclic origins are allowed. -/
 public theorem graph_cache_update {state : State} {source : Term} {address : Nat}
    {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (update : state.stack = .update address::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_cache_update_names byNames returned update
  exact graphBy_graph advanced

/-- A later demand reuses the memoized value, with independent source
reduction justified by the cache's graph relation. It covers all value shapes. -/
 public theorem graph_enter_cached {state : State} {source : Term} {address : Nat}
    {origin : Closure} {value : RuntimeValue}
    (represented : GraphRepresents state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.cached origin value)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_enter_cached_names byNames enter found
  exact graphBy_graph advanced

/-- Specifications and prototypes allocate two independently suspended
closures. Both names denote their lexical source computations; neither field
is forced by constructing the value. -/
 public theorem graph_evaluate_pair {state : State} {source first second : Term} {environment : Environment}
    {kind : PairObject} (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (kind.term first second) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_pair_names byNames evaluate
  exact graphBy_graph advanced

 public theorem graph_evaluate_record {state : State} {source : Term} {fields : List (String × Term)} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.record fields) environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_record_names byNames evaluate
  exact graphBy_graph advanced

end Obend.Core.Proofs.Adequacy
