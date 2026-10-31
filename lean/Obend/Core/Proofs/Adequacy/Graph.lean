module
/- The graph relation: demand contexts, immediate values, closures, allocation. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Meaning
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 public theorem graph_initializes {source : Term} (closed : Scoped 0 source) :
    GraphRepresents (initial source) source := by
  refine ⟨initial_lexicalInvariant closed,initial_busyInvariant source,initial_finalStackInvariant source,fun _ => .bound 0,?_,?_,source,?_,?_⟩
  · intro address allocated; simp [initial] at allocated
  · intro address cell found; simp [initial] at found
  · rfl
  · exact .refl _

 public theorem graph_complete_natural_sound {state : State} {source : Term} {number : Nat}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.natural number)) :
    Evaluates source (.nat number) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes,Evaluates] using And.intro steps (Value.natural number)

 public theorem graph_complete_label_sound {state : State} {source : Term} {name : String}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.label name)) :
    Evaluates source (.label name) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes,Evaluates] using And.intro steps (Value.label name)

 public theorem graph_complete_boolean_sound {state : State} {source : Term} {value : Bool}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.boolean value)) :
    Evaluates source (.boolean value) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes,Evaluates] using And.intro steps (Value.boolean value)

/-- Finished closures, records, specifications and prototypes have source
values through the same concrete heap graph assignment as scalars. The
existential retains the HeapRealizes proof; it is not an oracle or contextual
equivalence assertion about arbitrary external consumers. -/
 public theorem graph_complete_value_sound {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresents state source) (complete : state.control = .complete value) :
    ∃ meaning : AddressMeaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
      Evaluates source (valueMeaning meaning value) := by
  obtain ⟨_,_,final,meaning,names,heap,focus,control,stack⟩ := represented
  have empty := final value complete
  simp [controlMeaning,complete] at control
  subst focus
  refine ⟨meaning,names,heap,?_,valueMeaning_value meaning value⟩
  simpa only [empty,StackRealizes] using stack

/-- The concrete graph assignment justifies both fixed lexical names and the
phase-sensitive source focus used for demand simulation. All erased update
boundaries are discharged from their retained local source derivations. -/
 theorem graph_enteredFocus_source {state : State} {source : Term}
    (represented : GraphRepresents state source) :
    ∃ meaning : AddressMeaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
      ∀ focus, enteredFocus meaning state.heap state.control = some focus →
        Steps source (stackMeaning meaning state.stack focus) := by
  obtain ⟨_,_,_,meaning,names,heap,before,original,stack⟩ := represented
  refine ⟨meaning,names,heap,?_⟩
  intro focus entered
  exact sourceSteps_trans (stackRealizes_erases stack)
    (sourceSteps_stack meaning state.stack (enteredFocus_steps heap original entered))

/-- Every actual continuation frame demands its hole. A terminating whole
context therefore supplies a finite derivation for the demanded focus. -/
 theorem frame_derivation_demand {meaning : AddressMeaning} {frame : Frame} {focus result : Term} {cost : Nat}
    (derivation : SourceDerivation (frameMeaning meaning frame focus) result cost) :
    ∃ value demandCost, SourceDerivation focus value demandCost ∧ demandCost ≤ cost := by
  cases frame with
  | update address => exact ⟨result,cost,derivation,Nat.le_refl _⟩
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

 public theorem stack_derivation_demand {meaning : AddressMeaning} {stack : List Frame} {focus result : Term} {cost : Nat}
    (derivation : SourceDerivation (stackMeaning meaning stack focus) result cost) :
    ∃ value demandCost, SourceDerivation focus value demandCost ∧ demandCost ≤ cost := by
  induction stack generalizing focus result cost with
  | nil => exact ⟨result,cost,derivation,Nat.le_refl _⟩
  | cons frame rest ih =>
      obtain ⟨middle,middleCost,middleDerivation,middleLe⟩ := ih derivation
      obtain ⟨value,demandCost,demand,demandLe⟩ := frame_derivation_demand middleDerivation
      exact ⟨value,demandCost,demand,Nat.le_trans demandLe middleLe⟩

/-- Termination of the independent source program gives a finite demand
budget at every represented phase-sensitive focus. The heap assignment is
constructed by the existing graph theorem, rather than an evaluation oracle. -/
 theorem graph_terminating_demand {state : State} {source result : Term}
    (represented : GraphRepresents state source) (terminates : Evaluates source result) :
    ∃ meaning : AddressMeaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
      ∀ focus, enteredFocus meaning state.heap state.control = some focus →
        ∃ value cost, SourceDerivation focus value cost := by
  obtain ⟨meaning,names,heap,wholeSteps⟩ := graph_enteredFocus_source represented
  refine ⟨meaning,names,heap,?_⟩
  intro focus entered
  obtain ⟨wholeCost,whole⟩ := source_evaluates_derivation
    (sourceSteps_evaluates_tail (wholeSteps focus entered) terminates)
  obtain ⟨value,cost,demand,_⟩ := stack_derivation_demand whole
  exact ⟨value,cost,demand⟩

 public theorem demandContext_closes (context : DemandContext) (meaning : AddressMeaning)
    (environment : Environment) (hole : Term)
    (scope : Scoped environment.length (context.term hole)) :
    closeTerm meaning environment (context.term hole) =
      frameMeaning meaning (context.frame environment) (closeTerm meaning environment hole) := by
  cases environment with
  | cons address rest => cases context <;> simp [DemandContext.term,DemandContext.frame,closeTerm,Term.substitute,frameMeaning]
  | nil =>
      have lifted : liftSubstitution (environmentSubstitution meaning []) = Term.bound := by
        funext i
        cases i <;> simp [liftSubstitution,environmentSubstitution,Term.rename]
      cases context with
      | condition zero body =>
          have scopedBody : Scoped 1 body := (scoped_condition_iff ..).mp scope |>.2.2
          simp only [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning,lifted,
            scoped_substitute_identity scopedBody Term.bound (by intros; rfl)]
      | extend fields => simp [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning]
      | case arms =>
          have scopedArms : ∀ arm ∈ arms, Scoped 1 arm.2 := (scoped_case_iff ..).mp scope |>.2
          simp only [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning,lifted]
          congr 1
          apply Eq.symm
          apply Eq.trans _ (List.map_id' _)
          apply List.map_congr_left
          intro arm member
          exact Prod.ext rfl (scoped_substitute_identity (scopedArms arm member) Term.bound (by intros; rfl))
      | argument _ | field _ | reflect | metadata | project | binary _ _ | ifBool _ _ => rfl

 public theorem demandContext_dispatch {state : State} {context : DemandContext} {hole : Term} {environment : Environment}
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    stepRaw state = {state with control := .evaluate hole environment,stack := context.frame environment::state.stack} := by
  cases context <;> simp [stepRaw,evaluate,DemandContext.term,DemandContext.frame]





 public theorem valueTerm_meaning {value : RuntimeValue} {term : Term} (found : valueTerm value = some term)
    (meaning : AddressMeaning) : valueMeaning meaning value = term := by
  cases value <;> simp [valueTerm] at found
  all_goals subst term; rfl

 public theorem scalarValue_meaning {value : RuntimeValue} {term : Term} (found : scalarValue term = some value)
    (meaning : AddressMeaning) : valueMeaning meaning value = term := by
  cases term <;> simp [scalarValue] at found
  all_goals subst value; rfl









 public theorem closeTerm_app (meaning : AddressMeaning) (environment : Environment) (function argument : Term) :
    closeTerm meaning environment (.app function argument) =
      .app (closeTerm meaning environment function) (closeTerm meaning environment argument) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 public theorem closeTerm_lambda {meaning : AddressMeaning} {environment : Environment} {body : Term}
    (scope : Scoped (environment.length+1) body) :
    closeTerm meaning environment (.lam body) =
      .lam (body.substitute (liftSubstitution (environmentSubstitution meaning environment))) := by
  rw [closeTerm_eq_substitution (Scoped.lam scope)]
  simp only [Term.substitute]

 public theorem extendMeaning_prefix (meaning : AddressMeaning) (bound : Nat) (term : Term) :
    ∀ address, address < bound → meaning address = extendMeaning meaning bound term address := by
  intro address allocated
  simp [extendMeaning,Nat.ne_of_lt allocated]

/-- The shared allocation lemma records the actual suspended origin, its
closed source name and exact agreement at every old allocated address. -/
 public theorem allocateClosure_realizes {heap : Array Cell} {meaning : AddressMeaning}
    {term : Term} {environment : Environment} (validHeap : HeapValid heap)
    (names : MeaningsScoped heap.size meaning) (realizes : HeapRealizes meaning heap)
    (scope : Scoped environment.length term) (captures : EnvironmentValid heap.size environment) :
    ∃ extended : AddressMeaning,
      MeaningsScoped (heap.push (.suspended ⟨term,environment⟩)).size extended ∧
      HeapRealizes extended (heap.push (.suspended ⟨term,environment⟩)) ∧
      (∀ address, address < heap.size → meaning address = extended address) ∧
      extended heap.size = closeTerm meaning environment term := by
  let source := closeTerm meaning environment term
  let extended := extendMeaning meaning heap.size source
  have same : ∀ address, address < heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended heap.size = source := by simp [extended,extendMeaning]
  have closed := closeTerm_scoped names captures scope
  refine ⟨extended,?_,?_,same,fresh⟩
  · intro address allocated
    by_cases eq : address = heap.size
    · subst address; simpa only [fresh] using closed
    · have old : address < heap.size := by simp only [Array.size_push] at allocated; omega
      simpa only [←same address old] using names address old
  · apply heapRealizes_push (heapRealizes_congr validHeap same realizes)
    refine ⟨?_,True.intro⟩
    have originEq := closeTerm_meaning_congr captures scope same
    simpa only [fresh,cellOrigin,closeOrigin,←originEq] using Steps.refl source

 theorem allocationLoop_accumulator (environment : Environment) (fields : List (String × Term))
    (heap : Array Cell) (prior : List (String × Address)) :
    allocationLoop environment fields heap prior =
      ((allocationLoop environment fields heap []).1,(allocationLoop environment fields heap []).2++prior) := by
  induction fields generalizing heap prior with
  | nil => simp [allocationLoop]
  | cons field fields ih =>
      change allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) ((field.1,heap.size)::prior) =
        ((allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).1,
         (allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).2++prior)
      rw [ih _ ((field.1,heap.size)::prior),ih _ [(field.1,heap.size)]]
      simp [List.append_assoc]

 public theorem allocateFields_cons (heap : Array Cell) (environment : Environment) (field : String × Term)
    (fields : List (String × Term)) :
    allocateFields heap environment (field::fields) =
      ((allocateFields (heap.push (.suspended ⟨field.2,environment⟩)) environment fields).1,
       (field.1,heap.size)::(allocateFields (heap.push (.suspended ⟨field.2,environment⟩)) environment fields).2) := by
  change ((allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).1,
    (allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).2.reverse) = _
  rw [allocationLoop_accumulator]
  simp [allocateFields,allocationLoop,List.reverse_append]

/-- Arbitrary lazy record allocation: every generated field name denotes the
original captured computation, in field order, while all old graph meanings
and all source origins are retained. Fields may contain general Fix. -/
 public theorem allocateFields_realizes {heap : Array Cell} {meaning : AddressMeaning} {environment : Environment}
    {fields : List (String × Term)} (valid : HeapValid heap) (names : MeaningsScoped heap.size meaning)
    (realizes : HeapRealizes meaning heap) (captures : EnvironmentValid heap.size environment)
    (scopes : ∀ field ∈ fields, Scoped environment.length field.2) :
    ∃ extended : AddressMeaning,
      MeaningsScoped (allocateFields heap environment fields).1.size extended ∧
      HeapRealizes extended (allocateFields heap environment fields).1 ∧
      (∀ address, address < heap.size → meaning address = extended address) ∧
      ((allocateFields heap environment fields).2.map fun field => (field.1,extended field.2)) =
        (fields.map fun field => (field.1,closeTerm meaning environment field.2)) := by
  induction fields generalizing heap meaning with
  | nil => exact ⟨meaning,names,realizes,by intros; rfl,rfl⟩
  | cons field fields ih =>
      have headScope := scopes field (List.mem_cons_self ..)
      have tailScopes : ∀ field ∈ fields, Scoped environment.length field.2 :=
        fun field member => scopes field (List.mem_cons_of_mem _ member)
      obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ := allocateClosure_realizes valid names realizes headScope captures
      have oneValid := heapValid_push valid
        (show CellValid (heap.size+1) (.suspended ⟨field.2,environment⟩) from
          ⟨headScope,environmentValid_mono captures (Nat.le_succ _)⟩)
      have capturesOne : EnvironmentValid (heap.push (.suspended ⟨field.2,environment⟩)).size environment :=
        environmentValid_mono captures (by simp)
      obtain ⟨two,twoNames,twoHeap,twoSame,twoFields⟩ := ih oneValid oneNames oneHeap capturesOne tailScopes
      have same : ∀ address, address < heap.size → meaning address = two address := by
        intro address allocated
        exact (oneSame address allocated).trans (twoSame address (by simpa using Nat.lt_succ_of_lt allocated))
      refine ⟨two,?_,?_,same,?_⟩
      · simpa only [allocateFields_cons] using twoNames
      · simpa only [allocateFields_cons] using twoHeap
      · rw [allocateFields_cons,List.map_cons,twoFields]
        have firstEq : two heap.size = closeTerm meaning environment field.2 := by
          rw [←twoSame heap.size (by simp),oneFresh]
        rw [firstEq,List.map_cons]
        congr 1
        apply List.map_congr_left
        intro f member
        exact Prod.ext rfl (closeTerm_meaning_congr captures (tailScopes f member) oneSame).symm

 public theorem closeTerm_record (meaning : AddressMeaning) (environment : Environment) (fields : List (String × Term)) :
    closeTerm meaning environment (.record fields) =
      .record (fields.map fun field => (field.1,closeTerm meaning environment field.2)) := by
  cases environment <;> simp [closeTerm,Term.substitute]





 public theorem closeTerm_mixBody {bound : Nat} {meaning : AddressMeaning} {environment : Environment} {lower upper : Term}
    (names : MeaningsScoped bound meaning) (captures : EnvironmentValid bound environment)
    (lowerScope : Scoped environment.length lower) (upperScope : Scoped environment.length upper) :
    closeTerm meaning environment (mixBody lower upper) =
      mixBody (closeTerm meaning environment lower) (closeTerm meaning environment upper) := by
  let sigma := environmentSubstitution meaning environment
  have images : ∀ i, i < environment.length → Scoped 0 (sigma i) := environmentSubstitution_scoped names captures
  have shifted : ∀ term, Scoped environment.length term →
      (term.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma)) = term.substitute sigma := by
    intro term scope
    rw [scoped_rename_substitute scope]
    apply scoped_substitution_congr scope
    intro i hi
    simp only [liftSubstitution,
      scoped_rename_identity (images i hi) Nat.succ (by intro j hj; omega)]
  have lowerClosed := closeTerm_scoped names captures lowerScope
  have upperClosed := closeTerm_scoped names captures upperScope
  rw [closeTerm_eq_substitution (scoped_mixBody lowerScope upperScope)]
  simp only [mixBody,Term.substitute]
  have liftedOne : liftSubstitution (liftSubstitution (environmentSubstitution meaning environment)) 1 = .bound 1 := by
    simp [liftSubstitution,Term.rename]
  have liftedZero : liftSubstitution (liftSubstitution (environmentSubstitution meaning environment)) 0 = .bound 0 := rfl
  simp only [liftedOne,liftedZero]
  change Term.lam (.lam (.app (.app ((upper.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma))) (.bound 1))
    (.app (.app ((lower.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma))) (.bound 1)) (.bound 0)))) = _
  rw [shifted upper upperScope,shifted lower lowerScope]
  rw [scoped_rename_identity lowerClosed (fun n => n+2) (by intro j hj; omega),
    scoped_rename_identity upperClosed (fun n => n+2) (by intro j hj; omega)]
  simp only [closeTerm_eq_substitution lowerScope,closeTerm_eq_substitution upperScope,sigma]









 public theorem closeTerm_weaken {bound : Nat} {meaning extended : AddressMeaning}
    {environment : Environment} {term : Term}
    (captures : EnvironmentValid bound environment) (scope : Scoped environment.length term)
    (same : ∀ address, address < bound → meaning address = extended address) :
    closeTerm extended (bound::environment) (term.rename Nat.succ) = closeTerm meaning environment term := by
  have shifted := scoped_rename scope Nat.succ (environment.length+1) (by intro i hi; omega)
  rw [closeTerm_eq_substitution (by simpa using shifted),closeTerm_eq_substitution scope,
    scoped_rename_substitute scope]
  apply scoped_substitution_congr scope
  intro i hi
  have found : environment[i]? = some environment[i] := getElem?_pos environment i hi
  simp only [environmentSubstitution,List.getElem?_cons_succ,found]
  exact (same _ (captures _ (List.mem_of_getElem? found))).symm

 public theorem closeTerm_fix (meaning : AddressMeaning) (environment : Environment) (spec inherited : Term) :
    closeTerm meaning environment (.fix spec inherited) =
      .fix (closeTerm meaning environment spec) (closeTerm meaning environment inherited) := by
  cases environment <;> simp only [closeTerm,Term.substitute]











 public theorem graphBy_graph {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) : GraphRepresents state source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  exact ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩

 public theorem graphBy_initializes {source : Term} (closed : Scoped 0 source) :
    GraphRepresentsBy (fun _ => .bound 0) (initial source) source := by
  refine ⟨initial_lexicalInvariant closed,initial_busyInvariant source,initial_finalStackInvariant source,?_,?_,source,rfl,Steps.refl _⟩
  · intro address allocated; simp [initial] at allocated
  · intro address cell found; simp [initial] at found

end Obend.Core.Proofs.Adequacy
