module
/- Born origins: every heap origin is born of a reachable state. -/
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

/-- A tied Fix origin contains the permanent source name as a proper subterm.
Thus its unfolding cannot be a cost-neutral suspended pointer alias. -/
 public theorem tiedOrigin_name_proper (meaning : AddressMeaning) (address : Address)
    (spec inherited : Term) (captured : Environment) :
    sizeOf (meaning address) < sizeOf (closeOrigin meaning
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩) := by
  simp only [closeOrigin,closeTerm,Term.substitute,environmentSubstitution,List.getElem?_cons_zero]
  simp only [Term.app.sizeOf_spec]
  omega

/-- Every represented born thunk demand decreases either the source cost or
the lexical capture bound. Actual Fix sharing belongs to the strict-cost arm;
ordinary suspended aliases belong to the older-address arm. -/
 public theorem originBorn_demand_descent {meaning : AddressMeaning} {address : Address} {origin : Closure}
    {result : Term} {cost : Nat} (born : OriginBorn address origin)
    (originSteps : Steps (meaning address) (closeOrigin meaning origin))
    (derivation : SourceDerivation (meaning address) result cost) :
    EnvironmentValid address origin.environment ∨
      ∃ smaller, SourceDerivation (closeOrigin meaning origin) result smaller ∧ smaller < cost := by
  rcases born with ordinary | ⟨spec,inherited,captured,environmentEq,captures,termEq⟩
  · exact Or.inl ordinary
  · right
    apply sourceSteps_derivation_strict originSteps _ derivation
    intro equal
    have proper := tiedOrigin_name_proper meaning address spec inherited captured
    have originEq : origin =
        ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩ := by
      cases origin
      simp_all
    rw [← originEq,← equal] at proper
    exact Nat.lt_irrefl _ proper

 theorem heapOriginsBorn_sameSize {before after : Array Cell} (born : HeapOriginsBorn before)
    (preserved : PreservesOrigins before after) (size : before.size = after.size) : HeapOriginsBorn after := by
  intro address cell found
  have allocated : address < before.size := by rw [size]; exact (Array.getElem?_eq_some_iff.mp found).1
  have oldFound : before[address]? = some before[address] := Array.getElem?_eq_getElem allocated
  obtain ⟨new,nextFound,originEq⟩ := preserved.2 address _ oldFound
  have eq : new = cell := Option.some.inj (nextFound.symm.trans found)
  subst new
  rw [originEq]
  exact born address _ oldFound

 public theorem heapOriginsBorn_set {heap : Array Cell} {address : Address} {old next : Cell}
    (born : HeapOriginsBorn heap) (found : heap[address]? = some old)
    (same : cellOrigin next = cellOrigin old) : HeapOriginsBorn (heap.set! address next) :=
  heapOriginsBorn_sameSize born (preservesOrigins_set found same) (by simp [Array.set!])

 theorem heapOriginsBorn_push {heap : Array Cell} {cell : Cell} (born : HeapOriginsBorn heap)
    (fresh : OriginBorn heap.size (cellOrigin cell)) : HeapOriginsBorn (heap.push cell) := by
  intro address other found
  by_cases eq : address = heap.size
  · subst address; simp at found; subst other; exact fresh
  · apply born address other
    simpa [Array.getElem?_push,eq] using found

 theorem heapOriginsBorn_suspend {heap : Array Cell} {term : Term} {environment : Environment}
    (born : HeapOriginsBorn heap) (captures : EnvironmentValid heap.size environment) :
    HeapOriginsBorn (heap.push (.suspended ⟨term,environment⟩)) :=
  heapOriginsBorn_push born (Or.inl captures)

 theorem heapOriginsBorn_fix {heap : Array Cell} {spec inherited : Term} {environment : Environment}
    (born : HeapOriginsBorn heap) (captures : EnvironmentValid heap.size environment) :
    HeapOriginsBorn (heap.push (.suspended
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),heap.size::environment⟩)) :=
  heapOriginsBorn_push born (Or.inr ⟨spec,inherited,environment,rfl,captures,rfl⟩)

 theorem allocateFields_originsBorn {heap : Array Cell} {environment : Environment} {fields : List (String × Term)}
    (born : HeapOriginsBorn heap) (captures : EnvironmentValid heap.size environment) :
    HeapOriginsBorn (allocateFields heap environment fields).1 := by
  induction fields generalizing heap with
  | nil => exact born
  | cons field fields ih =>
      rw [allocateFields_cons]
      exact ih (heapOriginsBorn_suspend born captures) (environmentValid_mono captures (by simp))

private theorem stepRaw_originsBorn_evaluate {state : State} {term : Term} {environment : Environment}
    (hCtrl : state.control = .evaluate term environment)
    (captures : EnvironmentValid state.heap.size environment)
    (born : HeapOriginsBorn state.heap) : HeapOriginsBorn (stepRaw state).heap := by
  cases term with
  | bound index =>
      simp only [stepRaw, hCtrl]
      cases environment[index]? <;> exact born
  | fix spec inherited =>
      simp only [stepRaw, hCtrl]
      exact heapOriginsBorn_fix born captures
  | specification descriptor extension =>
      simp only [stepRaw, hCtrl]
      exact heapOriginsBorn_suspend (heapOriginsBorn_suspend born captures)
        (environmentValid_mono captures (by simp))
  | prototype spec target =>
      simp only [stepRaw, hCtrl]
      exact heapOriginsBorn_suspend (heapOriginsBorn_suspend born captures)
        (environmentValid_mono captures (by simp))
  | record fields =>
      simp only [stepRaw, hCtrl]
      exact allocateFields_originsBorn born captures
  | inject tag payload =>
      simp only [stepRaw, hCtrl]
      exact heapOriginsBorn_suspend born captures
  | perform plan =>
      simp only [stepRaw, hCtrl]
      cases forcingShared state.stack with
      | true => exact born
      | false => exact heapOriginsBorn_suspend born captures
  | hole _ _ | lam _ | app _ _ | mix _ _ | reflect _ | metadata _ | project _
  | nat _ | boolean _ | label _ | binary _ _ _ | extend _ _ | get _ _
  | ifZero _ _ _ | case _ _ | ifBool _ _ _ | done _ | split _ _ _ =>
      simpa [stepRaw, hCtrl] using born

private theorem stepRaw_originsBorn_returned {state : State} {value : RuntimeValue}
    (hCtrl : state.control = .returned value)
    (valValid : RuntimeValueValid state.heap.size value)
    (stackValid : ∀ frame ∈ state.stack, FrameValid state.heap.size frame)
    (born : HeapOriginsBorn state.heap) : HeapOriginsBorn (stepRaw state).heap := by
  cases hStack : state.stack with
  | nil => simpa [stepRaw, hCtrl, hStack] using born
  | cons frame rest =>
      have frameValid : FrameValid state.heap.size frame :=
        stackValid frame (hStack ▸ List.mem_cons_self)
      cases frame with
      | update address =>
          simp only [stepRaw, hCtrl, hStack]
          cases hCell : state.heap[address]? with
          | none => exact born
          | some cell =>
              cases cell with
              | evaluating origin => exact heapOriginsBorn_set born hCell rfl
              | suspended _ | cached _ _ => exact born
      | argument argument environment =>
          simp only [stepRaw, hCtrl, hStack]
          cases value with
          | closure body captured => exact heapOriginsBorn_suspend born frameValid.2
          | specification _ _ | natural _ | boolean _ | label _
          | record _ | prototype _ _ | variant _ _ => exact born
      | extend fields environment =>
          simp only [stepRaw, hCtrl, hStack]
          cases value with
          | record inherited => exact allocateFields_originsBorn born frameValid.1
          | closure _ _ | specification _ _ | natural _ | boolean _
          | label _ | prototype _ _ | variant _ _ => exact born
      | condition zero successorBody environment =>
          simp only [stepRaw, hCtrl, hStack]
          cases value with
          | natural n =>
              cases n with
              | zero => exact born
              | succ m =>
                  apply heapOriginsBorn_push born
                  left
                  intro address member
                  simp [cellOrigin] at member
          | closure _ _ | specification _ _ | boolean _ | label _
          | record _ | prototype _ _ | variant _ _ => exact born
      | case arms environment =>
          simp only [stepRaw, hCtrl, hStack]
          cases value with
          | variant tag payload =>
              dsimp only
              cases hFind : arms.find? (fun arm => arm.1 == tag) with
              | none => exact born
              | some arm =>
                  dsimp only
                  apply heapOriginsBorn_suspend born
                  intro address member
                  simp at member
                  subst member
                  exact valValid
          | closure _ _ | specification _ _ | natural _ | boolean _
          | label _ | record _ | prototype _ _ => exact born
      | split names function environment =>
          simp only [stepRaw, hCtrl, hStack]
          cases value with
          | record fields =>
              dsimp only
              cases hSplit : splitValues fields names with
              | none => exact born
              | some addresses =>
                  dsimp only
                  apply allocateFields_originsBorn born
                  intro address ha
                  obtain ⟨f, hf, rfl⟩ := Obend.Core.Invariant.splitValues_mem hSplit address ha
                  exact valValid f hf
          | closure _ _ | specification _ _ | natural _ | boolean _
          | label _ | prototype _ _ | variant _ _ => exact born
      | reflect =>
          simp only [stepRaw, hCtrl, hStack]
          cases value <;> exact born
      | metadata =>
          simp only [stepRaw, hCtrl, hStack]
          cases value <;> exact born
      | project =>
          simp only [stepRaw, hCtrl, hStack]
          cases value <;> exact born
      | field name =>
          simp only [stepRaw, hCtrl, hStack]
          cases value with
          | record fields =>
              dsimp only
              cases fields.find? (fun field => field.1 == name) <;> exact born
          | closure _ _ | specification _ _ | natural _ | boolean _
          | label _ | prototype _ _ | variant _ _ => exact born
      | binaryLeft primitive right environment =>
          simpa [stepRaw, hCtrl, hStack] using born
      | binaryRight primitive left =>
          simp only [stepRaw, hCtrl, hStack]
          cases (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
          | none => exact born
          | some res =>
              dsimp only
              cases scalarValue res <;> exact born
      | ifBool whenTrue whenFalse environment =>
          simp only [stepRaw, hCtrl, hStack]
          cases value with
          | boolean b => cases b <;> exact born
          | closure _ _ | specification _ _ | natural _ | label _
          | record _ | prototype _ _ | variant _ _ => exact born

/-- Birth provenance is preserved by EVERY real transition. It permits tied
Fix and sharing, while excluding arbitrary fabricated cyclic suspended aliases. -/
 public theorem stepRaw_originsBorn {state : State} (lexical : LexicalInvariant state)
    (born : HeapOriginsBorn state.heap) : HeapOriginsBorn (stepRaw state).heap := by
  cases hCtrl : state.control with
  | complete _ | refused _ | blackhole _ | yielded _ =>
      simpa [stepRaw, hCtrl] using born
  | enter address =>
      simp only [stepRaw, hCtrl]
      cases hCell : state.heap[address]? with
      | none => exact born
      | some cell =>
          cases cell with
          | suspended origin => exact heapOriginsBorn_set born hCell rfl
          | evaluating _ | cached _ _ => exact born
  | evaluate term environment =>
      have hValid : ClosureValid state.heap.size ⟨term, environment⟩ := by
        simpa [ControlValid, hCtrl] using lexical.2.1
      exact stepRaw_originsBorn_evaluate hCtrl hValid.2 born
  | returned value =>
      have hValid : RuntimeValueValid state.heap.size value := by
        simpa [ControlValid, hCtrl] using lexical.2.1
      exact stepRaw_originsBorn_returned hCtrl hValid lexical.2.2 born

 public theorem initial_originsBorn (source : Term) : HeapOriginsBorn (initial source).heap := by
  intro address cell found
  simp [initial] at found

 public theorem reachable_originsBorn {source : Term} {state : State} (closed : Scoped 0 source)
    (reachable : Reachable (initial source) state) : HeapOriginsBorn state.heap := by
  induction reachable with
  | start => exact initial_originsBorn source
  | next path ih => exact stepRaw_originsBorn (reachable_lexicalInvariant closed path) ih

end Obend.Core.Proofs.Adequacy
