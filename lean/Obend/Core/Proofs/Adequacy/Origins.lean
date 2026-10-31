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

set_option maxHeartbeats 800000 in
/-- Birth provenance is preserved by EVERY real transition. It permits tied
Fix and sharing, while excluding arbitrary fabricated cyclic suspended aliases. -/
 public theorem stepRaw_originsBorn {state : State} (lexical : LexicalInvariant state)
    (born : HeapOriginsBorn state.heap) : HeapOriginsBorn (stepRaw state).heap := by
  have headValid : ∀ frame rest, state.stack = frame::rest → FrameValid state.heap.size frame := by
    intro frame rest eq
    exact lexical.2.2 frame (eq ▸ List.mem_cons_self)
  have controlValid := lexical.2.1
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals try (have frameValid := headValid _ _ (by assumption))
  all_goals simp_all only [ControlValid,ClosureValid,FrameValid]
  all_goals try (have captures := controlValid.2)
  all_goals try (have frameCaptures := frameValid.2)
  all_goals try (have extensionCaptures := frameValid.1)
  all_goals solve
    | exact born
    | apply heapOriginsBorn_set born; assumption; rfl
    | apply heapOriginsBorn_suspend born; assumption
    | apply heapOriginsBorn_fix born; assumption
    | apply allocateFields_originsBorn born; assumption
    | apply heapOriginsBorn_suspend (heapOriginsBorn_suspend born (by assumption));
      exact environmentValid_mono (by assumption) (by simp)
    | apply heapOriginsBorn_push born; left; intro address member; simp [cellOrigin] at member
    | apply heapOriginsBorn_suspend born; intro address member; simp at member; subst member; assumption

 public theorem initial_originsBorn (source : Term) : HeapOriginsBorn (initial source).heap := by
  intro address cell found
  simp [initial] at found

 public theorem reachable_originsBorn {source : Term} {state : State} (closed : Scoped 0 source)
    (reachable : Reachable (initial source) state) : HeapOriginsBorn state.heap := by
  induction reachable with
  | start => exact initial_originsBorn source
  | next path ih => exact stepRaw_originsBorn (reachable_lexicalInvariant closed path) ih

end Obend.Core.Proofs.Adequacy
