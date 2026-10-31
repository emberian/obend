module
/- Address meanings: closed terms, value, cell, heap, frame and stack meaning. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Scoped
public import Obend.Core.Proofs.Adequacy.Source
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 public theorem environmentSubstitution_scoped {bound : Nat} {meaning : AddressMeaning}
    {environment : Environment} (names : MeaningsScoped bound meaning)
    (captures : EnvironmentValid bound environment) :
    ∀ index, index < environment.length → Scoped 0 (environmentSubstitution meaning environment index) := by
  intro index hi
  have found : environment[index]? = some environment[index] := getElem?_pos environment index hi
  simpa [environmentSubstitution,found] using names _ (captures _ (List.mem_of_getElem? found))

 public theorem closeTerm_eq_substitution {meaning : AddressMeaning} {environment : Environment}
    {term : Term} (h : Scoped environment.length term) :
    closeTerm meaning environment term = term.substitute (environmentSubstitution meaning environment) := by
  cases environment with
  | nil =>
      exact (scoped_substitute_identity h _ (by intro i hi; simp at hi)).symm
  | cons _ _ => rfl

/-- Extending an allocated prefix cannot change the source meaning of a
lexical capture. The agreement is only required at actually allocated names. -/
 public theorem closeTerm_meaning_congr {bound : Nat} {first second : AddressMeaning}
    {environment : Environment} {term : Term} (captures : EnvironmentValid bound environment)
    (scope : Scoped environment.length term) (same : ∀ address, address < bound → first address = second address) :
    closeTerm first environment term = closeTerm second environment term := by
  rw [closeTerm_eq_substitution scope,closeTerm_eq_substitution scope]
  apply scoped_substitution_congr scope
  intro index hi
  have found : environment[index]? = some environment[index] := getElem?_pos environment index hi
  simp only [environmentSubstitution,found]
  exact same _ (captures _ (List.mem_of_getElem? found))

/-- A call allocates a name for its lazy argument. This equation proves that
entering the captured body with that name is exactly independent source beta
substitution, even when the environment points into a cyclic heap. -/
 public theorem closeTerm_beta {bound : Nat} {meaning extended : AddressMeaning}
    {captured : Environment} {body argument : Term}
    (names : MeaningsScoped bound meaning) (captures : EnvironmentValid bound captured)
    (bodyScope : Scoped (captured.length+1) body) (argumentScope : Scoped 0 argument)
    (same : ∀ address, address < bound → meaning address = extended address)
    (fresh : extended bound = argument) :
    instantiate (body.substitute (liftSubstitution (environmentSubstitution meaning captured))) argument =
      closeTerm extended (bound::captured) body := by
  let sigma := environmentSubstitution meaning captured
  let inst : Nat → Term := fun i => match i with | 0 => argument | n+1 => .bound n
  have images : ∀ i, i < captured.length → Scoped 0 (sigma i) :=
    environmentSubstitution_scoped names captures
  have nextImages : ∀ i, i < 1 → Scoped 0 (inst i) := by
    intro i hi
    have : i = 0 := by omega
    subst i
    exact argumentScope
  change (body.substitute (liftSubstitution sigma)).substitute inst = _
  rw [scoped_substitute_comp bodyScope _ (lifted_substitution_scoped images) inst nextImages]
  rw [closeTerm_eq_substitution (by simpa using bodyScope)]
  apply scoped_substitution_congr bodyScope
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.substitute,environmentSubstitution,fresh,inst]
  | succ i =>
      have lt : i < captured.length := by omega
      have closed := images i lt
      have renameSame := scoped_rename_identity closed Nat.succ (by intro j hj; omega)
      have substSame := scoped_substitute_identity closed inst (by intro j hj; omega)
      have found : captured[i]? = some captured[i] := getElem?_pos captured i lt
      simp only [liftSubstitution,renameSame,substSame,environmentSubstitution,List.getElem?_cons_succ,found]
      simpa only [sigma,environmentSubstitution,found] using same _ (captures _ (List.mem_of_getElem? found))

 public theorem closeTerm_scoped {bound : Nat} {meaning : AddressMeaning} {environment : Environment}
    {term : Term} (names : MeaningsScoped bound meaning)
    (captures : EnvironmentValid bound environment) (hscope : Scoped environment.length term) :
    Scoped 0 (closeTerm meaning environment term) := by
  cases environment with
  | nil => exact hscope
  | cons address rest =>
      apply scoped_substitute hscope (environmentSubstitution meaning (address::rest)) 0
      intro index hi
      have found : (address::rest)[index]? = some (address::rest)[index] := getElem?_pos (address::rest) index hi
      have allocated := captures _ (List.mem_of_getElem? found)
      simpa [environmentSubstitution,found] using names _ allocated

 theorem valueMeaning_scoped {bound : Nat} {meaning : AddressMeaning} {value : RuntimeValue}
    (names : MeaningsScoped bound meaning) (valid : RuntimeValueValid bound value) :
    Scoped 0 (valueMeaning meaning value) := by
  cases value with
  | closure body environment => exact closeTerm_scoped names valid.2 (Scoped.lam valid.1)
  | natural n => exact .natural _
  | boolean n => exact .boolean _
  | label n => exact .label _
  | record fields =>
      apply Scoped.record
      intro field member
      obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
      exact names _ (valid original ho)
  | specification metadata extension => exact .specification (names _ valid.1) (names _ valid.2)
  | prototype specification target => exact .prototype (names _ valid.1) (names _ valid.2)
  | variant tag payload => exact .inject (names _ valid)

 public theorem valueMeaning_congr {bound : Nat} {first second : AddressMeaning} {value : RuntimeValue}
    (valid : RuntimeValueValid bound value)
    (same : ∀ address, address < bound → first address = second address) :
    valueMeaning first value = valueMeaning second value := by
  cases value with
  | closure body environment => exact closeTerm_meaning_congr valid.2 (Scoped.lam valid.1) same
  | natural _ | boolean _ | label _ => rfl
  | record fields =>
      simp only [valueMeaning]
      congr 1
      apply List.map_congr_left
      intro field member
      exact Prod.ext rfl (same _ (valid field member))
  | specification metadata extension => simp only [valueMeaning,same _ valid.1,same _ valid.2]
  | prototype specification target => simp only [valueMeaning,same _ valid.1,same _ valid.2]
  | variant tag payload => simp only [valueMeaning,same _ valid]

 theorem cellRealizes_congr {bound address : Nat} {first second : AddressMeaning} {cell : Cell}
    (allocated : address < bound) (valid : CellValid bound cell)
    (same : ∀ address, address < bound → first address = second address) :
    CellRealizes first address cell ↔ CellRealizes second address cell := by
  cases cell with
  | suspended origin | evaluating origin =>
      simp only [CellRealizes,cellOrigin,closeOrigin,same _ allocated,
        closeTerm_meaning_congr valid.2 valid.1 same]
  | cached origin value =>
      simp only [CellRealizes,cellOrigin,closeOrigin,same _ allocated,
        closeTerm_meaning_congr valid.1.2 valid.1.1 same,valueMeaning_congr valid.2 same]

 public theorem heapRealizes_congr {heap : Array Cell} {first second : AddressMeaning}
    (valid : HeapValid heap) (same : ∀ address, address < heap.size → first address = second address)
    (realizes : HeapRealizes first heap) : HeapRealizes second heap := by
  intro address cell found
  have allocated := (Array.getElem?_eq_some_iff.mp found).1
  exact (cellRealizes_congr allocated (valid address cell found) same).mp (realizes address cell found)

 public theorem heapRealizes_push {heap : Array Cell} {meaning : AddressMeaning} {cell : Cell}
    (realizes : HeapRealizes meaning heap) (fresh : CellRealizes meaning heap.size cell) :
    HeapRealizes meaning (heap.push cell) := by
  intro address other found
  by_cases eq : address = heap.size
  · subst address
    simp at found
    subst other
    exact fresh
  · apply realizes address other
    simpa [Array.getElem?_push,eq] using found

 public theorem frameMeaning_congr {bound : Nat} {first second : AddressMeaning} {frame : Frame} {hole : Term}
    (valid : FrameValid bound frame)
    (same : ∀ address, address < bound → first address = second address) :
    frameMeaning first frame hole = frameMeaning second frame hole := by
  cases frame with
  | argument term environment | binaryLeft primitive term environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.2 valid.1 same]
  | update _ | field _ | reflect | metadata | project => rfl
  | binaryRight primitive value => simp only [frameMeaning,valueMeaning_congr valid same]
  | extend fields environment =>
      simp only [frameMeaning]
      congr 1
      apply List.map_congr_left
      intro field member
      exact Prod.ext rfl (closeTerm_meaning_congr valid.1 (valid.2 field member) same)
  | condition zero body environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.1 valid.2.1 same]
      congr 1
      apply scoped_substitution_congr valid.2.2
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          have lt : i < environment.length := by omega
          have found : environment[i]? = some environment[i] := getElem?_pos environment i lt
          simp only [liftSubstitution,environmentSubstitution,found,same _ (valid.1 _ (List.mem_of_getElem? found))]
  | case arms environment =>
      simp only [frameMeaning]
      congr 1
      apply List.map_congr_left
      intro arm member
      refine Prod.ext rfl ?_
      apply scoped_substitution_congr (valid.2 arm member)
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          have lt : i < environment.length := by omega
          have found : environment[i]? = some environment[i] := getElem?_pos environment i lt
          simp only [liftSubstitution,environmentSubstitution,found,same _ (valid.1 _ (List.mem_of_getElem? found))]
  | ifBool whenTrue whenFalse environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.1 valid.2.1 same,
        closeTerm_meaning_congr valid.1 valid.2.2 same]

 public theorem valueMeaning_value (meaning : AddressMeaning) (value : RuntimeValue) :
    Value (valueMeaning meaning value) := by
  cases value with
  | closure body environment =>
      cases environment <;> simp only [valueMeaning,closeTerm,Term.substitute]
      all_goals exact .function _
  | natural n => exact .natural _
  | boolean n => exact .boolean _
  | label n => exact .label _
  | record fields => exact .record _
  | specification _ _ => exact .specification _ _
  | prototype _ _ => exact .prototype _ _
  | variant _ _ => exact .inject _ _

 public theorem enteredFocus_steps {meaning : AddressMeaning} {heap : Array Cell} {control : Control} {before after : Term}
    (heapRealizes : HeapRealizes meaning heap) (original : controlMeaning meaning control = some before)
    (entered : enteredFocus meaning heap control = some after) : Steps before after := by
  cases control with
  | enter address =>
      simp only [controlMeaning,Option.some.injEq] at original
      subst before
      cases found : heap[address]? with
      | none => simp [enteredFocus,found] at entered
      | some cell =>
          cases cell with
          | evaluating _ => simp [enteredFocus,found] at entered
          | suspended origin =>
              simp [enteredFocus,found] at entered
              subst after
              exact (heapRealizes address _ found).1
          | cached origin value =>
              simp [enteredFocus,found] at entered
              subst after
              exact (heapRealizes address _ found).2.1
  | evaluate _ _ | returned _ | complete _ | blackhole _ | refused _ | yielded _ =>
      have same : some before = some after := original.symm.trans entered
      have eq := Option.some.inj same
      subst after
      exact Steps.refl _

 theorem sourceSteps_frame (meaning : AddressMeaning) (frame : Frame)
    {before after : Term} (steps : Steps before after) :
    Steps (frameMeaning meaning frame before) (frameMeaning meaning frame after) := by
  induction steps with
  | refl => exact .refl _
  | next step steps ih =>
      apply Steps.next _ ih
      cases frame with
      | argument term environment => exact .application _ step
      | update _ => exact step
      | field name => exact .target _ step
      | reflect => exact .reflectStep step
      | metadata => exact .metadataStep step
      | project => exact .projectStep step
      | extend fields environment => exact .extendTarget _ step
      | condition zero successorBody environment => exact .condition _ _ step
      | binaryLeft primitive right environment => exact .binaryLeft _ _ step
      | binaryRight primitive left => exact .binaryRight _ _ (valueMeaning_value _ _) step
      | case arms environment => exact .caseTarget _ step
      | ifBool whenTrue whenFalse environment => exact .ifCondition _ _ step

 public theorem stackRealizes_congr {bound : Nat} {first second : AddressMeaning} {root focus : Term}
    {stack : List Frame} (valid : ∀ frame ∈ stack, FrameValid bound frame)
    (same : ∀ address, address < bound → first address = second address)
    (realizes : StackRealizes first root focus stack) : StackRealizes second root focus stack := by
  induction stack generalizing focus with
  | nil => exact realizes
  | cons frame rest ih =>
      have hv := valid frame (List.mem_cons_self ..)
      have ht : ∀ frame ∈ rest, FrameValid bound frame := fun f member => valid f (List.mem_cons_of_mem _ member)
      cases frame with
      | update address =>
          exact ⟨by simpa only [StackRealizes,same _ hv] using realizes.1,
            by simpa only [same _ hv] using ih ht realizes.2⟩
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          simpa only [StackRealizes,frameMeaning_congr hv same] using ih ht realizes

 public theorem stackRealizes_steps {meaning : AddressMeaning} {root before after : Term}
    {stack : List Frame} (realizes : StackRealizes meaning root before stack)
    (steps : Steps before after) : StackRealizes meaning root after stack := by
  induction stack generalizing before after with
  | nil => exact sourceSteps_trans realizes steps
  | cons frame rest ih =>
      cases frame with
      | update address => exact ⟨sourceSteps_trans realizes.1 steps,realizes.2⟩
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          exact ih realizes (sourceSteps_frame _ _ steps)

 public theorem sourceSteps_stack (meaning : AddressMeaning) (stack : List Frame) {before after : Term}
    (steps : Steps before after) : Steps (stackMeaning meaning stack before) (stackMeaning meaning stack after) := by
  induction stack generalizing before after with
  | nil => exact steps
  | cons frame rest ih => exact ih (sourceSteps_frame meaning frame steps)

/-- Erasing operational update frames is sound AFTER retaining their local
provenance: each erased boundary contributes its actual demand derivation. -/
 public theorem stackRealizes_erases {meaning : AddressMeaning} {root focus : Term} {stack : List Frame}
    (realizes : StackRealizes meaning root focus stack) : Steps root (stackMeaning meaning stack focus) := by
  induction stack generalizing focus with
  | nil => exact realizes
  | cons frame rest ih =>
      cases frame with
      | update address =>
          exact sourceSteps_trans (ih realizes.2) (sourceSteps_stack meaning rest realizes.1)
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          exact ih realizes

 public theorem heapRealizes_set {meaning : AddressMeaning} {heap : Array Cell}
    {address : Nat} {cell : Cell} (realizes : HeapRealizes meaning heap)
    (valid : CellRealizes meaning address cell) : HeapRealizes meaning (heap.set! address cell) := by
  intro index other found
  by_cases bound : address < heap.size
  · by_cases same : index = address
    · subst index
      simp [Array.set!,bound] at found
      subst other
      exact valid
    · apply realizes index other
      simpa [Array.set!,same,Ne.symm same] using found
  · apply realizes index other
    simpa [Array.set!,Array.setIfInBounds,bound] using found

/-- The cache proof is recovered from the actual local update segment, not an
assumed evaluator oracle. This works for cyclic assignments and arbitrary
runtime closures/records as well as scalars. -/
 public theorem cachedCell_realizes {meaning : AddressMeaning} {heap : Array Cell}
    {address : Nat} {origin : Closure} {root : Term} {rest : List Frame} {value : RuntimeValue}
    (heapRealizes : HeapRealizes meaning heap)
    (found : heap[address]? = some (.evaluating origin))
    (stackRealizes : StackRealizes meaning root (valueMeaning meaning value) (.update address::rest)) :
    CellRealizes meaning address (.cached origin value) :=
  ⟨(heapRealizes address _ found).1,stackRealizes.1,valueMeaning_value _ _⟩

end Obend.Core.Proofs.Adequacy
