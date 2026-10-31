module
/- Typing transfers to a related state. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Collect.Lockstep
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

open Obend.Core.Data
/-! ## Typing transfers to a related state -/

section Typing
open Obend.Core.Ty Obend.Core.Check
open Obend.Core.MachineTyping Obend.Core.Invariant

variable {f : Nat → Nat} {D : Nat → Prop} {assumptions : Assumptions} {types types' : AddressTypes}

/-- `types'` assigns each renamed address the type `types` assigns the original. -/
@[expose] public def TypesRel (f : Nat → Nat) (D : Nat → Prop) (types types' : AddressTypes) : Prop :=
  ∀ a, D a → types'[f a]? = types[a]?

public theorem environmentTyping_rename (rel : TypesRel f D types types') {context : Context}
    {environment : List Nat} (inside : AllIn D environment)
    (typed : EnvironmentTyping types context environment) :
    EnvironmentTyping types' context (environment.map f) := by
  refine ⟨by simp [typed.length], ?_⟩
  intro index declared lookup
  obtain ⟨address, member, assigned⟩ := typed.binding index declared lookup
  refine ⟨f address, by simp [member], ?_⟩
  rw [rel address (inside address (List.mem_of_getElem? member)), assigned]

@[expose] public def closureTyping_rename (rel : TypesRel f D types types') {closure : Closure} {type : Ty}
    (inside : AllIn D closure.environment) (typed : ClosureTyping assumptions types closure type) :
    ClosureTyping assumptions types' (renameClosure f closure) type where
  context := typed.context
  uses := typed.uses
  environment := environmentTyping_rename rel inside typed.environment
  source := typed.source
  safe := typed.safe
  contextValid := typed.contextValid

theorem valueTyping_rename (rel : TypesRel f D types types') {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    AllIn D (valueAddresses value) → ValueTyping assumptions types' (renameValue f value) type := by
  induction typed with
  | natural value => intro _; exact .natural value
  | boolean value => intro _; exact .boolean value
  | label value => intro _; exact .label value
  | closure environmentTyped body safe valid reusable =>
    intro inside
    exact .closure (environmentTyping_rename rel inside environmentTyped) body safe valid reusable
  | @record fields row isRow lookup =>
    intro inside
    refine .record isRow ?_
    intro fuel name member found
    obtain ⟨address, actual, findEq, assigned, path⟩ := lookup fuel name member found
    refine ⟨f address, actual, ?_, ?_, path⟩
    · simp only [List.find?_map, Function.comp_def, findEq]; rfl
    · have member := List.mem_of_find?_eq_some findEq
      rw [rel address (inside address (List.mem_map_of_mem (f := Prod.snd) member)), assigned]
  | @specification metadata extension _ _ one two =>
    intro inside
    refine .specification ?_ ?_
    · rw [rel metadata (inside metadata (by simp [valueAddresses])), one]
    · rw [rel extension (inside extension (by simp [valueAddresses])), two]
  | @prototype spec target _ _ one two =>
    intro inside
    refine .prototype ?_ ?_
    · rw [rel spec (inside spec (by simp [valueAddresses])), one]
    · rw [rel target (inside target (by simp [valueAddresses])), two]
  | conversion _ same ih => intro inside; exact .conversion (ih inside) same
  | @variant tag address _ _ _ _ lookup assigned path =>
    intro inside
    exact .variant lookup (by rw [rel address (inside address (by simp [valueAddresses])), assigned]) path

theorem cellTyping_rename (rel : TypesRel f D types types') {cell : Cell} {type : Ty}
    (inside : AllIn D (cellAddresses cell)) (typed : CellTyping assumptions types cell type) :
    CellTyping assumptions types' (renameCell f cell) type := by
  cases typed with
  | suspended closureTyped plain => exact .suspended (closureTyping_rename rel inside closureTyped) plain
  | evaluating closureTyped plain => exact .evaluating (closureTyping_rename rel inside closureTyped) plain
  | cached closureTyped valueTyped plain =>
    exact .cached (closureTyping_rename rel (fun x member => inside x (List.mem_append_left _ member)) closureTyped)
      (valueTyping_rename rel valueTyped (fun x member => inside x (List.mem_append_right _ member))) plain

theorem frameTyping_rename (rel : TypesRel f D types types') {frame : Frame} {input output : Ty}
    (inside : AllIn D (frameAddresses frame)) (typed : FrameTyping assumptions types frame input output) :
    FrameTyping assumptions types' (renameFrame f frame) input output := by
  cases typed with
  | argument argumentTyped callableEq allowed =>
    exact .argument (closureTyping_rename rel inside argumentTyped) callableEq allowed
  | @update address _ assigned plain =>
    exact .update (by rw [rel address (inside address (by simp [frameAddresses])), assigned]) plain
  | field lookup => exact .field lookup
  | reflect => exact .reflect _ _
  | metadata => exact .metadata _ _
  | project => exact .project _ _
  | extend environmentTyped fieldsTyped safe valid isRow =>
    exact .extend (environmentTyping_rename rel inside environmentTyped) fieldsTyped safe valid isRow
  | condition zeroTyped environmentTyped successor safe valid =>
    exact .condition (closureTyping_rename rel inside zeroTyped)
      (environmentTyping_rename rel inside environmentTyped) successor safe valid
  | binaryLeft rightTyped => exact .binaryLeft (closureTyping_rename rel inside rightTyped)
  | binaryRight leftTyped => exact .binaryRight (valueTyping_rename rel leftTyped inside)
  | case environmentTyped armsTyped valid =>
    exact .case (environmentTyping_rename rel inside environmentTyped) armsTyped valid
  | ifBool trueTyped falseTyped =>
    exact .ifBool (closureTyping_rename rel inside trueTyped) (closureTyping_rename rel inside falseTyped)
  | effectCase environmentTyped armsTyped valid plain =>
    exact .effectCase (environmentTyping_rename rel inside environmentTyped) armsTyped valid plain

theorem stackTyping_rename (rel : TypesRel f D types types') {stack : List Frame} {input output : Ty}
    (typed : StackTyping assumptions types stack input output) :
    (∀ frame ∈ stack, AllIn D (frameAddresses frame)) →
      StackTyping assumptions types' (stack.map (renameFrame f)) input output := by
  induction typed with
  | nil type => intro _; exact .nil type
  | cons frameTyped _ ih =>
    intro inside
    have ⟨head, tail⟩ := List.forall_mem_cons.mp inside
    exact .cons (frameTyping_rename rel head frameTyped) (ih tail)
  | conversion same _ ih => intro inside; exact .conversion same (ih inside)
  | returns plain _ ih => intro inside; exact .returns plain (ih inside)

theorem controlTyping_rename (rel : TypesRel f D types types') {control : Control} {type : Ty}
    (inside : AllIn D (controlAddresses control)) (typed : ControlTyping assumptions types control type) :
    ControlTyping assumptions types' (renameControl f control) type := by
  cases typed with
  | evaluate closureTyped => exact .evaluate (closureTyping_rename rel inside closureTyped)
  | @enter address _ assigned =>
    exact .enter (by rw [rel address (inside address (List.mem_singleton_self _)), assigned])
  | returned valueTyped => exact .returned (valueTyping_rename rel valueTyped inside)
  | complete valueTyped => exact .complete (valueTyping_rename rel valueTyped inside)
  | @blackhole address _ assigned =>
    exact .blackhole (by rw [rel address (inside address (List.mem_singleton_self _)), assigned])
  | @yielded plan _ _ assigned isPlan isData =>
    exact .yielded (by rw [rel plan (inside plan (List.mem_singleton_self _)), assigned]) isPlan isData

/-- Every cell of the second heap is the image of a cell of the first. -/
@[expose] public def Covers (f : Nat → Nat) (D : Nat → Prop) (heap heap' : Array Cell) : Prop :=
  ∀ k, k < heap'.size → ∃ a, D a ∧ a < heap.size ∧ f a = k

public theorem heapTyping_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap')
    (rel : TypesRel f D types types') (length : types'.length = heap'.size) (cover : Covers f D heap heap')
    (typed : HeapTyping assumptions types heap) : HeapTyping assumptions types' heap' := by
  refine ⟨length, ?_⟩
  intro k type found
  have bound : k < heap'.size := by rw [← length]; exact (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨a, inA, boundA, rfl⟩ := cover k bound
  rw [rel a inA] at found
  obtain ⟨stored, at_, cellTyped⟩ := typed.cell a type found
  obtain ⟨c, foundC, foundC', inC⟩ := hr.cells a inA boundA
  rw [at_] at foundC; cases foundC
  exact ⟨_, foundC', cellTyping_rename rel inC cellTyped⟩

/-! ### The representation invariants -/

public theorem image_lt {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {a : Nat} (inA : D a)
    (bound : a < heap.size) : f a < heap'.size := by
  obtain ⟨_, _, found', _⟩ := hr.cells a inA bound
  exact bound_of_some found'

theorem environmentValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap')
    {environment : List Nat} (inside : AllIn D environment) (valid : EnvironmentValid heap.size environment) :
    EnvironmentValid heap'.size (environment.map f) := by
  intro x member
  obtain ⟨a, memberA, rfl⟩ := List.mem_map.mp member
  exact image_lt hr (inside a memberA) (valid a memberA)

theorem runtimeValueValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap')
    {value : RuntimeValue} (inside : AllIn D (valueAddresses value)) (valid : RuntimeValueValid heap.size value) :
    RuntimeValueValid heap'.size (renameValue f value) := by
  cases value with
  | closure body environment =>
    exact ⟨by simpa [renameValue] using valid.1, environmentValid_rename hr inside valid.2⟩
  | natural _ | boolean _ | label _ => trivial
  | record fields =>
    intro field member
    simp only [List.mem_map] at member
    obtain ⟨original, memberO, rfl⟩ := member
    exact image_lt hr (inside _ (List.mem_map_of_mem memberO)) (valid original memberO)
  | specification metadata extension =>
    exact ⟨image_lt hr (inside metadata (by simp [valueAddresses])) valid.1,
      image_lt hr (inside extension (by simp [valueAddresses])) valid.2⟩
  | prototype spec target =>
    exact ⟨image_lt hr (inside spec (by simp [valueAddresses])) valid.1,
      image_lt hr (inside target (by simp [valueAddresses])) valid.2⟩
  | variant _ payload => exact image_lt hr (inside payload (by simp [valueAddresses])) valid

theorem closureValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {closure : Closure}
    (inside : AllIn D closure.environment) (valid : ClosureValid heap.size closure) :
    ClosureValid heap'.size (renameClosure f closure) :=
  ⟨by simpa [renameClosure] using valid.1, environmentValid_rename hr inside valid.2⟩

theorem cellValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {cell : Cell}
    (inside : AllIn D (cellAddresses cell)) (valid : CellValid heap.size cell) :
    CellValid heap'.size (renameCell f cell) := by
  cases cell with
  | suspended origin => exact closureValid_rename hr inside valid
  | evaluating origin => exact closureValid_rename hr inside valid
  | cached origin value =>
    exact ⟨closureValid_rename hr (fun x member => inside x (List.mem_append_left _ member)) valid.1,
      runtimeValueValid_rename hr (fun x member => inside x (List.mem_append_right _ member)) valid.2⟩

theorem frameValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {frame : Frame}
    (inside : AllIn D (frameAddresses frame)) (valid : FrameValid heap.size frame) :
    FrameValid heap'.size (renameFrame f frame) := by
  cases frame with
  | argument term environment => exact closureValid_rename hr inside valid
  | binaryLeft primitive term environment => exact closureValid_rename hr inside valid
  | update address => exact image_lt hr (inside address (List.mem_singleton_self _)) valid
  | field _ | reflect | metadata | project => trivial
  | extend fields environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩
  | condition zero successorBody environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩
  | binaryRight primitive value => exact runtimeValueValid_rename hr inside valid
  | case arms environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩
  | ifBool whenTrue whenFalse environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩

theorem controlValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {control : Control}
    (inside : AllIn D (controlAddresses control)) (valid : ControlValid heap.size control) :
    ControlValid heap'.size (renameControl f control) := by
  cases control with
  | evaluate term environment => exact closureValid_rename (closure := ⟨term, environment⟩) hr inside valid
  | enter address => exact image_lt hr (inside address (List.mem_singleton_self _)) valid
  | blackhole address => exact image_lt hr (inside address (List.mem_singleton_self _)) valid
  | returned value => exact runtimeValueValid_rename hr inside valid
  | complete value => exact runtimeValueValid_rename hr inside valid
  | refused _ => trivial
  | yielded plan => exact image_lt hr (inside plan (List.mem_singleton_self _)) valid

public theorem lexical_related {s t : State} (related : Related f D s t) (cover : Covers f D s.heap t.heap)
    (lexical : LexicalInvariant s) : LexicalInvariant t := by
  obtain ⟨cells, control, frames⟩ := lexical
  refine ⟨?_, ?_, ?_⟩
  · intro k cell found
    obtain ⟨a, inA, boundA, rfl⟩ := cover k (bound_of_some found)
    obtain ⟨c, foundC, foundC', inC⟩ := related.heap.cells a inA boundA
    rw [found] at foundC'; cases foundC'
    exact cellValid_rename related.heap inC (cells a c foundC)
  · rw [related.control]; exact controlValid_rename related.heap related.controlIn control
  · intro frame member
    rw [related.stack] at member
    obtain ⟨original, memberO, rfl⟩ := List.mem_map.mp member
    exact frameValid_rename related.heap (related.stackIn original memberO) (frames original memberO)

theorem stackUpdates_rename (stack : List Frame) :
    stackUpdates (stack.map (renameFrame f)) = (stackUpdates stack).map f := by
  induction stack with
  | nil => rfl
  | cons frame rest ih => cases frame <;> simp [stackUpdates, renameFrame, ih]

theorem stackUpdates_in {stack : List Frame} (inside : ∀ frame ∈ stack, AllIn D (frameAddresses frame)) :
    AllIn D (stackUpdates stack) := by
  induction stack with
  | nil => exact allIn_nil D
  | cons frame rest ih =>
    have ⟨head, tail⟩ := List.forall_mem_cons.mp inside
    cases frame <;> simp only [stackUpdates] <;> first
      | exact ih tail
      | exact allIn_cons (head _ (List.mem_singleton_self _)) (ih tail)

theorem nodup_map_on {l : List Nat} (inside : AllIn D l) (inj : ∀ a b, D a → D b → f a = f b → a = b)
    (nodup : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
    rw [List.nodup_cons] at nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun x member => inside x (List.mem_cons_of_mem _ member)) nodup.2⟩
    intro member
    obtain ⟨other, memberO, same⟩ := List.mem_map.mp member
    have := inj other head (inside other (List.mem_cons_of_mem _ memberO)) (inside head (List.mem_cons_self ..)) same
    exact nodup.1 (this ▸ memberO)

public theorem busy_related {s t : State} (related : Related f D s t) (cover : Covers f D s.heap t.heap)
    (busy : BusyInvariant s) : BusyInvariant t := by
  obtain ⟨nodup, marks⟩ := busy
  have updatesIn := stackUpdates_in related.stackIn
  unfold BusyInvariant Busy
  rw [related.stack, stackUpdates_rename]
  refine ⟨nodup_map_on updatesIn related.heap.inj nodup, ?_⟩
  intro k
  constructor
  · intro member
    obtain ⟨a, memberA, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, found⟩ := (marks a).mp memberA
    exact ⟨_, by rw [related.heap.lookup (updatesIn a memberA), found]; rfl⟩
  · rintro ⟨origin, found⟩
    obtain ⟨a, inA, boundA, rfl⟩ := cover k (bound_of_some found)
    rw [related.heap.lookup inA] at found
    cases foundA : s.heap[a]? with
    | none => rw [foundA] at found; cases found
    | some cell =>
      rw [foundA] at found
      cases cell with
      | evaluating o => exact List.mem_map_of_mem ((marks a).mpr ⟨o, foundA⟩)
      | suspended o => cases found
      | cached o v => cases found

public theorem finalStack_related {s t : State} (related : Related f D s t) (final : FinalStackInvariant s) :
    FinalStackInvariant t := by
  intro value complete
  rw [related.stack]
  rw [related.control] at complete
  cases control : s.control <;> rw [control] at complete <;> simp [renameControl] at complete
  rw [final _ control]; rfl

/-- **Typing transfers along a covering renaming.** -/
@[expose] public def typed_related {s t : State} {result : Ty} (related : Related f D s t) (cover : Covers f D s.heap t.heap)
    (rel : TypesRel f D types types') (length : types'.length = t.heap.size)
    (typed : StateTyping assumptions types s result) : StateTyping assumptions types' t result where
  current := typed.current
  heap := heapTyping_rename related.heap rel length cover typed.heap
  control := by rw [related.control]; exact controlTyping_rename rel related.controlIn typed.control
  stack := by rw [related.stack]; exact stackTyping_rename rel typed.stack related.stackIn
  assumptionsValid := typed.assumptionsValid
  lexical := lexical_related related cover typed.lexical
  busy := busy_related related cover typed.busy
  terminalStack := finalStack_related related typed.terminalStack

end Typing

end Obend.Core.Collect
