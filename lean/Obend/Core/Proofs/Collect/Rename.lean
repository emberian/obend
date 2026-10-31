module
/- The renaming simulation; heap agreement is preserved by allocation and update. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Collect.Compact
public import Obend.Core.Proofs.Collect.Mark
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

/-! ## The renaming simulation -/

@[expose] public def AllIn (D : Nat → Prop) (addresses : List Nat) : Prop := ∀ x ∈ addresses, D x

/-- Two heaps agree under a renaming `f` on a domain `D`: `D` contains everything past
the first heap (where `f` is the shift between the two ends), `f` is injective on `D`,
and every `D`-cell of the first heap is, renamed, the `f`-image cell of the second, with
its addresses again in `D`. Nothing is said about cells outside `D` (the garbage). -/
public structure HeapRel (f : Nat → Nat) (D : Nat → Prop) (heap heap' : Array Cell) : Prop where
  size_le : heap'.size ≤ heap.size
  beyond : ∀ a, heap.size ≤ a → D a ∧ f a + heap.size = a + heap'.size
  inj : ∀ a b, D a → D b → f a = f b → a = b
  cells : ∀ a, D a → a < heap.size →
    ∃ c, heap[a]? = some c ∧ heap'[f a]? = some (renameCell f c) ∧ AllIn D (cellAddresses c)

/-- **The simulation relation.** `t` is `s` renamed by `f` on everything `s` can reach
(`D` is closed under the heap and contains the roots): same control, same stack, and
the `D`-cells agree. -/
public structure Related (f : Nat → Nat) (D : Nat → Prop) (s t : State) : Prop where
  heap : HeapRel f D s.heap t.heap
  controlIn : AllIn D (controlAddresses s.control)
  control : t.control = renameControl f s.control
  stackIn : ∀ frame ∈ s.stack, AllIn D (frameAddresses frame)
  stack : t.stack = s.stack.map (renameFrame f)

/-- The domain `collect` traces: the live cells and everything past the heap. -/
@[expose] public def liveDomain (state : State) (a : Nat) : Prop :=
  state.heap.size ≤ a ∨ (liveMarks state)[a]? = some true

theorem liveDomain_of_not_false {state : State} {x : Nat}
    (notFalse : (liveMarks state)[x]? ≠ some false) : liveDomain state x := by
  by_cases bound : x < state.heap.size
  · right
    have size := (liveMarks_spec state).1
    have : x < (liveMarks state).size := by omega
    rw [Array.getElem?_eq_getElem this] at notFalse ⊢
    cases value : (liveMarks state)[x]
    · rw [value] at notFalse; exact absurd rfl notFalse
    · rfl
  · left; omega

public theorem collectRenaming_live {state : State} {a : Nat} (marked : (liveMarks state)[a]? = some true) :
    collectRenaming state a = ((liveMarks state).toList.take a).count true := by
  have size := (liveMarks_spec state).1
  have bound : a < state.heap.size := by rw [← size]; exact bound_of_some marked
  have ranks := rankTable_spec (liveMarks state)
  simp only [collectRenaming, relocate, bound, if_true]
  rw [Array.getD_eq_getD_getElem?, ranks.2.2 a (by omega)]
  rfl

public theorem collectRenaming_beyond {state : State} {a : Nat} (past : state.heap.size ≤ a) :
    collectRenaming state a = a - state.heap.size + (liveMarks state).count true := by
  have ranks := rankTable_spec (liveMarks state)
  simp only [collectRenaming, relocate, show ¬ a < state.heap.size by omega, if_false]
  rw [ranks.1]

public theorem collect_heap_size (state : State) :
    (collect state).heap.size = (liveMarks state).count true :=
  compact_size _ _ _ (liveMarks_spec state).1

/-- **Collection is a renaming of the state it collects.** -/
public theorem related_collect (state : State) :
    Related (collectRenaming state) (liveDomain state) state (collect state) := by
  obtain ⟨size, roots, closed⟩ := liveMarks_spec state
  have live_lt : ∀ a, (liveMarks state)[a]? = some true →
      collectRenaming state a < (liveMarks state).count true := by
    intro a marked
    rw [collectRenaming_live marked, ← Array.count_toList]
    exact count_take_lt_count _ (by simpa using marked)
  have count_le : (liveMarks state).count true ≤ state.heap.size := by
    rw [← size, ← Array.count_toList, ← Array.length_toList]; exact List.count_le_length
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, rfl, ?_, rfl⟩
  · rw [collect_heap_size]; exact count_le
  · intro a past
    refine ⟨.inl past, ?_⟩
    rw [collectRenaming_beyond past, collect_heap_size]; omega
  · intro a b inA inB same
    rcases inA with pastA | markedA <;> rcases inB with pastB | markedB
    · rw [collectRenaming_beyond pastA, collectRenaming_beyond pastB] at same; omega
    · have := live_lt b markedB; rw [collectRenaming_beyond pastA] at same; omega
    · have := live_lt a markedA; rw [collectRenaming_beyond pastB] at same; omega
    · rw [collectRenaming_live markedA, collectRenaming_live markedB] at same
      rcases Nat.lt_trichotomy a b with lt | eq | gt
      · have := count_take_lt (liveMarks state).toList lt (by simpa using markedA); omega
      · exact eq
      · have := count_take_lt (liveMarks state).toList gt (by simpa using markedB); omega
  · intro a inA bound
    have marked : (liveMarks state)[a]? = some true := by
      rcases inA with past | marked
      · omega
      · exact marked
    obtain ⟨c, found⟩ : ∃ c, state.heap[a]? = some c := ⟨_, Array.getElem?_eq_getElem bound⟩
    refine ⟨c, found, ?_, ?_⟩
    · rw [collectRenaming_live marked]
      exact compact_getElem _ _ _ found marked
    · intro x member
      apply liveDomain_of_not_false
      exact closed a x marked (by simp [children, found, member])
  · intro x member
    exact liveDomain_of_not_false (roots x (List.mem_append_left _ member))
  · intro frame member x inFrame
    exact liveDomain_of_not_false (roots x (List.mem_append_right _ (List.mem_flatMap.mpr ⟨frame, member, inFrame⟩)))


/-! ## Heap agreement is preserved by allocation and update -/

namespace HeapRel
variable {f : Nat → Nat} {D : Nat → Prop} {heap heap' : Array Cell}

public theorem lookup (hr : HeapRel f D heap heap') {a : Nat} (inD : D a) :
    heap'[f a]? = (heap[a]?).map (renameCell f) := by
  by_cases bound : a < heap.size
  · obtain ⟨c, found, found', _⟩ := hr.cells a inD bound
    rw [found, found']; rfl
  · have shift := (hr.beyond a (Nat.le_of_not_lt bound)).2
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound), Array.getElem?_eq_none (by omega)]
    rfl

public theorem cellIn (hr : HeapRel f D heap heap') {a : Nat} {c : Cell} (inD : D a)
    (found : heap[a]? = some c) : AllIn D (cellAddresses c) := by
  obtain ⟨c', found', _, inC⟩ := hr.cells a inD (bound_of_some found)
  rw [found] at found'; cases found'; exact inC

public theorem image_size (hr : HeapRel f D heap heap') : f heap.size = heap'.size ∧ D heap.size := by
  have := hr.beyond heap.size (Nat.le_refl _); exact ⟨by omega, this.1⟩

public theorem image_size_succ (hr : HeapRel f D heap heap') :
    f (heap.size + 1) = heap'.size + 1 ∧ D (heap.size + 1) := by
  have := hr.beyond (heap.size + 1) (Nat.le_succ _); exact ⟨by omega, this.1⟩

public theorem push (hr : HeapRel f D heap heap') {c : Cell} (cIn : AllIn D (cellAddresses c)) :
    HeapRel f D (heap.push c) (heap'.push (renameCell f c)) := by
  have sizeLe := hr.size_le
  refine ⟨by simp; omega, ?_, hr.inj, ?_⟩
  · intro a past
    simp at past
    have := hr.beyond a (by omega)
    exact ⟨this.1, by simp; omega⟩
  · intro a inD bound
    simp at bound
    by_cases old : a < heap.size
    · obtain ⟨c', found, found', inC⟩ := hr.cells a inD old
      have lt : f a < heap'.size := bound_of_some found'
      refine ⟨c', ?_, ?_, inC⟩
      · simp [Array.getElem?_push, Nat.ne_of_lt old, found]
      · simp [Array.getElem?_push, Nat.ne_of_lt lt, found']
    · have eq : a = heap.size := by omega
      subst eq
      refine ⟨c, by simp, ?_, cIn⟩
      rw [hr.image_size.1]; simp

public theorem set (hr : HeapRel f D heap heap') {a : Nat} {c : Cell} (inD : D a) (bound : a < heap.size)
    (cIn : AllIn D (cellAddresses c)) :
    HeapRel f D (heap.set! a c) (heap'.set! (f a) (renameCell f c)) := by
  obtain ⟨_, _, found', _⟩ := hr.cells a inD bound
  have lt : f a < heap'.size := bound_of_some found'
  refine ⟨by simp; exact hr.size_le, ?_, hr.inj, ?_⟩
  · intro b past; simp at past; have := hr.beyond b past; exact ⟨this.1, by simp; exact this.2⟩
  · intro b inB boundB
    simp at boundB
    by_cases same : a = b
    · subst same
      exact ⟨c, by simp [bound],
        by simp [lt], cIn⟩
    · obtain ⟨c', found, found'', inC⟩ := hr.cells b inB boundB
      have diff : f a ≠ f b := fun h => same (hr.inj a b inD inB h)
      exact ⟨c', by simp [same, found],
        by simp [diff, found''], inC⟩

end HeapRel

theorem allocateFields_foldl {f : Nat → Nat} {D : Nat → Prop} (environment : List Nat)
    (environmentIn : AllIn D environment) (fields : List (String × Term)) :
    ∀ (heap heap' : Array Cell) (acc : List (String × Nat)),
      HeapRel f D heap heap' → AllIn D (acc.map Prod.snd) →
      HeapRel f D
          (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (heap,acc)).1
          (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment.map f⟩),(field.1,prior.1.size)::prior.2))
            (heap',acc.map fun field => (field.1, f field.2))).1 ∧
        (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment.map f⟩),(field.1,prior.1.size)::prior.2))
            (heap',acc.map fun field => (field.1, f field.2))).2 =
          (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2))
            (heap,acc)).2.map (fun field => (field.1, f field.2)) ∧
        AllIn D ((fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2))
            (heap,acc)).2.map Prod.snd) := by
  induction fields with
  | nil => intro heap heap' acc hr accIn; exact ⟨hr, rfl, accIn⟩
  | cons field rest ih =>
    intro heap heap' acc hr accIn
    have ⟨image, sizeIn⟩ := hr.image_size
    have pushed := hr.push (c := .suspended ⟨field.2, environment⟩) environmentIn
    have accIn' : AllIn D (((field.1, heap.size) :: acc).map Prod.snd) := by
      intro x member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact sizeIn
      · exact accIn x member
    have := ih _ _ _ pushed accIn'
    simp only [List.foldl_cons]
    simp only [List.map_cons, image] at this
    exact this

public theorem allocateFields_related {f : Nat → Nat} {D : Nat → Prop} {heap heap' : Array Cell}
    (hr : HeapRel f D heap heap') {environment : List Nat} (environmentIn : AllIn D environment)
    (fields : List (String × Term)) :
    HeapRel f D (allocateFields heap environment fields).1
        (allocateFields heap' (environment.map f) fields).1 ∧
      (allocateFields heap' (environment.map f) fields).2 =
        (allocateFields heap environment fields).2.map (fun field => (field.1, f field.2)) ∧
      AllIn D ((allocateFields heap environment fields).2.map Prod.snd) := by
  obtain ⟨hr', same, inside⟩ := allocateFields_foldl environment environmentIn fields heap heap' []
    hr (fun _ member => by cases member)
  refine ⟨hr', ?_, ?_⟩
  · simp only [allocateFields]
    simp only [List.map_nil] at same
    rw [same, List.map_reverse]
  · intro x member
    simp only [allocateFields, List.map_reverse, List.mem_reverse] at member
    exact inside x member

end Obend.Core.Collect
