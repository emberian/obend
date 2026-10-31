module
/- Collection: covering, typing, inhabitants, and the T5 statements. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Collect.Segment
public import Obend.Core.Proofs.Collect.Typing
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

open Obend.Core.Data
/-! ## Collection: covering, typing, and the T5 statements -/

theorem count_take_surj : ∀ (M : List Bool) (k : Nat), k < M.count true →
    ∃ i, M[i]? = some true ∧ (M.take i).count true = k
  | [], k, bound => by simp at bound
  | m :: M, k, bound => by
    cases m with
    | true =>
      cases k with
      | zero => exact ⟨0, rfl, by simp⟩
      | succ k =>
        obtain ⟨i, marked, rank⟩ := count_take_surj M k (by simp at bound; omega)
        exact ⟨i + 1, by simpa using marked, by simp [rank]⟩
    | false =>
      obtain ⟨i, marked, rank⟩ := count_take_surj M k (by simpa [List.count_cons] using bound)
      exact ⟨i + 1, by simpa using marked, by simp [rank]⟩

/-- Every collected cell is the image of a live cell. -/
public theorem collect_covers (state : State) :
    Covers (collectRenaming state) (liveDomain state) state.heap (collect state).heap := by
  intro k bound
  rw [collect_heap_size, ← Array.count_toList] at bound
  obtain ⟨i, marked, rank⟩ := count_take_surj _ k bound
  have markedA : (liveMarks state)[i]? = some true := by simpa using marked
  refine ⟨i, .inr markedA, ?_, ?_⟩
  · rw [← (liveMarks_spec state).1]; exact bound_of_some markedA
  · rw [collectRenaming_live markedA, rank]

section CollectTyping
open Obend.Core.Ty Obend.Core.Check
open Obend.Core.MachineTyping Obend.Core.Invariant

/-- The address types of the collected heap: the live cells' types, in order. -/
@[expose] public def collectTypes (state : State) (types : AddressTypes) : AddressTypes :=
  (types.zip (liveMarks state).toList).filterMap fun entry => if entry.2 then some entry.1 else none

public theorem collectTypes_length {state : State} {types : AddressTypes} (length : types.length = state.heap.size) :
    (collectTypes state types).length = (collect state).heap.size := by
  rw [collect_heap_size, ← Array.count_toList]
  exact filterMap_zip_length (fun x => x) _ _ (by simp [length, (liveMarks_spec state).1])

public theorem collectTypes_rel {state : State} {types : AddressTypes} (length : types.length = state.heap.size) :
    TypesRel (collectRenaming state) (liveDomain state) types (collectTypes state types) := by
  intro a inA
  rcases inA with past | marked
  · rw [List.getElem?_eq_none (by omega : types.length ≤ a)]
    apply List.getElem?_eq_none
    have := collectRenaming_beyond past
    rw [collectTypes_length length, collect_heap_size]; omega
  · have bound : a < types.length := by
      rw [length, ← (liveMarks_spec state).1]; exact bound_of_some marked
    rw [List.getElem?_eq_getElem bound, collectRenaming_live marked]
    exact filterMap_zip_getElem (fun x => x) _ _ _ _ (List.getElem?_eq_getElem bound) (by simpa using marked)

/-- **Typing transfers to the collected state** (heap typing, control and stack
typing, and the lexical, busy and final-stack invariants), at the live cells' types. -/
@[expose] public def typed_collect {assumptions : Assumptions} {types : AddressTypes} {state : State} {result : Ty}
    (typed : StateTyping assumptions types state result) :
    StateTyping assumptions (collectTypes state types) (collect state) result :=
  typed_related (related_collect state) (collect_covers state) (collectTypes_rel typed.heap.length)
    (collectTypes_length typed.heap.length) typed

theorem typed_collect_exists {assumptions : Assumptions} {types : AddressTypes} {state : State} {result : Ty}
    (typed : StateTyping assumptions types state result) :
    ∃ types', Nonempty (StateTyping assumptions types' (collect state) result) :=
  ⟨_, ⟨typed_collect typed⟩⟩

/-! ### Inhabitants -/

/-- A typed state with garbage: a cached natural no root reaches. -/
@[expose] public def garbageTyped : State := ⟨#[.cached ⟨.nat 0, []⟩ (.natural 0)], .evaluate (.nat 5) [], []⟩

@[expose] public def garbageTyping : StateTyping {} [.natural] garbageTyped .natural where
  current := .natural
  heap := ⟨rfl, by
    intro address type found
    cases address with
    | zero =>
      simp at found; subst found
      exact ⟨_, rfl, .cached ⟨[], [], EnvironmentTyping.empty _, .natural [] 0, rfl, rfl⟩ (.natural 0) rfl⟩
    | succ n => simp at found⟩
  control := .evaluate ⟨[], [], EnvironmentTyping.empty _, .natural [] 5, rfl, rfl⟩
  stack := .nil _
  assumptionsValid := rfl
  lexical := ⟨by
      intro address cell found
      cases address with
      | zero => simp [garbageTyped] at found; subst found; exact ⟨⟨.natural 0, fun _ h => by cases h⟩, trivial⟩
      | succ n => simp [garbageTyped] at found,
    ⟨.natural 5, fun _ h => by cases h⟩, fun _ h => by cases h⟩
  busy := by
    refine ⟨List.nodup_nil, fun address => ?_⟩
    simp only [garbageTyped, stackUpdates, List.not_mem_nil, false_iff]
    rintro ⟨origin, found⟩
    cases address with
    | zero => simp at found
    | succ n => simp at found
  terminalStack := fun _ complete => by cases complete

/- `garbageTyped_collected` (the collected typed state drops the garbage cell: sizes 1 and 0) is in
`Obend.Core.Teeth.CollectTyping`, a legacy leaf: its `decide` evaluates `collect`. -/

theorem garbageTyped_collect_typed :
    Nonempty (StateTyping {} (collectTypes garbageTyped [.natural]) (collect garbageTyped) .natural) :=
  ⟨typed_collect garbageTyping⟩

end CollectTyping

/-! ### A run that yields with garbage, and its collected Plan

`ifZero ((λx. x) 0) (perform 5) 9`: the argument thunk is forced and cached, the
condition takes the zero branch, and the program yields Plan `5`. The forced argument
is garbage at the yield. -/

@[expose] public def yieldingTerm : Term := .ifZero (.app (.lam (.bound 0)) (.nat 0)) (.perform (.nat 5)) (.nat 9)
@[expose] public def exampleLimits : Limits := ⟨16, 16⟩
@[expose] public def exampleBudget : Budget := ⟨8, 64, 64⟩

@[expose] public def exampleYield : State :=
  match runBounded exampleLimits 32 (initial yieldingTerm) with
  | .yielded _ yielded => yielded
  | _ => initial yieldingTerm

/- The five executed teeth over `yieldingTerm`/`exampleYield` (it yields at cell 1; collection drops one
of two cells; both Plans extract to the same encoded Data; the segment premises are inhabited) are in
`Obend.Core.Teeth.CollectYield`, a legacy leaf: their `decide`/`rfl` run the machine and `collect`. -/

/-! ## The T5 statements for `collect` -/

/-- Collection never grows the heap. -/
theorem collect_heap_le (state : State) : (collect state).heap.size ≤ state.heap.size :=
  (related_collect state).heap.size_le

/-- A yielded state stays yielded, at its Plan cell's new address. -/
theorem collect_yielded {state : State} {plan : Nat} (yielded : state.control = .yielded plan) :
    (collect state).control = .yielded (collectRenaming state plan) := by
  rw [(related_collect state).control, yielded]; rfl

/-- **Resuming the collected state runs as resuming the original**: with any response,
for any tick budget, the outcomes agree (same constructor and reason, renamed payload,
related retained state) unless the original ran out of heap. -/
theorem collect_resume_runBounded {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits : Limits) (ticks : Nat)
    (notCapacity : ranOutOfHeap (runBounded limits ticks resumed) = false) :
    ∃ resumed', resume response (collect state) = some resumed' ∧
      OutcomeRel (collectRenaming state) (liveDomain state)
        (runBounded limits ticks resumed) (runBounded limits ticks resumed') := by
  obtain ⟨resumed', again, related⟩ := related_resume (related_collect state) response yielded
  exact ⟨resumed', again, related_runBounded limits limits ticks _ _ related (RoomFor.same _ _ _) notCapacity⟩

/-- **Exactly**, capacity included, once the collected run is charged the heap it freed. -/
theorem collect_resume_runBounded_exact {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits : Limits) (ticks : Nat)
    (fits : state.heap.size ≤ limits.heap) :
    ∃ resumed', resume response (collect state) = some resumed' ∧
      OutcomeRel (collectRenaming state) (liveDomain state) (runBounded limits ticks resumed)
        (runBounded ⟨limits.heap - (state.heap.size - (collect state).heap.size), limits.stack⟩ ticks resumed') := by
  obtain ⟨resumed', again, related⟩ := related_resume (related_collect state) response yielded
  have sameHeap : resumed.heap = state.heap := (resume_keeps_heap_and_stack _ _ _ yielded).1
  have sameHeap' : resumed'.heap = (collect state).heap := (resume_keeps_heap_and_stack _ _ _ again).1
  have := related_runBounded_exact limits ticks _ _ related (by rw [sameHeap]; exact fits)
  rw [sameHeap, sameHeap'] at this
  exact ⟨resumed', again, this⟩

/-- **The kernel's segment from a collected checkpoint** agrees with the segment from the
uncollected one: Plan Data, result Data, divergence and refusal reasons. -/
theorem collect_resume_segment {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits limits' : Limits)
    (heapRoom : limits.heap ≤ limits'.heap + (state.heap.size - (collect state).heap.size))
    (stackRoom : limits.stack ≤ limits'.stack) (ticks : Nat) (budget : Budget) :
    ∃ resumed', resume response (collect state) = some resumed' ∧
      (∀ plan y r, runBounded limits ticks resumed = .yielded plan y → yieldedPlan limits budget y = .ok r →
        ∃ y' r', runBounded limits' ticks resumed' = .yielded (collectRenaming state plan) y' ∧
          Related (collectRenaming state) (liveDomain state) y y' ∧
          yieldedPlan limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
      (∀ value y r, runBounded limits ticks resumed = .finished value y → complete limits budget y = .ok r →
        ∃ y' r', runBounded limits' ticks resumed' = .finished (renameValue (collectRenaming state) value) y' ∧
          complete limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
      (∀ address y, runBounded limits ticks resumed = .divergent address y →
        ∃ y', runBounded limits' ticks resumed' = .divergent (collectRenaming state address) y') ∧
      (∀ reason y, runBounded limits ticks resumed = .refused reason y →
        ∃ y', runBounded limits' ticks resumed' = .refused reason y') := by
  obtain ⟨resumed', again, related⟩ := related_resume (related_collect state) response yielded
  have sameHeap : resumed.heap = state.heap := (resume_keeps_heap_and_stack _ _ _ yielded).1
  have sameHeap' : resumed'.heap = (collect state).heap := (resume_keeps_heap_and_stack _ _ _ again).1
  have room : RoomFor limits limits' resumed resumed' :=
    ⟨by rw [sameHeap, sameHeap']; exact heapRoom, stackRoom⟩
  exact ⟨resumed', again, related_segment related limits limits' room ticks budget⟩

/-- The Plan of a yielded state extracts from its collection to the same Data. -/
theorem collect_yieldedPlan {state : State} {limits : Limits} {budget : Budget} {r : Result}
    (extracted : yieldedPlan limits budget state = .ok r) :
    ∃ r', yieldedPlan limits budget (collect state) = .ok r' ∧ r'.value = r.value := by
  obtain ⟨r', extracted', same, _, _⟩ :=
    related_yieldedPlanWith (fun _ _ _ _ => rfl) limits limits budget (related_collect state) (RoomFor.same _ _ _)
      extracted
  exact ⟨r', extracted', same⟩

end Obend.Core.Collect
