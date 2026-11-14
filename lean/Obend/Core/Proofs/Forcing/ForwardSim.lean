module
/- Forward simulation, bounded-segment halting, and pending-switch chains for demand forcing.
   Consolidates `Agree`, `Run`, `Nest`, `Pend`, `Switch`, `Chain`, and `Segment` (`Wave C2-Core`). -/
public import Obend.Core.Proofs.Collect.Runs
public import Obend.Core.Proofs.Collect.Segment
public import Obend.Core.Proofs.Collect.Typing
public import Obend.Core.Data
public import Obend.Core.Invariant
public import Obend.Tactic.Cases

namespace Obend.Core.Proofs.Forcing
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Collect
open Obend.Core.Data
open Obend.Core.Invariant (PreservesCached stepRaw_preservesCached)
set_option autoImplicit false

/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Agree.lean` -/

/-- Heaps agree under `f` on `D`, except at `U`. -/
public structure HeapAgree (f : Nat → Nat) (D U : Nat → Prop) (heap heap' : Array Cell) : Prop where
  beyond : ∀ a, heap.size ≤ a → D a ∧ ¬ U a ∧ f a + heap.size = a + heap'.size
  inj : ∀ a b, D a → D b → f a = f b → a = b
  cells : ∀ a, D a → ¬ U a → a < heap.size →
    ∃ c, heap[a]? = some c ∧ heap'[f a]? = some (renameCell f c) ∧ AllIn D (cellAddresses c)

/-- States agree: heaps agree, control and stack are renamed. -/
public structure StateAgree (f : Nat → Nat) (D U : Nat → Prop) (s t : State) : Prop where
  heap : HeapAgree f D U s.heap t.heap
  controlIn : AllIn D (controlAddresses s.control)
  control : t.control = renameControl f s.control
  stackIn : ∀ frame ∈ s.stack, AllIn D (frameAddresses frame)
  stack : t.stack = s.stack.map (renameFrame f)

/-- The heap cell a transition reads: the entered address, or the cell an update
frame on top of a returned value caches. -/
public def readsAt (state : State) : Option Nat :=
  match state.control, state.stack with
  | .enter address, _ => some address
  | .returned _, .update address :: _ => some address
  | _, _ => none

/-- The transition reads no cell of `U`. -/
public def Avoids (U : Nat → Prop) (state : State) : Prop := ∀ a, readsAt state = some a → ¬ U a

namespace HeapAgree
variable {f : Nat → Nat} {D U : Nat → Prop} {heap heap' : Array Cell}

public theorem lookup (hr : HeapAgree f D U heap heap') {a : Nat} (inD : D a) (notU : ¬ U a) :
    heap'[f a]? = (heap[a]?).map (renameCell f) := by
  by_cases bound : a < heap.size
  · obtain ⟨c, found, found', _⟩ := hr.cells a inD notU bound
    rw [found, found']; rfl
  · have shift := (hr.beyond a (Nat.le_of_not_lt bound)).2.2
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound), Array.getElem?_eq_none (by omega)]
    rfl

public theorem cellIn (hr : HeapAgree f D U heap heap') {a : Nat} {c : Cell} (inD : D a) (notU : ¬ U a)
    (found : heap[a]? = some c) : AllIn D (cellAddresses c) := by
  obtain ⟨c', found', _, inC⟩ := hr.cells a inD notU (bound_of_some found)
  rw [found] at found'; cases found'; exact inC

public theorem image_size (hr : HeapAgree f D U heap heap') : f heap.size = heap'.size ∧ D heap.size := by
  have := hr.beyond heap.size (Nat.le_refl _); exact ⟨by omega, this.1⟩

public theorem image_size_succ (hr : HeapAgree f D U heap heap') :
    f (heap.size + 1) = heap'.size + 1 ∧ D (heap.size + 1) := by
  have := hr.beyond (heap.size + 1) (Nat.le_succ _); exact ⟨by omega, this.1⟩

public theorem image_lt (hr : HeapAgree f D U heap heap') {a : Nat} (inD : D a) (bound : a < heap.size) :
    f a < heap'.size := by
  by_cases lt : f a < heap'.size
  · exact lt
  · have past : heap.size ≤ f a + heap.size - heap'.size := by omega
    have ⟨inD', _, shift⟩ := hr.beyond (f a + heap.size - heap'.size) past
    have same := hr.inj _ _ inD inD' (by omega)
    omega

public theorem push (hr : HeapAgree f D U heap heap') {c : Cell} (cIn : AllIn D (cellAddresses c)) :
    HeapAgree f D U (heap.push c) (heap'.push (renameCell f c)) := by
  refine ⟨?_, hr.inj, ?_⟩
  · intro a past
    simp at past
    have := hr.beyond a (by omega)
    exact ⟨this.1, this.2.1, by simp; omega⟩
  · intro a inD notU bound
    simp at bound
    by_cases old : a < heap.size
    · obtain ⟨c', found, found', inC⟩ := hr.cells a inD notU old
      have lt : f a < heap'.size := bound_of_some found'
      refine ⟨c', ?_, ?_, inC⟩
      · simp [Array.getElem?_push, Nat.ne_of_lt old, found]
      · simp [Array.getElem?_push, Nat.ne_of_lt lt, found']
    · have eq : a = heap.size := by omega
      subst eq
      refine ⟨c, by simp, ?_, cIn⟩
      rw [hr.image_size.1]; simp

public theorem set (hr : HeapAgree f D U heap heap') {a : Nat} {c : Cell} (inD : D a) (notU : ¬ U a)
    (bound : a < heap.size) (cIn : AllIn D (cellAddresses c)) :
    HeapAgree f D U (heap.set! a c) (heap'.set! (f a) (renameCell f c)) := by
  obtain ⟨_, _, found', _⟩ := hr.cells a inD notU bound
  have lt : f a < heap'.size := bound_of_some found'
  refine ⟨?_, hr.inj, ?_⟩
  · intro b past; simp at past; have := hr.beyond b past; exact ⟨this.1, this.2.1, by simp; exact this.2.2⟩
  · intro b inB notUB boundB
    simp at boundB
    by_cases same : a = b
    · subst same
      exact ⟨c, by simp [bound], by simp [lt], cIn⟩
    · obtain ⟨c', found, found'', inC⟩ := hr.cells b inB notUB boundB
      have diff : f a ≠ f b := fun h => same (hr.inj a b inD inB h)
      exact ⟨c', by simp [same, found], by simp [diff, found''], inC⟩

end HeapAgree

theorem allocateFields_foldl_agree {f : Nat → Nat} {D U : Nat → Prop} (environment : List Nat)
    (environmentIn : AllIn D environment) (fields : List (String × Term)) :
    ∀ (heap heap' : Array Cell) (acc : List (String × Nat)),
      HeapAgree f D U heap heap' → AllIn D (acc.map Prod.snd) →
      HeapAgree f D U
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

theorem allocateFields_agree {f : Nat → Nat} {D U : Nat → Prop} {heap heap' : Array Cell}
    (hr : HeapAgree f D U heap heap') {environment : List Nat} (environmentIn : AllIn D environment)
    (fields : List (String × Term)) :
    HeapAgree f D U (allocateFields heap environment fields).1
        (allocateFields heap' (environment.map f) fields).1 ∧
      (allocateFields heap' (environment.map f) fields).2 =
        (allocateFields heap environment fields).2.map (fun field => (field.1, f field.2)) ∧
      AllIn D ((allocateFields heap environment fields).2.map Prod.snd) := by
  obtain ⟨hr', same, inside⟩ := allocateFields_foldl_agree environment environmentIn fields heap heap' []
    hr (fun _ member => by cases member)
  refine ⟨hr', ?_, ?_⟩
  · simp only [allocateFields]
    simp only [List.map_nil] at same
    rw [same, List.map_reverse]
  · intro x member
    simp only [allocateFields, List.map_reverse, List.mem_reverse] at member
    exact inside x member

/-- **Lockstep.** An agreeing pair steps to an agreeing pair, provided the transition
reads no cell of `U`. -/
public theorem agree_stepRaw {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t)
    (avoids : Avoids U s) : StateAgree f D U (stepRaw s) (stepRaw t) := by
  obtain ⟨hr, controlIn, controlEq, stackIn, stackEq⟩ := related
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨heap', control', stack'⟩ := t
  simp only at hr controlIn controlEq stackIn stackEq
  subst controlEq stackEq
  have ⟨image, sizeIn⟩ := hr.image_size
  have ⟨image1, sizeIn1⟩ := hr.image_size_succ
  cases control with
  | complete v => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | refused r => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | blackhole a => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | yielded p => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | enter a =>
    have inA : D a := controlIn a (List.mem_singleton_self a)
    have notU : ¬ U a := avoids a (by simp [readsAt])
    simp only [stepRaw, renameControl]
    rw [hr.lookup inA notU]
    cases found : heap[a]? with
    | none => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | some cell =>
      have cellIn := hr.cellIn inA notU found
      cases cell with
      | evaluating o => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
      | cached o v => exact ⟨hr, fun x member => cellIn x (List.mem_append_right _ member), rfl, stackIn, rfl⟩
      | suspended o =>
        exact ⟨hr.set inA notU (bound_of_some found) (c := .evaluating o) cellIn, cellIn, rfl,
          frames_cons (allIn_cons inA (allIn_nil D)) stackIn, rfl⟩
  | evaluate term env =>
    have envIn : AllIn D env := controlIn
    cases term with
    | hole _ payload =>
      obend_cases payload with []
      all_goals exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | bound i =>
      simp only [stepRaw, renameControl]
      rw [List.getElem?_map]
      cases found : env[i]? with
      | none => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
      | some a => exact ⟨hr, allIn_cons (envIn a (List.mem_of_getElem? found)) (allIn_nil D), rfl, stackIn, rfl⟩
    | lam body => exact ⟨hr, envIn, rfl, stackIn, rfl⟩
    | nat n => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | boolean b => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | label l => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | app fn arg => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | mix lower upper => exact ⟨hr, envIn, rfl, stackIn, rfl⟩
    | fix spec inherited =>
      have pushed := hr.push (c := .suspended ⟨Term.app (Term.app (spec.rename Nat.succ) (.bound 0))
        (inherited.rename Nat.succ), heap.size :: env⟩) (allIn_cons sizeIn envIn)
      simp only [renameCell, renameClosure, List.map_cons, image] at pushed
      refine ⟨pushed, allIn_cons sizeIn (allIn_nil D), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, image]
    | specification descriptor extension =>
      have pushed := (hr.push (c := .suspended ⟨descriptor, env⟩) envIn).push
        (c := .suspended ⟨extension, env⟩) envIn
      refine ⟨pushed, allIn_cons sizeIn (allIn_cons sizeIn1 (allIn_nil D)), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, renameValue, image, image1]
    | prototype spec target =>
      have pushed := (hr.push (c := .suspended ⟨spec, env⟩) envIn).push
        (c := .suspended ⟨target, env⟩) envIn
      refine ⟨pushed, allIn_cons sizeIn (allIn_cons sizeIn1 (allIn_nil D)), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, renameValue, image, image1]
    | reflect body => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | metadata body => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | project body => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | record fields =>
      obtain ⟨hr', same, inside⟩ := allocateFields_agree hr envIn fields
      refine ⟨hr', inside, ?_, stackIn, rfl⟩
      simp only [stepRaw, renameControl, renameValue, same]
    | get target name => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | extend inherited fields => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | ifZero value zero successorBody => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | binary primitive left right => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | inject tag payload =>
      have pushed := hr.push (c := .suspended ⟨payload, env⟩) envIn
      refine ⟨pushed, allIn_cons sizeIn (allIn_nil D), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, renameValue, image]
    | case scrutinee arms => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | ifBool condition whenTrue whenFalse => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | done value => exact ⟨hr, envIn, rfl, stackIn, rfl⟩
    | split target names function => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | perform plan =>
      simp only [stepRaw, renameControl, forcingShared_rename]
      cases shared : forcingShared stack with
      | true => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
      | false =>
        have pushed := hr.push (c := .suspended ⟨plan, env⟩) envIn
        refine ⟨pushed, allIn_cons sizeIn (allIn_nil D), ?_, stackIn, rfl⟩
        simp [renameControl, image]
  | returned v =>
    have valueIn : AllIn D (valueAddresses v) := controlIn
    cases stack with
    | nil => exact ⟨hr, valueIn, rfl, stackIn, rfl⟩
    | cons frame rest =>
      have ⟨frameIn, restIn⟩ := List.forall_mem_cons.mp stackIn
      cases frame with
      | update a =>
        have inA : D a := frameIn a (List.mem_singleton_self a)
        have notU : ¬ U a := avoids a (by simp [readsAt])
        simp only [stepRaw, renameControl, List.map_cons, renameFrame]
        rw [hr.lookup inA notU]
        cases found : heap[a]? with
        | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
        | some cell =>
          have cellIn := hr.cellIn inA notU found
          cases cell with
          | suspended o => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | cached o w => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | evaluating o =>
            exact ⟨hr.set inA notU (bound_of_some found) (c := .cached o v) (allIn_append cellIn valueIn),
              valueIn, rfl, restIn, rfl⟩
      | reflect =>
        cases v with
        | prototype spec target =>
          exact ⟨hr, allIn_cons (valueIn spec (by simp [valueAddresses])) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | metadata =>
        cases v with
        | specification descriptor extension =>
          exact ⟨hr, allIn_cons (valueIn descriptor (by simp [valueAddresses])) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | project =>
        cases v with
        | prototype spec target =>
          exact ⟨hr, allIn_cons (valueIn target (by simp [valueAddresses])) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | argument argument environment =>
        cases v with
        | specification descriptor extension =>
          exact ⟨hr, allIn_cons (valueIn extension (by simp [valueAddresses])) (allIn_nil D), rfl, stackIn, rfl⟩
        | closure body captured =>
          have environmentIn : AllIn D environment := frameIn
          have capturedIn : AllIn D captured := valueIn
          have pushed := hr.push (c := .suspended ⟨argument, environment⟩) environmentIn
          refine ⟨pushed, allIn_cons sizeIn capturedIn, ?_, restIn, rfl⟩
          simp [stepRaw, renameControl, renameValue, renameFrame, image]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | field name =>
        cases v with
        | record fields =>
          simp only [stepRaw, renameControl, renameValue, List.map_cons, renameFrame, List.find?_map,
            Function.comp_def]
          cases found : fields.find? (fun field => field.1 == name) with
          | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | some entry =>
            have member := List.mem_of_find?_eq_some found
            exact ⟨hr, allIn_cons (valueIn entry.2 (List.mem_map_of_mem member)) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | extend fields environment =>
        cases v with
        | record inherited =>
          have environmentIn : AllIn D environment := frameIn
          obtain ⟨hr', same, inside⟩ := allocateFields_agree hr environmentIn fields
          refine ⟨hr', ?_, ?_, restIn, rfl⟩
          · have retainedIn : AllIn D ((inherited.filter
                (fun prior => !(fields.any fun field => field.1 == prior.1))).map Prod.snd) := by
              intro x member
              obtain ⟨entry, kept, eq⟩ := List.mem_map.mp member
              rw [← eq]; exact valueIn _ (List.mem_map_of_mem (List.mem_filter.mp kept).1)
            have := allIn_append inside retainedIn
            rw [← List.map_append] at this
            exact this
          · simp only [stepRaw, renameControl, renameValue, List.map_cons, renameFrame, same,
              List.filter_map, Function.comp_def, List.map_append]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | condition zero successorBody environment =>
        cases v with
        | natural n =>
          cases n with
          | zero => exact ⟨hr, frameIn, rfl, restIn, rfl⟩
          | succ n =>
            have environmentIn : AllIn D environment := frameIn
            have pushed := hr.push (c := .cached ⟨.nat n, []⟩ (.natural n)) (allIn_nil D)
            refine ⟨pushed, allIn_cons sizeIn environmentIn, ?_, restIn, rfl⟩
            simp [stepRaw, renameControl, renameFrame, renameValue, image]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | binaryLeft primitive right environment =>
        exact ⟨hr, frameIn, rfl, frames_cons valueIn restIn, rfl⟩
      | binaryRight primitive left =>
        simp only [stepRaw, renameControl, List.map_cons, renameFrame, valueTerm_rename]
        cases computed : (valueTerm left).bind (fun l => (valueTerm v).bind (primitiveResult primitive l)) with
        | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
        | some result =>
          dsimp only
          cases scalar : scalarValue result with
          | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | some next =>
            have ⟨renamed, empty⟩ := scalarValue_rename (f := f) scalar
            refine ⟨hr, ?_, ?_, restIn, rfl⟩
            · show AllIn D (valueAddresses next); rw [empty]; exact allIn_nil D
            · simp [renameControl, renamed]
      | case arms environment =>
        cases v with
        | variant tag payload =>
          simp only [stepRaw, renameControl, renameValue, List.map_cons, renameFrame]
          cases found : arms.find? (fun arm => arm.1 == tag) with
          | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | some arm =>
            have environmentIn : AllIn D environment := frameIn
            have pushed := hr.push (c := .suspended ⟨.bound 0, [payload]⟩) valueIn
            refine ⟨pushed, allIn_cons sizeIn environmentIn, ?_, restIn, rfl⟩
            simp [renameControl, image]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | ifBool whenTrue whenFalse environment =>
        cases v with
        | boolean b => cases b <;> exact ⟨hr, frameIn, rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | split names function environment =>
        cases v with
        | record fields =>
          simp only [stepRaw, renameControl, renameValue, List.map_cons, renameFrame]
          rw [splitValues_map f fields names]
          cases found : splitValues fields names with
          | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | some addresses =>
            have environmentIn : AllIn D environment := frameIn
            have addressesIn : AllIn D addresses := by
              intro address ha
              obtain ⟨field, hf, he⟩ := Obend.Core.Invariant.splitValues_mem found address ha
              exact he ▸ valueIn field.2 (List.mem_map_of_mem hf)
            obtain ⟨hr', same, inside⟩ := allocateFields_agree hr addressesIn (splitCells addresses.length)
            have lengthEq : (addresses.map f).length = addresses.length := List.length_map ..
            simp only [Option.map_some]
            rw [lengthEq]
            refine ⟨hr', environmentIn, ?_, ?_, ?_⟩
            · rfl
            · intro frame member
              rcases List.mem_append.mp member with m | m
              · simp only [splitFrames, List.mem_map] at m
                obtain ⟨address, ha, rfl⟩ := m
                exact allIn_cons (inside address (List.mem_map.mpr ha)) (allIn_nil D)
              · exact restIn frame m
            · simp only [same, splitFrames, List.map_append, List.map_map]
              rfl
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩

/-! ## Runs -/

/-- `n` raw transitions (no capacity, no tick budget). -/
@[expose] public def exec : Nat → State → State
  | 0, state => state
  | n + 1, state => exec n (stepRaw state)

public theorem exec_add (m n : Nat) (state : State) : exec (m + n) state = exec n (exec m state) := by
  induction m generalizing state with
  | zero => simp [exec]
  | succ m ih => rw [Nat.succ_add]; simp only [exec]; exact ih _

public theorem exec_succ (n : Nat) (state : State) : exec (n + 1) state = stepRaw (exec n state) := by
  rw [exec_add n 1]; rfl

public theorem exec_one (state : State) : exec 1 state = stepRaw state := rfl

/-- **A run that reads no `U` cell is mirrored step for step.** -/
public theorem agree_exec {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t)
    (n : Nat) (avoids : ∀ j, j < n → Avoids U (exec j s)) : StateAgree f D U (exec n s) (exec n t) := by
  induction n with
  | zero => exact related
  | succ n ih =>
    rw [exec_succ, exec_succ]
    exact agree_stepRaw (ih (fun j lt => avoids j (by omega))) (avoids n (by omega))

public theorem StateAgree.active_eq {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t) :
    active t.control = active s.control := by
  rw [related.control, active_rename]

public theorem StateAgree.stack_length {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t) :
    t.stack.length = s.stack.length := by
  rw [related.stack, List.length_map]

public theorem StateAgree.readsAt_eq {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t) :
    readsAt t = (readsAt s).map f := by
  obtain ⟨_, _, controlEq, _, stackEq⟩ := related
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨heap', control', stack'⟩ := t
  simp only at controlEq stackEq
  subst controlEq stackEq
  cases control <;> simp [readsAt, renameControl]
  rename_i v
  cases stack with
  | nil => simp
  | cons frame rest => cases frame <;> simp [renameFrame]


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Run.lean` -/


public theorem stepRaw_stack_shape (s : State) :
    (stepRaw s).stack = s.stack ∨ (∃ fr, (stepRaw s).stack = fr :: s.stack) ∨
    (∃ fr rest, s.stack = fr :: rest ∧ (∀ a, fr ≠ .update a) ∧ ∃ fr', (stepRaw s).stack = fr' :: rest) ∨
    (∃ fr rest, s.stack = fr :: rest ∧ (stepRaw s).stack = rest) ∨
    (∃ fr rest frs, s.stack = fr :: rest ∧ (∀ a, fr ≠ .update a) ∧ (∀ f ∈ frs, ∀ a, f ≠ .update a) ∧
      (stepRaw s).stack = frs ++ rest ∧ ∃ v, s.control = .returned v) := by
  obtain ⟨heap, control, stack⟩ := s
  cases control with
  | complete _ | refused _ | blackhole _ | yielded _ => left; rfl
  | enter a =>
    simp only [stepRaw]
    split <;> simp
  | evaluate term env =>
    cases term <;> simp only [stepRaw] <;> (try split) <;> (try split) <;> simp
  | returned v =>
    cases stack with
    | nil => left; rfl
    | cons frame rest =>
      cases frame
      case split names function environment =>
        simp only [stepRaw]
        split
        · split
          · rename_i addresses _
            right; right; right; right
            refine ⟨_, rest, _, rfl, by simp, ?_, rfl, _, rfl⟩
            intro f mem a
            simp only [splitFrames, List.mem_map] at mem
            obtain ⟨_, _, rfl⟩ := mem
            simp
          · simp
        · simp
      all_goals simp only [stepRaw] <;> (try split) <;> (try split) <;> (try split) <;> simp

public def withStack (s : State) (R : List Frame) : State := ⟨s.heap, s.control, s.stack ++ R⟩

public def FrameSafe (s : State) : Prop :=
  (∀ v, s.control = .returned v → s.stack ≠ []) ∧
  (∀ p e, s.control = .evaluate (.perform p) e → forcingShared s.stack = true)

theorem forcingShared_append_true {S : List Frame} (R : List Frame) (h : forcingShared S = true) :
    forcingShared (S ++ R) = true := by
  simp only [forcingShared, List.any_append, Bool.or_eq_true] at h ⊢
  exact Or.inl h

public theorem stepRaw_withStack (s : State) (R : List Frame) (safe : FrameSafe s) :
    stepRaw (withStack s R) = withStack (stepRaw s) R := by
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨safeR, safeP⟩ := safe
  simp only at safeR safeP
  cases control with
  | complete _ | refused _ | blackhole _ | yielded _ => rfl
  | enter a =>
    simp only [stepRaw, withStack]
    split <;> simp
  | evaluate term env =>
    cases term with
    | perform plan =>
      have shared := safeP plan env rfl
      simp [stepRaw, withStack, shared, forcingShared_append_true R shared]
    | _ => simp only [stepRaw, withStack] <;> (try split) <;> simp
  | returned v =>
    cases stack with
    | nil => exact absurd rfl (safeR v rfl)
    | cons frame rest =>
      cases frame <;> simp only [stepRaw, withStack, List.cons_append] <;> (try split) <;> (try split) <;>
        (try split) <;> simp



/-- Every address a heap's cells hold is allocated. -/
public def HeapValid (heap : Array Cell) : Prop :=
  ∀ (a : Nat) (c : Cell), heap[a]? = some c → AllIn (· < heap.size) (cellAddresses c)

/-- Every address a state holds is allocated (`LexicalInvariant` without the scoping). -/
public structure AddrValid (s : State) : Prop where
  heap : HeapValid s.heap
  control : AllIn (· < s.heap.size) (controlAddresses s.control)
  stack : ∀ frame ∈ s.stack, AllIn (· < s.heap.size) (frameAddresses frame)

theorem allIn_mono {P Q : Nat → Prop} {l : List Nat} (h : AllIn P l) (pq : ∀ a, P a → Q a) : AllIn Q l :=
  fun a member => pq a (h a member)

public theorem allBelow_mono {n m : Nat} {l : List Nat} (h : AllIn (· < n) l) (le : n ≤ m) : AllIn (· < m) l :=
  allIn_mono h (fun _ lt => Nat.lt_of_lt_of_le lt le)

@[simp] public theorem allIn_nil_iff {P : Nat → Prop} : AllIn P [] ↔ True := ⟨fun _ => trivial, fun _ _ m => by cases m⟩

@[simp] public theorem allIn_cons_iff {P : Nat → Prop} {a : Nat} {l : List Nat} : AllIn P (a :: l) ↔ P a ∧ AllIn P l :=
  ⟨fun h => ⟨h a (List.mem_cons_self ..), fun x m => h x (List.mem_cons_of_mem _ m)⟩,
   fun h => allIn_cons h.1 h.2⟩

public theorem frames_mono {stack : List Frame} {n m : Nat} (h : ∀ frame ∈ stack, AllIn (· < n) (frameAddresses frame))
    (le : n ≤ m) : ∀ frame ∈ stack, AllIn (· < m) (frameAddresses frame) :=
  fun frame member => allBelow_mono (h frame member) le

public theorem heapValid_push {heap : Array Cell} {c : Cell} (valid : HeapValid heap)
    (cIn : AllIn (· < heap.size + 1) (cellAddresses c)) : HeapValid (heap.push c) := by
  intro a c' found
  show AllIn (· < (heap.push c).size) _
  simp only [Array.size_push]
  by_cases eq : a = heap.size
  · subst eq; simp at found; subst found; exact cIn
  · have : heap[a]? = some c' := by simpa [Array.getElem?_push, eq] using found
    exact allBelow_mono (valid a c' this) (Nat.le_succ _)

public theorem heapValid_set {heap : Array Cell} {a : Nat} {c : Cell} (valid : HeapValid heap)
    (cIn : AllIn (· < heap.size) (cellAddresses c)) : HeapValid (heap.set! a c) := by
  intro b c' found
  show AllIn (· < (heap.set! a c).size) _
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  by_cases eq : a = b
  · subst eq
    by_cases bound : a < heap.size
    · simp [bound] at found; subst found; exact cIn
    · simp [bound] at found
  · have : heap[b]? = some c' := by simpa [eq] using found
    exact valid b c' this

theorem allocateFields_valid' {heap : Array Cell} {environment : List Nat} (valid : HeapValid heap)
    (envIn : AllIn (· < heap.size) environment) (fields : List (String × Term)) :
    HeapValid (allocateFields heap environment fields).1 ∧
      heap.size ≤ (allocateFields heap environment fields).1.size ∧
      AllIn (· < (allocateFields heap environment fields).1.size)
        ((allocateFields heap environment fields).2.map Prod.snd) := by
  suffices ∀ (h : Array Cell) (acc : List (String × Nat)), HeapValid h → heap.size ≤ h.size →
      AllIn (· < h.size) (acc.map Prod.snd) →
      HeapValid (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).1 ∧
      h.size ≤ (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).1.size ∧
      AllIn (· < (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).1.size)
        ((fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).2.map Prod.snd) by
    obtain ⟨v, le, inside⟩ := this heap [] valid (Nat.le_refl _) (allIn_nil _)
    refine ⟨v, le, ?_⟩
    intro x member
    simp only [allocateFields, List.map_reverse, List.mem_reverse] at member ⊢
    exact inside x member
  induction fields with
  | nil => intro h acc v le accIn; exact ⟨v, Nat.le_refl _, accIn⟩
  | cons field rest ih =>
    intro h acc v le accIn
    simp only [List.foldl_cons]
    have v' : HeapValid (h.push (.suspended ⟨field.2, environment⟩)) :=
      heapValid_push v (allBelow_mono envIn (by omega))
    have accIn' : AllIn (· < (h.push (.suspended ⟨field.2, environment⟩)).size)
        (((field.1, h.size) :: acc).map Prod.snd) := by
      intro x member
      simp only [List.map_cons, List.mem_cons, Array.size_push] at member ⊢
      rcases member with rfl | member
      · omega
      · exact Nat.lt_succ_of_lt (accIn x member)
    obtain ⟨a, b, c⟩ := ih _ _ v' (by simp; omega) accIn'
    exact ⟨a, by simp at b ⊢; omega, c⟩

public theorem addrValid_stepRaw {s : State} (valid : AddrValid s) : AddrValid (stepRaw s) := by
  obtain ⟨hv, cv, sv⟩ := valid
  obtain ⟨heap, control, stack⟩ := s
  simp only at hv cv sv
  have sizeSet : ∀ (a : Nat) (c : Cell), (heap.set! a c).size = heap.size := by intro a c; simp
  cases control with
  | complete v => exact ⟨hv, cv, sv⟩
  | refused r => exact ⟨hv, cv, sv⟩
  | blackhole a => exact ⟨hv, cv, sv⟩
  | yielded p => exact ⟨hv, cv, sv⟩
  | enter a =>
    simp only [stepRaw]
    cases found : heap[a]? with
    | none => exact ⟨hv, by simp [controlAddresses], sv⟩
    | some cell =>
      have cellIn := hv a cell found
      cases cell with
      | evaluating o => exact ⟨hv, cv, sv⟩
      | cached o v =>
        exact ⟨hv, fun x member => cellIn x (List.mem_append_right _ member), sv⟩
      | suspended o =>
        refine ⟨heapValid_set hv (c := .evaluating o) cellIn, ?_, ?_⟩
        · show AllIn _ o.environment; rw [sizeSet]; exact cellIn
        · intro frame member
          show AllIn (· < (heap.set! a (.evaluating o)).size) _
          rw [sizeSet]
          rcases List.mem_cons.mp member with rfl | member
          · exact cv
          · exact sv frame member
  | evaluate term env =>
    have envIn : AllIn (· < heap.size) env := cv
    obend_cases term with []
    case hole n σ => exact ⟨hv, allIn_nil _, sv⟩
    case bound i =>
      simp only [stepRaw]
      cases found : env[i]? with
      | none => exact ⟨hv, by simp [controlAddresses], sv⟩
      | some a => exact ⟨hv, by simpa [controlAddresses] using envIn a (List.mem_of_getElem? found), sv⟩
    case lam body => exact ⟨hv, envIn, sv⟩
    case nat n => exact ⟨hv, by simp [stepRaw, controlAddresses, valueAddresses], by simpa [stepRaw] using sv⟩
    case boolean b => exact ⟨hv, by simp [stepRaw, controlAddresses, valueAddresses], by simpa [stepRaw] using sv⟩
    case label l => exact ⟨hv, by simp [stepRaw, controlAddresses, valueAddresses], by simpa [stepRaw] using sv⟩
    case app fn arg => exact ⟨hv, envIn, frames_cons envIn sv⟩
    case mix lower upper => exact ⟨hv, envIn, sv⟩
    case fix spec inherited =>
      simp only [stepRaw]
      refine ⟨heapValid_push hv ?_, ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      · simp only [cellAddresses, allIn_cons_iff]
        exact ⟨by omega, allBelow_mono envIn (by omega)⟩
      · simp [controlAddresses]
    case specification descriptor extension =>
      simp only [stepRaw]
      refine ⟨heapValid_push (heapValid_push hv (allBelow_mono envIn (by omega)))
        (allBelow_mono envIn (by simp only [Array.size_push]; omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      simp [controlAddresses, valueAddresses] <;> omega
    case prototype spec target =>
      simp only [stepRaw]
      refine ⟨heapValid_push (heapValid_push hv (allBelow_mono envIn (by omega)))
        (allBelow_mono envIn (by simp only [Array.size_push]; omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      simp [controlAddresses, valueAddresses] <;> omega
    case reflect body => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    case metadata body => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    case project body => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    case record fields =>
      simp only [stepRaw]
      obtain ⟨v', le, inside⟩ := allocateFields_valid' hv envIn fields
      exact ⟨v', inside, frames_mono sv le⟩
    case get target name => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    case extend inherited fields => exact ⟨hv, envIn, frames_cons envIn sv⟩
    case ifZero value zero successorBody => exact ⟨hv, envIn, frames_cons envIn sv⟩
    case binary primitive left right => exact ⟨hv, envIn, frames_cons envIn sv⟩
    case inject tag payload =>
      simp only [stepRaw]
      refine ⟨heapValid_push hv (allBelow_mono envIn (by omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      simp [controlAddresses, valueAddresses] <;> omega
    case case scrutinee arms => exact ⟨hv, envIn, frames_cons envIn sv⟩
    case ifBool condition whenTrue whenFalse => exact ⟨hv, envIn, frames_cons envIn sv⟩
    case done value => exact ⟨hv, envIn, sv⟩
    case split target names function => exact ⟨hv, envIn, frames_cons envIn sv⟩
    case perform plan =>
      simp only [stepRaw]
      cases shared : forcingShared stack with
      | true => exact ⟨hv, by simp [controlAddresses], sv⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        refine ⟨heapValid_push hv (allBelow_mono envIn (by omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
        simp [controlAddresses] <;> omega
  | returned v =>
    have valueIn : AllIn (· < heap.size) (valueAddresses v) := cv
    cases stack with
    | nil => exact ⟨hv, valueIn, sv⟩
    | cons frame rest =>
      have ⟨frameIn, restIn⟩ := List.forall_mem_cons.mp sv
      cases frame with
      | update a =>
        simp only [stepRaw]
        cases found : heap[a]? with
        | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
        | some cell =>
          have cellIn := hv a cell found
          cases cell with
          | suspended o => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | cached o w => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | evaluating o =>
            refine ⟨heapValid_set hv (c := .cached o v) (allIn_append cellIn valueIn), ?_, ?_⟩
            · show AllIn (· < (heap.set! a (.cached o v)).size) _; rw [sizeSet]; exact valueIn
            · intro fr member
              show AllIn (· < (heap.set! a (.cached o v)).size) _; rw [sizeSet]; exact restIn fr member
      | reflect =>
        simp only [stepRaw]
        cases v with
        | prototype spec target =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn spec (by simp [valueAddresses]), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | metadata =>
        simp only [stepRaw]
        cases v with
        | specification descriptor extension =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn descriptor (by simp [valueAddresses]), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | project =>
        simp only [stepRaw]
        cases v with
        | prototype spec target =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn target (by simp [valueAddresses]), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | argument argument environment =>
        simp only [stepRaw]
        cases v with
        | specification descriptor extension =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn extension (by simp [valueAddresses]), sv⟩
        | closure body captured =>
          have environmentIn : AllIn (· < heap.size) environment := frameIn
          have capturedIn : AllIn (· < heap.size) captured := valueIn
          simp only [stepRaw]
          refine ⟨heapValid_push hv (allBelow_mono environmentIn (by omega)), ?_, frames_mono restIn (by simp only [Array.size_push]; omega)⟩
          simp only [controlAddresses, allIn_cons_iff, Array.size_push]
          exact ⟨by omega, allBelow_mono capturedIn (by omega)⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | field name =>
        simp only [stepRaw]
        cases v with
        | record fields =>
          simp only [stepRaw]
          cases found : fields.find? (fun field => field.1 == name) with
          | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | some entry =>
            have member := List.mem_of_find?_eq_some found
            exact ⟨hv, by simpa [controlAddresses] using valueIn entry.2 (List.mem_map_of_mem member), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | extend fields environment =>
        simp only [stepRaw]
        cases v with
        | record inherited =>
          have environmentIn : AllIn (· < heap.size) environment := frameIn
          simp only [stepRaw]
          obtain ⟨v', le, inside⟩ := allocateFields_valid' hv environmentIn fields
          refine ⟨v', ?_, frames_mono restIn le⟩
          have retainedIn : AllIn (· < (allocateFields heap environment fields).1.size)
              ((inherited.filter (fun prior => !(fields.any fun field => field.1 == prior.1))).map Prod.snd) := by
            intro x member
            obtain ⟨entry, kept, eq⟩ := List.mem_map.mp member
            rw [← eq]; exact Nat.lt_of_lt_of_le (valueIn _ (List.mem_map_of_mem (List.mem_filter.mp kept).1)) le
          have := allIn_append inside retainedIn
          rw [← List.map_append] at this
          exact this
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | condition zero successorBody environment =>
        simp only [stepRaw]
        cases v with
        | natural n =>
          cases n with
          | zero => exact ⟨hv, frameIn, restIn⟩
          | succ n =>
            have environmentIn : AllIn (· < heap.size) environment := frameIn
            simp only [stepRaw]
            refine ⟨heapValid_push hv (by simp [cellAddresses, valueAddresses]), ?_, frames_mono restIn (by simp only [Array.size_push]; omega)⟩
            simp only [controlAddresses, allIn_cons_iff, Array.size_push]
            exact ⟨by omega, allBelow_mono environmentIn (by omega)⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | binaryLeft primitive right environment =>
        exact ⟨hv, frameIn, frames_cons valueIn restIn⟩
      | binaryRight primitive left =>
        simp only [stepRaw]
        cases computed : (valueTerm left).bind (fun l => (valueTerm v).bind (primitiveResult primitive l)) with
        | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
        | some result =>
          dsimp only
          cases scalar : scalarValue result with
          | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | some next =>
            have ⟨_, empty⟩ := scalarValue_rename (f := id) scalar
            refine ⟨hv, ?_, restIn⟩
            show AllIn _ (valueAddresses next); rw [empty]; exact allIn_nil _
      | case arms environment =>
        simp only [stepRaw]
        cases v with
        | variant tag payload =>
          simp only [stepRaw]
          cases found : arms.find? (fun arm => arm.1 == tag) with
          | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | some arm =>
            have environmentIn : AllIn (· < heap.size) environment := frameIn
            refine ⟨heapValid_push hv (allBelow_mono valueIn (by omega)), ?_, frames_mono restIn (by simp only [Array.size_push]; omega)⟩
            simp only [controlAddresses, allIn_cons_iff, Array.size_push]
            exact ⟨by omega, allBelow_mono environmentIn (by omega)⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | ifBool whenTrue whenFalse environment =>
        simp only [stepRaw]
        cases v with
        | boolean b => cases b <;> exact ⟨hv, frameIn, restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | split names function environment =>
        simp only [stepRaw]
        cases v with
        | record fields =>
          dsimp only
          cases found : splitValues fields names with
          | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | some addresses =>
            dsimp only
            have environmentIn : AllIn (· < heap.size) environment := frameIn
            have addressesIn : AllIn (· < heap.size) addresses := by
              intro x hx
              obtain ⟨field, hf, rfl⟩ := Obend.Core.Invariant.splitValues_mem found x hx
              exact valueIn _ (List.mem_map_of_mem hf)
            obtain ⟨v', le, inside⟩ := allocateFields_valid' hv addressesIn (splitCells addresses.length)
            refine ⟨v', allBelow_mono environmentIn le, ?_⟩
            intro frame member
            rcases List.mem_append.mp member with m | m
            · simp only [splitFrames, List.mem_map] at m
              obtain ⟨a, ha, rfl⟩ := m
              exact allIn_cons (inside a (List.mem_map.mpr ha)) (allIn_nil _)
            · exact frames_mono restIn le frame m
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩



/-- `after` extends `before`: every allocated cell is unchanged. -/
public def PrefixExt (before after : Array Cell) : Prop :=
  before.size ≤ after.size ∧ ∀ b, b < before.size → after[b]? = before[b]?

theorem prefixExt_refl (h : Array Cell) : PrefixExt h h := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem prefixExt_trans {a b c : Array Cell} (ab : PrefixExt a b) (bc : PrefixExt b c) : PrefixExt a c :=
  ⟨Nat.le_trans ab.1 bc.1, fun x lt => by rw [bc.2 x (Nat.lt_of_lt_of_le lt ab.1), ab.2 x lt]⟩

theorem prefixExt_push (h : Array Cell) (c : Cell) : PrefixExt h (h.push c) :=
  ⟨by simp, fun b lt => by simp [Array.getElem?_push, Nat.ne_of_lt lt]⟩

theorem prefixExt_alloc (heap : Array Cell) (environment : Environment) (fields : List (String × Term)) :
    PrefixExt heap (allocateFields heap environment fields).1 := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      PrefixExt pair.1
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 := by
    intro fields
    induction fields with
    | nil => intro pair; exact prefixExt_refl _
    | cons field fields ih =>
      intro pair
      simpa only [List.foldl_cons] using prefixExt_trans (prefixExt_push pair.1 (.suspended ⟨field.2,environment⟩))
        (ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2))
  exact loop fields (heap,[])

/-- A transition leaves the heap, writes the cell it reads, or only allocates. -/
theorem stepRaw_heap_cases (s : State) :
    (stepRaw s).heap = s.heap ∨ (∃ a c, readsAt s = some a ∧ (stepRaw s).heap = s.heap.set! a c) ∨
      PrefixExt s.heap (stepRaw s).heap := by
  obtain ⟨heap, control, stack⟩ := s
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inr (prefixExt_push _ _))
    | exact Or.inr (Or.inr (prefixExt_trans (prefixExt_push _ _) (prefixExt_push _ _)))
    | exact Or.inr (Or.inr (prefixExt_alloc _ _ _))
    | (refine Or.inr (Or.inl ⟨_, _, ?_, rfl⟩); simp_all [readsAt])

/-- **A cell no transition reads is unchanged.** -/
public theorem stepRaw_heap_keep (s : State) {b : Nat} (bound : b < s.heap.size) (unread : readsAt s ≠ some b) :
    (stepRaw s).heap[b]? = s.heap[b]? := by
  rcases stepRaw_heap_cases s with same | ⟨a, c, reads, eq⟩ | ext
  · rw [same]
  · rw [eq]
    have ne : a ≠ b := fun h => unread (h ▸ reads)
    simp [ne]
  · exact ext.2 b bound

public theorem stepRaw_size_mono (s : State) : s.heap.size ≤ (stepRaw s).heap.size := by
  rcases stepRaw_heap_cases s with same | ⟨a, c, _, eq⟩ | ext
  · rw [same]; exact Nat.le_refl _
  · rw [eq]; simp
  · exact ext.1



/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Nest.lean` -/

/-- Away from a returned value, a transition keeps the stack or pushes one frame. -/
theorem stepRaw_stack_grows (s : State) (notReturned : ∀ v, s.control ≠ .returned v) :
    (stepRaw s).stack = s.stack ∨ ∃ fr, (stepRaw s).stack = fr :: s.stack := by
  obtain ⟨heap, control, stack⟩ := s
  cases control with
  | returned v => exact absurd rfl (notReturned v)
  | complete _ | refused _ | blackhole _ | yielded _ => left; rfl
  | enter a => simp only [stepRaw]; split <;> simp
  | evaluate term env => cases term <;> simp only [stepRaw] <;> (try split) <;> simp

/-- Only a returned value consumes the top frame. -/
theorem stepRaw_consumes_returned (s : State) {fr : Frame} {rest : List Frame} (stack : s.stack = fr :: rest)
    (consumed : (stepRaw s).stack = rest ∨ ∃ fr', (stepRaw s).stack = fr' :: rest ∧ fr' ≠ fr) :
    ∃ v, s.control = .returned v := by
  by_cases r : ∃ v, s.control = .returned v
  · exact r
  · have notReturned : ∀ v, s.control ≠ .returned v := fun v h => r ⟨v, h⟩
    rcases stepRaw_stack_grows s notReturned with same | ⟨fr'', push⟩ <;>
      rcases consumed with h | ⟨fr', h, ne⟩
    · rw [same, stack] at h; have := congrArg List.length h; simp at this
    · rw [same, stack] at h; simp at h; exact absurd h.symm ne
    · rw [push, stack] at h; have := congrArg List.length h; simp at this; omega
    · rw [push, stack] at h; simp at h

/-- The update-frame discipline: an update frame below the top stays until popped,
and it is popped only from a returned value. -/
theorem persist_step {s : State} {w : Nat} {R Y : List Frame} (h : s.stack = Y ++ .update w :: R) :
    (∃ Y', (stepRaw s).stack = Y' ++ .update w :: R) ∨
      (Y = [] ∧ (stepRaw s).stack = R ∧ ∃ v, s.control = .returned v) := by
  rcases stepRaw_stack_shape s with same | ⟨fr, push⟩ | ⟨fr, rest, eq, notUpdate, fr', next⟩ | ⟨fr, rest, eq, next⟩ |
      ⟨fr, rest, frs, eq, notUpdate, _, next, _⟩
  · exact Or.inl ⟨Y, by rw [same, h]⟩
  · exact Or.inl ⟨fr :: Y, by rw [push, h]; rfl⟩
  · cases Y with
    | nil =>
      rw [h] at eq; simp at eq; exact absurd eq.1.symm (notUpdate w)
    | cons y ys =>
      rw [h] at eq; simp at eq
      exact Or.inl ⟨fr' :: ys, by rw [next, ← eq.2]; rfl⟩
  · cases Y with
    | nil =>
      rw [h] at eq; simp at eq
      refine Or.inr ⟨rfl, by rw [next, ← eq.2], ?_⟩
      exact stepRaw_consumes_returned s (by rw [h]; rfl) (Or.inl (by rw [next, ← eq.2]))
    | cons y ys =>
      rw [h] at eq; simp at eq
      exact Or.inl ⟨ys, by rw [next, ← eq.2]⟩
  · cases Y with
    | nil =>
      rw [h] at eq; simp at eq; exact absurd eq.1.symm (notUpdate w)
    | cons y ys =>
      rw [h] at eq; simp at eq
      exact Or.inl ⟨frs ++ ys, by rw [next, ← eq.2]; simp⟩


theorem splitFrames_update {cs : List Address} {rest X : List Frame} {a : Nat}
    (h : splitFrames cs ++ rest = .update a :: X) : cs = [] ∧ rest = .update a :: X := by
  cases cs with
  | nil => exact ⟨rfl, by simpa [splitFrames] using h⟩
  | cons c cs => simp [splitFrames] at h

/-- Only entering a cell pushes its update frame. -/
public theorem stepRaw_push_update (s : State) {fr : Frame} (push : (stepRaw s).stack = fr :: s.stack)
    {a : Nat} (isUpdate : fr = .update a) : s.control = .enter a := by
  subst isUpdate
  obtain ⟨heap, control, stack⟩ := s
  have lenFalse : ∀ (l : List Frame) (x : Frame), l ≠ x :: l := fun l x h => by
    have := congrArg List.length h; simp at this
  have lenFalse2 : ∀ (l : List Frame) (x y : Frame), l ≠ x :: y :: l := fun l x y h => by
    have := congrArg List.length h; simp at this; omega
  cases control with
  | enter b =>
    simp only [stepRaw] at push
    split at push <;> simp at push
    all_goals first | (subst push; rfl) | exact absurd push (lenFalse _ _)
  | complete _ | refused _ | blackhole _ | yielded _ =>
    simp [stepRaw] at push <;> exact absurd push (lenFalse _ _)
  | evaluate term env =>
    cases term <;> simp only [stepRaw] at push <;> (try split at push) <;> simp at push <;>
      exact absurd push (lenFalse _ _)
  | returned v =>
    cases stack with
    | nil => simp [stepRaw] at push
    | cons frame rest =>
      cases frame <;> simp only [stepRaw] at push <;> (try split at push) <;> (try split at push) <;>
        (try split at push) <;> simp at push <;>
        first | exact absurd push (lenFalse2 _ _ _) | exact absurd push.2 (lenFalse2 _ _ _) | exact absurd (splitFrames_update push).2 (lenFalse2 _ _ _) | skip

/-- A transition never writes an update frame over another top frame. -/
public theorem stepRaw_top_update (s : State) {fr : Frame} {rest : List Frame} (stack : s.stack = fr :: rest)
    {a : Nat} (next : (stepRaw s).stack = .update a :: rest) : fr = .update a := by
  by_cases r : ∃ v, s.control = .returned v
  · obtain ⟨v, hv⟩ := r
    obtain ⟨heap, control, stack'⟩ := s
    simp only at stack hv; subst stack hv
    cases fr <;> simp only [stepRaw] at next <;> (try split at next) <;> (try split at next) <;>
      (try split at next) <;> simp at next <;>
      first | rfl | (have := congrArg List.length (splitFrames_update next).2; simp at this; done) | (have := congrArg List.length next; simp at this) | skip
  · have notReturned : ∀ v, s.control ≠ .returned v := fun v h => r ⟨v, h⟩
    rcases stepRaw_stack_grows s notReturned with same | ⟨fr'', push⟩
    · rw [same, stack] at next; simp at next; exact next
    · rw [push, stack] at next; have := congrArg List.length next; simp at this

theorem exec_zero (s : State) : exec 0 s = s := rfl

public theorem stepRaw_enter_evaluating {s : State} {b : Nat} {o : Closure} (ctl : s.control = .enter b)
    (ev : s.heap[b]? = some (.evaluating o)) : (stepRaw s).control = .blackhole b := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl ev; subst ctl
  simp [stepRaw, ev]

theorem stepRaw_pop_update {s : State} {w : Nat} {o : Closure} {v : RuntimeValue} {R : List Frame}
    (ctl : s.control = .returned v) (st : s.stack = .update w :: R) (ev : s.heap[w]? = some (.evaluating o)) :
    stepRaw s = ⟨s.heap.set! w (.cached o v), .returned v, R⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl st ev; subst ctl st
  simp [stepRaw, ev]

theorem stepRaw_enter_suspended {s : State} {b : Nat} {o : Closure} (ctl : s.control = .enter b)
    (su : s.heap[b]? = some (.suspended o)) :
    stepRaw s = ⟨s.heap.set! b (.evaluating o), .evaluate o.term o.environment, .update b :: s.stack⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl su; subst ctl
  simp [stepRaw, su]

public theorem exists_first_fail {P : Nat → Prop} (h : ∃ m, ¬ P m) : ∃ m, ¬ P m ∧ ∀ m', m' < m → P m' := by
  classical
  obtain ⟨m, hm⟩ := h
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases all : ∀ m', m' < m → P m'
    · exact ⟨m, hm, all⟩
    · have : ∃ m', m' < m ∧ ¬ P m' := by
        apply Classical.byContradiction; intro hc; apply all; intro m' lt
        apply Classical.byContradiction; intro hp; exact hc ⟨m', lt, hp⟩
      obtain ⟨m', lt, hp⟩ := this
      exact ih m' lt hp

/-- **An entered suspended cell's evaluation.** Its update frame stays on the stack, with
no other update frame for it above, and the cell stays evaluating, until a returned value
pops the frame and caches the cell. -/
public theorem nested_pop {σ : State} {w : Nat} {o : Closure} {R : List Frame} {k : Nat}
    (enter : σ.control = .enter w) (stack : σ.stack = R) (susp : σ.heap[w]? = some (.suspended o))
    (pos : 1 ≤ k) (alive : ∀ j, j < k → active (exec j σ).control = true)
    (gone : ∀ Y, (exec k σ).stack ≠ Y ++ .update w :: R) :
    ∃ p v, 1 ≤ p ∧ p < k ∧
      (∀ j, 1 ≤ j → j ≤ p → (∃ Y, (exec j σ).stack = Y ++ .update w :: R ∧ ∀ fr ∈ Y, fr ≠ .update w) ∧
        (exec j σ).heap[w]? = some (.evaluating o)) ∧
      (exec p σ).stack = .update w :: R ∧ (exec p σ).control = .returned v ∧
      exec (p+1) σ = ⟨(exec p σ).heap.set! w (.cached o v), .returned v, R⟩ := by
  classical
  have wBound : w < σ.heap.size := bound_of_some susp
  have one : exec 1 σ = ⟨σ.heap.set! w (.evaluating o), .evaluate o.term o.environment, .update w :: R⟩ := by
    rw [exec_one, stepRaw_enter_suspended enter susp, stack]
  let P : Nat → Prop := fun m => ∃ Y, (exec (m+1) σ).stack = Y ++ .update w :: R
  have exists_fail : ∃ m, ¬ P m := ⟨k - 1, fun ⟨Y, h⟩ => gone Y (by rw [show k = k - 1 + 1 by omega]; exact h)⟩
  obtain ⟨p, pFail, pMin⟩ := exists_first_fail exists_fail
  have pPos : 1 ≤ p := by
    by_cases zero : p = 0
    · exfalso; apply pFail; rw [zero]; exact ⟨[], by rw [one]; rfl⟩
    · omega
  have pLt : p < k := by
    apply Classical.byContradiction; intro ge
    obtain ⟨Y, h⟩ := pMin (k - 1) (by omega)
    exact gone Y (by rw [show k = k - 1 + 1 by omega]; exact h)
  -- the invariant from 1 to p
  have inv : ∀ j, 1 ≤ j → j ≤ p →
      (∃ Y, (exec j σ).stack = Y ++ .update w :: R ∧ ∀ fr ∈ Y, fr ≠ .update w) ∧
        (exec j σ).heap[w]? = some (.evaluating o) := by
    intro j hj hjp
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases jzero : j = 0
      · subst jzero
        rw [one]
        refine ⟨⟨[], rfl, fun _ m => by cases m⟩, ?_⟩
        simp [wBound]
      · obtain ⟨⟨Y, hY, noW⟩, evalW⟩ := ih (by omega) (by omega)
        obtain ⟨Y', hY'⟩ := pMin j (by omega)
        have hY'' : (exec (j+1) σ).stack = Y' ++ .update w :: R := hY'
        rw [exec_succ] at hY''
        -- no read of w at step j
        have noRead : readsAt (exec j σ) ≠ some w := by
          intro reads
          cases ctl : (exec j σ).control with
          | enter b =>
            have : b = w := by simp [readsAt, ctl] at reads; exact reads
            subst this
            have blk : (stepRaw (exec j σ)).control = .blackhole b := stepRaw_enter_evaluating ctl evalW
            have := alive (j + 1) (by omega)
            rw [exec_succ, blk] at this; simp [active] at this
          | returned v =>
            have top : ∃ rest, (exec j σ).stack = .update w :: rest := by
              cases st : (exec j σ).stack with
              | nil => simp [readsAt, ctl, st] at reads
              | cons fr rest =>
                cases fr <;> simp [readsAt, ctl, st] at reads
                exact ⟨rest, by rw [reads]⟩
            obtain ⟨rest, top⟩ := top
            have yNil : Y = [] := by
              cases Y with
              | nil => rfl
              | cons y ys =>
                rw [hY] at top; simp at top
                exact absurd top.1 (noW y (List.mem_cons_self ..))
            subst yNil
            simp at hY
            have popped : (stepRaw (exec j σ)).stack = R := by
              rw [stepRaw_pop_update ctl hY evalW]
            rw [popped] at hY''
            have := congrArg List.length hY''; simp at this; omega
          | _ => simp [readsAt, ctl] at reads
        have keepW : (stepRaw (exec j σ)).heap[w]? = (exec j σ).heap[w]? :=
          stepRaw_heap_keep _ (bound_of_some evalW) noRead
        refine ⟨⟨Y', by rw [exec_succ]; exact hY'', ?_⟩, by rw [exec_succ, keepW]; exact evalW⟩
        -- no update w in Y'
        rcases stepRaw_stack_shape (exec j σ) with same | ⟨fr, push⟩ | ⟨fr, rest, eq, notUpd, fr', next⟩ |
            ⟨fr, rest, eq, next⟩ | ⟨fr, rest, frs, eq, notUpd, frsNo, next, _⟩
        · rw [same, hY] at hY''
          have := List.append_cancel_right hY''
          subst this; exact noW
        · rw [push, hY] at hY''
          have := List.append_cancel_right (show (fr :: Y) ++ Frame.update w :: R = Y' ++ Frame.update w :: R by
            simpa using hY'')
          subst this
          intro f mem
          rcases List.mem_cons.mp mem with rfl | mem
          · intro isW
            have := stepRaw_push_update _ push isW
            exact noRead (by simp [readsAt, this])
          · exact noW f mem
        · cases Y with
          | nil => rw [hY] at eq; simp at eq; exact absurd eq.1.symm (notUpd w)
          | cons y ys =>
            rw [hY] at eq; simp at eq
            obtain ⟨rfl, rfl⟩ := eq
            rw [next] at hY''
            have := List.append_cancel_right (show (fr' :: ys) ++ Frame.update w :: R = Y' ++ Frame.update w :: R by
              simpa using hY'')
            subst this
            intro f mem
            rcases List.mem_cons.mp mem with rfl | mem
            · intro isW
              have := stepRaw_top_update (exec j σ) hY (by rw [next, isW]; rfl)
              exact noW _ (List.mem_cons_self ..) this
            · exact noW f (List.mem_cons_of_mem _ mem)
        · cases Y with
          | nil =>
            rw [hY] at eq; simp at eq
            rw [next, ← eq.2] at hY''
            have := congrArg List.length hY''; simp at this; omega
          | cons y ys =>
            rw [hY] at eq; simp at eq
            rw [next, ← eq.2] at hY''
            have := List.append_cancel_right hY''
            subst this
            exact fun f mem => noW f (List.mem_cons_of_mem _ mem)
        · cases Y with
          | nil => rw [hY] at eq; simp at eq; exact absurd eq.1.symm (notUpd w)
          | cons y ys =>
            rw [hY] at eq; simp at eq
            rw [next, ← eq.2] at hY''
            have := List.append_cancel_right (show (frs ++ ys) ++ Frame.update w :: R = Y' ++ Frame.update w :: R by
              simpa using hY'')
            subst this
            intro f mem
            rcases List.mem_append.mp mem with m | m
            · intro isW; exact frsNo f m w isW
            · exact noW f (List.mem_cons_of_mem _ m)
  obtain ⟨⟨Yp, hYp, noWp⟩, evalp⟩ := inv p pPos (Nat.le_refl _)
  rcases persist_step hYp with ⟨Y', h⟩ | ⟨rfl, popped, v, ctl⟩
  · exact absurd ⟨Y', by rw [exec_succ]; exact h⟩ pFail
  · refine ⟨p, v, pPos, pLt, inv, by simpa using hYp, ctl, ?_⟩
    rw [exec_succ]
    exact stepRaw_pop_update ctl (by simpa using hYp) evalp

/-! ## Halting runs and closed demands -/

/-- The run from `s` is active for its first `n` states and stops at the `n`-th. -/
@[expose] public def Halts (s : State) (n : Nat) : Prop :=
  (∀ j, j < n → active (exec j s).control = true) ∧ active (exec n s).control = false

public theorem halts_unique {s : State} {n m : Nat} (one : Halts s n) (two : Halts s m) : n = m := by
  apply Classical.byContradiction; intro ne
  rcases Nat.lt_or_gt_of_ne ne with lt | lt
  · have := two.1 n lt; rw [one.2] at this; cases this
  · have := one.1 m lt; rw [two.2] at this; cases this

/-- The closed demand of `w` on `P`: enter it with an empty stack. -/
public def demandStart (P : Array Cell) (w : Nat) : State := ⟨P, .enter w, []⟩

/-- The closed demand of `w` on `P` finishes in `n` transitions with `v`, leaving `Pf`. -/
public structure Demand (P : Array Cell) (w n : Nat) (Pf : Array Cell) (v : RuntimeValue) : Prop where
  halts : Halts (demandStart P w) n
  final : exec n (demandStart P w) = ⟨Pf, .complete v, []⟩

theorem withStack_nil (s : State) : withStack s [] = s := by
  obtain ⟨h, c, st⟩ := s; simp [withStack]

theorem frame_run {s : State} {R : List Frame} {m : Nat} (safe : ∀ j, j < m → FrameSafe (exec j s)) :
    ∀ j, j ≤ m → exec j (withStack s R) = withStack (exec j s) R := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih => rw [exec_succ, exec_succ, ih (by omega), stepRaw_withStack _ _ (safe j (by omega))]

theorem frameSafe_of_update {s : State} {w : Nat} {Y : List Frame} (h : s.stack = Y ++ [.update w]) :
    FrameSafe s := by
  refine ⟨fun _ _ => by rw [h]; simp, fun _ _ _ => ?_⟩
  rw [h]; simp [forcingShared]

theorem frameSafe_enter {s : State} {w : Nat} (h : s.control = .enter w) : FrameSafe s :=
  ⟨fun _ hv => (by rw [h] at hv; cases hv), fun _ _ hp => (by rw [h] at hp; cases hp)⟩

theorem withStack_inj {s : State} {h : Array Cell} {c : Control} {st R : List Frame}
    (eq : withStack s R = ⟨h, c, st ++ R⟩) : s = ⟨h, c, st⟩ := by
  obtain ⟨h', c', st'⟩ := s
  simp only [withStack, State.mk.injEq] at eq
  obtain ⟨rfl, rfl, e⟩ := eq
  rw [List.append_cancel_right e]

/-- **The nested evaluation is a closed demand.** Until the entered cell's frame pops, the
run is the closed demand of that cell with the outer stack appended, and that demand
finishes. -/
public theorem nested_demand {σ : State} {w : Nat} {o : Closure} {R : List Frame} {k : Nat}
    (enter : σ.control = .enter w) (stack : σ.stack = R) (susp : σ.heap[w]? = some (.suspended o))
    (pos : 1 ≤ k) (alive : ∀ j, j < k → active (exec j σ).control = true)
    (gone : ∀ Y, (exec k σ).stack ≠ Y ++ .update w :: R) :
    ∃ p v, 1 ≤ p ∧ p < k ∧
      (∀ j, 1 ≤ j → j ≤ p → (∃ Y, (exec j σ).stack = Y ++ .update w :: R ∧ ∀ fr ∈ Y, fr ≠ .update w) ∧
        (exec j σ).heap[w]? = some (.evaluating o)) ∧
      (exec p σ).stack = .update w :: R ∧ (exec p σ).control = .returned v ∧
      exec (p+1) σ = ⟨(exec p σ).heap.set! w (.cached o v), .returned v, R⟩ ∧
      (∀ j, j ≤ p + 1 → exec j σ = withStack (exec j (demandStart σ.heap w)) R) ∧
      Demand σ.heap w (p + 2) ((exec p σ).heap.set! w (.cached o v)) v := by
  obtain ⟨p, v, pPos, pLt, inv, stP, ctlP, nextP⟩ := nested_pop enter stack susp pos alive gone
  have start : σ = withStack (demandStart σ.heap w) R := by
    obtain ⟨h, c, st⟩ := σ; simp only at enter stack; subst enter stack; rfl
  have strip : ∀ j, j ≤ p + 1 → exec j σ = withStack (exec j (demandStart σ.heap w)) R := by
    -- frame safety, proved together with the stripping by induction
    intro j hj
    induction j with
    | zero => exact start
    | succ j ih =>
      have eq := ih (by omega)
      have safe : FrameSafe (exec j (demandStart σ.heap w)) := by
        by_cases jz : j = 0
        · subst jz; exact frameSafe_enter (w := w) rfl
        · obtain ⟨⟨Y, hY, _⟩, _⟩ := inv j (by omega) (by omega)
          rw [eq] at hY
          have : (exec j (demandStart σ.heap w)).stack ++ R = (Y ++ [.update w]) ++ R := by
            simpa [withStack] using hY
          exact frameSafe_of_update (List.append_cancel_right this)
      rw [exec_succ, exec_succ, eq, stepRaw_withStack _ _ safe]
  have lastEq : exec (p+1) (demandStart σ.heap w) = ⟨(exec p σ).heap.set! w (.cached o v), .returned v, []⟩ := by
    have := strip (p + 1) (Nat.le_refl _)
    rw [nextP] at this
    exact withStack_inj (st := []) (by rw [← this]; rfl)
  refine ⟨p, v, pPos, pLt, inv, stP, ctlP, nextP, strip, ⟨fun j hj => ?_, ?_⟩, ?_⟩
  · by_cases last : j = p + 1
    · subst last; rw [lastEq]; rfl
    · have := strip j (by omega)
      have ctl := congrArg State.control this
      simp only [withStack] at ctl
      rw [← ctl]; exact alive j (by omega)
  · rw [show p + 2 = (p + 1) + 1 by omega, exec_succ, lastEq]; rfl
  · rw [show p + 2 = (p + 1) + 1 by omega, exec_succ, lastEq]; rfl

/-- **A finished closed demand of a suspended cell**: it takes at least four transitions,
caches the cell with its result, returns that result one transition before it stops, and
runs the same over any stack appended below. -/
public theorem demand_props {P : Array Cell} {w n : Nat} {Pf : Array Cell} {v : RuntimeValue} {o : Closure}
    (d : Demand P w n Pf v) (susp : P[w]? = some (.suspended o)) :
    4 ≤ n ∧ Pf[w]? = some (.cached o v) ∧ exec (n-1) (demandStart P w) = ⟨Pf, .returned v, []⟩ ∧
      (∀ j, 1 ≤ j → j ≤ n - 2 → ∃ Y, (exec j (demandStart P w)).stack = Y ++ [.update w]) ∧
      (∀ (R : List Frame) j, j ≤ n - 1 → exec j ⟨P, .enter w, R⟩ = withStack (exec j (demandStart P w)) R) := by
  have pos : 1 ≤ n := by
    apply Classical.byContradiction; intro h
    have := d.halts.2; rw [show n = 0 by omega] at this; simp [exec, demandStart, active] at this
  have gone : ∀ Y, (exec n (demandStart P w)).stack ≠ Y ++ [.update w] := by
    intro Y h; rw [d.final] at h; have := congrArg List.length h; simp at this
  obtain ⟨p, v', pPos, pLt, inv, stP, ctlP, nextP, strip, d'⟩ :=
    nested_demand (σ := demandStart P w) (R := []) rfl rfl susp pos d.halts.1 gone
  have nEq : n = p + 2 := halts_unique d.halts d'.halts
  subst nEq
  have finEq := d.final.symm.trans d'.final
  simp only [State.mk.injEq, Control.complete.injEq] at finEq
  obtain ⟨heapEq, valEq, -⟩ := finEq
  subst valEq
  have p2 : 2 ≤ p := by
    apply Classical.byContradiction; intro h
    have p1 : p = 1 := by omega
    subst p1
    have := stepRaw_enter_suspended (s := demandStart P w) rfl susp
    rw [← exec_one] at this
    rw [this] at ctlP; cases ctlP
  have wBound : w < (exec p (demandStart P w)).heap.size := bound_of_some (inv p pPos (Nat.le_refl _)).2
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [heapEq]; simp [wBound]
  · rw [show p + 2 - 1 = p + 1 by omega, nextP, heapEq]
  · intro j hj hjp
    obtain ⟨⟨Y, hY, _⟩, _⟩ := inv j hj (by omega)
    exact ⟨Y, hY⟩
  · intro R j hj
    have safe : ∀ i, i < p + 1 → FrameSafe (exec i (demandStart P w)) := by
      intro i hi
      by_cases iz : i = 0
      · subst iz; exact frameSafe_enter (w := w) rfl
      · obtain ⟨⟨Y, hY, _⟩, _⟩ := inv i (by omega) (by omega)
        exact frameSafe_of_update hY
    exact frame_run safe j (by omega)


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Pend.lean` -/

public def everywhere : Nat → Prop := fun _ => True

public theorem allIn_everywhere (l : List Nat) : AllIn everywhere l := fun _ _ => trivial

/-! ## Runs: monotone sizes, kept cells, validity -/

public theorem exec_size_mono (s : State) (n : Nat) : s.heap.size ≤ (exec n s).heap.size := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => rw [exec_succ]; exact Nat.le_trans ih (stepRaw_size_mono _)

public theorem exec_heap_keep (s : State) {a : Nat} (bound : a < s.heap.size) :
    ∀ n, (∀ j, j < n → readsAt (exec j s) ≠ some a) → (exec n s).heap[a]? = s.heap[a]? := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro unread
    rw [exec_succ, stepRaw_heap_keep _ (Nat.lt_of_lt_of_le bound (exec_size_mono s n)) (unread n (by omega)),
      ih (fun j lt => unread j (by omega))]

public theorem exec_preservesCached (s : State) (n : Nat) : PreservesCached s.heap (exec n s).heap := by
  induction n with
  | zero => exact fun _ _ _ h => h
  | succ n ih => rw [exec_succ]; exact fun a o v h => stepRaw_preservesCached _ a o v (ih a o v h)

public theorem addrValid_exec {s : State} (valid : AddrValid s) (n : Nat) : AddrValid (exec n s) := by
  induction n with
  | zero => exact valid
  | succ n ih => rw [exec_succ]; exact addrValid_stepRaw ih

public theorem halts_succ {s : State} {n : Nat} (active : active s.control = true) (h : Halts (stepRaw s) n) :
    Halts s (n + 1) := by
  refine ⟨fun j lt => ?_, ?_⟩
  · cases j with
    | zero => exact active
    | succ j => rw [exec_succ', ]; exact h.1 j (by omega)
  · rw [exec_succ']; exact h.2
where exec_succ' {s : State} {n : Nat} : exec (n + 1) s = exec n (stepRaw s) := rfl

public theorem halts_tail {s : State} {n : Nat} (h : Halts s (n + 1)) : Halts (stepRaw s) n :=
  ⟨fun j lt => h.1 (j + 1) (by omega), h.2⟩

public theorem halts_drop {s : State} {n m : Nat} (h : Halts s (m + n)) : Halts (exec m s) n := by
  refine ⟨fun j lt => ?_, ?_⟩
  · rw [← exec_add]; exact h.1 (m + j) (by omega)
  · rw [← exec_add]; exact h.2

/-- Forced states are bounded by lazy states no earlier. -/
public def Bounded (σ τ : State) (n n' gap : Nat) : Prop :=
  ∀ j', j' ≤ n' → ∃ j, j ≤ n ∧ j' ≤ j ∧ (exec j' τ).heap.size ≤ (exec j σ).heap.size + gap ∧
    (exec j' τ).stack.length ≤ (exec j σ).stack.length

/-- Every forced address up to the heap end is an image. -/
public def Covers (f : Nat → Nat) (H T : Array Cell) : Prop := ∀ b, b < T.size → ∃ a, a < H.size ∧ f a = b

/-! ## Agreement without exception -/

/-- The lazy and forced states agree under `f` with no exception. -/
public structure AgreeRel (f : Nat → Nat) (σ τ : State) : Prop where
  agree : StateAgree f everywhere (fun _ => False) σ τ
  valid : AddrValid σ

theorem agree_sizes {f : Nat → Nat} {σ τ σ' τ' : State}
    (one : StateAgree f everywhere (fun _ => False) σ τ) (two : StateAgree f everywhere (fun _ => False) σ' τ')
    (grow : σ.heap.size ≤ σ'.heap.size) : τ'.heap.size + σ.heap.size = σ'.heap.size + τ.heap.size := by
  have := (one.heap.beyond σ'.heap.size grow).2.2
  rw [two.heap.image_size.1] at this
  omega

theorem agree_covers_step {f : Nat → Nat} {σ τ σ' τ' : State}
    (one : StateAgree f everywhere (fun _ => False) σ τ) (two : StateAgree f everywhere (fun _ => False) σ' τ')
    (grow : σ.heap.size ≤ σ'.heap.size) (cov : Covers f σ.heap τ.heap) : Covers f σ'.heap τ'.heap := by
  intro b lt
  have sizes := agree_sizes one two grow
  by_cases old : b < τ.heap.size
  · obtain ⟨a, aLt, eq⟩ := cov b old
    exact ⟨a, by omega, eq⟩
  · refine ⟨b + σ.heap.size - τ.heap.size, by omega, ?_⟩
    have := (one.heap.beyond (b + σ.heap.size - τ.heap.size) (by omega)).2.2
    omega

/-- **Agreeing runs halt together and keep agreeing.** -/
public theorem agree_transfer {f : Nat → Nat} {σ τ : State} (rel : AgreeRel f σ τ) {n : Nat} (halts : Halts σ n) :
    Halts τ n ∧ AgreeRel f (exec n σ) (exec n τ) ∧
      (∀ j, j ≤ n → (exec j τ).heap.size + σ.heap.size = (exec j σ).heap.size + τ.heap.size ∧
        (exec j τ).stack.length = (exec j σ).stack.length) ∧
      (Covers f σ.heap τ.heap → Covers f (exec n σ).heap (exec n τ).heap) := by
  have all : ∀ j, StateAgree f everywhere (fun _ => False) (exec j σ) (exec j τ) :=
    fun j => agree_exec rel.agree j (fun _ _ _ _ h => h)
  refine ⟨⟨fun j lt => ?_, ?_⟩, ⟨all n, addrValid_exec rel.valid n⟩, fun j _ => ?_, fun cov => ?_⟩
  · rw [(all j).active_eq]; exact halts.1 j lt
  · rw [(all n).active_eq]; exact halts.2
  · exact ⟨agree_sizes rel.agree (all j) (exec_size_mono σ j), (all j).stack_length⟩
  · exact agree_covers_step rel.agree (all n) (exec_size_mono σ n) cov

/-! ## The pending demand -/

/-- The cells a pending demand may read: its own cell and cached cells of its base. -/
public def Footprint (B : Array Cell) (y a : Nat) : Prop := a = y ∨ ∃ o w, B[a]? = some (.cached o w)

/-- The closed demand of `y` on `B` reads, of `B`'s cells, only its footprint. -/
public def PreShallow (B : Array Cell) (y n : Nat) : Prop :=
  ∀ j, j < n → ∀ a, readsAt (exec j (demandStart B y)) = some a → a < B.size → Footprint B y a

/-- A pending closed demand and its result. -/
public structure Pending where
  base : Array Cell
  cell : Nat
  steps : Nat
  final : Array Cell
  value : RuntimeValue
  origin : Closure

public structure Pending.Valid (e : Pending) : Prop where
  demand : Demand e.base e.cell e.steps e.final e.value
  susp : e.base[e.cell]? = some (.suspended e.origin)
  shallow : PreShallow e.base e.cell e.steps
  baseValid : HeapValid e.base

/-- How many cells the pending demand allocates. -/
public def Pending.gap (e : Pending) : Nat := e.final.size - e.base.size

/-- The lazy heap with `e` pending, against the forced heap. -/
public structure PendHeap (e : Pending) (f : Nat → Nat) (Hσ Hτ : Array Cell) : Prop where
  valid : e.Valid
  grows : e.base.size ≤ Hσ.size
  cellKept : Hσ[e.cell]? = some (.suspended e.origin)
  cachedKept : ∀ (a : Nat) (o : Closure) (w : RuntimeValue), e.base[a]? = some (.cached o w) → Hσ[a]? = some (.cached o w)
  mapOld : ∀ a, a < e.base.size → f a = a
  mapNew : ∀ a, e.base.size ≤ a → f a = a + e.gap
  agree : HeapAgree f everywhere (· = e.cell) Hσ Hτ
  block : ∀ a, e.base.size ≤ a → a < e.final.size → Hτ[a]? = e.final[a]?
  cached : Hτ[e.cell]? = e.final[e.cell]?

public structure PendRel (e : Pending) (f : Nat → Nat) (σ τ : State) : Prop where
  heap : PendHeap e f σ.heap τ.heap
  control : τ.control = renameControl f σ.control
  stack : τ.stack = σ.stack.map (renameFrame f)
  valid : AddrValid σ

theorem PendRel.stateAgree {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ) :
    StateAgree f everywhere (· = e.cell) σ τ :=
  ⟨rel.heap.agree, allIn_everywhere _, rel.control, fun _ _ => allIn_everywhere _, rel.stack⟩

public theorem Pending.final_ge {e : Pending} (valid : e.Valid) : e.base.size ≤ e.final.size := by
  have := exec_size_mono (demandStart e.base e.cell) e.steps
  rw [valid.demand.final] at this; exact this

public theorem Pending.cell_lt {e : Pending} (valid : e.Valid) : e.cell < e.base.size := bound_of_some valid.susp

public theorem PendHeap.sizes {e : Pending} {f : Nat → Nat} {Hσ Hτ : Array Cell} (ph : PendHeap e f Hσ Hτ) :
    Hτ.size = Hσ.size + e.gap := by
  have := ph.agree.image_size.1
  rw [ph.mapNew _ ph.grows] at this; omega

/-- The renaming never lands in the pending demand's block. -/
public theorem PendHeap.not_block {e : Pending} {f : Nat → Nat} {Hσ Hτ : Array Cell} (ph : PendHeap e f Hσ Hτ) (a : Nat) :
    f a < e.base.size ∨ e.final.size ≤ f a := by
  have ge := Pending.final_ge ph.valid
  by_cases lt : a < e.base.size
  · left; rw [ph.mapOld a lt]; exact lt
  · right; rw [ph.mapNew a (by omega)]; unfold Pending.gap; omega

theorem PendHeap.f_eq_cell {e : Pending} {f : Nat → Nat} {Hσ Hτ : Array Cell} (ph : PendHeap e f Hσ Hτ) {a : Nat}
    (eq : f a = e.cell) : a = e.cell := by
  have cellLt := Pending.cell_lt ph.valid
  have ge := Pending.final_ge ph.valid
  by_cases lt : a < e.base.size
  · rw [ph.mapOld a lt] at eq; exact eq
  · rw [ph.mapNew a (by omega)] at eq; unfold Pending.gap at eq; omega

/-- **A lazy transition that does not read the pending cell keeps the relation.** -/
public theorem pend_step {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ)
    (unread : readsAt σ ≠ some e.cell) : PendRel e f (stepRaw σ) (stepRaw τ) := by
  have ph := rel.heap
  have next := agree_stepRaw rel.stateAgree (fun a reads isCell => unread (isCell ▸ reads))
  have readsT := rel.stateAgree.readsAt_eq
  have cellLt : e.cell < σ.heap.size := bound_of_some ph.cellKept
  have tSize := ph.sizes
  have ge := Pending.final_ge ph.valid
  have grows := ph.grows
  refine ⟨⟨ph.valid, Nat.le_trans ph.grows (stepRaw_size_mono σ), ?_, ?_, ph.mapOld, ph.mapNew, next.heap, ?_, ?_⟩,
    next.control, next.stack, addrValid_stepRaw rel.valid⟩
  · rw [stepRaw_heap_keep σ cellLt unread]; exact ph.cellKept
  · intro a o w found; exact stepRaw_preservesCached σ a o w (ph.cachedKept a o w found)
  · intro a lo hi
    have tUnread : readsAt τ ≠ some a := by
      rw [readsT]; intro h
      cases r : readsAt σ with
      | none => rw [r] at h; cases h
      | some b =>
        rw [r] at h; simp at h
        rcases ph.not_block b with lt | geq <;> omega
    rw [stepRaw_heap_keep τ (by unfold Pending.gap at tSize; omega) tUnread]; exact ph.block a lo hi
  · have tUnread : readsAt τ ≠ some e.cell := by
      rw [readsT]; intro h
      cases r : readsAt σ with
      | none => rw [r] at h; cases h
      | some b =>
        rw [r] at h; simp at h
        exact unread (by rw [r, ph.f_eq_cell h])
    rw [stepRaw_heap_keep τ (by unfold Pending.gap at tSize; have := Pending.cell_lt ph.valid; omega) tUnread]
    exact ph.cached


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Switch.lean` -/

/-! ## Renamings that agree on the addresses held -/

theorem renameValue_congr {f g : Nat → Nat} {v : RuntimeValue} (same : ∀ x ∈ valueAddresses v, f x = g x) :
    renameValue f v = renameValue g v := by
  cases v with
  | closure body env => simp only [renameValue]; congr 1; exact List.map_congr_left same
  | natural _ => rfl
  | boolean _ => rfl
  | label _ => rfl
  | record fields =>
    simp only [renameValue]; congr 1
    apply List.map_congr_left; intro x m
    exact Prod.ext rfl (same _ (List.mem_map_of_mem (f := Prod.snd) m))
  | specification a b =>
    simp only [renameValue]; rw [same a (by simp [valueAddresses]), same b (by simp [valueAddresses])]
  | prototype a b =>
    simp only [renameValue]; rw [same a (by simp [valueAddresses]), same b (by simp [valueAddresses])]
  | variant l a => simp only [renameValue]; rw [same a (by simp [valueAddresses])]

theorem renameClosure_id {f : Nat → Nat} {c : Closure} (same : ∀ x ∈ c.environment, f x = x) :
    renameClosure f c = c := by
  obtain ⟨t, env⟩ := c
  simp only [renameClosure] at same ⊢
  congr 1
  conv => rhs; rw [← List.map_id env]
  exact List.map_congr_left same

public theorem renameValue_id {f : Nat → Nat} {v : RuntimeValue} (same : ∀ x ∈ valueAddresses v, f x = x) :
    renameValue f v = v := by
  rw [renameValue_congr (g := id) same]; cases v <;> simp [renameValue]

theorem renameCell_congr {f g : Nat → Nat} {c : Cell} (same : ∀ x ∈ cellAddresses c, f x = g x) :
    renameCell f c = renameCell g c := by
  cases c with
  | suspended o => simp only [renameCell, renameClosure]; congr 2; exact List.map_congr_left same
  | evaluating o => simp only [renameCell, renameClosure]; congr 2; exact List.map_congr_left same
  | cached o v =>
    simp only [renameCell, renameClosure, cellAddresses] at same ⊢
    rw [List.map_congr_left (fun x m => same x (List.mem_append_left _ m)),
      renameValue_congr (fun x m => same x (List.mem_append_right _ m))]

public theorem renameCell_id {f : Nat → Nat} {c : Cell} (same : ∀ x ∈ cellAddresses c, f x = x) :
    renameCell f c = c := by
  rw [renameCell_congr (g := id) same]; cases c <;> simp [renameCell, renameClosure, renameValue_id]

public theorem renameFrame_congr {f g : Nat → Nat} {fr : Frame} (same : ∀ x ∈ frameAddresses fr, f x = g x) :
    renameFrame f fr = renameFrame g fr := by
  cases fr <;> simp only [renameFrame, frameAddresses] at same ⊢ <;>
    first
      | rfl
      | (congr 1; exact List.map_congr_left same)
      | (rw [same _ (List.mem_singleton_self _)])
      | (congr 1; exact renameValue_congr same)

public theorem renameControl_congr {f g : Nat → Nat} {c : Control} (same : ∀ x ∈ controlAddresses c, f x = g x) :
    renameControl f c = renameControl g c := by
  cases c <;> simp only [renameControl, controlAddresses] at same ⊢ <;>
    first
      | rfl
      | (congr 1; exact List.map_congr_left same)
      | (rw [same _ (List.mem_singleton_self _)])
      | (congr 1; exact renameValue_congr same)

/-! ## The switch -/

/-- `e` on its base, carried to the lazy heap (its fresh cells after the lazy end). -/
public def liftMap (base lazySize : Nat) : Nat → Nat := fun a => if a < base then a else a + (lazySize - base)

/-- After the switch: the lazy run's copy of `e`'s cells lands on `e`'s block. -/
public def switchMap (e : Pending) (f : Nat → Nat) (lazySize : Nat) : Nat → Nat := fun a =>
  if a < lazySize then f a else if a < lazySize + e.gap then e.base.size + (a - lazySize) else a

theorem stepRaw_enter_cached {s : State} {b : Nat} {o : Closure} {v : RuntimeValue} (ctl : s.control = .enter b)
    (ca : s.heap[b]? = some (.cached o v)) : stepRaw s = ⟨s.heap, .returned v, s.stack⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl ca; subst ctl
  simp [stepRaw, ca]

public theorem state_ext {s : State} : s = ⟨s.heap, s.control, s.stack⟩ := rfl

public theorem heapValid_exec {s : State} (valid : AddrValid s) (n : Nat) : HeapValid (exec n s).heap :=
  (addrValid_exec valid n).heap

public theorem addrValid_demandStart {P : Array Cell} {w : Nat} (valid : HeapValid P) (lt : w < P.size) :
    AddrValid (demandStart P w) :=
  ⟨valid, by simp [demandStart, controlAddresses, lt], fun _ m => by simp [demandStart] at m⟩

/-- **The switch.** When the lazy run enters the pending cell, it runs the pending demand
(over its own stack) to the demand's result, renamed; the forced run returns the cached
result in one transition; and the two then agree exactly, the forced heap covering the
lazy heap, the renaming the identity on the demand's base. -/
public theorem pend_switch {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ)
    (enter : σ.control = .enter e.cell) :
    4 ≤ e.steps ∧ (∀ j, j ≤ e.steps - 1 → active (exec j σ).control = true) ∧
      (∀ j, j ≤ e.steps - 1 → σ.stack.length ≤ (exec j σ).stack.length) ∧
      (exec (e.steps - 1) σ).heap.size = τ.heap.size ∧ (exec (e.steps - 1) σ).stack = σ.stack ∧
      stepRaw τ = ⟨τ.heap, (stepRaw τ).control, τ.stack⟩ ∧
      AgreeRel (switchMap e f σ.heap.size) (exec (e.steps - 1) σ) (stepRaw τ) ∧
      Covers (switchMap e f σ.heap.size) (exec (e.steps - 1) σ).heap (stepRaw τ).heap ∧
      (∀ a, a < e.base.size → switchMap e f σ.heap.size a = a) := by
  have ph := rel.heap
  have ev := ph.valid
  have baseLe := ph.grows
  have finalGe := Pending.final_ge ev
  have cellLt := Pending.cell_lt ev
  have tSize := ph.sizes
  let g := liftMap e.base.size σ.heap.size
  let U' : Nat → Prop := fun a => a < e.base.size ∧ ¬ Footprint e.base e.cell a
  -- e on its base, against e on the lazy heap
  have startAgree : StateAgree g everywhere U' (demandStart e.base e.cell) (demandStart σ.heap e.cell) := by
    refine ⟨⟨?_, ?_, ?_⟩, allIn_everywhere _, ?_, fun _ _ => allIn_everywhere _, rfl⟩
    · intro a past
      have past' : e.base.size ≤ a := past
      refine ⟨trivial, fun h => by simp only [U'] at h; omega, ?_⟩
      simp only [g, liftMap, show ¬ a < e.base.size by omega, if_false]
      show a + (σ.heap.size - e.base.size) + e.base.size = a + σ.heap.size
      omega
    · intro a b _ _ eq
      simp only [g, liftMap] at eq
      split at eq <;> split at eq <;> omega
    · intro a _ notU bound
      have bnd : a < e.base.size := bound
      have fp : Footprint e.base e.cell a := by
        apply Classical.byContradiction; intro h; exact notU ⟨bnd, h⟩
      have gId : ∀ x, x < e.base.size → g x = x := fun x lt => by simp [g, liftMap, lt]
      rcases fp with rfl | ⟨o, w, ca⟩
      · refine ⟨_, ev.susp, ?_, allIn_everywhere _⟩
        rw [show g e.cell = e.cell from gId _ cellLt, renameCell_id (fun x m => gId x (ev.baseValid _ _ ev.susp x m))]
        exact ph.cellKept
      · refine ⟨_, ca, ?_, allIn_everywhere _⟩
        rw [show g a = a from gId _ bnd, renameCell_id (fun x m => gId x (ev.baseValid _ _ ca x m))]
        exact ph.cachedKept a o w ca
    · show Control.enter e.cell = Control.enter (g e.cell)
      simp only [g, liftMap, cellLt, if_true]
  have avoids : ∀ j, j < e.steps → Avoids U' (exec j (demandStart e.base e.cell)) := by
    intro j lt a reads isU
    rcases ev.shallow j lt a reads isU.1 with fp
    exact isU.2 fp
  have agreeAt : ∀ j, j ≤ e.steps →
      StateAgree g everywhere U' (exec j (demandStart e.base e.cell)) (exec j (demandStart σ.heap e.cell)) :=
    fun j hj => agree_exec startAgree j (fun i lt => avoids i (by omega))
  have finalAgree := agreeAt e.steps (Nat.le_refl _)
  rw [ev.demand.final] at finalAgree
  -- the demand on the lazy heap
  let Hf := (exec e.steps (demandStart σ.heap e.cell)).heap
  have lazyDemand : Demand σ.heap e.cell e.steps Hf (renameValue g e.value) := by
    refine ⟨⟨fun j lt => ?_, ?_⟩, ?_⟩
    · rw [(agreeAt j (by omega)).active_eq]; exact ev.demand.halts.1 j lt
    · rw [(agreeAt e.steps (Nat.le_refl _)).active_eq]; exact ev.demand.halts.2
    · have ctl := finalAgree.control
      have st := finalAgree.stack
      simp only [renameControl, List.map_nil] at ctl st
      rw [state_ext (s := exec e.steps (demandStart σ.heap e.cell)), ctl, st]
  obtain ⟨four, cachedLazy, lastLazy, _, frame⟩ := demand_props lazyDemand ph.cellKept
  obtain ⟨_, cachedFinal, _, _, _⟩ := demand_props ev.demand ev.susp
  have σEq : σ = ⟨σ.heap, .enter e.cell, σ.stack⟩ := by rw [state_ext (s := σ), enter]
  have lazyAt : ∀ j, j ≤ e.steps - 1 → exec j σ = withStack (exec j (demandStart σ.heap e.cell)) σ.stack := by
    intro j hj; rw [σEq]; exact frame σ.stack j hj
  have σ1 : exec (e.steps - 1) σ = ⟨Hf, .returned (renameValue g e.value), σ.stack⟩ := by
    rw [lazyAt _ (Nat.le_refl _), lastLazy]; rfl
  -- sizes
  have hfSize : Hf.size = σ.heap.size + e.gap := by
    have := finalAgree.heap.image_size.1
    simp only [g, liftMap, show ¬ e.final.size < e.base.size by omega, if_false] at this
    show (exec e.steps (demandStart σ.heap e.cell)).heap.size = _
    rw [← this]; unfold Pending.gap; show e.final.size + (σ.heap.size - e.base.size) = σ.heap.size + (e.final.size - e.base.size)
    omega
  -- the forced side
  have τEnter : τ.control = .enter e.cell := by
    rw [rel.control, enter]; simp [renameControl, ph.mapOld _ cellLt]
  have τCached : τ.heap[e.cell]? = some (.cached e.origin e.value) := by rw [ph.cached]; exact cachedFinal
  have τ1 := stepRaw_enter_cached τEnter τCached
  -- the map after the switch
  let f' := switchMap e f σ.heap.size
  have f'Old : ∀ a, a < σ.heap.size → f' a = f a := fun a lt => by simp [f', switchMap, lt]
  have f'G : ∀ x, x < e.final.size → f' (g x) = x := by
    intro x lt
    by_cases small : x < e.base.size
    · simp [g, liftMap, small, f', switchMap, Nat.lt_of_lt_of_le small baseLe, ph.mapOld x small]
    · simp only [g, liftMap, small, if_false, f', switchMap]
      have : ¬ x + (σ.heap.size - e.base.size) < σ.heap.size := by omega
      simp only [this, if_false]
      have : x + (σ.heap.size - e.base.size) < σ.heap.size + e.gap := by unfold Pending.gap; omega
      simp only [this, if_true]; omega
  have finalValid : HeapValid e.final := by
    have := heapValid_exec (addrValid_demandStart ev.baseValid cellLt) e.steps
    rw [ev.demand.final] at this; exact this
  have valueValid : AllIn (· < e.final.size) (valueAddresses e.value) := by
    have := (addrValid_exec (addrValid_demandStart ev.baseValid cellLt) e.steps).control
    rw [ev.demand.final] at this; exact this
  have lazyValid := rel.valid
  have nb := ph.not_block
  have img : ∀ x, x < σ.heap.size → f x < τ.heap.size := fun x lt => ph.agree.image_lt trivial lt
  have grows := ph.grows
  have gapEq : e.gap = e.final.size - e.base.size := rfl
  have fNew : ∀ x, e.base.size ≤ x → f x = x + e.gap := ph.mapNew
  have fOld : ∀ x, x < e.base.size → f x = x := ph.mapOld
  -- the new agreement, on the concrete states
  have agreeNew : AgreeRel f' ⟨Hf, .returned (renameValue g e.value), σ.stack⟩ ⟨τ.heap, .returned e.value, τ.stack⟩ := by
    refine ⟨⟨⟨?_, ?_, ?_⟩, allIn_everywhere _, ?_, fun _ _ => allIn_everywhere _, ?_⟩, ?_⟩
    · intro a past
      simp only at past
      refine ⟨trivial, fun h => h, ?_⟩
      simp only [f', switchMap, show ¬ a < σ.heap.size by omega, show ¬ a < σ.heap.size + e.gap by omega, if_false]
      omega
    · intro a b _ _ eq
      simp only [f', switchMap] at eq
      by_cases ha : a < σ.heap.size <;> by_cases hb : b < σ.heap.size <;> simp only [ha, hb, if_true, if_false] at eq
      · exact ph.agree.inj a b trivial trivial eq
      · by_cases hb2 : b < σ.heap.size + e.gap <;> simp only [hb2, if_true, if_false] at eq
        · rcases nb a with h | h <;> omega
        · have := img a ha; omega
      · by_cases ha2 : a < σ.heap.size + e.gap <;> simp only [ha2, if_true, if_false] at eq
        · rcases nb b with h | h <;> omega
        · have := img b hb; omega
      · by_cases ha2 : a < σ.heap.size + e.gap <;> by_cases hb2 : b < σ.heap.size + e.gap <;>
          simp only [ha2, hb2, if_true, if_false] at eq <;> omega
    · intro a _ _ bound
      simp only at bound ⊢
      by_cases old : a < σ.heap.size
      · by_cases isCell : a = e.cell
        · subst isCell
          refine ⟨_, cachedLazy, ?_, allIn_everywhere _⟩
          rw [f'Old _ old, fOld _ cellLt, τCached]
          simp only [renameCell, renameValue_comp]
          rw [renameClosure_id (fun x m => by
              have xlt := ev.baseValid _ _ ev.susp x m
              rw [f'Old _ (by omega), fOld _ xlt]),
            renameValue_id (f := f' ∘ g) (fun x m => f'G x (valueValid x m))]
        · obtain ⟨c, found⟩ : ∃ c, σ.heap[a]? = some c := by
            cases h : σ.heap[a]? with
            | none => simp [Array.getElem?_eq_none_iff] at h; omega
            | some c => exact ⟨c, rfl⟩
          have kept : Hf[a]? = some c := by
            by_cases isCached : ∃ o w, c = .cached o w
            · obtain ⟨o, w, rfl⟩ := isCached
              exact exec_preservesCached _ e.steps a o w found
            · have unread : ∀ j, j < e.steps → readsAt (exec j (demandStart σ.heap e.cell)) ≠ some a := by
                intro j lt reads
                rw [(agreeAt j (by omega)).readsAt_eq] at reads
                cases r : readsAt (exec j (demandStart e.base e.cell)) with
                | none => rw [r] at reads; cases reads
                | some a' =>
                  rw [r] at reads; simp only [Option.map_some, Option.some.injEq] at reads
                  by_cases small : a' < e.base.size
                  · simp only [g, liftMap, small, if_true] at reads
                    subst reads
                    rcases ev.shallow j lt a' r small with rfl | ⟨o, w, ca⟩
                    · exact isCell rfl
                    · have := ph.cachedKept a' o w ca
                      rw [found] at this; cases this
                      exact isCached ⟨o, w, rfl⟩
                  · simp only [g, liftMap, small, if_false] at reads; omega
              have := exec_heap_keep (demandStart σ.heap e.cell) (show a < (demandStart σ.heap e.cell).heap.size from old)
                e.steps unread
              rw [this]; exact found
          refine ⟨c, kept, ?_, allIn_everywhere _⟩
          obtain ⟨c', found', found'', _⟩ := ph.agree.cells a trivial isCell old
          rw [found] at found'; cases found'
          rw [f'Old _ old, found'']
          congr 1
          exact renameCell_congr (fun x m => (f'Old x (rel.valid.heap _ _ found x m)).symm)
      · have hiA : a < σ.heap.size + e.gap := by rw [hfSize] at bound; exact bound
        let b := e.base.size + (a - σ.heap.size)
        have bLt : b < e.final.size := by simp only [b]; omega
        have gb : g b = a := by simp only [g, liftMap, b, show ¬ e.base.size + (a - σ.heap.size) < e.base.size by omega, if_false]; omega
        obtain ⟨c, foundF, foundL, _⟩ := finalAgree.heap.cells b trivial (fun h => by simp only [U', b] at h; omega) bLt
        rw [gb] at foundL
        refine ⟨_, foundL, ?_, allIn_everywhere _⟩
        have fa : f' a = b := by simp only [f', switchMap, old, hiA, if_false, if_true, b]
        rw [fa, ph.block b (by simp [b]) bLt, foundF, renameCell_comp,
          renameCell_id (f := f' ∘ g) (fun x m => f'G x (finalValid _ _ foundF x m))]
    · simp only [renameControl, renameValue_comp]
      rw [renameValue_id (f := f' ∘ g) (fun x m => f'G x (valueValid x m))]
    · simp only; rw [rel.stack]
      apply List.map_congr_left; intro fr m
      exact renameFrame_congr (fun x mx => (f'Old x (rel.valid.stack fr m x mx)).symm)
    · rw [← σ1]; exact addrValid_exec rel.valid _
  have cover : Covers f' Hf τ.heap := by
    intro b bLt
    by_cases small : b < e.base.size
    · exact ⟨b, by omega, by rw [f'Old _ (by omega), fOld _ small]⟩
    · by_cases mid : b < e.final.size
      · refine ⟨σ.heap.size + (b - e.base.size), by rw [hfSize]; unfold Pending.gap; omega, ?_⟩
        simp only [f', switchMap, show ¬ σ.heap.size + (b - e.base.size) < σ.heap.size by omega,
          show σ.heap.size + (b - e.base.size) < σ.heap.size + e.gap by unfold Pending.gap; omega, if_false, if_true]
        omega
      · refine ⟨b - e.gap, by rw [hfSize]; unfold Pending.gap at *; omega, ?_⟩
        rw [f'Old _ (by unfold Pending.gap at *; omega), fNew _ (by unfold Pending.gap at *; omega)]
        unfold Pending.gap at *; omega
  refine ⟨four, fun j hj => ?_, fun j hj => ?_, by rw [σ1]; simp only; rw [hfSize, tSize], by rw [σ1], by rw [τ1],
    by rw [σ1, τ1]; exact agreeNew, by rw [σ1, τ1]; exact cover, fun a lt => ?_⟩
  · rw [lazyAt j hj]; simp only [withStack]; exact lazyDemand.halts.1 j (by omega)
  · rw [lazyAt j hj]; simp [withStack]
  · simp only [switchMap, show a < σ.heap.size by omega, if_true]; exact fOld a lt

theorem stepRaw_update_not_evaluating {s : State} {v : RuntimeValue} {a : Nat} {rest : List Frame}
    (ctl : s.control = .returned v) (st : s.stack = .update a :: rest)
    (notEval : ∀ o, s.heap[a]? ≠ some (.evaluating o)) :
    stepRaw s = ⟨s.heap, .refused .invalidUpdate, rest⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl st notEval; subst ctl st
  simp only [stepRaw]
  try (split <;> first | (rename_i o h; exact absurd h (notEval o)) | rfl)

/-- A lazy update frame for the pending cell finds it suspended, the forced one finds it
cached: both refuse alike. -/
public theorem pend_update_read {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ) {v : RuntimeValue}
    {rest : List Frame} (ctl : σ.control = .returned v) (st : σ.stack = .update e.cell :: rest) :
    PendRel e f (stepRaw σ) (stepRaw τ) ∧ active (stepRaw σ).control = false := by
  have ph := rel.heap
  have cellLt := Pending.cell_lt ph.valid
  have σStep := stepRaw_update_not_evaluating ctl st (fun o h => by rw [ph.cellKept] at h; cases h)
  have τCtl : τ.control = .returned (renameValue f v) := by rw [rel.control, ctl]; rfl
  have τSt : τ.stack = .update e.cell :: rest.map (renameFrame f) := by
    rw [rel.stack, st]; simp [renameFrame, ph.mapOld _ cellLt]
  have τStep := stepRaw_update_not_evaluating τCtl τSt (fun o h => by
    rw [ph.cached, (demand_props ph.valid.demand ph.valid.susp).2.1] at h; cases h)
  rw [σStep, τStep]
  refine ⟨⟨ph, rfl, rfl, ?_⟩, rfl⟩
  have := addrValid_stepRaw rel.valid
  rw [σStep] at this; exact this

/-- **Transfer through a pending demand.** -/
public theorem pend_transfer {e : Pending} {f : Nat → Nat} :
    ∀ (n : Nat) (σ τ : State), PendRel e f σ τ → Halts σ n →
      ∃ n', n' ≤ n ∧ Halts τ n' ∧ Bounded σ τ n n' e.gap ∧
        (PendRel e f (exec n σ) (exec n' τ) ∨
          ∃ g, AgreeRel g (exec n σ) (exec n' τ) ∧ Covers g (exec n σ).heap (exec n' τ).heap ∧
            (∀ a, a < e.base.size → g a = a) ∧ (∀ a, a < σ.heap.size → g a = f a) ∧ n' < n ∧
            (exec n' τ).heap.size = (exec n σ).heap.size) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro σ τ rel halts
  have ph := rel.heap
  have sizes := ph.sizes
  have activeT : active τ.control = active σ.control := by rw [rel.control, active_rename]
  have stackT : τ.stack.length = σ.stack.length := by rw [rel.stack, List.length_map]
  cases act : active σ.control with
  | false =>
    have n0 : n = 0 := by
      apply Classical.byContradiction; intro h
      have := halts.1 0 (by omega); simp only [exec] at this; rw [act] at this; cases this
    subst n0
    refine ⟨0, Nat.le_refl _, ⟨fun _ h => by omega, by simp only [exec]; rw [activeT, act]⟩, ?_, Or.inl rel⟩
    intro j' hj'
    refine ⟨0, Nat.le_refl _, hj', ?_⟩
    have : j' = 0 := by omega
    subst this; simp only [exec]; exact ⟨by omega, by omega⟩
  | true =>
    have npos : 1 ≤ n := by
      apply Classical.byContradiction; intro h
      have := halts.2; rw [show n = 0 by omega] at this; simp only [exec] at this; rw [act] at this; cases this
    by_cases reads : readsAt σ = some e.cell
    · cases ctl : σ.control with
      | enter b =>
        have bEq : b = e.cell := by simp [readsAt, ctl] at reads; exact reads
        subst bEq
        obtain ⟨four, liveLazy, _, sizeEq, _, heapT0, agreeNew, cover, ident⟩ := pend_switch rel ctl
        generalize hm : e.steps - 1 = m at liveLazy sizeEq agreeNew cover
        have mlt : m < n := by
          apply Classical.byContradiction; intro h
          have := liveLazy n (by omega); rw [halts.2] at this; cases this
        have haltsRest : Halts (exec m σ) (n - m) := halts_drop (by rw [show m + (n - m) = n by omega]; exact halts)
        obtain ⟨haltsT1, agreeEnd, sizesT1, coverEnd⟩ := agree_transfer agreeNew haltsRest
        have τActive : active τ.control = true := by rw [activeT, act]
        have finalSize : (exec ((n - m) + 1) τ).heap.size = (exec n σ).heap.size := by
          have ⟨sz, _⟩ := sizesT1 (n - m) (Nat.le_refl _)
          have e1 : exec n σ = exec (n - m) (exec m σ) := by rw [← exec_add, show m + (n - m) = n by omega]
          rw [show exec ((n - m) + 1) τ = exec (n - m) (stepRaw τ) from rfl, e1]
          have hT : (stepRaw τ).heap.size = τ.heap.size := by rw [heapT0]
          omega
        refine ⟨(n - m) + 1, by omega, halts_succ τActive haltsT1, ?_, Or.inr ⟨_, ?_, ?_, ident,
          fun a lt => by simp only [switchMap, lt, if_true], by omega, finalSize⟩⟩
        · intro j' hj'
          cases j' with
          | zero => exact ⟨0, Nat.zero_le _, Nat.le_refl _, by simp only [exec]; omega, by simp only [exec]; omega⟩
          | succ i =>
            refine ⟨m + i, by omega, by omega, ?_⟩
            have ⟨sz, stk⟩ := sizesT1 i (by omega)
            have heapT : (stepRaw τ).heap = τ.heap := by rw [heapT0]
            rw [show exec (i + 1) τ = exec i (stepRaw τ) from rfl, exec_add]
            rw [heapT, ← sizeEq] at sz
            exact ⟨by omega, by omega⟩
        · have := agreeEnd; rw [← exec_add, show m + (n - m) = n by omega] at this; exact this
        · have := coverEnd cover; rw [← exec_add, show m + (n - m) = n by omega] at this; exact this
      | returned v =>
        obtain ⟨rest, st⟩ : ∃ rest, σ.stack = .update e.cell :: rest := by
          cases st : σ.stack with
          | nil => simp [readsAt, ctl, st] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, ctl, st] at reads
            exact ⟨rest, by rw [reads]⟩
        obtain ⟨next, inactive⟩ := pend_update_read rel ctl st
        have n1 : n = 1 := by
          apply Classical.byContradiction; intro h
          have := halts.1 1 (by omega); rw [exec_one, inactive] at this; cases this
        subst n1
        have τActive : active τ.control = true := by rw [activeT, act]
        have τInactive : active (stepRaw τ).control = false := by rw [next.control, active_rename, inactive]
        refine ⟨1, Nat.le_refl _, ⟨fun j h => by rw [show j = 0 by omega]; exact τActive, τInactive⟩, ?_,
          Or.inl next⟩
        intro j' hj'
        refine ⟨j', hj', Nat.le_refl _, ?_⟩
        cases j' with
        | zero => simp only [exec]; omega
        | succ i =>
          have : i = 0 := by omega
          subst this
          have s1 := next.heap.sizes
          have k1 : (stepRaw τ).stack.length = (stepRaw σ).stack.length := by rw [next.stack, List.length_map]
          simp only [exec]; omega
      | _ => simp [readsAt, ctl] at reads
    · have next := pend_step rel reads
      obtain ⟨n'', le, haltsT, bounded, result⟩ := ih (n - 1) (by omega) _ _ next
        (halts_tail (by rw [show n - 1 + 1 = n by omega]; exact halts))
      have τActive : active τ.control = true := by rw [activeT, act]
      have eqS : exec n σ = exec (n - 1) (stepRaw σ) := by
        rw [show n = (n - 1) + 1 by omega]; rfl
      refine ⟨n'' + 1, by omega, halts_succ τActive haltsT, ?_, ?_⟩
      · intro j' hj'
        cases j' with
        | zero => exact ⟨0, Nat.zero_le _, Nat.le_refl _, by simp only [exec]; omega, by simp only [exec]; omega⟩
        | succ i =>
          obtain ⟨j, hj, hij, sz, stk⟩ := bounded i (by omega)
          refine ⟨j + 1, by omega, by omega, ?_, ?_⟩
          · show (exec i (stepRaw τ)).heap.size ≤ (exec j (stepRaw σ)).heap.size + e.gap; exact sz
          · show (exec i (stepRaw τ)).stack.length ≤ (exec j (stepRaw σ)).stack.length; exact stk
      · rw [eqS]
        show PendRel e f (exec (n - 1) (stepRaw σ)) (exec n'' (stepRaw τ)) ∨ _
        rcases result with p | ⟨g, a, c, i, ext, lt, sz⟩
        · exact Or.inl p
        · exact Or.inr ⟨g, a, c, i, fun x hx => ext x (Nat.lt_of_lt_of_le hx (stepRaw_size_mono σ)), by omega, sz⟩


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Chain.lean` -/

/-- **`σ` forces to `τ`** under the address map `F`, with heap headroom `gap`: a finite
chain of pending demands and exact agreements. -/
public inductive ForcesBy : Nat → (Nat → Nat) → State → State → Prop where
  | pend {e : Pending} {f : Nat → Nat} {gap : Nat} {σ τ : State} :
      PendRel e f σ τ → e.gap ≤ gap → ForcesBy gap f σ τ
  | agree {f : Nat → Nat} {gap : Nat} {σ τ : State} :
      AgreeRel f σ τ → τ.heap.size ≤ σ.heap.size + gap → ForcesBy gap f σ τ
  | trans {g1 g2 gap : Nat} {F1 F2 : Nat → Nat} {σ μ τ : State} :
      ForcesBy g1 F1 σ μ → ForcesBy g2 F2 μ τ → g1 + g2 ≤ gap → ForcesBy gap (F2 ∘ F1) σ τ

namespace ForcesBy

public theorem mono {gap gap' : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) (le : gap ≤ gap') :
    ForcesBy gap' F σ τ := by
  cases h with
  | pend r g => exact .pend r (Nat.le_trans g le)
  | agree r g => exact .agree r (by omega)
  | trans a b g => exact .trans a b (Nat.le_trans g le)

public theorem renames {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    τ.control = renameControl F σ.control ∧ τ.stack = σ.stack.map (renameFrame F) := by
  induction h with
  | pend r _ => exact ⟨r.control, r.stack⟩
  | agree r _ => exact ⟨r.agree.control, r.agree.stack⟩
  | trans _ _ _ ih1 ih2 =>
    refine ⟨by rw [ih2.1, ih1.1, renameControl_comp], ?_⟩
    rw [ih2.2, ih1.2, List.map_map]; congr 1; funext fr; exact renameFrame_comp _ _ fr

public theorem lazyValid {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) : AddrValid σ := by
  induction h with
  | pend r _ => exact r.valid
  | agree r _ => exact r.valid
  | trans _ _ _ ih1 _ => exact ih1

public theorem image {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    ∀ x, x < σ.heap.size → F x < τ.heap.size := by
  induction h with
  | pend r _ => exact fun x lt => r.heap.agree.image_lt trivial lt
  | agree r _ => exact fun x lt => r.agree.heap.image_lt trivial lt
  | trans _ _ _ ih1 ih2 => exact fun x lt => ih2 _ (ih1 x lt)

/-- **Re-entry**: the relation is a relation of heaps; any valid control and stack of the
lazy heap, renamed, are related to the forced heap alike. -/
public theorem reenter {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) (c : Control) (S : List Frame)
    (cIn : AllIn (· < σ.heap.size) (controlAddresses c))
    (sIn : ∀ fr ∈ S, AllIn (· < σ.heap.size) (frameAddresses fr)) :
    ForcesBy gap F ⟨σ.heap, c, S⟩ ⟨τ.heap, renameControl F c, S.map (renameFrame F)⟩ := by
  induction h generalizing c S with
  | pend r g =>
    exact .pend ⟨r.heap, rfl, rfl, ⟨r.valid.heap, cIn, sIn⟩⟩ g
  | agree r g =>
    exact .agree ⟨⟨r.agree.heap, allIn_everywhere _, rfl, fun _ _ => allIn_everywhere _, rfl⟩,
      ⟨r.valid.heap, cIn, sIn⟩⟩ g
  | @trans g1 g2 gap F1 F2 σ μ τ one two g ih1 ih2 =>
    have img := one.image
    have l1 := ih1 c S cIn sIn
    have l2 := ih2 (renameControl F1 c) (S.map (renameFrame F1))
      (by rw [controlAddresses_rename]; intro x m; obtain ⟨y, my, rfl⟩ := List.mem_map.mp m; exact img y (cIn y my))
      (by intro fr m; obtain ⟨fr0, m0, rfl⟩ := List.mem_map.mp m
          rw [frameAddresses_rename]; intro x mx; obtain ⟨y, my, rfl⟩ := List.mem_map.mp mx
          exact img y (sIn fr0 m0 y my))
    have := ForcesBy.trans l1 l2 g
    rw [renameControl_comp, List.map_map] at this
    have eq : (renameFrame F2 ∘ renameFrame F1) = renameFrame (F2 ∘ F1) := by
      funext fr; exact renameFrame_comp _ _ fr
    rw [eq] at this; exact this

end ForcesBy

/-- Bounds compose along a chain. -/
theorem bounded_trans {σ μ τ : State} {n n1 n2 g1 g2 : Nat} (one : Bounded σ μ n n1 g1) (two : Bounded μ τ n1 n2 g2) :
    Bounded σ τ n n2 (g1 + g2) := by
  intro j' hj'
  obtain ⟨j1, hj1, le1, sz1, st1⟩ := two j' hj'
  obtain ⟨j, hj, le, sz, st⟩ := one j1 hj1
  exact ⟨j, hj, by omega, by omega, by omega⟩

theorem bounded_mono {σ τ : State} {n n' g g' : Nat} (b : Bounded σ τ n n' g) (le : g ≤ g') : Bounded σ τ n n' g' := by
  intro j' hj'
  obtain ⟨j, hj, lj, sz, st⟩ := b j' hj'
  exact ⟨j, hj, lj, by omega, st⟩

/-- **Transfer along a forcing chain.** -/
public theorem forces_transfer {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    ∀ n, Halts σ n → ∃ n' F', n' ≤ n ∧ Halts τ n' ∧ Bounded σ τ n n' gap ∧ ForcesBy gap F' (exec n σ) (exec n' τ) ∧
      ∀ a, a < σ.heap.size → F' a = F a := by
  induction h with
  | @pend e f gap σ τ r g =>
    intro n halts
    obtain ⟨n', le, haltsT, bounded, result⟩ := pend_transfer n σ τ r halts
    rcases result with p | ⟨g', a, _, _, ext, _, sz⟩
    · exact ⟨n', f, le, haltsT, bounded_mono bounded g, .pend p g, fun _ _ => rfl⟩
    · exact ⟨n', g', le, haltsT, bounded_mono bounded g, .agree a (by omega), ext⟩
  | @agree f gap σ τ r g =>
    intro n halts
    obtain ⟨haltsT, agreeEnd, sizes, _⟩ := agree_transfer r halts
    refine ⟨n, f, Nat.le_refl _, haltsT, ?_, .agree agreeEnd ?_, fun _ _ => rfl⟩
    · intro j' hj'
      have ⟨sz, st⟩ := sizes j' hj'
      exact ⟨j', hj', Nat.le_refl _, by omega, by omega⟩
    · have ⟨sz, _⟩ := sizes n (Nat.le_refl _); omega
  | trans one two g ih1 ih2 =>
    intro n halts
    obtain ⟨n1, F1', le1, halts1, b1, r1, e1⟩ := ih1 n halts
    obtain ⟨n2, F2', le2, halts2, b2, r2, e2⟩ := ih2 n1 halts1
    refine ⟨n2, _, by omega, halts2, bounded_mono (bounded_trans b1 b2) g, .trans r1 r2 g, fun a lt => ?_⟩
    simp only [Function.comp_apply]
    rw [e1 a lt, e2 _ (one.image a lt)]

/-! ## Exact agreements: the identity, and the inverse of a covering one -/

public theorem agreeRel_refl {σ : State} (valid : AddrValid σ) : AgreeRel id σ σ := by
  refine ⟨⟨⟨fun a _ => ⟨trivial, fun h => h, rfl⟩, fun _ _ _ _ h => h, ?_⟩, allIn_everywhere _, ?_,
    fun _ _ => allIn_everywhere _, ?_⟩, valid⟩
  · intro a _ _ lt
    obtain ⟨c, found⟩ : ∃ c, σ.heap[a]? = some c := ⟨σ.heap[a], by simp [lt]⟩
    exact ⟨c, found, by rw [renameCell_id (f := id) (fun _ _ => rfl)]; exact found, allIn_everywhere _⟩
  · cases h : σ.control <;> simp [renameControl, renameValue_id (f := id) (fun _ _ => rfl)]
  · conv => lhs; rw [← List.map_id σ.stack]
    apply List.map_congr_left; intro fr _
    rw [renameFrame_congr (g := id) (fun _ _ => rfl)]; cases fr <;> simp [renameFrame, renameValue_id (f := id) (fun _ _ => rfl)]

/-- **The inverse of a covering exact agreement** between equal-size heaps. -/
public theorem agree_inverse {g : Nat → Nat} {H1 H2 : Array Cell} (hr : HeapAgree g everywhere (fun _ => False) H1 H2)
    (cov : Covers g H1 H2) (sizes : H2.size = H1.size) (valid : HeapValid H1) :
    ∃ ginv : Nat → Nat, HeapAgree ginv everywhere (fun _ => False) H2 H1 ∧
      (∀ a, a < H1.size → ginv (g a) = a) := by
  classical
  let ginv : Nat → Nat := fun b => if h : b < H2.size then Classical.choose (cov b h) else b - H2.size + H1.size
  have spec : ∀ b (h : b < H2.size), ginv b < H1.size ∧ g (ginv b) = b := by
    intro b h; simp only [ginv, h, dif_pos]; exact Classical.choose_spec (cov b h)
  have left : ∀ a, a < H1.size → ginv (g a) = a := by
    intro a lt
    have gl := hr.image_lt trivial lt
    obtain ⟨l1, l2⟩ := spec (g a) gl
    exact hr.inj _ _ trivial trivial l2
  refine ⟨ginv, ⟨?_, ?_, ?_⟩, left⟩
  · intro b past
    refine ⟨trivial, fun h => h, ?_⟩
    simp only [ginv, show ¬ b < H2.size by omega, dif_neg, not_false_eq_true]; omega
  · have beyondEq : ∀ b, ¬ b < H2.size → ginv b = b - H2.size + H1.size := by
      intro b h; simp only [ginv, h, dif_neg, not_false_eq_true]
    intro b1 b2 _ _ eq
    by_cases h1 : b1 < H2.size <;> by_cases h2 : b2 < H2.size
    · have := congrArg g eq; rw [(spec b1 h1).2, (spec b2 h2).2] at this; exact this
    · have v1 := (spec b1 h1).1; rw [beyondEq b2 h2] at eq; omega
    · have v2 := (spec b2 h2).1; rw [beyondEq b1 h1] at eq; omega
    · rw [beyondEq b1 h1, beyondEq b2 h2] at eq; omega
  · intro b _ _ lt
    obtain ⟨al, ga⟩ := spec b lt
    obtain ⟨c, found, found', _⟩ := hr.cells (ginv b) trivial (fun h => h) al
    rw [ga] at found'
    refine ⟨_, found', ?_, allIn_everywhere _⟩
    rw [found, renameCell_comp, renameCell_id (f := ginv ∘ g) (fun x m => left x (valid _ _ found x m))]

/-- When the transition enters an unsuspended cell, nothing in the heap or stack changes. -/
public theorem stepRaw_enter_cases {s : State} {b : Nat} (ctl : s.control = .enter b) :
    (∃ o, s.heap[b]? = some (.suspended o)) ∨ ((stepRaw s).heap = s.heap ∧ (stepRaw s).stack = s.stack) := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl; subst ctl
  cases h : heap[b]? with
  | none => right; simp [stepRaw, h]
  | some c => cases c with
    | suspended o => left; exact ⟨o, rfl⟩
    | evaluating o => right; simp [stepRaw, h]
    | cached o v => right; simp [stepRaw, h]

public theorem StateAgree.readsIn {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (rel : StateAgree f D U s t)
    {a : Nat} (reads : readsAt s = some a) : D a := by
  obtain ⟨heap, control, stack⟩ := s
  have cIn := rel.controlIn; have sIn := rel.stackIn
  simp only at cIn sIn
  cases control with
  | enter b => simp [readsAt] at reads; subst reads; exact cIn _ (List.mem_singleton_self _)
  | returned v =>
    cases stack with
    | nil => simp [readsAt] at reads
    | cons fr rest =>
      cases fr <;> simp [readsAt] at reads
      subst reads; exact sIn _ (List.mem_cons_self ..) _ (List.mem_singleton_self _)
  | _ => simp [readsAt] at reads


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Segment.lean` -/

/-- Every state after the first `n` transitions fits the limits. -/
public def FitsFrom (L : Limits) (s : State) (n : Nat) : Prop :=
  ∀ j, 1 ≤ j → j ≤ n → (exec j s).heap.size ≤ L.heap ∧ (exec j s).stack.length ≤ L.stack

theorem fitsFrom_tail {L : Limits} {s : State} {n : Nat} (h : FitsFrom L s (n + 1)) : FitsFrom L (stepRaw s) n :=
  fun j lo hi => h (j + 1) (by omega) (by omega)

/-- **A bounded run that does not suspend is a halting raw run that fits.** -/
public theorem runBounded_halts (L : Limits) :
    ∀ (ticks : Nat) (s : State), (∀ r st, runBounded L ticks s ≠ .suspended r st) →
      ∃ n, n ≤ ticks ∧ Halts s n ∧ FitsFrom L s n ∧ runBounded L ticks s = runBounded L 0 (exec n s) := by
  intro ticks
  induction ticks with
  | zero =>
    intro s ns
    refine ⟨0, Nat.le_refl _, ⟨fun _ h => by omega, ?_⟩, fun _ h1 h2 => by omega, rfl⟩
    show active s.control = false
    cases ctl : s.control with
    | evaluate term environment => exact (ns .ticks s (by simp [runBounded, ctl])).elim
    | enter address => exact (ns .ticks s (by simp [runBounded, ctl])).elim
    | returned value => exact (ns .ticks s (by simp [runBounded, ctl])).elim
    | _ => rfl
  | succ ticks ih =>
    intro s ns
    cases c : active s.control with
    | false =>
      refine ⟨0, Nat.zero_le _, ⟨fun _ h => by omega, c⟩, fun _ h1 h2 => by omega, ?_⟩
      rw [runBounded_succ_inactive c]; rfl
    | true =>
      rw [runBounded_succ_active c] at ns ⊢
      by_cases fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack
      · rw [if_pos fits] at ns ⊢
        obtain ⟨n, le, halts, fit, eq⟩ := ih (stepRaw s) ns
        refine ⟨n + 1, by omega, halts_succ c halts, ?_, eq⟩
        intro j lo hi
        cases j with
        | zero => omega
        | succ j =>
          by_cases j0 : j = 0
          · subst j0; exact fits
          · exact fit j (by omega) (by omega)
      · rw [if_neg fits] at ns; exact absurd rfl (ns .capacity s)

/-- **A halting raw run that fits is the bounded run.** -/
public theorem runBounded_of_halts (L : Limits) :
    ∀ (ticks : Nat) (s : State) (n : Nat), Halts s n → n ≤ ticks → FitsFrom L s n →
      runBounded L ticks s = runBounded L 0 (exec n s) := by
  intro ticks
  induction ticks with
  | zero => intro s n halts le _; rw [show n = 0 by omega]; rfl
  | succ ticks ih =>
    intro s n halts le fit
    cases n with
    | zero =>
      have inactive : active s.control = false := halts.2
      rw [runBounded_succ_inactive inactive]; rfl
    | succ n =>
      have act : active s.control = true := halts.1 0 (by omega)
      have fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack :=
        fit 1 (Nat.le_refl _) (by omega)
      rw [runBounded_succ_active act, if_pos fits]
      exact ih (stepRaw s) n (halts_tail halts) (by omega) (fitsFrom_tail fit)

/-- Forcing with the open policy finishes exactly when the raw run halts complete, fitting. -/
public theorem forceWith_finished (L : Limits) :
    ∀ (ticks : Nat) (s : State) (v : RuntimeValue) (st : State) (r : Nat),
      forceWith (fun _ => true) L ticks s = (.finished v st, r) →
      ∃ n, n ≤ ticks ∧ Halts s n ∧ FitsFrom L s n ∧ exec n s = st ∧ st.control = .complete v ∧ r = ticks - n := by
  intro ticks
  induction ticks with
  | zero =>
    intro s v st r h
    simp only [forceWith] at h
    cases ctl : s.control <;> simp [runBounded, ctl] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨0, Nat.le_refl _, ⟨fun _ h => by omega, by simp [exec, ctl, active]⟩, fun _ h1 h2 => by omega, rfl, ctl, rfl⟩
  | succ ticks ih =>
    intro s v st r h
    cases c : active s.control with
    | false =>
      rw [forceWith_succ_inactive c] at h
      cases ctl : s.control <;> simp [active, ctl] at c <;> simp [runBounded, ctl] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨0, Nat.zero_le _, ⟨fun _ h => by omega, by simp [exec, ctl, active]⟩, fun _ h1 h2 => by omega, rfl, ctl, by omega⟩
    | true =>
      rw [forceWith_succ_active c] at h
      simp only [Bool.true_eq_false, if_false] at h
      rw [runBounded_succ_active c] at h
      by_cases fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack
      · rw [if_pos fits] at h
        have h0 : runBounded L 0 (stepRaw s) = runBounded L 0 (stepRaw s) := rfl
        cases ctl1 : active (stepRaw s).control with
        | true =>
          have run1 : runBounded L 0 (stepRaw s) = .suspended .ticks (stepRaw s) := by
            cases ctl : (stepRaw s).control <;> simp [active, ctl] at ctl1 <;> simp [runBounded, ctl]
          rw [run1] at h; simp only [continueForce] at h
          obtain ⟨n, le, halts, fit, eq, ctlV, rEq⟩ := ih (stepRaw s) v st r h
          refine ⟨n + 1, by omega, halts_succ c halts, ?_, eq, ctlV, by omega⟩
          intro j lo hi
          cases j with
          | zero => omega
          | succ j =>
            by_cases j0 : j = 0
            · subst j0; exact fits
            · exact fit j (by omega) (by omega)
        | false =>
          cases ctl : (stepRaw s).control <;> simp [active, ctl] at ctl1 <;>
            simp [runBounded, ctl, continueForce] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          refine ⟨1, by omega, ⟨fun j lt => by rw [show j = 0 by omega]; exact c, by simp [exec_one, ctl, active]⟩,
            fun j lo hi => by rw [show j = 1 by omega]; exact fits, rfl, ctl, by omega⟩
      · rw [if_neg fits] at h; simp [continueForce] at h

public theorem forceWith_of_halts (L : Limits) :
    ∀ (ticks : Nat) (s : State) (n : Nat) (v : RuntimeValue), Halts s n → n ≤ ticks → FitsFrom L s n →
      (exec n s).control = .complete v →
      forceWith (fun _ => true) L ticks s = (.finished v (exec n s), ticks - n) := by
  intro ticks
  induction ticks with
  | zero =>
    intro s n v halts le _ ctl
    have : n = 0 := by omega
    subst this
    simp [forceWith, runBounded, exec] at ctl ⊢; simp [ctl]
  | succ ticks ih =>
    intro s n v halts le fit ctl
    cases n with
    | zero =>
      have inactive : active s.control = false := halts.2
      have ctl' : s.control = .complete v := ctl
      rw [forceWith_succ_inactive inactive]
      simp [runBounded, ctl', exec]
    | succ n =>
      have act : active s.control = true := halts.1 0 (by omega)
      have fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack :=
        fit 1 (Nat.le_refl _) (by omega)
      rw [forceWith_succ_active act]
      simp only [Bool.true_eq_false, if_false]
      rw [show runBounded L 1 s = runBounded L (0 + 1) s from rfl, runBounded_succ_active act, if_pos fits]
      have tail := halts_tail halts
      cases n with
      | zero =>
        have inact : active (stepRaw s).control = false := tail.2
        have ctl' : (stepRaw s).control = .complete v := ctl
        simp [runBounded, ctl', continueForce, exec]
      | succ n =>
        have act1 : active (stepRaw s).control = true := tail.1 0 (by omega)
        have run1 : runBounded L 0 (stepRaw s) = .suspended .ticks (stepRaw s) := by
          cases c : (stepRaw s).control <;> simp [active, c] at act1 <;> simp [runBounded, c]
        rw [run1]; simp only [continueForce]
        rw [ih (stepRaw s) (n + 1) v tail (by omega) (fitsFrom_tail fit) ctl]
        congr 1
        omega


/-! ## Resource vectors -/

/-- `L` gives at least the room `L0` gives. -/
@[expose] public def LimitsLe (L0 L : Limits) : Prop := L0.heap ≤ L.heap ∧ L0.stack ≤ L.stack

@[expose] public def limitsMax (L L' : Limits) : Limits := ⟨max L.heap L'.heap, max L.stack L'.stack⟩

public theorem limitsLe_refl (L : Limits) : LimitsLe L L := ⟨Nat.le_refl _, Nat.le_refl _⟩

public theorem limitsLe_trans {L1 L2 L3 : Limits} (a : LimitsLe L1 L2) (b : LimitsLe L2 L3) : LimitsLe L1 L3 :=
  ⟨Nat.le_trans a.1 b.1, Nat.le_trans a.2 b.2⟩

public theorem limitsLe_max_left (L L' : Limits) : LimitsLe L (limitsMax L L') :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

public theorem limitsLe_max_right (L L' : Limits) : LimitsLe L' (limitsMax L L') :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem fitsFrom_mono {L L' : Limits} (le : LimitsLe L L') {s : State} {n : Nat} (h : FitsFrom L s n) :
    FitsFrom L' s n :=
  fun j lo hi => let ⟨a, b⟩ := h j lo hi; ⟨Nat.le_trans a le.1, Nat.le_trans b le.2⟩

/-- Every finite run fits some limits (the peak heap and stack it reaches). -/
theorem fitsFrom_exists (s : State) : ∀ n, ∃ L, FitsFrom L s n := by
  intro n
  induction n with
  | zero => exact ⟨⟨0, 0⟩, fun j lo hi => by omega⟩
  | succ n ih =>
    obtain ⟨L, fit⟩ := ih
    refine ⟨⟨max L.heap (exec (n + 1) s).heap.size, max L.stack (exec (n + 1) s).stack.length⟩,
      fun j lo hi => ?_⟩
    by_cases jn : j = n + 1
    · subst jn; exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
    · obtain ⟨a, b⟩ := fit j lo (by omega)
      exact ⟨Nat.le_trans a (Nat.le_max_left _ _), Nat.le_trans b (Nat.le_max_left _ _)⟩


/-! ## Endings -/

/-- How a segment ends, as what a kernel commits from it. -/
public inductive Ending where
  | yielded (plan : Data)
  | finished (result : Data)
  | divergent
  | refused (reason : Refusal)

/-- The segment from `s` under limits `L`, `T` ticks and extraction budget `budget`: its
ending and the state the run stopped in (for a yield, the yielded state), or `none` (out of
ticks or room, or an extraction that did not succeed). -/
@[expose] public def endsWith (L : Limits) (T : Nat) (budget : Budget) (s : State) : Option (Ending × State) :=
  match runBounded L T s with
  | .yielded _ y => match yieldedPlan L budget y with
    | .ok r => some (.yielded r.value, y)
    | .error _ => none
  | .finished _ y => match complete L budget y with
    | .ok r => some (.finished r.value, y)
    | .error _ => none
  | .divergent _ y => some (.divergent, y)
  | .refused reason y => some (.refused reason, y)
  | .suspended _ _ => none

/-- **The ending above a threshold**: under every resource vector at least `(L0, T0, E0)`
(the same output nodes and bytes as `budget`), the segment from `s` ends with `e`, stopping in
`y` (which does not depend on the resources). -/
@[expose] public def EndsAbove (s : State) (budget : Budget) (e : Ending) (y : State) : Prop :=
  ∃ (L0 : Limits) (T0 E0 : Nat), ∀ (L : Limits) (T k : Nat), LimitsLe L0 L → T0 ≤ T →
    endsWith L T ⟨budget.nodes, E0 + k, budget.bytes⟩ s = some (e, y)


/-- A run that halts is a bounded run that does not suspend, read back. -/
public theorem halts_of_endsWith {L : Limits} {T : Nat} {budget : Budget} {s : State} {e : Ending} {y : State}
    (ran : endsWith L T budget s = some (e, y)) : ∃ n, Halts s n := by
  have notSusp : ∀ r st, Obend.Core.Machine.runBounded L T s ≠ .suspended r st := by
    intro r st h; unfold endsWith at ran; rw [h] at ran; cases ran
  obtain ⟨n, _, halts, _, _⟩ := runBounded_halts L T s notSusp
  exact ⟨n, halts⟩


end Obend.Core.Proofs.Forcing
