module
/- Lockstep: one machine transition. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Collect.Rename
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

/-! ## Lockstep: one machine transition -/

public theorem forcingShared_rename (f : Nat → Nat) (stack : List Frame) :
    forcingShared (stack.map (renameFrame f)) = forcingShared stack := by
  induction stack with
  | nil => rfl
  | cons frame rest ih =>
    simp only [forcingShared, List.map_cons, List.any_cons] at ih ⊢
    rw [ih]; cases frame <;> rfl

public theorem valueTerm_rename (f : Nat → Nat) (value : RuntimeValue) :
    valueTerm (renameValue f value) = valueTerm value := by
  cases value <;> rfl

public theorem scalarValue_rename {f : Nat → Nat} {result : Term} {next : RuntimeValue}
    (scalar : scalarValue result = some next) : renameValue f next = next ∧ valueAddresses next = [] := by
  cases result <;> simp [scalarValue] at scalar <;> subst scalar <;> exact ⟨rfl, rfl⟩

public theorem allIn_nil (D : Nat → Prop) : AllIn D [] := fun _ member => by cases member

public theorem allIn_cons {D : Nat → Prop} {a : Nat} {rest : List Nat} (head : D a) (tail : AllIn D rest) :
    AllIn D (a :: rest) := by
  intro x member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail x member

public theorem allIn_append {D : Nat → Prop} {first second : List Nat} (one : AllIn D first)
    (two : AllIn D second) : AllIn D (first ++ second) := by
  intro x member
  rcases List.mem_append.mp member with member | member
  · exact one x member
  · exact two x member

public theorem frames_cons {D : Nat → Prop} {frame : Frame} {rest : List Frame}
    (head : AllIn D (frameAddresses frame)) (tail : ∀ frame ∈ rest, AllIn D (frameAddresses frame)) :
    ∀ frame' ∈ frame :: rest, AllIn D (frameAddresses frame') :=
  List.forall_mem_cons.mpr ⟨head, tail⟩

/-- **Lockstep.** A related pair steps to a related pair: the renaming and its domain
are fixed, and the two machines allocate at the two heap ends (`f heap.size = heap'.size`). -/
public theorem related_stepRaw {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t) :
    Related f D (stepRaw s) (stepRaw t) := by
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
    simp only [stepRaw, renameControl]
    rw [hr.lookup inA]
    cases found : heap[a]? with
    | none => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | some cell =>
      have cellIn := hr.cellIn inA found
      cases cell with
      | evaluating o => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
      | cached o v => exact ⟨hr, fun x member => cellIn x (List.mem_append_right _ member), rfl, stackIn, rfl⟩
      | suspended o =>
        exact ⟨hr.set inA (bound_of_some found) (c := .evaluating o) cellIn, cellIn, rfl,
          frames_cons (allIn_cons inA (allIn_nil D)) stackIn, rfl⟩
  | evaluate term env =>
    have envIn : AllIn D env := controlIn
    cases term with
    | hole n σ =>
      obend_cases σ with []
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
      obtain ⟨hr', same, inside⟩ := allocateFields_related hr envIn fields
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
        simp only [stepRaw, renameControl, List.map_cons, renameFrame]
        rw [hr.lookup inA]
        cases found : heap[a]? with
        | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
        | some cell =>
          have cellIn := hr.cellIn inA found
          cases cell with
          | suspended o => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | cached o w => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | evaluating o =>
            exact ⟨hr.set inA (bound_of_some found) (c := .cached o v) (allIn_append cellIn valueIn),
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
          obtain ⟨hr', same, inside⟩ := allocateFields_related hr environmentIn fields
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

end Obend.Core.Collect
