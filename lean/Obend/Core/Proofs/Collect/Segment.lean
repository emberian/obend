module
/- The kernel's segment; composition: collecting at every yield. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Collect.Extract
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

open Obend.Core.Data
/-! ## The kernel's segment -/

/-- **One activity segment agrees** (the shape of `Kernel.ObjectiveActivity.runSegment`):
if the original yields and its Plan extracts, the related state yields at the renamed
Plan address with a related state whose Plan is the same Data; a finished original
completes to the same result Data; a divergent or refused original diverges or is
refused for the same reason. -/
public theorem related_segment {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t)
    (limits limits' : Limits) (room : RoomFor limits limits' s t) (ticks : Nat) (budget : Budget) :
    (∀ plan y r, runBounded limits ticks s = .yielded plan y → yieldedPlan limits budget y = .ok r →
      ∃ y' r', runBounded limits' ticks t = .yielded (f plan) y' ∧ Related f D y y' ∧
        yieldedPlan limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
    (∀ value y r, runBounded limits ticks s = .finished value y → complete limits budget y = .ok r →
      ∃ y' r', runBounded limits' ticks t = .finished (renameValue f value) y' ∧
        complete limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
    (∀ address y, runBounded limits ticks s = .divergent address y →
      ∃ y', runBounded limits' ticks t = .divergent (f address) y') ∧
    (∀ reason y, runBounded limits ticks s = .refused reason y →
      ∃ y', runBounded limits' ticks t = .refused reason y') := by
  have always : ∀ s t, Related f D s t → (fun _ => true : State → Bool) s = true →
      (fun _ => true : State → Bool) t = true := fun _ _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro plan y r ran extracted
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    obtain ⟨planEq, yRel⟩ := rel
    obtain ⟨r', extracted', value, _, _⟩ :=
      related_yieldedPlanWith always limits limits' budget yRel (room.shift related yRel) extracted
    exact ⟨_, r', by rw [planEq], yRel, extracted', value⟩
  · intro value y r ran completed
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    obtain ⟨valueEq, _, yRel⟩ := rel
    obtain ⟨r', completed', same, _, _⟩ :=
      related_completeWith always limits limits' budget yRel (room.shift related yRel) completed
    exact ⟨_, r', by rw [valueEq], completed', same⟩
  · intro address y ran
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    exact ⟨_, by rw [rel.1]⟩
  · intro reason y ran
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    exact ⟨_, by rw [rel.1]⟩

/-! ## Composition: collecting at every yield -/

public theorem renameValue_comp (f g : Nat → Nat) (value : RuntimeValue) :
    renameValue g (renameValue f value) = renameValue (g ∘ f) value := by
  cases value <;> simp [renameValue, Function.comp_def]

public theorem renameCell_comp (f g : Nat → Nat) (cell : Cell) :
    renameCell g (renameCell f cell) = renameCell (g ∘ f) cell := by
  cases cell <;> simp [renameCell, renameClosure, renameValue_comp, Function.comp_def]

public theorem renameFrame_comp (f g : Nat → Nat) (frame : Frame) :
    renameFrame g (renameFrame f frame) = renameFrame (g ∘ f) frame := by
  cases frame <;> simp [renameFrame, renameValue_comp, Function.comp_def]

public theorem renameControl_comp (f g : Nat → Nat) (control : Control) :
    renameControl g (renameControl f control) = renameControl (g ∘ f) control := by
  cases control <;> simp [renameControl, renameValue_comp, Function.comp_def]

theorem valueAddresses_rename (f : Nat → Nat) (value : RuntimeValue) :
    valueAddresses (renameValue f value) = (valueAddresses value).map f := by
  cases value <;> simp [renameValue, valueAddresses, Function.comp_def]

theorem cellAddresses_rename (f : Nat → Nat) (cell : Cell) :
    cellAddresses (renameCell f cell) = (cellAddresses cell).map f := by
  cases cell <;> simp [renameCell, renameClosure, cellAddresses, valueAddresses_rename]

public theorem frameAddresses_rename (f : Nat → Nat) (frame : Frame) :
    frameAddresses (renameFrame f frame) = (frameAddresses frame).map f := by
  cases frame <;> simp [renameFrame, frameAddresses, valueAddresses_rename]

public theorem controlAddresses_rename (f : Nat → Nat) (control : Control) :
    controlAddresses (renameControl f control) = (controlAddresses control).map f := by
  cases control <;> simp [renameControl, controlAddresses, valueAddresses_rename]

/-- **Relations compose**, so a history that collects at every yield stays related to
the history that never collects. -/
public theorem Related.trans {f g : Nat → Nat} {D E : Nat → Prop} {s t u : State}
    (one : Related f D s t) (two : Related g E t u) :
    Related (g ∘ f) (fun a => D a ∧ E (f a)) s u := by
  have sizeOne := one.heap.size_le
  have sizeTwo := two.heap.size_le
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a past
    have ⟨inD, shift⟩ := one.heap.beyond a past
    have ⟨inE, shift2⟩ := two.heap.beyond (f a) (by omega)
    exact ⟨⟨inD, inE⟩, by simp only [Function.comp_apply]; omega⟩
  · intro a b inA inB same
    exact one.heap.inj a b inA.1 inB.1 (two.heap.inj _ _ inA.2 inB.2 same)
  · intro a inA bound
    obtain ⟨c, found, foundT, inC⟩ := one.heap.cells a inA.1 bound
    obtain ⟨c2, foundT2, foundU, inC2⟩ := two.heap.cells (f a) inA.2 (bound_of_some foundT)
    rw [foundT] at foundT2; cases foundT2
    refine ⟨c, found, by rw [Function.comp_apply, foundU, renameCell_comp], ?_⟩
    intro x member
    refine ⟨inC x member, ?_⟩
    rw [cellAddresses_rename] at inC2
    exact inC2 (f x) (List.mem_map_of_mem member)
  · intro x member
    refine ⟨one.controlIn x member, ?_⟩
    have := two.controlIn
    rw [one.control, controlAddresses_rename] at this
    exact this (f x) (List.mem_map_of_mem member)
  · rw [two.control, one.control, renameControl_comp]
  · intro frame member x inFrame
    refine ⟨one.stackIn frame member x inFrame, ?_⟩
    have := two.stackIn (renameFrame f frame) (by rw [one.stack]; exact List.mem_map_of_mem member)
    rw [frameAddresses_rename] at this
    exact this (f x) (List.mem_map_of_mem inFrame)
  · rw [two.stack, one.stack, List.map_map]
    congr 1
    funext frame
    exact renameFrame_comp f g frame

end Obend.Core.Collect
