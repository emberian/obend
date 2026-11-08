module
public import Obend.Hardware.Gpu.BlockLower
public import Obend.Hardware.ArrayKernelOwnership
@[expose] public section

/-! Pointwise semantics for the actual ArrayKernel phase evaluator.
These lemmas expose simultaneous, unique scatters without introducing a second
execution model. They are the bridge from register/tree invariants to evalProgram.
Bounds and uniqueness are explicit; source admission supplies both independently.
-/
namespace Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

abbrev valueAt (mem : Memory) (a i : Nat) : Word :=
  (mem.getD a #[]).getD i 0#64

def writeLoc (w : Nat × Nat × Word) : Nat × Nat := (w.1, w.2.1)

/-- One valid store changes exactly its destination, preserving every other cell. -/
theorem applyWrite_value (p : Program) (mem : Memory) (w : Nat × Nat × Word)
    (hg : Good p mem) (hv : Valid p w.1 w.2.1) (a i : Nat) :
    valueAt (applyWrite mem w) a i =
      if writeLoc w = (a,i) then w.2.2 else valueAt mem a i := by
  have ha : w.1 < mem.size := by rw [hg.1]; exact hv.1
  have hi : w.2.1 < (mem.getD w.1 #[]).size := by rw [hg.2 _ hv.1]; exact hv.2
  simpa [valueAt, writeLoc, Prod.mk.injEq] using
    applyWrite_get mem w.1 w.2.1 w.2.2 ha hi a i

/-- A list of bounded stores preserves any cell outside its write footprint. -/
theorem foldWrites_value_untouched (p : Program) (ws : List (Nat × Nat × Word))
    (mem : Memory) (hg : Good p mem)
    (hv : ∀ w ∈ ws, Valid p w.1 w.2.1) (a i : Nat)
    (hu : ∀ w ∈ ws, writeLoc w ≠ (a,i)) :
    valueAt (ws.foldl applyWrite mem) a i = valueAt mem a i := by
  induction ws generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons, ih _ (applyWrite_good p mem w hg)
      (fun x hx => hv x (List.mem_cons_of_mem _ hx))
      (fun x hx => hu x (List.mem_cons_of_mem _ hx))]
    rw [applyWrite_value p mem w hg (hv w (by simp)) a i, ite_eq_right (hu w (by simp))]

/-- A unique store's value is the final value, regardless of the enumeration order. -/
theorem foldWrites_value_written (p : Program) (ws : List (Nat × Nat × Word))
    (mem : Memory) (hg : Good p mem)
    (hv : ∀ w ∈ ws, Valid p w.1 w.2.1)
    (hn : (ws.map writeLoc).Nodup) (w : Nat × Nat × Word) (hw : w ∈ ws) :
    valueAt (ws.foldl applyWrite mem) w.1 w.2.1 = w.2.2 := by
  induction ws generalizing mem with
  | nil => simp at hw
  | cons x ws ih =>
    have hn' := List.nodup_cons.mp (show (writeLoc x :: ws.map writeLoc).Nodup from hn)
    rcases List.mem_cons.mp hw with he | hw
    · subst w
      rw [List.foldl_cons, foldWrites_value_untouched p ws _ (applyWrite_good p mem x hg)
        (fun y hy => hv y (List.mem_cons_of_mem _ hy)) x.1 x.2.1 ?_]
      · rw [applyWrite_value p mem x hg (hv x (by simp)) x.1 x.2.1]
        simp [writeLoc]
      · intro y hy he
        exact hn'.1 (List.mem_map.mpr ⟨y, hy, he⟩)
    · exact ih (applyWrite mem x) (applyWrite_good p mem x hg)
        (fun y hy => hv y (List.mem_cons_of_mem _ hy)) hn'.2 hw

/-- The evaluator's computed write list has precisely the phase's address list. -/
theorem phaseWrites_locations (ph : Phase) (mem : Memory) (g : Nat) :
    (phaseWrites ph mem g).map writeLoc = ph.writeAddresses g := by
  simp [phaseWrites, Phase.writeAddresses, laneWrites, writeLoc, List.map_flatMap,
    List.map_map, Function.comp_def]

/-- Phase bounds apply to the concrete values calculated from its input snapshot. -/
theorem phaseWrites_valid (p : Program) (ph : Phase) (mem : Memory) (g : Nat)
    (hb : PhaseInBounds p ph g) :
    ∀ w ∈ phaseWrites ph mem g, Valid p w.1 w.2.1 := by
  intro w hw
  obtain ⟨l, hl, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨out, ho, he⟩ := List.mem_map.mp hw
  subst w
  exact hb.2 l (List.mem_range.mp hl) out ho

/-- A phase leaves every cell outside its scatter addresses unchanged. -/
theorem evalPhase_value_untouched (p : Program) (ph : Phase) (mem : Memory) (g a i : Nat)
    (hg : Good p mem) (hb : PhaseInBounds p ph g)
    (hu : (a,i) ∉ ph.writeAddresses g) :
    valueAt (evalPhase ph g mem) a i = valueAt mem a i := by
  apply foldWrites_value_untouched p (phaseWrites ph mem g) mem hg (phaseWrites_valid p ph mem g hb)
  intro w hw he
  apply hu
  rw [← phaseWrites_locations ph mem g]
  exact List.mem_map.mpr ⟨w, hw, he⟩

/-- Read the result of any actual logical invocation and declared write. Loads and
register computation are evaluated against the original phase snapshot. -/
theorem evalPhase_value_written (p : Program) (ph : Phase) (mem : Memory) (g l : Nat)
    (hg : Good p mem) (hb : PhaseInBounds p ph g)
    (hn : (ph.writeAddresses g).Nodup) (hl : l < ph.lanes)
    (w : Write) (hw : w ∈ ph.writes) :
    valueAt (evalPhase ph g mem) w.array (w.index.eval g l) =
      (runRegisters ph.code (loadRegisters ph mem g l)).getD w.value 0#64 := by
  refine foldWrites_value_written p (phaseWrites ph mem g) mem hg
    (phaseWrites_valid p ph mem g hb) ?_
    (w.array, w.index.eval g l,
      (runRegisters ph.code (loadRegisters ph mem g l)).getD w.value 0#64) ?_
  · rw [phaseWrites_locations]; exact hn
  · apply List.mem_flatMap.mpr
    refine ⟨l, List.mem_range.mpr hl, ?_⟩
    exact List.mem_map.mpr ⟨w, hw, rfl⟩

/-- A sequence of phases preserves cells outside every phase's write footprint. -/
theorem evalPhases_value_untouched (p : Program) (phases : List Phase)
    (mem : Memory) (g a i : Nat) (hg : Good p mem)
    (hb : ∀ ph ∈ phases, PhaseInBounds p ph g)
    (hu : ∀ ph ∈ phases, (a,i) ∉ ph.writeAddresses g) :
    valueAt (phases.foldl (fun m ph => evalPhase ph g m) mem) a i = valueAt mem a i := by
  induction phases generalizing mem with
  | nil => rfl
  | cons ph phases ih =>
    rw [List.foldl_cons, ih (evalPhase ph g mem)
      (show Good p (evalPhase ph g mem) from foldWrites_good p mem (phaseWrites ph mem g) hg)
      (fun q hq => hb q (List.mem_cons_of_mem _ hq))
      (fun q hq => hu q (List.mem_cons_of_mem _ hq))]
    exact evalPhase_value_untouched p ph mem g a i hg (hb ph (by simp)) (hu ph (by simp))

/-- Group execution does not alter another tile's cells when its scatters avoid them. -/
theorem evalGroup_value_untouched (p : Program) (d : Dispatch)
    (mem : Memory) (g a i : Nat) (hg : Good p mem)
    (hb : ∀ ph ∈ d.phases, PhaseInBounds p ph g)
    (hu : ∀ ph ∈ d.phases, (a,i) ∉ ph.writeAddresses g) :
    valueAt (evalGroup d g mem) a i = valueAt mem a i :=
  evalPhases_value_untouched p d.phases mem g a i hg hb hu

/-- Arbitrary groups compose the same frame property. No ordering between
independent groups is smuggled into a tree invariant. -/
theorem evalGroups_value_untouched (p : Program) (d : Dispatch) (groups : List Nat)
    (mem : Memory) (a i : Nat) (hg : Good p mem)
    (hb : ∀ g ∈ groups, ∀ ph ∈ d.phases, PhaseInBounds p ph g)
    (hu : ∀ g ∈ groups, ∀ ph ∈ d.phases, (a,i) ∉ ph.writeAddresses g) :
    valueAt (groups.foldl (fun m g => evalGroup d g m) mem) a i = valueAt mem a i := by
  induction groups generalizing mem with
  | nil => rfl
  | cons g groups ih =>
    rw [List.foldl_cons, ih _ (evalGroup_good p d g mem hg)
      (fun k hk => hb k (List.mem_cons_of_mem _ hk))
      (fun k hk => hu k (List.mem_cons_of_mem _ hk))]
    exact evalGroup_value_untouched p d mem g a i hg (hb g (by simp)) (hu g (by simp))

/-- Dispatch-level frame rule for the actual group traversal. -/
theorem evalDispatch_value_untouched (p : Program) (d : Dispatch)
    (mem : Memory) (a i : Nat) (hg : Good p mem) (hb : DispatchInBounds p d)
    (hu : ∀ g < d.groups, ∀ ph ∈ d.phases, (a,i) ∉ ph.writeAddresses g) :
    valueAt (evalDispatch d mem) a i = valueAt mem a i :=
  evalGroups_value_untouched p d (List.range d.groups) mem a i hg
    (fun g hg => hb g (List.mem_range.mp hg))
    (fun g hg => hu g (List.mem_range.mp hg))

/-- Admission provides phase bounds and unique scatter addresses for every group. -/
theorem checkedPhase (p : Program) (hc : p.check = .ok ())
    (d : Dispatch) (hd : d ∈ p.dispatches) (g : Nat) (hg : g < d.groups)
    (ph : Phase) (hph : ph ∈ d.phases) :
    PhaseInBounds p ph g ∧ (ph.writeAddresses g).Nodup := by
  refine ⟨boundsSafe_sound p (p.check_boundsSafe hc) d hd g hg ph hph, ?_⟩
  have ho := p.check_ownershipSafe hc
  simp only [Program.ownershipSafe, List.all_eq_true, Bool.and_eq_true] at ho
  exact Unique.checkUnique_sound _ ((ho d hd).1.1.2 g (List.mem_range.mpr hg) ph hph)

end Obend.Hardware.Gpu.PhaseSemantics
