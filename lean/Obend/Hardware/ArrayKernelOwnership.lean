module
public import Obend.Hardware.ArrayKernel
@[expose] public section

/-! Ownership facts extracted from the executable source admission checker. -/
namespace Obend.Hardware.ArrayKernel
set_option autoImplicit false

/-- The device writes of a single workgroup, before combining the groups into one dispatch. -/
def Dispatch.groupDeviceWriteAddresses (p : Program) (d : Dispatch) (g : Nat) : List (Nat × Nat) :=
  d.phases.flatMap fun ph => (List.range ph.lanes).flatMap fun l =>
    ph.writes.filterMap fun w =>
      if (p.buffers.getD w.array default).storage == .device then
        some (w.array, w.index.eval g l) else none

theorem deviceReadArrays_mem (p : Program) (d : Dispatch) (ph : Phase) (hph : ph ∈ d.phases)
    (r : Read) (hr : r ∈ ph.reads) (hs : (p.buffers.getD r.array default).storage = .device) :
    r.array ∈ d.deviceReadArrays p := by
  apply List.mem_flatMap.mpr
  refine ⟨ph, hph, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨r, hr, by simp only [hs, beq_self_eq_true, ↓reduceIte]⟩

theorem groupDeviceWriteAddresses_mem (p : Program) (d : Dispatch) (g : Nat)
    (ph : Phase) (hph : ph ∈ d.phases) (l : Nat) (hl : l < ph.lanes)
    (w : Write) (hw : w ∈ ph.writes) (hs : (p.buffers.getD w.array default).storage = .device) :
    (w.array, w.index.eval g l) ∈ d.groupDeviceWriteAddresses p g := by
  apply List.mem_flatMap.mpr
  refine ⟨ph, hph, List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, ?_⟩⟩
  apply List.mem_filterMap.mpr
  exact ⟨w, hw, by simp only [hs, beq_self_eq_true, ↓reduceIte]⟩

theorem deviceWriteAddresses_mem (p : Program) (d : Dispatch) (g : Nat) (hg : g < d.groups)
    (ph : Phase) (hph : ph ∈ d.phases) (l : Nat) (hl : l < ph.lanes)
    (w : Write) (hw : w ∈ ph.writes) (hs : (p.buffers.getD w.array default).storage = .device) :
    (w.array, w.index.eval g l) ∈ d.deviceWriteAddresses p := by
  apply List.mem_flatMap.mpr
  exact ⟨g, List.mem_range.mpr hg, groupDeviceWriteAddresses_mem p d g ph hph l hl w hw hs⟩

/-- Every admitted source write targets mutable storage. -/
theorem Program.check_noConstantWrite (p : Program) (h : p.check = .ok ())
    (d : Dispatch) (hd : d ∈ p.dispatches) (ph : Phase) (hph : ph ∈ d.phases)
    (w : Write) (hw : w ∈ ph.writes) :
    (p.buffers.getD w.array default).storage ≠ .constant := by
  have hn := p.check_noConstantWrites h
  simp only [Program.noConstantWrites, List.all_eq_true, bne_iff_ne] at hn
  exact hn d hd ph hph w hw

/-- The actual hash-set admission certifies uniqueness across the whole dispatch. -/
theorem Program.check_deviceWrites_nodup (p : Program) (h : p.check = .ok ())
    (d : Dispatch) (hd : d ∈ p.dispatches) : (d.deviceWriteAddresses p).Nodup := by
  have ho := p.check_ownershipSafe h
  simp only [Program.ownershipSafe, List.all_eq_true, Bool.and_eq_true] at ho
  exact Unique.checkUnique_sound _ (ho d hd).1.2

/-- Device writes and reads belong to different arrays throughout an admitted dispatch, including
accesses from different phases, different lanes, and different workgroups. -/
theorem Program.check_deviceReadWrite_disjoint (p : Program) (h : p.check = .ok ())
    (d : Dispatch) (hd : d ∈ p.dispatches)
    (readPhase : Phase) (hrph : readPhase ∈ d.phases)
    (r : Read) (hr : r ∈ readPhase.reads)
    (hrs : (p.buffers.getD r.array default).storage = .device)
    (g : Nat) (hg : g < d.groups) (writePhase : Phase) (hwph : writePhase ∈ d.phases)
    (l : Nat) (hl : l < writePhase.lanes) (w : Write) (hw : w ∈ writePhase.writes)
    (hws : (p.buffers.getD w.array default).storage = .device) : r.array ≠ w.array := by
  have ho := p.check_ownershipSafe h
  simp only [Program.ownershipSafe, List.all_eq_true, Bool.and_eq_true] at ho
  have hn := (ho d hd).2 (w.array, w.index.eval g l)
    (deviceWriteAddresses_mem p d g hg writePhase hwph l hl w hw hws)
  have hm := deviceReadArrays_mem p d readPhase hrph r hr hrs
  intro he
  rw [he] at hm
  have hc := List.contains_iff_mem.mpr hm
  simp only [Bool.not_eq_true'] at hn
  exact Bool.noConfusion (hn.symm.trans hc)

/-- Unique flattened writes make the write sets of distinct groups disjoint. -/
theorem Program.check_deviceWrites_crossGroup (p : Program) (h : p.check = .ok ())
    (d : Dispatch) (hd : d ∈ p.dispatches)
    (g₁ g₂ : Nat) (hg₁ : g₁ < d.groups) (hg₂ : g₂ < d.groups) (hne : g₁ ≠ g₂)
    (ph₁ ph₂ : Phase) (hp₁ : ph₁ ∈ d.phases) (hp₂ : ph₂ ∈ d.phases)
    (l₁ l₂ : Nat) (hl₁ : l₁ < ph₁.lanes) (hl₂ : l₂ < ph₂.lanes)
    (w₁ w₂ : Write) (hw₁ : w₁ ∈ ph₁.writes) (hw₂ : w₂ ∈ ph₂.writes)
    (hs₁ : (p.buffers.getD w₁.array default).storage = .device)
    (hs₂ : (p.buffers.getD w₂.array default).storage = .device) :
    (w₁.array, w₁.index.eval g₁ l₁) ≠ (w₂.array, w₂.index.eval g₂ l₂) := by
  have hn := p.check_deviceWrites_nodup h d hd
  change ((List.range d.groups).flatMap (d.groupDeviceWriteAddresses p)).Pairwise Ne at hn
  have hp := (List.pairwise_flatMap.mp hn).2
  have hm₁ := groupDeviceWriteAddresses_mem p d g₁ ph₁ hp₁ l₁ hl₁ w₁ hw₁ hs₁
  have hm₂ := groupDeviceWriteAddresses_mem p d g₂ ph₂ hp₂ l₂ hl₂ w₂ hw₂ hs₂
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hrel := List.pairwise_iff_getElem.mp hp g₁ g₂ (by simpa using hg₁) (by simpa using hg₂) hlt
    simp only [List.getElem_range] at hrel
    exact hrel _ hm₁ _ hm₂
  · have hrel := List.pairwise_iff_getElem.mp hp g₂ g₁ (by simpa using hg₂) (by simpa using hg₁) hlt
    simp only [List.getElem_range] at hrel
    exact Ne.symm (hrel _ hm₂ _ hm₁)

end Obend.Hardware.ArrayKernel
