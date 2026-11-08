module
public import Obend.Hardware.Gpu.Ntt
public import Obend.Hardware.Gpu.PhaseSemantics
@[expose] public section

/-! Concrete index and invocation semantics for the NTT builder's tile batching.
The transformed phases below are definitionally the phases in `batchTiles`.
Memory relations concern source reads; register arithmetic is unchanged. -/
namespace Obend.Hardware.Gpu.NttBatchCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt.BlockNtt Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

theorem substitute_eval (group lane : Ix) (i : Ix) (g l : Nat) :
    (substitute group lane i).eval g l = i.eval (group.eval g l) (lane.eval g l) := by
  induction i <;> simp_all [substitute,Ix.eval]

/-- Shared rows carry a tile coordinate; device and constant rows do not. -/
def tileIndex (stride tile array i : Nat) : Nat :=
  if array == 2 || array == 3 then i+tile*stride else i

def batchIndex (stride k lanes array : Nat) (i : Ix) : Ix :=
  let tile : Ix := .div .lane lanes
  let group : Ix := .add (.mul .group (.lit k)) tile
  let lane : Ix := .mod .lane lanes
  let i := substitute group lane i
  if array == 2 || array == 3 then .add i (.mul tile (.lit stride)) else i

def batchPhase (stride k : Nat) (ph : Phase) : Phase :=
  { ph with lanes := ph.lanes*k
            reads := ph.reads.map fun r => {r with index := batchIndex stride k ph.lanes r.array r.index}
            writes := ph.writes.map fun w => {w with index := batchIndex stride k ph.lanes w.array w.index} }

theorem batchTiles_phases (stride : Nat) (d : Dispatch) :
    (batchTiles stride d).phases = d.phases.map (batchPhase stride (packing d)) := rfl

theorem batchTiles_groups (stride : Nat) (d : Dispatch) :
    (batchTiles stride d).groups = d.groups / packing d := rfl

theorem batchIndex_eval (stride k lanes array : Nat) (i : Ix) (g l : Nat) :
    (batchIndex stride k lanes array i).eval g l =
      tileIndex stride (l/lanes) array (i.eval (g*k+l/lanes) (l%lanes)) := by
  unfold batchIndex tileIndex
  split <;> simp [Ix.eval,substitute_eval]

theorem batchIndex_eval_tile (stride k lanes array : Nat) (i : Ix)
    (g tile l : Nat) (hl : l < lanes) :
    (batchIndex stride k lanes array i).eval g (tile*lanes+l) =
      tileIndex stride tile array (i.eval (g*k+tile) l) := by
  rw [batchIndex_eval]
  have hd : (tile*lanes+l)/lanes = tile := by
    rw [Nat.mul_comm tile lanes,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hl,Nat.add_zero]
  simp [hd,Nat.mul_add_mod_of_lt hl]

theorem packing_pos (d : Dispatch) : 0 < packing d := by
  unfold packing
  dsimp only
  split <;> omega

theorem packing_divides (d : Dispatch) : packing d ∣ d.groups := by
  unfold packing
  dsimp only
  split
  · rename_i h
    exact Nat.dvd_of_mod_eq_zero (by simpa using h)
  · exact Nat.one_dvd _

/-- Every packed invocation names an existing original group. -/
theorem packed_group_bound (d : Dispatch) (g tile : Nat)
    (hg : g < d.groups / packing d) (ht : tile < packing d) :
    g*packing d+tile < d.groups := by
  have h1 := Nat.mul_le_mul_right (packing d) (Nat.succ_le_of_lt hg)
  have h2 := Nat.div_mul_le_self d.groups (packing d)
  simp only [Nat.succ_mul] at h1
  omega

theorem packed_lane_bound (lanes k tile l : Nat) (ht : tile < k) (hl : l < lanes) :
    tile*lanes+l < lanes*k := by
  have h := Nat.mul_le_mul_right lanes (Nat.succ_le_of_lt ht)
  simp only [Nat.succ_mul] at h
  rw [Nat.mul_comm lanes k]
  omega

def tileWrite (stride tile : Nat) (w : Nat × Nat × Word) : Nat × Nat × Word :=
  (w.1,tileIndex stride tile w.1 w.2.1,w.2.2)

/-- Agreement on exactly the loads of one original invocation is sufficient;
there is no assumption about its arithmetic result or stored outputs. -/
def TileReads (stride k : Nat) (ph : Phase) (g tile l : Nat)
    (source target : Memory) : Prop :=
  ∀ r ∈ ph.reads,
    valueAt target r.array (tileIndex stride tile r.array (r.index.eval (g*k+tile) l)) =
      valueAt source r.array (r.index.eval (g*k+tile) l)

theorem loadRegisters_batch (stride k : Nat) (ph : Phase) (g tile l : Nat)
    (hl : l < ph.lanes) (source target : Memory)
    (hr : TileReads stride k ph g tile l source target) :
    loadRegisters (batchPhase stride k ph) target g (tile*ph.lanes+l) =
      loadRegisters ph source (g*k+tile) l := by
  unfold loadRegisters batchPhase
  simp only [List.foldl_map,batchIndex_eval_tile stride k ph.lanes _ _ g tile l hl]
  have hreads : ∀ reads : List Read,
      (∀ r ∈ reads, valueAt target r.array (tileIndex stride tile r.array (r.index.eval (g*k+tile) l)) =
        valueAt source r.array (r.index.eval (g*k+tile) l)) →
      ∀ regs : Registers,
      reads.foldl (fun regs r => regs.insert r.dst
        (valueAt target r.array (tileIndex stride tile r.array (r.index.eval (g*k+tile) l)))) regs =
      reads.foldl (fun regs r => regs.insert r.dst (valueAt source r.array (r.index.eval (g*k+tile) l))) regs := by
    intro reads h
    induction reads with
    | nil => intro regs; rfl
    | cons r rs ih =>
      intro regs
      simp only [List.foldl_cons]
      rw [h r (by simp)]
      exact ih (fun r hr => h r (by simp [hr])) _
  exact hreads ph.reads hr ∅

/-- Actual per-invocation register execution is unchanged by batching, and its
scatter is exactly the original scatter with the shared tile offset attached. -/
theorem laneWrites_batch (stride k : Nat) (ph : Phase) (g tile l : Nat)
    (hl : l < ph.lanes) (source target : Memory)
    (hr : TileReads stride k ph g tile l source target) :
    laneWrites (batchPhase stride k ph) target g (tile*ph.lanes+l) =
      (laneWrites ph source (g*k+tile) l).map (tileWrite stride tile) := by
  have hload := loadRegisters_batch stride k ph g tile l hl source target hr
  unfold laneWrites
  rw [hload]
  simp only [batchPhase,List.map_map,Function.comp_def,tileWrite]
  apply List.map_congr_left
  intro w _
  rw [batchIndex_eval_tile stride k ph.lanes w.array w.index g tile l hl]


/-- Packed lane order is tile-major, preserving each tile's original lane order. -/
theorem range_tiles (lanes k : Nat) :
    List.range (lanes*k) =
      (List.range k).flatMap (fun tile => (List.range lanes).map (fun l => tile*lanes+l)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,List.range_add,ih,List.range_succ,List.flatMap_append]
    simp [Nat.mul_comm]

/-- Exact complete scatter list of the transformed phase. The original tile
memories may differ in their shared rows; each is related only on accessed cells. -/
theorem phaseWrites_batch (stride k : Nat) (ph : Phase) (g : Nat)
    (source : Nat → Memory) (target : Memory)
    (hr : ∀ tile < k, ∀ l < ph.lanes, TileReads stride k ph g tile l (source tile) target) :
    phaseWrites (batchPhase stride k ph) target g =
      (List.range k).flatMap fun tile =>
        (phaseWrites ph (source tile) (g*k+tile)).map (tileWrite stride tile) := by
  change (List.range (ph.lanes*k)).flatMap _ = _
  rw [range_tiles,List.flatMap_assoc]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro tile ht
  change ((List.range ph.lanes).map (fun l => tile*ph.lanes+l)).flatMap _ = _
  rw [List.flatMap_map]
  simp only [phaseWrites,List.map_flatMap,List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro l hl
  exact laneWrites_batch stride k ph g tile l (List.mem_range.mp hl) _ target
    (hr tile (List.mem_range.mp ht) l (List.mem_range.mp hl))

/-- This is the actual phase evaluator, with the exact transformed writes. -/
theorem evalPhase_batch_trace (stride k : Nat) (ph : Phase) (g : Nat)
    (source : Nat → Memory) (target : Memory)
    (hr : ∀ tile < k, ∀ l < ph.lanes, TileReads stride k ph g tile l (source tile) target) :
    evalPhase (batchPhase stride k ph) g target =
      ((List.range k).flatMap fun tile =>
        (phaseWrites ph (source tile) (g*k+tile)).map (tileWrite stride tile)).foldl applyWrite target := by
  change (phaseWrites (batchPhase stride k ph) target g).foldl applyWrite target = _
  rw [phaseWrites_batch stride k ph g source target hr]

/-- A word stored by a checked batched phase is computed by precisely the
original tile's register program on its corresponding input cells. -/
theorem evalPhase_batch_value (p : Program) (stride k : Nat) (ph : Phase)
    (g tile l : Nat) (source target : Memory)
    (hg : Good p target) (hb : PhaseInBounds p (batchPhase stride k ph) g)
    (hn : ((batchPhase stride k ph).writeAddresses g).Nodup)
    (ht : tile < k) (hl : l < ph.lanes)
    (hr : TileReads stride k ph g tile l source target) (w : Write) (hw : w ∈ ph.writes) :
    valueAt (evalPhase (batchPhase stride k ph) g target) w.array
      (tileIndex stride tile w.array (w.index.eval (g*k+tile) l)) =
      (runRegisters ph.code (loadRegisters ph source (g*k+tile) l)).getD w.value 0#64 := by
  have h := evalPhase_value_written p (batchPhase stride k ph) target g (tile*ph.lanes+l)
    hg hb hn (packed_lane_bound ph.lanes k tile l ht hl)
    {w with index := batchIndex stride k ph.lanes w.array w.index}
    (List.mem_map.mpr ⟨w,hw,rfl⟩)
  have hload := loadRegisters_batch stride k ph g tile l hl source target hr
  have hcode : (batchPhase stride k ph).code = ph.code := rfl
  simpa only [batchIndex_eval_tile stride k ph.lanes w.array w.index g tile l hl,hload,hcode] using h


/-- Every original group has exactly its quotient/remainder packed coordinates. -/
theorem packed_group_split (d : Dispatch) (q : Nat) (hq : q < d.groups) :
    q/packing d < (batchTiles (tileSize d) d).groups ∧ q%packing d < packing d ∧
      (q/packing d)*packing d+q%packing d = q := by
  exact ⟨Nat.div_lt_div_of_lt_of_dvd (packing_divides d) hq,
    Nat.mod_lt q (packing_pos d),by simpa [Nat.mul_comm] using Nat.div_add_mod q (packing d)⟩

/-- The public builder's admitted phase provides all write-side proof premises. -/
theorem checked_batch_value (p : Program) (hc : p.check = .ok ())
    (stride : Nat) (d : Dispatch) (hd : batchTiles stride d ∈ p.dispatches)
    (ph : Phase) (hph : ph ∈ d.phases) (g tile l : Nat)
    (hg : g < (batchTiles stride d).groups) (ht : tile < packing d) (hl : l < ph.lanes)
    (source target : Memory) (hgood : Good p target)
    (hr : TileReads stride (packing d) ph g tile l source target)
    (w : Write) (hw : w ∈ ph.writes) :
    valueAt (evalPhase (batchPhase stride (packing d) ph) g target) w.array
      (tileIndex stride tile w.array (w.index.eval (g*packing d+tile) l)) =
      (runRegisters ph.code (loadRegisters ph source (g*packing d+tile) l)).getD w.value 0#64 := by
  have hm : batchPhase stride (packing d) ph ∈ (batchTiles stride d).phases := by
    rw [batchTiles_phases]
    exact List.mem_map.mpr ⟨ph,hph,rfl⟩
  obtain ⟨hb,hn⟩ := checkedPhase p hc _ hd g hg _ hm
  exact evalPhase_batch_value p stride (packing d) ph g tile l source target
    hgood hb hn ht hl hr w hw


/-- Canonical semantic view of one packed tile. The shared rows are projected
onto the tile's stride; device and constant rows retain their original storage. -/
def tileMemory (stride tile : Nat) (mem : Memory) : Memory :=
  (List.range mem.size).toArray.map fun a =>
    let row := mem.getD a #[]
    if a == 2 || a == 3 then
      (List.range stride).toArray.map fun i => row.getD (i+tile*stride) 0#64
    else row

theorem tileMemory_value (stride tile : Nat) (mem : Memory) (a i : Nat)
    (hi : a = 2 ∨ a = 3 → i < stride) :
    valueAt (tileMemory stride tile mem) a i = valueAt mem a (tileIndex stride tile a i) := by
  by_cases ha : a < mem.size
  · by_cases hs : a = 2 ∨ a = 3
    · have hb : (a == 2 || a == 3) = true := by simpa using hs
      simp [tileMemory,valueAt,tileIndex,Array.getD_eq_getD_getElem?,ha,hb,hs,hi hs]
    · have hb : (a == 2 || a == 3) = false := by simp_all
      simp [tileMemory,valueAt,tileIndex,Array.getD_eq_getD_getElem?,ha,hb,hs]
  · simp [tileMemory,valueAt,Array.getD_eq_getD_getElem?,ha]

theorem tileMemory_reads (stride k : Nat) (ph : Phase) (g tile l : Nat) (target : Memory)
    (hb : ∀ r ∈ ph.reads, r.array = 2 ∨ r.array = 3 → r.index.eval (g*k+tile) l < stride) :
    TileReads stride k ph g tile l (tileMemory stride tile target) target := by
  intro r hr
  exact (tileMemory_value stride tile target r.array _ (hb r hr)).symm

/-- No semantic-memory premise is needed when the original tile is read through
its canonical view; only the source's declared shared-index bounds remain. -/
theorem checked_batch_view_value (p : Program) (hc : p.check = .ok ())
    (stride : Nat) (d : Dispatch) (hd : batchTiles stride d ∈ p.dispatches)
    (ph : Phase) (hph : ph ∈ d.phases) (g tile l : Nat)
    (hg : g < (batchTiles stride d).groups) (ht : tile < packing d) (hl : l < ph.lanes)
    (target : Memory) (hgood : Good p target)
    (hreads : ∀ r ∈ ph.reads, r.array = 2 ∨ r.array = 3 →
      r.index.eval (g*packing d+tile) l < stride)
    (w : Write) (hw : w ∈ ph.writes) :
    valueAt (evalPhase (batchPhase stride (packing d) ph) g target) w.array
      (tileIndex stride tile w.array (w.index.eval (g*packing d+tile) l)) =
      (runRegisters ph.code (loadRegisters ph (tileMemory stride tile target)
        (g*packing d+tile) l)).getD w.value 0#64 :=
  checked_batch_value p hc stride d hd ph hph g tile l hg ht hl _ target hgood
    (tileMemory_reads stride (packing d) ph g tile l target hreads) w hw

end Obend.Hardware.Gpu.NttBatchCorrect
end
