module
public import Obend.Hardware.Gpu.CollectiveHierarchy
@[expose] public section
namespace Obend.Hardware.Gpu.CollectiveWork
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
set_option autoImplicit false

/-- Logical source work: one unit per load, scalar instruction, or store per
logical lane. Physical barriers and instruction lowering have separate costs. -/
def phaseWork (ph : Phase) : Nat :=
  ph.lanes * (ph.reads.length + ph.code.length + ph.writes.length)

def work (phases : List Phase) : Nat := (phases.map phaseWork).sum

theorem sum_scale (xs : List Nat) (c : Nat) :
    (xs.map (fun n => c*n)).sum = c*xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

/-- The actual builder's row widths form the geometric tree series. -/
theorem row_widths (depth : Nat) :
    ((List.range depth).map (fun k => 2^(depth-k-1))).sum = internalNodes depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    have hm : (List.range depth).map (fun k => 2^(depth+1-k-1)) =
        ((List.range depth).map (fun k => 2^(depth-k-1))).map (fun n => 2*n) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range.mp hk
      have he : depth+1-k-1 = (depth-k-1)+1 := by omega
      simp [he, Nat.pow_succ, Nat.mul_comm]
    rw [hm, sum_scale, ih]
    simp [internalNodes]

@[simp] theorem work_append (as bs : List Phase) : work (as++bs) = work as + work bs := by
  simp [work]

@[simp] theorem work_up (op : ReduceOp) (depth base : Nat) :
    work ((List.range depth).map fun k => upPhase op (2^(depth-k-1)) (base+k) (base+k+1)) =
      4*internalNodes depth := by
  simp only [work, List.map_map, phaseWork, upPhase, List.length_cons, List.length_nil]
  change ((List.range depth).map (fun k => 2^(depth-k-1)*4)).sum = _
  rw [show (fun k => 2^(depth-k-1)*4) = (fun k => 4*2^(depth-k-1)) by funext k; omega]
  simpa only [List.map_map, Function.comp_def, row_widths] using
    sum_scale ((List.range depth).map (fun k => 2^(depth-k-1))) 4

@[simp] theorem work_down (op : ReduceOp) (depth up down : Nat) :
    work ((List.range depth).reverse.map fun k =>
      downPhase op (2^(depth-k-1)) (up+k) (down+k+1) (down+k)) =
      5*internalNodes depth := by
  simp only [work, List.map_map, phaseWork, downPhase, List.length_cons, List.length_nil]
  change ((List.range depth).reverse.map (fun k => 2^(depth-k-1)*5)).sum = _
  rw [List.map_reverse, List.sum_reverse]
  rw [show (fun k => 2^(depth-k-1)*5) = (fun k => 5*2^(depth-k-1)) by funext k; omega]
  simpa only [List.map_map, Function.comp_def, row_widths] using
    sum_scale ((List.range depth).map (fun k => 2^(depth-k-1))) 5

theorem work_upsweep (op : ReduceOp) (tree : Trees) (src valid depth : Nat)
    (offset : Ix) (hv : valid ≤ 2^depth) :
    work (upsweep op tree src valid depth offset) = 2*2^depth+4*internalNodes depth := by
  simp only [upsweep, work_append, work_up]
  by_cases h : valid < 2^depth
  · simp [h, work, phaseWork, loadPhase, fillPhase]
    omega
  · have he : valid = 2^depth := by omega
    simp [h, he, work, phaseWork, loadPhase]
    omega

@[simp] theorem work_seed (op : ReduceOp) (dst : Nat) (seed : Option (Nat × Ix)) :
    work [seedPhase op dst seed] = 2 := by
  cases seed <;> simp [seedPhase, fillPhase, work, phaseWork]

/-- Exact work of the real emitted local schedule, including input load, padding,
root seed, and output. The inclusive mode adds one load/combine per valid word. -/
theorem scan_work (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst valid depth : Nat) (offset : Ix) (seed : Option (Nat × Ix))
    (hv : valid ≤ 2^depth) :
    work (scanPhases op mode tree src dst valid depth offset seed)+7 =
      11*2^depth + (2+2*mode.extra)*valid := by
  simp only [scanPhases, work_append, work_upsweep op tree src valid depth offset hv,
    work_seed, work_down]
  have hi := internalNodes_size depth
  cases mode <;> simp [work, phaseWork, storeScanPhase, ScanMode.extra] <;> omega

/-- Reduction is also linear in padded capacity; an empty segment explicitly
writes its identity and costs two source actions. -/
theorem reduce_work (op : ReduceOp) (tree : Trees) (src dst valid depth : Nat)
    (offset result : Ix) (hv : valid ≤ 2^depth) :
    if valid = 0 then work (reducePhases op tree src dst valid depth offset result) = 2
    else work (reducePhases op tree src dst valid depth offset result)+2 = 6*2^depth := by
  by_cases hz : valid = 0
  · simp [hz, reducePhases, work, phaseWork]
  · simp only [hz, ↓reduceIte, reducePhases, beq_iff_eq, work_append,
      work_upsweep op tree src valid depth offset hv]
    have hi := internalNodes_size depth
    simp [work, phaseWork]
    omega
/-- Rounding a nonempty tile to a binary tree never doubles its capacity. -/
theorem tile_capacity (n : Nat) (hn : 0 < n) : 2^(tileDepth n) ≤ 2*n := by
  unfold tileDepth
  split
  · simp only [Nat.pow_zero]; omega
  · rename_i h
    have hz : n-1 ≠ 0 := by omega
    have hp : 2^(Nat.log2 (n-1)) ≤ n-1 := by
      apply Nat.le_of_not_gt
      intro hc
      have := (Nat.log2_lt hz).mpr hc
      omega
    rw [Nat.pow_succ]
    omega

/-- Work efficiency of each actual nonempty local scan, in source actions. -/
theorem scan_linear (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst valid : Nat) (offset : Ix) (seed : Option (Nat × Ix)) (hv : 0 < valid) :
    work (scanPhases op mode tree src dst valid (tileDepth valid) offset seed) ≤ 26*valid := by
  have he := scan_work op mode tree src dst valid (tileDepth valid) offset seed
    (CollectiveHierarchy.tileDepth_covers valid)
  have hp := tile_capacity valid hv
  cases mode <;> simp only [ScanMode.extra] at he <;> omega

/-- Empty reductions have constant work; every other local reduction has linear work. -/
theorem reduce_linear (op : ReduceOp) (tree : Trees) (src dst valid : Nat)
    (offset result : Ix) :
    work (reducePhases op tree src dst valid (tileDepth valid) offset result) ≤ 12*(max 1 valid) := by
  have he := reduce_work op tree src dst valid (tileDepth valid) offset result
    (CollectiveHierarchy.tileDepth_covers valid)
  by_cases hz : valid = 0
  · subst valid
    simp only [↓reduceIte] at he
    omega
  · simp only [hz, ↓reduceIte] at he
    have hp := tile_capacity valid (by omega)
    omega

end Obend.Hardware.Gpu.CollectiveWork
end
