module
/-
# Ordered monoid trees for GPU collectives

Blelloch, Prefix Sums and Their Applications (1993), §1.2, pp.39–44:
https://www.cs.cmu.edu/~guyb/papers/Ble93.pdf.
Sengupta, Harris and Garland, Efficient Parallel Scan Algorithms for GPUs (2008),
§§2–4: https://research.nvidia.com/sites/default/files/publications/nvr-2008-003.pdf.

Upsweep combines adjacent ordered subtrees; downsweep sends the parent's prefix
left and parent-prefix ⊕ left-total right. Commutativity is never used. Separate
materialized rows match ArrayKernel's snapshot-separated phases and require linear
storage/work across levels. The recursive value functions below are reference
invariants, not the executable evaluator: actual execution materializes each row
once using Array-backed maps (or the corresponding ArrayKernel phases).
-/
public import Obend.Hardware.ArrayFold
@[expose] public section
namespace Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.ArrayHypergraph
set_option autoImplicit false

/-- A left accumulator can be factored out because the operator is associative. -/
theorem foldRange_init (op : ReduceOp) (read : Nat → Word) (start len : Nat) (init : Word) :
    foldRange op read start len init = op.combine init (foldRange op read start len op.identity) := by
  induction len with
  | zero => simp [foldRange]
  | succ n ih =>
    rw [foldRange_succ, foldRange_succ, ih, op.assoc]

/-- Prefix/chunk composition, preserving operand order. This also supplies the
fix-up rule for a scan of chunk totals followed by local chunk scans. -/
theorem foldRange_compose (op : ReduceOp) (read : Nat → Word) (start a b : Nat) (init : Word) :
    op.combine (foldRange op read start a init)
      (foldRange op read (start+a) b op.identity) = foldRange op read start (a+b) init := by
  rw [foldRange_add]
  exact (foldRange_init op read (start+a) b (foldRange op read start a init)).symm

/-- One upsweep lane combines two adjacent entries of the preceding row. -/
def upStep (op : ReduceOp) (read : Nat → Word) (parent : Nat) : Word :=
  op.combine (read (2*parent)) (read (2*parent+1))

/-- One downsweep lane writes two entries in a separate child row. -/
def downLeft (prefixes : Nat → Word) (parent : Nat) : Word := prefixes parent

def downRight (op : ReduceOp) (totals prefixes : Nat → Word) (parent : Nat) : Word :=
  op.combine (prefixes parent) (totals (2*parent))

/-- The same two writes, indexed by child instead of parent. -/
def downStep (op : ReduceOp) (totals prefixes : Nat → Word) (child : Nat) : Word :=
  if child % 2 = 0 then downLeft prefixes (child/2) else downRight op totals prefixes (child/2)

@[simp] theorem downStep_even (op : ReduceOp) (totals prefixes : Nat → Word) (i : Nat) :
    downStep op totals prefixes (2*i) = downLeft prefixes i := by simp [downStep]

@[simp] theorem downStep_odd (op : ReduceOp) (totals prefixes : Nat → Word) (i : Nat) :
    downStep op totals prefixes (2*i+1) = downRight op totals prefixes i := by
  have hd : (2*i+1)/2 = i := by omega
  simp [downStep, hd]

/-- Efficient row executors: no expression closure is evaluated recursively per
output, and the arrays supply constant-time reads. -/
def upRow (op : ReduceOp) (parents : Nat) (input : Array Word) : Array Word :=
  (Array.range parents).map fun i => upStep op (input.getD · op.identity) i

def downRow (op : ReduceOp) (parents : Nat) (totals prefixes : Array Word) : Array Word :=
  (Array.range (2*parents)).map fun i => downStep op (totals.getD · op.identity) (prefixes.getD · op.identity) i

theorem upRow_read (op : ReduceOp) (parents : Nat) (input : Array Word) (i : Nat) (hi : i < parents) :
    (upRow op parents input).getD i op.identity = upStep op (input.getD · op.identity) i := by
  simp [upRow, Array.getD_eq_getD_getElem?, hi]

theorem downRow_read (op : ReduceOp) (parents : Nat) (totals prefixes : Array Word)
    (i : Nat) (hi : i < 2*parents) :
    (downRow op parents totals prefixes).getD i op.identity =
      downStep op (totals.getD · op.identity) (prefixes.getD · op.identity) i := by
  simp [downRow, Array.getD_eq_getD_getElem?, hi]

/-- Reference value of one materialized upsweep row entry. -/
def upValue (op : ReduceOp) (read : Nat → Word) (start : Nat) : Nat → Nat → Word
  | 0, i => read (start+i)
  | level+1, i => upStep op (upValue op read start level) i

theorem upValue_eq_fold (op : ReduceOp) (read : Nat → Word) (start level i : Nat) :
    upValue op read start level i = foldRange op read (start+i*2^level) (2^level) op.identity := by
  induction level generalizing i with
  | zero => simp [upValue, foldRange]
  | succ level ih =>
    simp only [upValue, upStep, ih]
    have hright : start+(2*i+1)*2^level = (start+(2*i)*2^level)+2^level := by
      simp [Nat.add_mul, Nat.add_assoc]
    rw [hright, foldRange_compose]
    have hstart : start+(2*i)*2^level = start+i*2^(level+1) := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
    have hlen : 2^level+2^level = 2^(level+1) := by simp [Nat.pow_succ]; omega
    rw [hstart, hlen]

/-- One level of the upsweep invariant, suitable for proving a concrete phase
whose readback agrees with the preceding row. -/
theorem upStep_fold (op : ReduceOp) (read : Nat → Word) (start level : Nat)
    (row : Nat → Word) (i : Nat)
    (hl : row (2*i) = foldRange op read (start+(2*i)*2^level) (2^level) op.identity)
    (hr : row (2*i+1) = foldRange op read (start+(2*i+1)*2^level) (2^level) op.identity) :
    upStep op row i = foldRange op read (start+i*2^(level+1)) (2^(level+1)) op.identity := by
  rw [← upValue_eq_fold]
  simp only [upValue, upStep, hl, hr, upValue_eq_fold]

/-- One level of the downsweep invariant. The only hypotheses concern readback
of the preceding rows, established by upsweep and earlier downsweep phases. -/
theorem downStep_fold (op : ReduceOp) (read : Nat → Word) (start level parents : Nat)
    (totals prefixes : Nat → Word) (init : Word)
    (ht : ∀ i, i < 2*parents → totals i = foldRange op read (start+i*2^level) (2^level) op.identity)
    (hp : ∀ i, i < parents → prefixes i = foldRange op read start (i*2^(level+1)) init)
    (i : Nat) (hi : i < 2*parents) :
    downStep op totals prefixes i = foldRange op read start (i*2^level) init := by
  have hparent : i/2 < parents := by omega
  have hleft : 2*(i/2) < 2*parents := by omega
  have hmod : i%2 < 2 := Nat.mod_lt i (by decide)
  unfold downStep downLeft downRight
  split
  · rename_i heven
    rw [hp _ hparent]
    have he : i = 2*(i/2) := by omega
    congr 1
    rw [he]
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · rename_i hodd
    have ho : i = 2*(i/2)+1 := by omega
    rw [hp _ hparent, ht _ hleft]
    have hstart : start+(2*(i/2))*2^level = start+(i/2)*2^(level+1) := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hstart, foldRange_compose]
    congr 1
    calc
      (i/2)*2^(level+1)+2^level = (2*(i/2)+1)*2^level := by
        simp [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = i*2^level := by rw [← ho]

/-- Reference of the root-to-leaf row sequence. Actual execution retains upsweep
rows and materializes each downsweep row once. -/
def downValue (op : ReduceOp) (read : Nat → Word) (start : Nat) :
    Nat → (Nat → Word) → Nat → Word
  | 0, prefixes => prefixes
  | level+1, prefixes => downValue op read start level (downStep op (upValue op read start level) prefixes)

theorem downValue_eq_fold (op : ReduceOp) (read : Nat → Word) (start level parents : Nat)
    (prefixes : Nat → Word) (init : Word)
    (hp : ∀ i, i < parents → prefixes i = foldRange op read start (i*2^level) init)
    (i : Nat) (hi : i < parents*2^level) :
    downValue op read start level prefixes i = foldRange op read start i init := by
  induction level generalizing parents prefixes i with
  | zero => simpa [downValue] using hp i (by simpa using hi)
  | succ level ih =>
    apply ih (2*parents) (downStep op (upValue op read start level) prefixes)
    · intro j hj
      exact downStep_fold op read start level parents _ prefixes init
        (fun k _ => upValue_eq_fold op read start level k) hp j hj
    · simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hi

/-- Complete tree scan: root starts at the input accumulator; inclusive mode
combines the leaf value after the exclusive prefixes. -/
def scanValue (op : ReduceOp) (read : Nat → Word) (start level : Nat) (init : Word)
    (mode : ScanMode) (i : Nat) : Word :=
  let prefixes := downValue op read start level (fun _ => init) i
  match mode with
  | .exclusive => prefixes
  | .inclusive => op.combine prefixes (read (start+i))

theorem scanValue_eq_fold (op : ReduceOp) (read : Nat → Word) (start level : Nat)
    (init : Word) (mode : ScanMode) (i : Nat) (hi : i < 2^level) :
    scanValue op read start level init mode i = foldRange op read start (i+mode.extra) init := by
  have hp : ∀ j, j < 1 → (fun _ : Nat => init) j = foldRange op read start (j*2^level) init := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simp [foldRange]
  have hd := downValue_eq_fold op read start level 1 (fun _ => init) init hp i (by simpa using hi)
  cases mode <;> simp [scanValue, hd, ScanMode.extra, foldRange_succ]

/-- One combine at every internal node in either pass. These are structural
work/space bounds for the tree schedule, not benchmark counts. -/
def internalNodes : Nat → Nat
  | 0 => 0
  | level+1 => 2*internalNodes level+1

theorem internalNodes_size (level : Nat) : internalNodes level+1 = 2^level := by
  induction level with
  | zero => rfl
  | succ level ih =>
    simp only [internalNodes, Nat.pow_succ]
    omega

/-- Exclusive scan uses one combine per internal node in each sweep. -/
theorem exclusive_work (level : Nat) : 2*internalNodes level+2 = 2*(2^level) := by
  have := internalNodes_size level
  omega

/-- Keeping every compact row costs strictly less than twice the leaf capacity. -/
theorem compact_rows_space (level : Nat) : 2^level+internalNodes level < 2*(2^level) := by
  have := internalNodes_size level
  omega

/-- Retaining the full upsweep tree and full mirrored prefix tree (including
both roots and both leaf rows) uses exactly `4*N-2` words. -/
theorem both_trees_storage (level : Nat) :
    2*(2^level+internalNodes level)+2 = 4*(2^level) := by
  have := internalNodes_size level
  omega

/-- Compact row widths, in descending order. Upsweep executes this list and
 downsweep executes its reverse. Each width denotes parent lanes, with one
 upsweep output or two downsweep outputs per lane. -/
def sweepWidths : Nat → List Nat
  | 0 => []
  | level+1 => 2^level :: sweepWidths level

theorem sweepWidths_length (level : Nat) : (sweepWidths level).length = level := by
  induction level with
  | zero => rfl
  | succ level ih => simp [sweepWidths, ih]

theorem sweepWidths_sum (level : Nat) : (sweepWidths level).sum = internalNodes level := by
  induction level with
  | zero => rfl
  | succ level ih =>
    simp only [sweepWidths, List.sum_cons, ih, internalNodes]
    have := internalNodes_size level
    omega

/-- Exact output-action count for materializing every upsweep and downsweep
row: one up write and two down writes per parent. The root initialization,
leaf load, and optional inclusive finalization are separate linear passes. -/
theorem sweep_output_actions (level : Nat) :
    ((sweepWidths level).map (fun parents => 3*parents)).sum + 3 = 3*(2^level) := by
  have hs : ((sweepWidths level).map (fun parents => 3*parents)).sum =
      3*(sweepWidths level).sum := by
    induction sweepWidths level with
    | nil => rfl
    | cons n ns ih => simp [ih, Nat.mul_add]
  rw [hs, sweepWidths_sum]
  have := internalNodes_size level
  omega

/-- The two sweeps have exactly twice the binary tree depth in synchronized
row phases. This is a count of materialized phases, not recursive evaluator cost. -/
theorem sweep_depth (level : Nat) :
    (sweepWidths level ++ (sweepWidths level).reverse).length = 2*level := by
  simp [sweepWidths_length, Nat.two_mul]

/-- Identity padding is explicit and supports every input length, including zero. -/
def paddedRead (op : ReduceOp) (read : Nat → Word) (start len : Nat) (i : Nat) : Word :=
  if i < len then read (start+i) else op.identity

theorem foldRange_shift (op : ReduceOp) (read : Nat → Word) (offset start len : Nat) (init : Word) :
    foldRange op (fun i => read (offset+i)) start len init =
      foldRange op read (offset+start) len init := by
  induction len with
  | zero => rfl
  | succ n ih => simp only [foldRange_succ, ih, Nat.add_assoc]

theorem padded_prefix (op : ReduceOp) (read : Nat → Word) (start len count : Nat)
    (init : Word) (h : count ≤ len) :
    foldRange op (paddedRead op read start len) 0 count init = foldRange op read start count init := by
  rw [foldRange_congr op _ (fun i => read (start+i)) 0 count init
    (by intro i _ hi; simp [paddedRead, show i < len by omega])]
  simpa using foldRange_shift op read start 0 count init

theorem foldRange_identity (op : ReduceOp) (start len : Nat) (init : Word) :
    foldRange op (fun _ => op.identity) start len init = init := by
  induction len with
  | zero => rfl
  | succ n ih => simp [foldRange_succ, ih]

theorem padded_total (op : ReduceOp) (read : Nat → Word) (start len extent : Nat)
    (init : Word) (h : len ≤ extent) :
    foldRange op (paddedRead op read start len) 0 extent init = foldRange op read start len init := by
  rw [show extent = len+(extent-len) by omega, foldRange_add, padded_prefix op read start len len init (Nat.le_refl _)]
  rw [foldRange_congr op _ (fun _ => op.identity) (0+len) (extent-len) _
    (by intro i hi _; simp [paddedRead, show ¬i<len by omega])]
  exact foldRange_identity op _ _ _

theorem padded_scan (op : ReduceOp) (read : Nat → Word) (start len level : Nat)
    (mode : ScanMode) (i : Nat) (hsize : len ≤ 2^level) (hi : i < len) :
    scanValue op (paddedRead op read start len) 0 level op.identity mode i =
      foldRange op read start (i+mode.extra) op.identity := by
  rw [scanValue_eq_fold op _ 0 level op.identity mode i (by omega)]
  apply padded_prefix
  cases mode <;> simp [ScanMode.extra] <;> omega

theorem padded_reduce (op : ReduceOp) (read : Nat → Word) (start len level : Nat)
    (hsize : len ≤ 2^level) :
    upValue op (paddedRead op read start len) 0 level 0 = foldRange op read start len op.identity := by
  rw [upValue_eq_fold]
  simpa using padded_total op read start len (2^level) op.identity hsize

/-- The fixed-up result of any chunk prefix and its local scan is the global
prefix. Chunk hierarchy can repeat this law at every level. -/
theorem chunk_fixup (op : ReduceOp) (read : Nat → Word) (start chunkOffset i : Nat)
    (init : Word) (mode : ScanMode) :
    op.combine (foldRange op read start chunkOffset init)
      (foldRange op read (start+chunkOffset) (i+mode.extra) op.identity) =
      foldRange op read start (chunkOffset+i+mode.extra) init := by
  simpa [Nat.add_assoc] using foldRange_compose op read start chunkOffset (i+mode.extra) init

/-- Ordered tree results for arbitrary descriptor lengths. This reference is
used only in the proof bridge; the executable schedule materializes rows once. -/
def segmentResults (op : ReduceOp) (read : Nat → Word) (depth : Nat → Nat)
    (mode : Option ScanMode) : Nat → List Nat → List Vec
  | _, [] => []
  | start, len::lengths =>
      (match mode with
      | none => [upValue op (paddedRead op read start len) 0 (depth len) 0]
      | some m => (List.range len).map fun i =>
          scanValue op (paddedRead op read start len) 0 (depth len) op.identity m i) ::
      segmentResults op read depth mode (start+len) lengths

theorem segmentResults_flatten (op : ReduceOp) (read : Nat → Word) (depth : Nat → Nat)
    (mode : Option ScanMode) (start : Nat) (lengths : List Nat)
    (hdepth : ∀ n ∈ lengths, n ≤ 2^(depth n)) :
    (segmentResults op read depth mode start lengths).flatten =
      (segmentRanges mode start lengths).map (fun r => foldRange op read r.1 r.2 op.identity) := by
  induction lengths generalizing start with
  | nil => rfl
  | cons n ns ih =>
    have hn := hdepth n (by simp)
    have hs : ∀ k ∈ ns, k ≤ 2^(depth k) := fun k hk => hdepth k (by simp [hk])
    cases mode with
    | none =>
      simp [segmentResults, segmentRanges, padded_reduce op read start n (depth n) hn, ih _ hs]
    | some mode =>
      simp only [segmentResults, List.flatten_cons, segmentRanges, List.map_append, List.map_map, ih _ hs]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact padded_scan op read start n (depth n) mode i hn (List.mem_range.mp hi)

/-- The complete reduction/scan value bridge to the existing array semantics,
including leading, interior and trailing empty segments. -/
theorem foldShape_tree (op : ReduceOp) (shape : FoldShape) (read : Nat → Word) (depth : Nat → Nat)
    (hdepth : ∀ n ∈ shape.segments, n ≤ 2^(depth n)) :
    (segmentResults op read depth shape.mode 0 shape.segments).flatten = evalFold op shape read := by
  rw [segmentResults_flatten op read depth shape.mode 0 shape.segments hdepth]
  cases shape <;> simp [FoldShape.mode, FoldShape.segments, FoldShape.ranges, segmentRanges, evalFold]

end Obend.Hardware.Gpu.CollectiveTree
end
