module
/-
Array SOACs, following Futhark PLDI 2017 §2 (associative reduce and inclusive scan),
Accelerate's foldSeg (segment lengths), and NESL's flat segment descriptors. Both scan
modes preserve input length. Empty reductions return the identity, including empty
segments; empty scan segments emit nothing. Lift's separation of pattern and schedule
is retained: the descriptor does not prescribe a parallel implementation.

References: https://futhark-lang.org/publications/pldi17.pdf
https://hackage.haskell.org/package/accelerate/docs/Data-Array-Accelerate.html
https://www.cs.cmu.edu/~scandal/nesl.html
https://eprints.gla.ac.uk/146596/1/146596.pdf
-/
public import Std
@[expose] public section
namespace Obend.Hardware.ArrayHypergraph
set_option autoImplicit false
abbrev Word := BitVec 64
abbrev Vec := List Word

/-- Guard before the native Nat shift allocates an enormous intermediate. The raw
BitVec operation is mathematically zero for an oversized count but can panic natively. -/
def wordShl (x count : Word) : Word :=
  if count.toNat < 64 then x <<< count.toNat else 0#64

def wordShr (x count : Word) : Word :=
  if count.toNat < 64 then x >>> count.toNat else 0#64

@[simp] theorem wordShl_eq (x count : Word) : wordShl x count = x <<< count.toNat := by
  by_cases h : count.toNat < 64
  · simp [wordShl, h]
  · simp [wordShl, h, BitVec.shiftLeft_eq_zero (Nat.le_of_not_lt h)]

@[simp] theorem wordShr_eq (x count : Word) : wordShr x count = x >>> count.toNat := by
  by_cases h : count.toNat < 64
  · simp [wordShr, h]
  · simp [wordShr, h, BitVec.ushiftRight_eq_zero (Nat.le_of_not_lt h)]

/-- Exactly associative word monoids; floating point addition is deliberately absent. -/
inductive ReduceOp where
  | add | mul | band | bor
  deriving DecidableEq, Repr

def ReduceOp.combine : ReduceOp → Word → Word → Word
  | .add => (· + ·)
  | .mul => (· * ·)
  | .band => (· &&& ·)
  | .bor => (· ||| ·)

def ReduceOp.identity : ReduceOp → Word
  | .add | .bor => 0#64
  | .mul => 1#64
  | .band => BitVec.allOnes 64

theorem ReduceOp.assoc (op : ReduceOp) (a b c : Word) :
    op.combine (op.combine a b) c = op.combine a (op.combine b c) := by
  cases op
  · exact BitVec.add_assoc a b c
  · exact BitVec.mul_assoc a b c
  · exact BitVec.and_assoc a b c
  · exact BitVec.or_assoc a b c

@[simp] theorem ReduceOp.identity_left (op : ReduceOp) (a : Word) :
    op.combine op.identity a = a := by
  cases op
  · simp [ReduceOp.combine, ReduceOp.identity]
  · simp [ReduceOp.combine, ReduceOp.identity]
  · exact BitVec.allOnes_and
  · simp [ReduceOp.combine, ReduceOp.identity]

@[simp] theorem ReduceOp.identity_right (op : ReduceOp) (a : Word) :
    op.combine a op.identity = a := by
  cases op
  · simp [ReduceOp.combine, ReduceOp.identity]
  · simp [ReduceOp.combine, ReduceOp.identity]
  · exact BitVec.and_allOnes
  · simp [ReduceOp.combine, ReduceOp.identity]

inductive ScanMode where
  | inclusive | exclusive
  deriving DecidableEq, Repr

def ScanMode.extra : ScanMode → Nat
  | .inclusive => 1
  | .exclusive => 0

/-- Static segment lengths, including zero lengths, preserve empty segments. -/
inductive FoldShape where
  | reduce (n : Nat)
  | scan (n : Nat) (mode : ScanMode)
  | segReduce (lengths : List Nat)
  | segScan (lengths : List Nat) (mode : ScanMode)
  deriving DecidableEq, Repr

def FoldShape.inputLen : FoldShape → Nat
  | .reduce n | .scan n _ => n
  | .segReduce ls | .segScan ls _ => ls.sum

/-- A result is the fold of a contiguous input interval `(start, length)`. -/
def segmentRanges (scan : Option ScanMode) : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | start, n :: ns =>
    (match scan with
     | none => [(start, n)]
     | some mode => (List.range n).map fun i => (start, i + mode.extra)) ++
    segmentRanges scan (start + n) ns

def FoldShape.ranges : FoldShape → List (Nat × Nat)
  | .reduce n => [(0, n)]
  | .scan n mode => (List.range n).map fun i => (0, i + mode.extra)
  | .segReduce ns => segmentRanges none 0 ns
  | .segScan ns mode => segmentRanges (some mode) 0 ns

def FoldShape.outLen (shape : FoldShape) : Nat := shape.ranges.length

theorem segmentRanges_bound (mode : Option ScanMode) (ns : List Nat) (start : Nat)
    (r : Nat × Nat) (hr : r ∈ segmentRanges mode start ns) :
    start ≤ r.1 ∧ r.1 + r.2 ≤ start + ns.sum := by
  induction ns generalizing start with
  | nil => simp [segmentRanges] at hr
  | cons n ns ih =>
    simp only [segmentRanges, List.mem_append] at hr
    rcases hr with hr | hr
    · cases mode with
      | none => simp only [List.mem_singleton] at hr; subst r; simp
      | some mode =>
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
        have hi' := List.mem_range.mp hi
        cases mode <;> simp [ScanMode.extra] <;> omega
    · have h := ih (start + n) hr
      simp only [List.sum_cons]
      constructor <;> omega

theorem FoldShape.ranges_bound (shape : FoldShape) (r : Nat × Nat) (hr : r ∈ shape.ranges) :
    r.1 + r.2 ≤ shape.inputLen := by
  cases shape with
  | reduce n => simp [FoldShape.ranges] at hr; subst r; simp [FoldShape.inputLen]
  | scan n mode =>
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hi' := List.mem_range.mp hi
    cases mode <;> simp [FoldShape.inputLen, ScanMode.extra] <;> omega
  | segReduce ns => simpa [FoldShape.inputLen] using (segmentRanges_bound none ns 0 r hr).2
  | segScan ns mode => simpa [FoldShape.inputLen] using (segmentRanges_bound (some mode) ns 0 r hr).2

/-- Left fold in index order. The initial accumulator is explicit for chunk composition. -/
def foldRange (op : ReduceOp) (read : Nat → Word) (start len : Nat) (init : Word) : Word :=
  (List.range' start len).foldl (fun acc i => op.combine acc (read i)) init

theorem foldRange_add (op : ReduceOp) (read : Nat → Word) (start a b : Nat) (init : Word) :
    foldRange op read start (a + b) init =
      foldRange op read (start + a) b (foldRange op read start a init) := by
  unfold foldRange
  rw [← List.range'_append_1, List.foldl_append]

theorem foldRange_congr (op : ReduceOp) (read read' : Nat → Word) (start len : Nat) (init : Word)
    (h : ∀ i, start ≤ i → i < start + len → read i = read' i) :
    foldRange op read start len init = foldRange op read' start len init := by
  have hm : (List.range' start len).map read = (List.range' start len).map read' := by
    apply List.map_congr_left
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hi
    apply h <;> omega
  simpa [List.foldl_map, foldRange] using congrArg (List.foldl op.combine init) hm

/-- Reference semantics, independent of the cached execution strategy. -/
def evalFold (op : ReduceOp) (shape : FoldShape) (read : Nat → Word) : Vec :=
  shape.ranges.map fun r => foldRange op read r.1 r.2 op.identity

/-- Reuse the previous prefix when the next interval extends it. Generated scan ranges
extend by one, so Array reads and arithmetic are linear in the input and output sizes.
A segment boundary resets the accumulator. This also works for arbitrary range lists. -/
def foldRangesCached (op : ReduceOp) (read : Nat → Word) :
    List (Nat × Nat) → Nat → Nat → Word → Vec
  | [], _, _, _ => []
  | (start, len) :: rs, prevStart, prevLen, prev =>
    let value := if start == prevStart && prevLen ≤ len then
      foldRange op read (start + prevLen) (len - prevLen) prev
      else foldRange op read start len op.identity
    value :: foldRangesCached op read rs start len value

theorem foldRangesCached_eq (op : ReduceOp) (read : Nat → Word) (rs : List (Nat × Nat))
    (start len : Nat) (prev : Word) (hprev : prev = foldRange op read start len op.identity) :
    foldRangesCached op read rs start len prev =
      rs.map (fun r => foldRange op read r.1 r.2 op.identity) := by
  induction rs generalizing start len prev with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨s, n⟩
    simp only [foldRangesCached, List.map_cons]
    have hv : (if s == start && len ≤ n then foldRange op read (s + len) (n - len) prev
        else foldRange op read s n op.identity) = foldRange op read s n op.identity := by
      split
      · rename_i h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        rw [hprev, ← h.1, ← foldRange_add, Nat.add_sub_of_le h.2]
      · rfl
    rw [hv, ih s n _ rfl]

/-- Tail-recursive execution with an owned Array accumulator; `push` reuses its storage.
The list specification above is only for proof, not the executable evaluator. -/
def foldRangesCachedArr (op : ReduceOp) (read : Nat → Word) :
    List (Nat × Nat) → Nat → Nat → Word → Array Word → Array Word
  | [], _, _, _, out => out
  | (start, len) :: rs, prevStart, prevLen, prev, out =>
    let value := if start == prevStart && prevLen ≤ len then
      foldRange op read (start + prevLen) (len - prevLen) prev
      else foldRange op read start len op.identity
    foldRangesCachedArr op read rs start len value (out.push value)

theorem foldRangesCachedArr_toList (op : ReduceOp) (read : Nat → Word) (rs : List (Nat × Nat))
    (start len : Nat) (prev : Word) (out : Array Word) :
    (foldRangesCachedArr op read rs start len prev out).toList =
      out.toList ++ foldRangesCached op read rs start len prev := by
  induction rs generalizing start len prev out with
  | nil => simp [foldRangesCachedArr, foldRangesCached]
  | cons r rs ih =>
    rcases r with ⟨s, n⟩
    simp [foldRangesCachedArr, foldRangesCached, ih, List.append_assoc]

def evalFoldExec (op : ReduceOp) (shape : FoldShape) (read : Nat → Word) : Array Word :=
  foldRangesCachedArr op read shape.ranges 0 0 op.identity #[]

theorem evalFoldExec_toList (op : ReduceOp) (shape : FoldShape) (read : Nat → Word) :
    (evalFoldExec op shape read).toList = evalFold op shape read := by
  simp only [evalFoldExec, foldRangesCachedArr_toList, List.nil_append, evalFold]
  exact foldRangesCached_eq op read shape.ranges 0 0 op.identity rfl

theorem foldRange_succ (op : ReduceOp) (read : Nat → Word) (start n : Nat) (init : Word) :
    foldRange op read start (n + 1) init =
      op.combine (foldRange op read start n init) (read (start + n)) := by
  rw [foldRange_add]
  simp [foldRange]

/-- The scan loop executed by one invocation, with an explicit loop index and accumulator. -/
def scanRange (op : ReduceOp) (mode : ScanMode) (read : Nat → Word) (start : Nat) :
    Nat → Nat → Word → Vec
  | _, 0, _ => []
  | i, n + 1, acc =>
    let next := op.combine acc (read (start + i))
    (match mode with | .inclusive => next | .exclusive => acc) ::
      scanRange op mode read start (i + 1) n next

theorem scanRange_eq (op : ReduceOp) (mode : ScanMode) (read : Nat → Word) (start i n : Nat)
    (acc : Word) (ha : acc = foldRange op read start i op.identity) :
    scanRange op mode read start i n acc =
      (List.range' i n).map (fun j => foldRange op read start (j + mode.extra) op.identity) := by
  induction n generalizing i acc with
  | zero => rfl
  | succ n ih =>
    simp only [scanRange, List.range'_succ, List.map_cons]
    have hn : op.combine acc (read (start + i)) = foldRange op read start (i + 1) op.identity := by
      rw [ha, foldRange_succ]
    rw [ih (i + 1) _ hn]
    cases mode <;> simp [ScanMode.extra, ha, foldRange_succ]

theorem flatten_map_singletons (xs : List Nat) (f : Nat → Word) :
    (xs.map (fun i => [f i])).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem map_range_getD (xs : Vec) (n : Nat) (hn : n = xs.length) :
    (List.range n).map (fun i => xs.getD i 0#64) = xs := by
  subst n
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- Each segment is assigned one invocation. The sequential-segment GPU schedule is
linear work and has parallelism across segments, but none within one segment. -/
def segmentValues (op : ReduceOp) (mode : Option ScanMode) (read : Nat → Word) :
    Nat → List Nat → List Vec
  | _, [] => []
  | start, n :: ns =>
    (match mode with
      | none => [foldRange op read start n op.identity]
      | some m => scanRange op m read start 0 n op.identity) ::
      segmentValues op mode read (start + n) ns

theorem segmentValues_flatten (op : ReduceOp) (mode : Option ScanMode) (read : Nat → Word)
    (ns : List Nat) (start : Nat) :
    (segmentValues op mode read start ns).flatten =
      (segmentRanges mode start ns).map (fun r => foldRange op read r.1 r.2 op.identity) := by
  induction ns generalizing start with
  | nil => rfl
  | cons n ns ih =>
    cases mode with
    | none => simp [segmentValues, segmentRanges, ih]
    | some m =>
      rw [segmentValues, List.flatten_cons, ih, scanRange_eq op m read start 0 n op.identity rfl]
      simp [segmentRanges, List.map_map, List.range_eq_range']

def FoldShape.segments : FoldShape → List Nat
  | .reduce n | .scan n _ => [n]
  | .segReduce ns | .segScan ns _ => ns

def FoldShape.mode : FoldShape → Option ScanMode
  | .reduce _ | .segReduce _ => none
  | .scan _ m | .segScan _ m => some m

/-- Invocation `t` writes the `t`th segment vector, at the sum of prior vectors'
lengths. Thus ranges are disjoint and every output is written exactly once. -/
def foldThreadValues (op : ReduceOp) (shape : FoldShape) (read : Nat → Word) : List Vec :=
  segmentValues op shape.mode read 0 shape.segments

/-- Soundness of the sequential-segment invocation schedule, for every input function.
This is the bridge from the emitter's multi-store invocations to output-address semantics. -/
theorem foldThreadValues_flatten (op : ReduceOp) (shape : FoldShape) (read : Nat → Word) :
    (foldThreadValues op shape read).flatten = evalFold op shape read := by
  unfold foldThreadValues
  rw [segmentValues_flatten]
  cases shape <;> simp [FoldShape.mode, FoldShape.segments, FoldShape.ranges, segmentRanges, evalFold]

end Obend.Hardware.ArrayHypergraph
