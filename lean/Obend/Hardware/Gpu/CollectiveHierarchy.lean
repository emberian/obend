module
public import Obend.Hardware.Gpu.CollectiveBlock
@[expose] public section

/-! Mathematical composition of the actual chunk hierarchy. These definitions
name descriptor values and invariants; execution remains `CollectiveBlock.build`.
In particular, no second reduction or scan schedule is introduced here. -/
namespace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveBlock
set_option autoImplicit false

theorem segmentsFrom_length (start result : Nat) (ns : List Nat) :
    (segmentsFrom start result ns).length = ns.length := by
  induction ns generalizing start result with
  | nil => rfl
  | cons n ns ih => simp [segmentsFrom, ih]

theorem segmentChunks_length (tile start result len : Nat) :
    (segmentChunks tile start result len).length = (len+tile-1)/tile := by
  simp [segmentChunks]

/-- The descriptor at position j has the exact input offset and result slot
used by the source builder. -/
theorem segmentChunks_get (tile start result len j : Nat)
    (hj : j < (len+tile-1)/tile) :
    (segmentChunks tile start result len)[j]? =
      some ⟨start+j*tile,min tile (len-j*tile),result+j⟩ := by
  simp [segmentChunks, hj]

theorem chunksFrom_length (tile start result : Nat) (ns : List Nat) :
    (chunksFrom tile start result ns).length =
      (ns.map fun n => (n+tile-1)/tile).sum := by
  induction ns generalizing start result with
  | nil => rfl
  | cons n ns ih => simp [chunksFrom, segmentChunks_length, ih]

/-- Ceiling chunk count covers the input, including the zero-length case. -/
theorem chunk_count_covers (tile len : Nat) (htile : 0 < tile) :
    len ≤ ((len+tile-1)/tile)*tile := by
  have hm := Nat.mod_lt (len+tile-1) htile
  have hd := Nat.div_add_mod (len+tile-1) tile
  rw [Nat.mul_comm tile] at hd
  omega

/-- Every emitted chunk has positive length; no padding chunk becomes a
recursive summary element. -/
theorem chunk_positive (tile len j : Nat) (htile : 0 < tile)
    (hj : j < (len+tile-1)/tile) :
    0 < min tile (len-j*tile) := by
  have hm := Nat.mod_lt (len+tile-1) htile
  have hd := Nat.div_add_mod (len+tile-1) tile
  rw [Nat.mul_comm tile] at hd
  have hj' : (j+1)*tile ≤ ((len+tile-1)/tile)*tile :=
    Nat.mul_le_mul_right tile (by omega)
  rw [Nat.add_mul] at hj'
  omega

/-- Value stored in one aggregate slot by `localReduce`. -/
def aggregateValue (op : ReduceOp) (read : Nat → Word)
    (start tile len chunk : Nat) : Word :=
  foldRange op read (start+chunk*tile) (min tile (len-chunk*tile)) op.identity

/-- Scanning chunk aggregates is exactly scanning the corresponding original
prefix. The minimum also covers empty input, partial final chunks, and any
identity-only chunks beyond the input. Operand order is preserved. -/
theorem aggregate_prefix (op : ReduceOp) (read : Nat → Word)
    (start tile len count : Nat) (init : Word) :
    foldRange op (aggregateValue op read start tile len) 0 count init =
      foldRange op read start (min len (count*tile)) init := by
  induction count with
  | zero => simp [foldRange]
  | succ count ih =>
    rw [foldRange_succ, ih]
    simp only [Nat.zero_add, aggregateValue]
    by_cases h : count*tile ≤ len
    · rw [Nat.min_eq_right h, foldRange_compose]
      congr 1
      rw [Nat.succ_mul]
      omega
    · have hnext : len ≤ (count+1)*tile := by
        rw [Nat.add_mul]
        omega
      have hz : len-count*tile = 0 := by omega
      simp [Nat.min_eq_left (Nat.le_of_not_ge h), Nat.min_eq_left hnext,
        hz, foldRange]

/-- A chunk-summary reduction recovers the complete original segment whenever
its descriptor count covers the segment. This is the induction step for every
level of `reduceInto`, not a hypothesis about the final output. -/
theorem aggregate_total (op : ReduceOp) (read : Nat → Word)
    (start tile len count : Nat) (init : Word) (hcover : len ≤ count*tile) :
    foldRange op (aggregateValue op read start tile len) 0 count init =
      foldRange op read start len init := by
  rw [aggregate_prefix, Nat.min_eq_left hcover]

/-- Exclusive chunk prefixes seed a local scan to produce the original prefix.
The only range premise is the valid local output lane of that chunk. -/
theorem aggregate_seed_scan (op : ReduceOp) (read : Nat → Word)
    (start tile len chunk i : Nat) (init : Word) (mode : ScanMode)
    (hi : i < min tile (len-chunk*tile)) :
    foldRange op read (start+chunk*tile) (i+mode.extra)
      (foldRange op (aggregateValue op read start tile len) 0 chunk init) =
      foldRange op read start (chunk*tile+i+mode.extra) init := by
  have hstart : chunk*tile ≤ len := by omega
  rw [aggregate_prefix, Nat.min_eq_right hstart]
  rw [foldRange_init, chunk_fixup]

/-- The padded tree used by `localScan`, seeded by the aggregate exclusive scan,
returns the original segment prefix. Padding is internal to the tree. -/
theorem aggregate_seed_tree (op : ReduceOp) (read : Nat → Word)
    (start tile len chunk depth i : Nat) (init : Word) (mode : ScanMode)
    (hsize : min tile (len-chunk*tile) ≤ 2^depth)
    (hi : i < min tile (len-chunk*tile)) :
    scanValue op
      (paddedRead op read (start+chunk*tile) (min tile (len-chunk*tile)))
      0 depth (foldRange op (aggregateValue op read start tile len) 0 chunk init) mode i =
      foldRange op read start (chunk*tile+i+mode.extra) init := by
  rw [scanValue_eq_fold op _ 0 depth _ mode i (by omega)]
  rw [padded_prefix op read (start+chunk*tile) (min tile (len-chunk*tile)) (i+mode.extra) _
    (by cases mode <;> simp [ScanMode.extra] <;> omega)]
  exact aggregate_seed_scan op read start tile len chunk i init mode hi

/-- Readback of concrete aggregate slots transfers the prefix theorem to the
actual summary buffer. These are local reduction results, not an assumption
about the final scan or reduction. -/
theorem chunk_totals_prefix (op : ReduceOp) (read totals : Nat → Word)
    (start result tile len count : Nat) (init : Word)
    (hslots : ∀ j, j < count → totals (result+j) =
      foldRange op read (start+j*tile) (min tile (len-j*tile)) op.identity) :
    foldRange op totals result count init =
      foldRange op read start (min len (count*tile)) init := by
  have hs := foldRange_shift op totals result 0 count init
  simp only [Nat.add_zero] at hs
  rw [← hs]
  rw [foldRange_congr op _ (aggregateValue op read start tile len) 0 count init
    (by intro j _ hj; exact hslots j (by omega))]
  exact aggregate_prefix op read start tile len count init

/-- Per-segment reductions of the summary buffer are exactly the original
segment reductions, with the actual constructor's input/result offsets.
This equality composes at every recursive level of `reduceInto`. -/
theorem descriptor_reductions (op : ReduceOp) (read totals : Nat → Word)
    (tile start result output : Nat) (ns : List Nat) (htile : 0 < tile)
    (hslots : ∀ c ∈ chunksFrom tile start result ns,
      totals c.result = foldRange op read c.start c.length op.identity) :
    ((segmentsFrom result output (ns.map fun n => (n+tile-1)/tile)).map fun c =>
      foldRange op totals c.start c.length op.identity) =
    ((segmentsFrom start output ns).map fun c =>
      foldRange op read c.start c.length op.identity) := by
  induction ns generalizing start result output with
  | nil => rfl
  | cons n ns ih =>
    have hhead : ∀ j, j < (n+tile-1)/tile → totals (result+j) =
        foldRange op read (start+j*tile) (min tile (n-j*tile)) op.identity := by
      intro j hj
      apply hslots ⟨start+j*tile,min tile (n-j*tile),result+j⟩
      simp only [chunksFrom, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    have htail : ∀ c ∈ chunksFrom tile (start+n) (result+(n+tile-1)/tile) ns,
        totals c.result = foldRange op read c.start c.length op.identity := by
      intro c hc
      exact hslots c (by simp only [chunksFrom, List.mem_append]; exact Or.inr hc)
    simp only [List.map_cons, segmentsFrom]
    congr 1
    · rw [chunk_totals_prefix op read totals start result tile n _ op.identity hhead,
        Nat.min_eq_left (chunk_count_covers tile n htile)]
    · exact ih (start+n) (result+(n+tile-1)/tile) (output+1) htail

/-- Concrete prefix-buffer readback, followed by the actual local padded tree,
returns the original segment prefix at every valid lane. -/
theorem descriptor_seed_tree (op : ReduceOp) (read totals prefixes : Nat → Word)
    (tile start result len chunk depth i : Nat) (mode : ScanMode)
    (hslots : ∀ j, j < chunk → totals (result+j) =
      foldRange op read (start+j*tile) (min tile (len-j*tile)) op.identity)
    (hprefix : prefixes (result+chunk) = foldRange op totals result chunk op.identity)
    (hsize : min tile (len-chunk*tile) ≤ 2^depth)
    (hi : i < min tile (len-chunk*tile)) :
    scanValue op
      (paddedRead op read (start+chunk*tile) (min tile (len-chunk*tile)))
      0 depth (prefixes (result+chunk)) mode i =
      foldRange op read start (chunk*tile+i+mode.extra) op.identity := by
  rw [hprefix, chunk_totals_prefix op read totals start result tile len chunk op.identity hslots]
  rw [← aggregate_prefix op read start tile len chunk op.identity]
  exact aggregate_seed_tree op read start tile len chunk depth i op.identity mode hsize hi

/-- A bound on the segment length gives a bound on its actual ceiling chunk
count, without requiring divisibility or a nonempty segment. -/
theorem chunk_count_le (tile len cap : Nat) (htile : 0 < tile)
    (hlen : len ≤ cap*tile) : (len+tile-1)/tile ≤ cap := by
  have hd := Nat.div_add_mod (len+tile-1) tile
  rw [Nat.mul_comm tile] at hd
  by_cases h : (len+tile-1)/tile ≤ cap
  · exact h
  · have hm : (cap+1)*tile ≤ ((len+tile-1)/tile)*tile :=
      Nat.mul_le_mul_right tile (by omega)
    rw [Nat.add_mul] at hm
    omega

theorem member_le_sum (ns : List Nat) (n : Nat) (hn : n ∈ ns) : n ≤ ns.sum := by
  induction ns with
  | nil => simp at hn
  | cons k ns ih =>
    simp only [List.mem_cons] at hn
    simp only [List.sum_cons]
    cases hn with
    | inl h => omega
    | inr h => have := ih h; omega

/-- The builder's chosen local depth covers a partial tile. -/
theorem tileDepth_covers (n : Nat) : n ≤ 2^(tileDepth n) := by
  unfold tileDepth
  split
  · rename_i h; simp only [Nat.pow_zero]; exact h
  · rename_i h
    have hp := Nat.lt_log2_self (n := n-1)
    omega

/-- A bucket's local tree fits the preallocated tile tree. -/
theorem tileDepth_le (n depth : Nat) (hn : n ≤ 2^depth) : tileDepth n ≤ depth := by
  unfold tileDepth
  split
  · omega
  · rename_i h
    have hz : n-1 ≠ 0 := by omega
    have hp : n-1 < 2^depth := by omega
    have hl := (Nat.log2_lt hz).mpr hp
    omega

/-- Every valid segment lane belongs to an emitted positive chunk, including
lanes in a partial final chunk. -/
theorem chunk_lane_partition (tile len i : Nat) (htile : 0 < tile) (hi : i < len) :
    i/tile < (len+tile-1)/tile ∧
      i%tile < min tile (len-(i/tile)*tile) ∧
      i = (i/tile)*tile+i%tile := by
  have hc := chunk_count_covers tile len htile
  have hm := Nat.mod_lt i htile
  have hd := Nat.div_add_mod i tile
  rw [Nat.mul_comm tile] at hd
  constructor
  · apply (Nat.div_lt_iff_lt_mul htile).mpr
    omega
  · omega

/-- The recursive reduction contract composes with concrete chunk readback.
Both descriptor lists are the lists consumed by the actual builder. -/
theorem descriptor_reduce_compose (op : ReduceOp) (read totals output : Nat → Word)
    (tile start result out : Nat) (ns : List Nat) (htile : 0 < tile)
    (hslots : ∀ c ∈ chunksFrom tile start result ns,
      totals c.result = foldRange op read c.start c.length op.identity)
    (hrecursive : ∀ c ∈ segmentsFrom result out (ns.map fun n => (n+tile-1)/tile),
      output c.result = foldRange op totals c.start c.length op.identity) :
    ∀ c ∈ segmentsFrom start out ns,
      output c.result = foldRange op read c.start c.length op.identity := by
  induction ns generalizing start result out with
  | nil => simp [segmentsFrom]
  | cons n ns ih =>
    intro c hc
    simp only [segmentsFrom, List.mem_cons] at hc
    cases hc with
    | inl hc =>
      subst c
      have hr := hrecursive ⟨result,(n+tile-1)/tile,out⟩ (by simp [segmentsFrom])
      have hs : ∀ j, j < (n+tile-1)/tile → totals (result+j) =
          foldRange op read (start+j*tile) (min tile (n-j*tile)) op.identity := by
        intro j hj
        apply hslots ⟨start+j*tile,min tile (n-j*tile),result+j⟩
        simp only [chunksFrom, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      rw [chunk_totals_prefix op read totals start result tile n _ op.identity hs,
        Nat.min_eq_left (chunk_count_covers tile n htile)] at hr
      exact hr
    | inr hc =>
      apply ih (start+n) (result+(n+tile-1)/tile) (out+1)
      · intro d hd
        exact hslots d (by simp only [chunksFrom, List.mem_append]; exact Or.inr hd)
      · intro d hd
        exact hrecursive d (by simp only [List.map_cons, segmentsFrom, List.mem_cons]; exact Or.inr hd)
      · exact hc

/-- Exclusive scan of summary segments, followed by local scans seeded from
those concrete slots, equals the original segmented scan. The hypotheses are
precisely the three preceding builder actions' readback contracts. -/
theorem descriptor_scan_compose (op : ReduceOp) (mode : ScanMode)
    (read totals prefixes output : Nat → Word) (tile start result out : Nat)
    (ns : List Nat) (htile : 0 < tile)
    (hslots : ∀ c ∈ chunksFrom tile start result ns,
      totals c.result = foldRange op read c.start c.length op.identity)
    (hrecursive : ∀ c ∈ segmentsFrom result out (ns.map fun n => (n+tile-1)/tile),
      ∀ i < c.length, prefixes (c.start+i) = foldRange op totals c.start i op.identity)
    (hlocal : ∀ c ∈ chunksFrom tile start result ns, ∀ i < c.length,
      output (c.start+i) = foldRange op read c.start (i+mode.extra) (prefixes c.result)) :
    ∀ c ∈ segmentsFrom start out ns, ∀ i < c.length,
      output (c.start+i) = foldRange op read c.start (i+mode.extra) op.identity := by
  induction ns generalizing start result out with
  | nil => simp [segmentsFrom]
  | cons n ns ih =>
    intro c hc i hi
    simp only [segmentsFrom, List.mem_cons] at hc
    cases hc with
    | inl hc =>
      subst c
      obtain ⟨hj, hlane, he⟩ := chunk_lane_partition tile n i htile hi
      have hmember : (⟨start+(i/tile)*tile,min tile (n-(i/tile)*tile),result+i/tile⟩ : Chunk)
          ∈ chunksFrom tile start result (n::ns) := by
        simp only [chunksFrom, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨i/tile,List.mem_range.mpr hj,rfl⟩)
      have hv := hlocal _ hmember (i%tile) hlane
      have hp := hrecursive ⟨result,(n+tile-1)/tile,out⟩
        (by simp [segmentsFrom]) (i/tile) hj
      have hs : ∀ j, j < i/tile → totals (result+j) =
          foldRange op read (start+j*tile) (min tile (n-j*tile)) op.identity := by
        intro j hj'
        apply hslots ⟨start+j*tile,min tile (n-j*tile),result+j⟩
        simp only [chunksFrom, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩)
      simp only at hv hp
      rw [hp, chunk_totals_prefix op read totals start result tile n (i/tile) op.identity hs,
        ← aggregate_prefix op read start tile n (i/tile) op.identity,
        aggregate_seed_scan op read start tile n (i/tile) (i%tile) op.identity mode hlane] at hv
      have hindex : start+(i/tile)*tile+i%tile = start+i := by omega
      have hlength : (i/tile)*tile+i%tile+mode.extra = i+mode.extra := by omega
      simpa only [hindex, hlength] using hv
    | inr hc =>
      apply ih (start+n) (result+(n+tile-1)/tile) (out+1)
      · intro d hd
        exact hslots d (by simp only [chunksFrom, List.mem_append]; exact Or.inr hd)
      · intro d hd j hj
        exact hrecursive d (by simp only [List.map_cons, segmentsFrom, List.mem_cons]; exact Or.inr hd) j hj
      · intro d hd j hj
        exact hlocal d (by simp only [chunksFrom, List.mem_append]; exact Or.inr hd) j hj
      · exact hc
      · exact hi

/-- Reduction descriptor readback determines the complete contiguous output
vector, including one identity result per empty segment. -/
theorem reduction_output (op : ReduceOp) (read output : Nat → Word)
    (start result : Nat) (ns : List Nat)
    (hvalues : ∀ c ∈ segmentsFrom start result ns,
      output c.result = foldRange op read c.start c.length op.identity) :
    (List.range' result ns.length).map output =
      (segmentRanges none start ns).map fun r => foldRange op read r.1 r.2 op.identity := by
  induction ns generalizing start result with
  | nil => rfl
  | cons n ns ih =>
    have hhead := hvalues ⟨start,n,result⟩ (by simp [segmentsFrom])
    have htail : ∀ c ∈ segmentsFrom (start+n) (result+1) ns,
        output c.result = foldRange op read c.start c.length op.identity := by
      intro c hc
      exact hvalues c (by simp only [segmentsFrom, List.mem_cons]; exact Or.inr hc)
    simpa [List.range', segmentRanges, hhead] using congrArg (fun tail =>
      foldRange op read start n op.identity :: tail) (ih (start+n) (result+1) htail)

/-- Scan descriptor readback determines the complete contiguous output vector.
Empty segments contribute no outputs and preserve following segment boundaries. -/
theorem scan_output (op : ReduceOp) (mode : ScanMode) (read output : Nat → Word)
    (start result : Nat) (ns : List Nat)
    (hvalues : ∀ c ∈ segmentsFrom start result ns, ∀ i < c.length,
      output (c.start+i) = foldRange op read c.start (i+mode.extra) op.identity) :
    (List.range' start ns.sum).map output =
      (segmentRanges (some mode) start ns).map fun r => foldRange op read r.1 r.2 op.identity := by
  induction ns generalizing start result with
  | nil => rfl
  | cons n ns ih =>
    have hhead : (List.range' start n).map output =
        (List.range n).map (fun i => foldRange op read start (i+mode.extra) op.identity) := by
      rw [List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hvalues ⟨start,n,result⟩ (by simp [segmentsFrom]) i (List.mem_range.mp hi)
    have htail : ∀ c ∈ segmentsFrom (start+n) (result+1) ns, ∀ i < c.length,
        output (c.start+i) = foldRange op read c.start (i+mode.extra) op.identity := by
      intro c hc i hi
      exact hvalues c (by simp only [segmentsFrom, List.mem_cons]; exact Or.inr hc) i hi
    rw [List.sum_cons, ← List.range'_append_1, List.map_append, hhead, ih (start+n) (result+1) htail]
    simp [segmentRanges, List.map_map]

/-- The final semantic boundary. The actual interpreter proof supplies the
per-descriptor contracts; this theorem converts them to the public fold vector. -/
theorem descriptor_output_eq_evalFold (op : ReduceOp) (shape : FoldShape)
    (read output : Nat → Word)
    (hvalues : match shape.mode with
      | none => ∀ c ∈ segments shape.segments,
          output c.result = foldRange op read c.start c.length op.identity
      | some mode => ∀ c ∈ segments shape.segments, ∀ i < c.length,
          output (c.start+i) = foldRange op read c.start (i+mode.extra) op.identity) :
    (List.range shape.outLen).map output = evalFold op shape read := by
  cases shape with
  | reduce n =>
    have h := reduction_output op read output 0 0 [n] hvalues
    simpa [FoldShape.outLen, FoldShape.ranges, segmentRanges, evalFold, List.range_eq_range'] using h
  | scan n mode =>
    have h := scan_output op mode read output 0 0 [n] hvalues
    simpa [FoldShape.outLen, FoldShape.ranges, segmentRanges, evalFold, List.range_eq_range'] using h
  | segReduce ns =>
    have h := reduction_output op read output 0 0 ns hvalues
    have hlen : ∀ start, (segmentRanges none start ns).length = ns.length := by
      clear h hvalues
      induction ns with
      | nil => intro start; rfl
      | cons n ns ih => intro start; simp [segmentRanges, ih]
    simpa [FoldShape.outLen, FoldShape.ranges, evalFold, hlen, List.range_eq_range'] using h
  | segScan ns mode =>
    have h := scan_output op mode read output 0 0 ns hvalues
    have hlen : ∀ start, (segmentRanges (some mode) start ns).length = ns.sum := by
      clear h hvalues
      induction ns with
      | nil => intro start; rfl
      | cons n ns ih => intro start; simp [segmentRanges, ih]
    simpa [FoldShape.outLen, FoldShape.ranges, evalFold, hlen, List.range_eq_range'] using h

theorem segmentsFrom_results (start result : Nat) (ns : List Nat) :
    (segmentsFrom start result ns).map (·.result) = List.range' result ns.length := by
  induction ns generalizing start result with
  | nil => rfl
  | cons n ns ih => simp [segmentsFrom, List.range', ih]

theorem segmentChunks_results (tile start result len : Nat) :
    (segmentChunks tile start result len).map (·.result) =
      List.range' result ((len+tile-1)/tile) := by
  simp [segmentChunks, List.map_map, List.range'_eq_map_range]

theorem chunksFrom_results (tile start result : Nat) (ns : List Nat) :
    (chunksFrom tile start result ns).map (·.result) =
      List.range' result ((ns.map fun n => (n+tile-1)/tile).sum) := by
  induction ns generalizing start result with
  | nil => rfl
  | cons n ns ih => simp [chunksFrom, segmentChunks_results, ih]

/-- Consecutive result slots are unique, so two descriptors with the same slot
are the same descriptor even when buckets execute in a different order. -/
theorem result_injective (cs : List Chunk) (hunique : (cs.map (·.result)).Nodup)
    (c d : Chunk) (hc : c ∈ cs) (hd : d ∈ cs) (he : c.result = d.result) : c = d := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    simp only [List.map_cons, List.nodup_cons] at hunique
    simp only [List.mem_cons] at hc hd
    rcases hc with rfl | hc
    · rcases hd with rfl | hd
      · rfl
      · exact False.elim (hunique.1 (List.mem_map.mpr ⟨d,hd,he.symm⟩))
    · rcases hd with rfl | hd
      · exact False.elim (hunique.1 (List.mem_map.mpr ⟨c,hc,he⟩))
      · exact ih hunique.2 hc hd

/-- Descriptor intervals stay inside their original contiguous input span. -/
theorem segmentsFrom_bounds (start result : Nat) (ns : List Nat) (c : Chunk)
    (hc : c ∈ segmentsFrom start result ns) :
    start ≤ c.start ∧ c.start+c.length ≤ start+ns.sum := by
  induction ns generalizing start result with
  | nil => simp [segmentsFrom] at hc
  | cons n ns ih =>
    simp only [segmentsFrom, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · have h := ih (start+n) (result+1) hc
      simp only [List.sum_cons]
      omega

theorem segmentChunks_bounds (tile start result len : Nat) (htile : 0 < tile)
    (c : Chunk) (hc : c ∈ segmentChunks tile start result len) :
    start ≤ c.start ∧ c.start+c.length ≤ start+len := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
  have hp := chunk_positive tile len j htile (List.mem_range.mp hj)
  simp only
  omega

theorem chunksFrom_bounds (tile start result : Nat) (ns : List Nat) (htile : 0 < tile)
    (c : Chunk) (hc : c ∈ chunksFrom tile start result ns) :
    start ≤ c.start ∧ c.start+c.length ≤ start+ns.sum := by
  induction ns generalizing start result with
  | nil => simp [chunksFrom] at hc
  | cons n ns ih =>
    simp only [chunksFrom, List.mem_append] at hc
    rcases hc with hc | hc
    · have h := segmentChunks_bounds tile start result n htile c hc
      simp only [List.sum_cons]
      omega
    · have h := ih (start+n) (result+(n+tile-1)/tile) hc
      simp only [List.sum_cons]
      omega

/-- Distinct segment descriptors have disjoint input/output scan intervals. -/
theorem segmentsFrom_disjoint (start result : Nat) (ns : List Nat) (c d : Chunk)
    (hc : c ∈ segmentsFrom start result ns) (hd : d ∈ segmentsFrom start result ns)
    (i j : Nat) (hi : i < c.length) (hj : j < d.length)
    (he : c.start+i = d.start+j) : c = d := by
  induction ns generalizing start result with
  | nil => simp [segmentsFrom] at hc
  | cons n ns ih =>
    simp only [segmentsFrom, List.mem_cons] at hc hd
    rcases hc with rfl | hc
    · rcases hd with rfl | hd
      · rfl
      · have hb := segmentsFrom_bounds (start+n) (result+1) ns d hd
        simp only at hi he
        omega
    · rcases hd with rfl | hd
      · have hb := segmentsFrom_bounds (start+n) (result+1) ns c hc
        simp only at hj he
        omega
      · exact ih (start+n) (result+1) hc hd

theorem segmentChunks_disjoint (tile start result len : Nat) (htile : 0 < tile)
    (c d : Chunk) (hc : c ∈ segmentChunks tile start result len)
    (hd : d ∈ segmentChunks tile start result len)
    (i j : Nat) (hi : i < c.length) (hj : j < d.length)
    (he : c.start+i = d.start+j) : c = d := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hd
  simp only at hi hj he ⊢
  have hi' : i < tile := by omega
  have hj' : j < tile := by omega
  have he' : i+a*tile = j+b*tile := by omega
  have hq := congrArg (fun x => x/tile) he'
  rw [Nat.add_mul_div_right i a htile, Nat.add_mul_div_right j b htile,
    Nat.div_eq_of_lt hi', Nat.div_eq_of_lt hj'] at hq
  have hab : a = b := by omega
  subst b
  rfl

theorem chunksFrom_disjoint (tile start result : Nat) (ns : List Nat) (htile : 0 < tile)
    (c d : Chunk) (hc : c ∈ chunksFrom tile start result ns)
    (hd : d ∈ chunksFrom tile start result ns)
    (i j : Nat) (hi : i < c.length) (hj : j < d.length)
    (he : c.start+i = d.start+j) : c = d := by
  induction ns generalizing start result with
  | nil => simp [chunksFrom] at hc
  | cons n ns ih =>
    simp only [chunksFrom, List.mem_append] at hc hd
    rcases hc with hc | hc
    · rcases hd with hd | hd
      · exact segmentChunks_disjoint tile start result n htile c d hc hd i j hi hj he
      · have hb := segmentChunks_bounds tile start result n htile c hc
        have hb' := chunksFrom_bounds tile (start+n) (result+(n+tile-1)/tile) ns htile d hd
        omega
    · rcases hd with hd | hd
      · have hb := segmentChunks_bounds tile start result n htile d hd
        have hb' := chunksFrom_bounds tile (start+n) (result+(n+tile-1)/tile) ns htile c hc
        omega
      · exact ih (start+n) (result+(n+tile-1)/tile) hc hd

/-- Compact result slots of the unfinished descriptors' split chunks. -/
theorem splitChunksFrom_results (tile result : Nat) (cs : List Chunk) :
    (splitChunksFrom tile result cs).map (·.result) =
      List.range' result ((cs.map fun c => (c.length+tile-1)/tile).sum) := by
  induction cs generalizing result with
  | nil => rfl
  | cons c cs ih => simp [splitChunksFrom,segmentChunks_results,ih]

theorem splitChunksFrom_length (tile result : Nat) (cs : List Chunk) :
    (splitChunksFrom tile result cs).length =
      (cs.map fun c => (c.length+tile-1)/tile).sum := by
  have h := congrArg List.length (splitChunksFrom_results tile result cs)
  simpa using h

/-- Reduction destination slots survive summary compaction unchanged. -/
theorem summaryChunksFrom_results (tile start : Nat) (cs : List Chunk) :
    (summaryChunksFrom tile start cs).map (·.result) = cs.map (·.result) := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih => simp [summaryChunksFrom,ih]

theorem summaryChunksFrom_lengths (tile start : Nat) (cs : List Chunk) :
    (summaryChunksFrom tile start cs).map (·.length) =
      cs.map (fun c => (c.length+tile-1)/tile) := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih => simp [summaryChunksFrom,ih]

/-- Compacted-summary reduction composes for arbitrary original descriptor
positions. Finished short descriptors are absent from this recursion. -/
theorem split_reduce_compose (op : ReduceOp) (read totals output : Nat → Word)
    (tile result : Nat) (cs : List Chunk) (htile : 0 < tile)
    (hslots : ∀ c ∈ splitChunksFrom tile result cs,
      totals c.result = foldRange op read c.start c.length op.identity)
    (hrecursive : ∀ c ∈ summaryChunksFrom tile result cs,
      output c.result = foldRange op totals c.start c.length op.identity) :
    ∀ c ∈ cs, output c.result = foldRange op read c.start c.length op.identity := by
  induction cs generalizing result with
  | nil => simp
  | cons c0 cs ih =>
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with hc | hc
    · subst c
      have hr := hrecursive ⟨result,(c0.length+tile-1)/tile,c0.result⟩ (by simp [summaryChunksFrom])
      have hs : ∀ j, j < (c0.length+tile-1)/tile → totals (result+j) =
          foldRange op read (c0.start+j*tile) (min tile (c0.length-j*tile)) op.identity := by
        intro j hj
        apply hslots ⟨c0.start+j*tile,min tile (c0.length-j*tile),result+j⟩
        simp only [splitChunksFrom,List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)
      rw [chunk_totals_prefix op read totals c0.start result tile c0.length _ op.identity hs,
        Nat.min_eq_left (chunk_count_covers tile c0.length htile)] at hr
      exact hr
    · apply ih (result+(c0.length+tile-1)/tile)
      · intro d hd
        exact hslots d (by simp only [splitChunksFrom,List.mem_append]; exact Or.inr hd)
      · intro d hd
        exact hrecursive d (by simp only [summaryChunksFrom,List.mem_cons]; exact Or.inr hd)
      · exact hc

/-- Summary-exclusive-prefix plus seeded split-chunk scans composes for any
original descriptor positions and retained reduction result identifiers. -/
theorem split_scan_compose (op : ReduceOp) (mode : ScanMode)
    (read totals prefixes output : Nat → Word) (tile result : Nat)
    (cs : List Chunk) (htile : 0 < tile)
    (hslots : ∀ c ∈ splitChunksFrom tile result cs,
      totals c.result = foldRange op read c.start c.length op.identity)
    (hrecursive : ∀ c ∈ summaryChunksFrom tile result cs, ∀ i < c.length,
      prefixes (c.start+i) = foldRange op totals c.start i op.identity)
    (hlocal : ∀ c ∈ splitChunksFrom tile result cs, ∀ i < c.length,
      output (c.start+i) = foldRange op read c.start (i+mode.extra) (prefixes c.result)) :
    ∀ c ∈ cs, ∀ i < c.length,
      output (c.start+i) = foldRange op read c.start (i+mode.extra) op.identity := by
  induction cs generalizing result with
  | nil => simp
  | cons c0 cs ih =>
    intro c hc i hi
    simp only [List.mem_cons] at hc
    rcases hc with hc | hc
    · subst c
      obtain ⟨hj,hlane,he⟩ := chunk_lane_partition tile c0.length i htile hi
      have hmember : (⟨c0.start+(i/tile)*tile,min tile (c0.length-(i/tile)*tile),result+i/tile⟩ : Chunk)
          ∈ splitChunksFrom tile result (c0::cs) := by
        simp only [splitChunksFrom,List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨i/tile,List.mem_range.mpr hj,rfl⟩)
      have hv := hlocal _ hmember (i%tile) hlane
      have hp := hrecursive ⟨result,(c0.length+tile-1)/tile,c0.result⟩
        (by simp [summaryChunksFrom]) (i/tile) hj
      have hs : ∀ j, j < i/tile → totals (result+j) =
          foldRange op read (c0.start+j*tile) (min tile (c0.length-j*tile)) op.identity := by
        intro j hj'
        apply hslots ⟨c0.start+j*tile,min tile (c0.length-j*tile),result+j⟩
        simp only [splitChunksFrom,List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩)
      simp only at hv hp
      rw [hp,chunk_totals_prefix op read totals c0.start result tile c0.length (i/tile) op.identity hs,
        ← aggregate_prefix op read c0.start tile c0.length (i/tile) op.identity,
        aggregate_seed_scan op read c0.start tile c0.length (i/tile) (i%tile) op.identity mode hlane] at hv
      have hindex : c0.start+(i/tile)*tile+i%tile = c0.start+i := by omega
      have hlength : (i/tile)*tile+i%tile+mode.extra = i+mode.extra := by omega
      simpa only [hindex,hlength] using hv
    · apply ih (result+(c0.length+tile-1)/tile)
      · intro d hd
        exact hslots d (by simp only [splitChunksFrom,List.mem_append]; exact Or.inr hd)
      · intro d hd j hj
        exact hrecursive d (by simp only [summaryChunksFrom,List.mem_cons]; exact Or.inr hd) j hj
      · intro d hd j hj
        exact hlocal d (by simp only [splitChunksFrom,List.mem_append]; exact Or.inr hd) j hj
      · exact hc
      · exact hi

/-- Each split interval remains inside one original unfinished descriptor. -/
theorem splitChunksFrom_origin (tile result : Nat) (cs : List Chunk) (htile : 0 < tile)
    (part : Chunk) (hp : part ∈ splitChunksFrom tile result cs) :
    ∃ c ∈ cs, c.start ≤ part.start ∧ part.start+part.length ≤ c.start+c.length := by
  induction cs generalizing result with
  | nil => simp [splitChunksFrom] at hp
  | cons c cs ih =>
    simp only [splitChunksFrom,List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨c,by simp,segmentChunks_bounds tile c.start result c.length htile part hp⟩
    · obtain ⟨d,hd,hbounds⟩ := ih (result+(c.length+tile-1)/tile) hp
      exact ⟨d,by simp [hd],hbounds⟩

theorem splitChunksFrom_capacity (tile result : Nat) (cs : List Chunk) :
    ∀ c ∈ splitChunksFrom tile result cs, c.length ≤ tile := by
  induction cs generalizing result with
  | nil => simp [splitChunksFrom]
  | cons c cs ih =>
    intro d hd
    simp only [splitChunksFrom,List.mem_append] at hd
    rcases hd with hd | hd
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hd
      exact Nat.min_le_left _ _
    · exact ih (result+(c.length+tile-1)/tile) d hd

/-- Summary inputs form a compact nonoverlapping sequence, regardless of their
retained original result slots. -/
theorem summaryChunksFrom_bounds (tile start : Nat) (cs : List Chunk)
    (c : Chunk) (hc : c ∈ summaryChunksFrom tile start cs) :
    start ≤ c.start ∧ c.start+c.length ≤ start+(cs.map fun c => (c.length+tile-1)/tile).sum := by
  induction cs generalizing start with
  | nil => simp [summaryChunksFrom] at hc
  | cons d cs ih =>
    simp only [summaryChunksFrom,List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · have h := ih (start+(d.length+tile-1)/tile) hc
      constructor
      · exact Nat.le_trans (Nat.le_add_right _ _) h.1
      · simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using h.2

theorem summaryChunksFrom_disjoint (tile start : Nat) (cs : List Chunk) (c d : Chunk)
    (hc : c ∈ summaryChunksFrom tile start cs) (hd : d ∈ summaryChunksFrom tile start cs)
    (i j : Nat) (hi : i < c.length) (hj : j < d.length)
    (he : c.start+i = d.start+j) : c = d := by
  induction cs generalizing start with
  | nil => simp [summaryChunksFrom] at hc
  | cons a cs ih =>
    simp only [summaryChunksFrom,List.mem_cons] at hc hd
    rcases hc with rfl | hc
    · rcases hd with rfl | hd
      · rfl
      · have h := summaryChunksFrom_bounds tile (start+(a.length+tile-1)/tile) cs d hd
        simp only at hi he
        omega
    · rcases hd with rfl | hd
      · have h := summaryChunksFrom_bounds tile (start+(a.length+tile-1)/tile) cs c hc
        simp only at hj he
        omega
      · exact ih (start+(a.length+tile-1)/tile) hc hd

/-- Splitting preserves disjointness of descriptor intervals. Result uniqueness
excludes repeated original descriptors, independently of their input values. -/
theorem splitChunksFrom_disjoint (tile result : Nat) (cs : List Chunk) (htile : 0 < tile)
    (hu : (cs.map (·.result)).Nodup)
    (hs : ∀ c ∈ cs, ∀ d ∈ cs, ∀ i < c.length, ∀ j < d.length,
      c.start+i = d.start+j → c = d)
    (c d : Chunk) (hc : c ∈ splitChunksFrom tile result cs)
    (hd : d ∈ splitChunksFrom tile result cs)
    (i j : Nat) (hi : i < c.length) (hj : j < d.length)
    (he : c.start+i = d.start+j) : c = d := by
  induction cs generalizing result with
  | nil => simp [splitChunksFrom] at hc
  | cons a cs ih =>
    have hun : a.result ∉ cs.map (·.result) := (List.nodup_cons.mp hu).1
    have hut : (cs.map (·.result)).Nodup := (List.nodup_cons.mp hu).2
    have hst : ∀ c ∈ cs, ∀ d ∈ cs, ∀ i < c.length, ∀ j < d.length,
        c.start+i = d.start+j → c = d := by
      intro c hc d hd
      exact hs c (by simp [hc]) d (by simp [hd])
    have cross : ∀ c ∈ segmentChunks tile a.start result a.length,
        ∀ d ∈ splitChunksFrom tile (result+(a.length+tile-1)/tile) cs,
        ∀ i < c.length, ∀ j < d.length, c.start+i ≠ d.start+j := by
      intro c hc d hd i hi j hj he
      have hb := segmentChunks_bounds tile a.start result a.length htile c hc
      obtain ⟨orig,ho,hob⟩ := splitChunksFrom_origin tile (result+(a.length+tile-1)/tile) cs htile d hd
      have hea := hs a (by simp) orig (by simp [ho]) (c.start+i-a.start) (by omega)
        (d.start+j-orig.start) (by omega) (by omega)
      apply hun
      exact List.mem_map.mpr ⟨orig,ho,congrArg Chunk.result hea.symm⟩
    simp only [splitChunksFrom,List.mem_append] at hc hd
    rcases hc with hc | hc
    · rcases hd with hd | hd
      · exact segmentChunks_disjoint tile a.start result a.length htile c d hc hd i j hi hj he
      · exact False.elim (cross c hc d hd i hi j hj he)
    · rcases hd with hd | hd
      · exact False.elim (cross d hd c hc j hj i hi he.symm)
      · exact ih (result+(a.length+tile-1)/tile) hut hst hc hd

/-- Length-only certificate for the actual pruned recursion: completed short
descriptors leave the hierarchy before the remaining summaries recur. -/
def EnoughChunkFuel (tile : Nat) (cs : List Chunk) : Nat → Prop
  | 0 => False
  | fuel+1 => (cs.filter (tile < ·.length)) = [] ∨
      EnoughChunkFuel tile (summaryChunks tile (cs.filter (tile < ·.length))) fuel

/-- Each summary capacity halves for tile at least two; pruning only removes
additional work. This is a sufficient bound for the actual builder's fuel. -/
theorem enoughChunkFuel_of_capacity (tile depth : Nat) (cs : List Chunk)
    (htile : 2 ≤ tile) (hsize : ∀ c ∈ cs, c.length ≤ 2^depth) :
    EnoughChunkFuel tile cs (depth+1) := by
  induction depth generalizing cs with
  | zero =>
    apply Or.inl
    apply List.filter_eq_nil_iff.mpr
    intro c hc
    have h := hsize c hc
    simp only [Nat.pow_zero] at h
    simp
    omega
  | succ depth ih =>
    apply Or.inr
    apply ih
    intro summary hs
    have hm : summary.length ∈ (summaryChunks tile (cs.filter (tile < ·.length))).map (·.length) :=
      List.mem_map.mpr ⟨summary,hs,rfl⟩
    rw [summaryChunks,summaryChunksFrom_lengths] at hm
    obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
    rw [← he]
    apply chunk_count_le tile c.length (2^depth) (by omega)
    have h := hsize c (List.mem_filter.mp hc).1
    have hm := Nat.mul_le_mul_left (2^depth) htile
    rw [Nat.pow_succ] at h
    omega

/-- Exact fuel formula used by the public builder, now certified for its
pruned descriptor hierarchy, including arbitrary empty segments. -/
theorem build_enoughChunkFuel (tile : Nat) (shape : FoldShape) (htile : 2 ≤ tile) :
    EnoughChunkFuel tile (segments shape.segments) (Nat.log2 (max 1 shape.inputLen)+2) := by
  have hsum : shape.segments.sum = shape.inputLen := by
    cases shape <;> simp [FoldShape.segments,FoldShape.inputLen]
  apply enoughChunkFuel_of_capacity tile (Nat.log2 (max 1 shape.inputLen)+1) _ htile
  intro c hc
  have hlen : c.length ∈ shape.segments := by
    have hm : c.length ∈ (segments shape.segments).map (·.length) := List.mem_map.mpr ⟨c,hc,rfl⟩
    have hl : ∀ start result ns, (segmentsFrom start result ns).map (·.length) = ns := by
      intro start result ns
      induction ns generalizing start result with
      | nil => rfl
      | cons n ns ih => simp [segmentsFrom,ih]
    simpa only [segments,hl] using hm
  have h := member_le_sum shape.segments c.length hlen
  rw [hsum] at h
  have hp := Nat.lt_log2_self (n := max 1 shape.inputLen)
  omega

end Obend.Hardware.Gpu.CollectiveHierarchy
end
