module
public import Obend.Hardware.Gpu.CollectiveCompose
@[expose] public section

/-! End-to-end execution of the actual collective builder. Predicate definitions
below package only numeric metadata, input readback, and memory framing. -/
namespace Obend.Hardware.Gpu.CollectiveExecute
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveTrace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.Gpu.CollectiveCorrect Obend.Hardware.Gpu.CollectiveCompose
set_option autoImplicit false

/-- A device array is outside all shared rows of the allocated tree. -/
def Outside (tree : Trees) (a : Nat) : Prop :=
  ∀ k ≤ tree.depth, tree.up+k ≠ a ∧ tree.down+k ≠ a

def RowsBelow (tree : Trees) (bound : Nat) : Prop :=
  ∀ k ≤ tree.depth, tree.up+k < bound ∧ tree.down+k < bound

def Split (tree : Trees) : Prop :=
  ∀ k ≤ tree.depth, ∀ j ≤ tree.depth, tree.up+k ≠ tree.down+j

/-- Numeric ownership invariant for a descriptor list, before local tiling. -/
structure Layout (cs : List Chunk) : Prop where
  unique : (cs.map (·.result)).Nodup
  disjoint : ∀ c ∈ cs, ∀ d ∈ cs, ∀ i < c.length, ∀ j < d.length,
    c.start+i = d.start+j → c = d

/-- Static descriptors have bounded local trees, unique result slots, and
pairwise disjoint scan intervals. -/
structure Descriptors (tree : Trees) (cs : List Chunk) : Prop where
  capacity : ∀ c ∈ cs, c.length ≤ 2^tree.depth
  unique : (cs.map (·.result)).Nodup
  disjoint : ∀ c ∈ cs, ∀ d ∈ cs, ∀ i < c.length, ∀ j < d.length,
    c.start+i = d.start+j → c = d

def Reductions (op : ReduceOp) (ns : List Nat) (read output : Nat → Word) : Prop :=
  ∀ c ∈ segments ns, output c.result = foldRange op read c.start c.length op.identity

def Scans (op : ReduceOp) (mode : ScanMode) (ns : List Nat)
    (read output : Nat → Word) : Prop :=
  ∀ c ∈ segments ns, ∀ i < c.length,
    output (c.start+i) = foldRange op read c.start (i+mode.extra) op.identity

def Frame (tree : Trees) (bound dst : Nat) (before after : Memory) : Prop :=
  ∀ a < bound, Outside tree a → a ≠ dst → ∀ i, valueAt after a i = valueAt before a i

theorem outside_of_rowsBelow (tree : Trees) (bound a : Nat) (hrows : RowsBelow tree bound)
    (ha : bound ≤ a) : Outside tree a := by
  intro k hk
  have h := hrows k hk
  constructor <;> omega

theorem rowsBelow_mono (tree : Trees) (a b : Nat) (h : RowsBelow tree a) (hab : a ≤ b) :
    RowsBelow tree b := by
  intro k hk
  have hh := h k hk
  constructor <;> omega

theorem descriptors_segments (tree : Trees) (ns : List Nat)
    (hcap : ∀ n ∈ ns, n ≤ 2^tree.depth) : Descriptors tree (segments ns) := by
  refine ⟨segments_capacity ns tree.depth hcap, ?_, ?_⟩
  · rw [segments,segmentsFrom_results]
    exact List.nodup_range' _
  · intro c hc d hd i hi j hj he
    exact segmentsFrom_disjoint 0 0 ns c d hc hd i j hi hj he

theorem descriptors_chunks (tree : Trees) (ns : List Nat) :
    Descriptors tree (chunks (2^tree.depth) ns) := by
  refine ⟨chunks_capacity _ ns, ?_, ?_⟩
  · rw [chunks,chunksFrom_results]
    exact List.nodup_range' _
  · intro c hc d hd i hi j hj he
    exact chunksFrom_disjoint _ 0 0 ns (Nat.two_pow_pos _) c d hc hd i j hi hj he

/-- Local reduction correctness and an array frame, universally over the memory
contents. Admission supplies every concrete phase bound and scatter proof. -/
theorem local_reduce (p : Program) (hcheck : p.check = .ok ()) (op : ReduceOp)
    (tree : Trees) (src dst : Nat) (cs : List Chunk) (mem : Memory) (hg : Good p mem)
    (hdesc : Descriptors tree cs) (hsrc : Outside tree src) (hdst : Outside tree dst)
    (hne : src ≠ dst) (htrace : TraceIn p (reduceDispatches op tree src dst cs)) :
    (∀ c ∈ cs, valueAt (evalTrace (reduceDispatches op tree src dst cs) mem) dst c.result =
      foldRange op (valueAt mem src) c.start c.length op.identity) ∧
    (∀ a, Outside tree a → a ≠ dst → ∀ i,
      valueAt (evalTrace (reduceDispatches op tree src dst cs) mem) a i = valueAt mem a i) := by
  have hdepth := bucket_depth_le cs tree.depth hdesc.capacity
  have hphase := reduceTrace_checked p hcheck op tree src dst cs htrace
  constructor
  · intro c hc
    exact localReduce_trace_value p op tree src dst cs mem hg hdepth
      (fun k hk => (hsrc k hk).1) (fun k hk => (hdst k hk).1) hne hdesc.unique
      (fun v b hb g hg ph hp => (hphase v b hb g hg ph hp).1)
      (fun v b hb g hg ph hp => (hphase v b hb g hg ph hp).2) c hc
  · intro a ha hne' i
    exact localReduce_trace_frame p op tree src dst cs mem hg hdepth
      (fun v b hb g hg ph hp => (hphase v b hb g hg ph hp).1) a i
      (fun k hk => (ha k hk).1) (by intro he; exact False.elim (hne' he))

/-- Local scan correctness and frame for its actual source dispatch trace. -/
theorem local_scan (p : Program) (hcheck : p.check = .ok ()) (op : ReduceOp)
    (mode : ScanMode) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (prefixBuffer : Option Nat) (mem : Memory) (hg : Good p mem)
    (hdesc : Descriptors tree cs) (hsplit : Split tree)
    (hsrc : Outside tree src) (hdst : Outside tree dst) (hne : src ≠ dst)
    (hpre : ∀ a, prefixBuffer = some a → Outside tree a ∧ a ≠ dst)
    (htrace : TraceIn p (scanDispatches op mode tree src dst cs prefixBuffer)) :
    (∀ c ∈ cs, ∀ i < c.length,
      valueAt (evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem) dst (c.start+i) =
      foldRange op (valueAt mem src) c.start (i+mode.extra) (prefixValue op mem prefixBuffer c.result)) ∧
    (∀ a, Outside tree a → a ≠ dst → ∀ i,
      valueAt (evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem) a i = valueAt mem a i) := by
  have hdepth := bucket_depth_le cs tree.depth hdesc.capacity
  have hphase := scanTrace_checked p hcheck op mode tree src dst cs prefixBuffer htrace
  constructor
  · intro c hc i hi
    exact localScan_trace_value p op mode tree src dst cs prefixBuffer mem hg hdepth hsplit
      (fun k hk => (hsrc k hk).1) (fun k hk => (hsrc k hk).2) hne
      (fun k hk => (hdst k hk).1) (fun k hk => (hdst k hk).2)
      (by intro a ha; have h := hpre a ha; exact ⟨h.2,fun k hk => (h.1 k hk).1,fun k hk => (h.1 k hk).2⟩)
      hdesc.unique hdesc.disjoint
      (fun v b hb hv g hg ph hp => (hphase v b hb hv g hg ph hp).1)
      (fun v b hb hv g hg ph hp => (hphase v b hb hv g hg ph hp).2) c hc i hi
  · intro a ha hne' i
    exact localScan_trace_frame p op mode tree src dst cs prefixBuffer mem hg hdepth
      (fun v b hb hv g hg ph hp => (hphase v b hb hv g hg ph hp).1) a i
      (fun k hk => (ha k hk).1) (fun k hk => (ha k hk).2)
      (by intro he; exact False.elim (hne' he))

theorem layout_filter (cs : List Chunk) (pred : Chunk → Bool) (h : Layout cs) :
    Layout (cs.filter pred) := by
  constructor
  · exact List.Nodup.sublist (List.Sublist.map Chunk.result (List.filter_sublist (p := pred) (l := cs))) h.unique
  · intro c hc d hd
    exact h.disjoint c (List.mem_filter.mp hc).1 d (List.mem_filter.mp hd).1

theorem layout_segments (ns : List Nat) : Layout (segments ns) := by
  constructor
  · rw [segments,segmentsFrom_results]
    exact List.nodup_range' _
  · intro c hc d hd i hi j hj he
    exact segmentsFrom_disjoint 0 0 ns c d hc hd i j hi hj he

theorem layout_summary (tile : Nat) (cs : List Chunk) (h : Layout cs) :
    Layout (summaryChunks tile cs) := by
  constructor
  · rw [summaryChunks,summaryChunksFrom_results]
    exact h.unique
  · intro c hc d hd i hi j hj he
    exact summaryChunksFrom_disjoint tile 0 cs c d hc hd i j hi hj he

theorem layout_split (tile : Nat) (cs : List Chunk) (htile : 0 < tile) (h : Layout cs) :
    Layout (splitChunks tile cs) := by
  constructor
  · rw [splitChunks,splitChunksFrom_results]
    exact List.nodup_range' _
  · intro c hc d hd i hi j hj he
    exact splitChunksFrom_disjoint tile 0 cs htile h.unique h.disjoint c d hc hd i j hi hj he

theorem descriptors_small (tree : Trees) (cs : List Chunk) (h : Layout cs) :
    Descriptors tree (cs.filter (·.length ≤ 2^tree.depth)) := by
  have hl := layout_filter cs (·.length ≤ 2^tree.depth) h
  refine ⟨?_,hl.unique,hl.disjoint⟩
  intro c hc
  simpa using (List.mem_filter.mp hc).2

theorem descriptors_split (tree : Trees) (cs : List Chunk) (h : Layout cs) :
    Descriptors tree (splitChunks (2^tree.depth) cs) := by
  have hl := layout_split (2^tree.depth) cs (Nat.two_pow_pos _) h
  exact ⟨splitChunksFrom_capacity _ 0 cs,hl.unique,hl.disjoint⟩

/-- Point frame retains finished reductions while unfinished descriptors recurse
into the same destination array. -/
theorem local_reduce_point_frame (p : Program) (hcheck : p.check = .ok ()) (op : ReduceOp)
    (tree : Trees) (src dst : Nat) (cs : List Chunk) (mem : Memory) (hg : Good p mem)
    (hdesc : Descriptors tree cs) (htrace : TraceIn p (reduceDispatches op tree src dst cs))
    (a i : Nat) (ha : Outside tree a) (hout : a = dst → ∀ c ∈ cs, i ≠ c.result) :
    valueAt (evalTrace (reduceDispatches op tree src dst cs) mem) a i = valueAt mem a i := by
  have hphase := reduceTrace_checked p hcheck op tree src dst cs htrace
  exact localReduce_trace_frame p op tree src dst cs mem hg
    (bucket_depth_le cs tree.depth hdesc.capacity)
    (fun v b hb g hg ph hp => (hphase v b hb g hg ph hp).1) a i
    (fun k hk => (ha k hk).1) hout

/-- Point frame retains finished scan intervals during the long-descriptor
fix-up dispatches. -/
theorem local_scan_point_frame (p : Program) (hcheck : p.check = .ok ()) (op : ReduceOp)
    (mode : ScanMode) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (prefixBuffer : Option Nat) (mem : Memory) (hg : Good p mem)
    (hdesc : Descriptors tree cs)
    (htrace : TraceIn p (scanDispatches op mode tree src dst cs prefixBuffer))
    (a i : Nat) (ha : Outside tree a)
    (hout : a = dst → ∀ c ∈ cs, i < c.start ∨ c.start+c.length ≤ i) :
    valueAt (evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem) a i = valueAt mem a i := by
  have hphase := scanTrace_checked p hcheck op mode tree src dst cs prefixBuffer htrace
  exact localScan_trace_frame p op mode tree src dst cs prefixBuffer mem hg
    (bucket_depth_le cs tree.depth hdesc.capacity)
    (fun v b hb hv g hg ph hp => (hphase v b hb hv g hg ph hp).1) a i
    (fun k hk => (ha k hk).1) (fun k hk => (ha k hk).2) hout

theorem stateTraceIn_before (p : Program) (before after : Build) (he : Extends before after)
    (htrace : TraceIn p after.dispatches.toList) : TraceIn p before.dispatches.toList := by
  obtain ⟨ds,hds⟩ := he.2
  intro d hd
  apply htrace d
  rw [hds]
  exact List.mem_append_left ds hd

theorem traceIn_localReduce (p : Program) (op : ReduceOp) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (before after : Build)
    (h : (localReduce op tree src dst cs).run before = .ok ((),after))
    (htrace : TraceIn p after.dispatches.toList) : TraceIn p (reduceDispatches op tree src dst cs) := by
  have he := localReduce_success op tree src dst cs before after h
  subst after
  intro d hd
  apply htrace d
  simpa [appendTrace] using (List.mem_append_right before.dispatches.toList hd)

theorem traceIn_localScan (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (prefixBuffer : Option Nat) (before after : Build)
    (h : (localScan op mode tree src dst cs prefixBuffer).run before = .ok ((),after))
    (htrace : TraceIn p after.dispatches.toList) : TraceIn p (scanDispatches op mode tree src dst cs prefixBuffer) := by
  have he := localScan_success op mode tree src dst cs prefixBuffer before after h
  subst after
  intro d hd
  apply htrace d
  simpa [appendTrace] using (List.mem_append_right before.dispatches.toList hd)

end Obend.Hardware.Gpu.CollectiveExecute
end
