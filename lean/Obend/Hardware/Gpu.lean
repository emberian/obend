module
/-
# Obend.Hardware.Gpu — an array hypergraph lowered to compute shaders, one dispatch per wavefront

Rung G1 of `review/GPU-PROGRAM-20261105.md`: the first rung of the hardware tier that a GPU we own runs
(`hardware/gpu/verify_gpu.sh`, on hbox's RDNA2 card through Vulkan and on the Mac's GPU through Metal).

The source is an `ArrayGraph` (`Obend.Hardware.ArrayHypergraph`): wires carry vectors of 64-bit words,
a hyperedge is one array operation. The artifact is a `GpuProgram`: one flat wire buffer `w` holding
every wire at its base offset, a constant buffer `c`, an index buffer `ix` for gathers, and one compute
shader per wavefront stage of `layerGraph`. A stage's hyperedges become kernels; thread `t` of the stage
belongs to the kernel whose thread range holds it and is element `e` of that kernel: it reads its
operands from `w` as they stood when the dispatch began and writes `w[dstBase + e]`. Stages are separate
dispatches; the host orders them. Nothing a stage reads is written in that stage
(`layerEdges_all_stages_independent`), and two threads never write the same word (distinct destination
wires, disjoint wire ranges), so the program never depends on the device's memory model: it lives in the
apex fibre of the GPU fibration, sequential and exact modulo `2^64`. The memory model is rung G4's.

The scalar graphs of `Obend.Hardware.OpenHypergraph` run through the same lowering as their one-element
instance (`ofScalar`): `lowerHypergraphToGpu g = lowerArrayToGpu (ofScalar g)`.

## What is proved

* `lowerArrayToGpu_sound`: for a graph whose edges pass `edgeOk` (declared lengths consistent, every
  wire named exists; `ArrayGraph.wf` checks it, `wf_edgeOk`) and whose outputs exist, and for any wire environment of the declared lengths
  flattened into the buffer at the program's bases, `runProgram` (the order-free reading of every
  dispatch: a word's value is the write of the one thread that owns it) shows on every output wire the
  single-pass combinational evaluation `evalGraph`. The proof goes through the layering theorem and a
  per-stage flattening invariant; distinct destinations within a stage come from the layering's
  independence, disjoint ranges from the prefix-sum layout (`base_disjoint`).
* `lowerHypergraphToGpu_sound`: the scalar corollary, against `evalLayeredStagesSyncBv` of the scalar
  layering, through `ofScalar_layered_sound`.

## What is the gate

`emitStageWgsl` is text, like `emitModuleSV`; its faithfulness to `runProgram` is checked by running
it: `verify_gpu.sh` regenerates every committed shader and plan byte for byte, runs every vector of every
graph on the device against `runProgram`'s expected values, and requires each planted emitter rule
(`addAsSub`, `swapMux`) to make a comparison fail. With Mesa's RADV it also captures the final gfx1031
assembly of each shader, the artifact rung G2 reads.

## Departures from the device, named

WGSL `i64` arithmetic is modulo `2^64` by the WGSL specification, as `BitVec 64` is. A shift's amount is
`u32(x)` on the device and `x.toNat` in the model; both shift out everything at `64` and above, and they
agree for amounts below `2^32`, which is every amount a graph here produces. A missing operand reads as
`0`, as `evalHypergraphOpBv`'s `getD` does. Threads past a stage's last kernel do nothing. There is no
claim about workgroups, caches or scopes.
-/
public import Obend.Hardware.ArrayHypergraph
@[expose] public section

namespace Obend.Hardware.Gpu
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
set_option autoImplicit false

/-! ## 1. The program -/

/-- What one kernel's threads compute; element `e` writes `w[dstBase + e]`. -/
inductive KernelBody where
  /-- `op` of the operands `w[srcBase_i + e]`. -/
  | map (op : ElemOp) (srcBases : List Nat)
  /-- `c[cIdx]` for every element. -/
  | fill (cIdx : Nat)
  /-- `c[cIdx]` times the first operand `w[srcBase_0 + e]` (`0` with no operand). -/
  | scaleBy (cIdx : Nat) (srcBases : List Nat)
  /-- `w[srcBase + ix[ixBase + e]]`. -/
  | gather (ixBase srcBase : Nat)
  /-- `w[src0Base + e]` for `e < len0`, else `w[src1Base + (e - len0)]`. -/
  | concat (src0Base len0 src1Base : Nat)
  /-- `c[cBase + e]`. -/
  | const (cBase : Nat)
  deriving DecidableEq, Repr

structure Kernel where
  dstBase : Nat
  count   : Nat
  body    : KernelBody
  deriving DecidableEq, Repr

/-- One dispatch: its kernels' thread ranges are laid end to end. -/
structure GpuStage where
  kernels : List Kernel
  deriving DecidableEq, Repr

structure GpuProgram where
  words    : Nat
  wireBase : List Nat
  wireLen  : List Nat
  consts   : List Word
  tables   : List Nat
  inputs   : List Nat
  outputs  : List Nat
  stages   : List GpuStage
  deriving Repr

def workgroupSize : Nat := 64

def GpuStage.threads (s : GpuStage) : Nat := sumNatList (s.kernels.map (·.count))

/-! ## 2. Layout -/

/-- The base offset of wire `w`: the lengths of the wires before it. -/
def base : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | l :: ls, w + 1 => l + base ls w

theorem base_mono (ls : List Nat) (w1 w2 : Nat) (h12 : w1 < w2) (h1 : w1 < ls.length) :
    base ls w1 + ls.getD w1 0 ≤ base ls w2 := by
  induction ls generalizing w1 w2 with
  | nil => simp at h1
  | cons l ls ih =>
    cases w1 with
    | zero =>
      cases w2 with
      | zero => omega
      | succ k => simp [base]
    | succ a =>
      cases w2 with
      | zero => omega
      | succ b =>
        simp only [base, List.getD_cons_succ, List.length_cons] at *
        have := ih a b (by omega) (by omega)
        omega

/-- Words of distinct wires never coincide. -/
theorem base_disjoint (ls : List Nat) (w w' e e' : Nat) (hw : w < ls.length) (hw' : w' < ls.length)
    (he : e < ls.getD w 0) (he' : e' < ls.getD w' 0) (hne : w ≠ w') :
    base ls w + e ≠ base ls w' + e' := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := base_mono ls w w' h hw; omega
  · have := base_mono ls w' w h hw'; omega

/-! ## 3. Lowering -/

structure LowerState where
  c  : List Word
  ix : List Nat
  deriving Repr

def lowerEdge (ls : List Nat) (e : ArrayEdge) (st : LowerState) : Kernel × LowerState :=
  let len (w : Nat) := ls.getD w 0
  let b (w : Nat) := base ls w
  let dst := b e.dstWire
  let count := len e.dstWire
  match e.op with
  | .map _ (.scalar (.const v)) =>
    (⟨dst, count, .fill st.c.length⟩, { st with c := st.c ++ [BitVec.ofInt 64 v] })
  | .map _ (.scalar (.scale k)) =>
    (⟨dst, count, .scaleBy st.c.length (e.srcWires.map b)⟩, { st with c := st.c ++ [BitVec.ofInt 64 k] })
  | .map _ op => (⟨dst, count, .map op (e.srcWires.map b)⟩, st)
  | .gather f =>
    (⟨dst, count, .gather st.ix.length (b (e.srcWires.getD 0 0))⟩, { st with ix := st.ix ++ f.table })
  | .concat =>
    (⟨dst, count, .concat (b (e.srcWires.getD 0 0)) (len (e.srcWires.getD 0 0)) (b (e.srcWires.getD 1 0))⟩, st)
  | .const vs => (⟨dst, count, .const st.c.length⟩, { st with c := st.c ++ vs })

def lowerEdges (ls : List Nat) : List ArrayEdge → LowerState → List Kernel × LowerState
  | [], st => ([], st)
  | e :: es, st =>
    let r := lowerEdge ls e st
    let rs := lowerEdges ls es r.2
    (r.1 :: rs.1, rs.2)

def lowerStages (ls : List Nat) : List (List ArrayEdge) → LowerState → List GpuStage × LowerState
  | [], st => ([], st)
  | s :: ss, st =>
    let r := lowerEdges ls s st
    let rs := lowerStages ls ss r.2
    (⟨r.1⟩ :: rs.1, rs.2)

def lowerArrayToGpu (g : ArrayGraph) : GpuProgram :=
  let r := lowerStages g.lengths (layerGraph g) ⟨[], []⟩
  { words    := sumNatList g.lengths
  , wireBase := (List.range g.lengths.length).map (base g.lengths)
  , wireLen  := g.lengths
  , consts   := r.2.c
  , tables   := r.2.ix
  , inputs   := g.inputs
  , outputs  := g.outputs
  , stages   := r.1 }

/-- The scalar graphs, through their one-element instance. -/
def lowerHypergraphToGpu (g : StrictOpenHypergraph) : GpuProgram :=
  lowerArrayToGpu (ofScalar g)

/-! ## 4. Semantics (order-free: a word is the write of the thread that owns it) -/

def Kernel.owns (k : Kernel) (a : Nat) : Bool := decide (k.dstBase ≤ a ∧ a < k.dstBase + k.count)

def kernelValue (c : List Word) (ix : List Nat) (entry : Nat → Word) (k : Kernel) (e : Nat) : Word :=
  match k.body with
  | .map op bases     => evalElemOp op (bases.map fun b => entry (b + e))
  | .fill i           => c.getD i 0#64
  | .scaleBy i bases  => c.getD i 0#64 * (bases.map fun b => entry (b + e)).getD 0 0#64
  | .gather ixb b     => entry (b + ix.getD (ixb + e) 0)
  | .concat b0 l0 b1  => if e < l0 then entry (b0 + e) else entry (b1 + (e - l0))
  | .const cb         => c.getD (cb + e) 0#64

def runStage (c : List Word) (ix : List Nat) (entry : Nat → Word) (s : GpuStage) : Nat → Word :=
  fun a =>
    match s.kernels.find? (fun k => k.owns a) with
    | some k => kernelValue c ix entry k (a - k.dstBase)
    | none   => entry a

def runStages (c : List Word) (ix : List Nat) (entry : Nat → Word) (ss : List GpuStage) : Nat → Word :=
  ss.foldl (runStage c ix) entry

/-- The program's output wires, read from the buffer after every dispatch. -/
def runProgram (p : GpuProgram) (flat : Nat → Word) : List Vec :=
  let final := runStages p.consts p.tables flat p.stages
  p.outputs.map fun w => (List.range (p.wireLen.getD w 0)).map fun e => final (p.wireBase.getD w 0 + e)

/-! ## 5. Well-formed edges, environments and flattenings -/

/-- Every existing wire holds its declared length. -/
def Good (ls : List Nat) (env : Nat → Vec) : Prop :=
  ∀ w, w < ls.length → (env w).length = ls.getD w 0

/-- `flat` holds `env` at the layout's bases. -/
def Flat (ls : List Nat) (env : Nat → Vec) (flat : Nat → Word) : Prop :=
  ∀ w e, w < ls.length → e < ls.getD w 0 → flat (base ls w + e) = (env w).getD e 0#64

/-- A kernel realizes an edge: it owns the destination's range and, from any good flattening, each of
its elements is the edge's value there. -/
def KernelFor (ls : List Nat) (c : List Word) (ix : List Nat) (d : ArrayEdge) (k : Kernel) : Prop :=
  k.dstBase = base ls d.dstWire ∧ k.count = ls.getD d.dstWire 0 ∧
  ∀ (env : Nat → Vec) (flat : Nat → Word), Good ls env → Flat ls env flat →
    ∀ e, e < k.count →
      kernelValue c ix flat k e = (evalArrayOp d.op (d.srcWires.map env)).getD e 0#64

/-- Kernels realize edges one for one. -/
def KernelsFor (ls : List Nat) (c : List Word) (ix : List Nat) : List ArrayEdge → List Kernel → Prop
  | [], [] => True
  | d :: ds, k :: ks => KernelFor ls c ix d k ∧ KernelsFor ls c ix ds ks
  | _, _ => False

theorem getD_append_of_lt {α : Type} (c d : List α) (k : Nat) (z : α) (hk : k < c.length) :
    (c ++ d).getD k z = c.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_append_right {α : Type} (c d : List α) (k : Nat) (z : α) :
    (c ++ d).getD (c.length + k) z = d.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem getD_range_map {α : Type} (n : Nat) (f : Nat → α) (z : α) (e : Nat) (he : e < n) :
    ((List.range n).map f).getD e z = f e := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]

theorem lowerEdge_dst_count (ls : List Nat) (d : ArrayEdge) (st : LowerState) :
    (lowerEdge ls d st).1.dstBase = base ls d.dstWire ∧ (lowerEdge ls d st).1.count = ls.getD d.dstWire 0 := by
  cases hop : d.op with
  | map n op =>
    cases op with
    | scalar o => cases o <;> simp [lowerEdge, hop]
    | ult | band | bor | shr | shl => simp [lowerEdge, hop]
  | gather f => simp [lowerEdge, hop]
  | concat => simp [lowerEdge, hop]
  | const vs => simp [lowerEdge, hop]

/-- The edge's value at `e`, read from the flat buffer, for each operation. -/
theorem lowerEdge_kernelFor (ls : List Nat) (d : ArrayEdge) (st : LowerState) (hOk : edgeOk ls d = true)
    (dc : List Word) (dix : List Nat) :
    KernelFor ls ((lowerEdge ls d st).2.c ++ dc) ((lowerEdge ls d st).2.ix ++ dix) d (lowerEdge ls d st).1 := by
  simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk
  obtain ⟨⟨⟨hDst, hSrcs⟩, hLen⟩, hOp⟩ := hOk
  obtain ⟨hBase, hCount⟩ := lowerEdge_dst_count ls d st
  refine ⟨hBase, hCount, ?_⟩
  intro env flat hGood hFlat e he
  rw [hCount] at he
  have hRead : ∀ s, s ∈ d.srcWires → ∀ i, i < ls.getD s 0 → flat (base ls s + i) = (env s).getD i 0#64 :=
    fun s hs i hi => hFlat s i (hSrcs s hs) hi
  cases hop : d.op with
  | map n op =>
    simp only [hop, ArrayOp.outLen, List.all_eq_true, beq_iff_eq] at hLen hOp
    have hElem : ∀ s ∈ d.srcWires, flat (base ls s + e) = (env s).getD e 0#64 :=
      fun s hs => hRead s hs e (by rw [hOp s hs]; exact he)
    have hArr : (evalArrayOp (.map n op) (d.srcWires.map env)).getD e 0#64 =
        evalElemOp op (d.srcWires.map fun s => (env s).getD e 0#64) := by
      simp only [evalArrayOp]
      rw [getD_range_map n _ _ e (by rw [hLen]; exact he)]
      simp [List.map_map, Function.comp_def]
    have hOps : (d.srcWires.map (base ls)).map (fun b => flat (b + e)) =
        d.srcWires.map fun s => (env s).getD e 0#64 := by
      rw [List.map_map]
      exact List.map_congr_left fun s hs => by simp [Function.comp_def, hElem s hs]
    rw [hArr]
    cases op with
    | scalar o =>
      cases o with
      | const v =>
        simp only [lowerEdge, hop, kernelValue]
        rw [getD_append_of_lt _ _ _ _ (by simp)]
        simp [evalElemOp, evalHypergraphOpBv, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
      | scale k =>
        simp only [lowerEdge, hop, kernelValue]
        rw [getD_append_of_lt _ _ _ _ (by simp), hOps]
        simp [evalElemOp, evalHypergraphOpBv, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
      | add | sub | mul | mac | mux =>
        simp only [lowerEdge, hop, kernelValue]
        rw [hOps]
    | ult | band | bor | shr | shl =>
      simp only [lowerEdge, hop, kernelValue]
      rw [hOps]
  | gather f =>
    simp only [hop, ArrayOp.outLen, Bool.and_eq_true, beq_iff_eq] at hLen hOp
    obtain ⟨⟨hfwf, hOne⟩, hTarget⟩ := hOp
    rw [← hLen] at he
    simp only [FiniteFunction.wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hfwf
    obtain ⟨hTabLen, hTabLt⟩ := hfwf
    have heTab : e < f.table.length := by rw [hTabLen]; exact he
    obtain ⟨s, hs⟩ : ∃ s, d.srcWires = [s] := by
      cases h : d.srcWires with
      | nil => simp [h] at hOne
      | cons s rest => cases rest with
        | nil => exact ⟨s, rfl⟩
        | cons _ _ => simp [h] at hOne
    have hsMem : s ∈ d.srcWires := by rw [hs]; exact List.mem_cons_self
    rw [hs] at hTarget
    simp only [List.getD_cons_zero] at hTarget
    have hIdx : f.table.getD e 0 = f.table[e] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem heTab]
    have hi : f.table.getD e 0 < ls.getD s 0 := by
      rw [← hTarget, hIdx]
      exact hTabLt _ (List.getElem_mem heTab)
    have hkv : kernelValue ((lowerEdge ls d st).2.c ++ dc) ((lowerEdge ls d st).2.ix ++ dix) flat
        (lowerEdge ls d st).1 e = flat (base ls s + f.table.getD e 0) := by
      simp only [lowerEdge, hop, kernelValue, hs, List.getD_cons_zero]
      rw [List.append_assoc, getD_append_right st.ix (f.table ++ dix) e 0, getD_append_of_lt f.table dix e 0 heTab]
    have hav : (evalArrayOp (.gather f) (d.srcWires.map env)).getD e 0#64 = (env s).getD (f.table.getD e 0) 0#64 := by
      simp only [evalArrayOp, hs, List.map_cons, List.map_nil, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem heTab, hIdx]
      rfl
    rw [hkv, hav]
    exact hRead s hsMem _ hi
  | concat =>
    simp only [hop, ArrayOp.outLen, beq_iff_eq] at hLen hOp
    obtain ⟨s0, s1, hs⟩ : ∃ s0 s1, d.srcWires = [s0, s1] := by
      cases h : d.srcWires with
      | nil => simp [h] at hOp
      | cons s0 rest => cases rest with
        | nil => simp [h] at hOp
        | cons s1 rest2 => cases rest2 with
          | nil => exact ⟨s0, s1, rfl⟩
          | cons _ _ => simp [h] at hOp
    have h0 : s0 ∈ d.srcWires := by rw [hs]; exact List.mem_cons_self
    have h1 : s1 ∈ d.srcWires := by rw [hs]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have he' : e < ls.getD s0 0 + ls.getD s1 0 := by
      rw [← hLen, hs] at he
      simpa using he
    have hLen0 := hGood s0 (hSrcs s0 h0)
    simp only [lowerEdge, hop, kernelValue, evalArrayOp, hs, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    by_cases hlt : e < ls.getD s0 0
    · rw [if_pos hlt, hRead s0 h0 e hlt]
      exact (getD_append_of_lt (env s0) (env s1) e 0#64 (by rw [hLen0]; exact hlt)).symm
    · rw [if_neg hlt, hRead s1 h1 (e - ls.getD s0 0) (by omega)]
      have h' := getD_append_right (env s0) (env s1) (e - ls.getD s0 0) 0#64
      rw [hLen0, show ls.getD s0 0 + (e - ls.getD s0 0) = e by omega] at h'
      exact h'.symm
  | const vs =>
    simp only [hop, ArrayOp.outLen] at hLen
    rw [← hLen] at he
    simp only [lowerEdge, hop, kernelValue, evalArrayOp]
    rw [List.append_assoc, getD_append_right st.c (vs ++ dc) e 0#64, getD_append_of_lt vs dc e 0#64 he]

/-- Lowering only appends to the constant and index buffers. -/
theorem lowerEdge_extends (ls : List Nat) (d : ArrayEdge) (st : LowerState) :
    ∃ dc dix, (lowerEdge ls d st).2.c = st.c ++ dc ∧ (lowerEdge ls d st).2.ix = st.ix ++ dix := by
  cases hop : d.op with
  | map n op =>
    cases op with
    | scalar o => cases o <;> simp [lowerEdge, hop]
    | ult | band | bor | shr | shl => simp [lowerEdge, hop]
  | gather f => exact ⟨[], f.table, by simp [lowerEdge, hop]⟩
  | concat => simp [lowerEdge, hop]
  | const vs => exact ⟨vs, [], by simp [lowerEdge, hop]⟩

theorem lowerEdges_extends (ls : List Nat) (es : List ArrayEdge) (st : LowerState) :
    ∃ dc dix, (lowerEdges ls es st).2.c = st.c ++ dc ∧ (lowerEdges ls es st).2.ix = st.ix ++ dix := by
  induction es generalizing st with
  | nil => exact ⟨[], [], by simp [lowerEdges]⟩
  | cons e es ih =>
    obtain ⟨c1, i1, hc1, hi1⟩ := lowerEdge_extends ls e st
    obtain ⟨c2, i2, hc2, hi2⟩ := ih (lowerEdge ls e st).2
    refine ⟨c1 ++ c2, i1 ++ i2, ?_, ?_⟩
    · simp only [lowerEdges]; rw [hc2, hc1, List.append_assoc]
    · simp only [lowerEdges]; rw [hi2, hi1, List.append_assoc]

theorem lowerStages_extends (ls : List Nat) (ss : List (List ArrayEdge)) (st : LowerState) :
    ∃ dc dix, (lowerStages ls ss st).2.c = st.c ++ dc ∧ (lowerStages ls ss st).2.ix = st.ix ++ dix := by
  induction ss generalizing st with
  | nil => exact ⟨[], [], by simp [lowerStages]⟩
  | cons s ss ih =>
    obtain ⟨c1, i1, hc1, hi1⟩ := lowerEdges_extends ls s st
    obtain ⟨c2, i2, hc2, hi2⟩ := ih (lowerEdges ls s st).2
    refine ⟨c1 ++ c2, i1 ++ i2, ?_, ?_⟩
    · simp only [lowerStages]; rw [hc2, hc1, List.append_assoc]
    · simp only [lowerStages]; rw [hi2, hi1, List.append_assoc]

/-- A lowered stage's kernels realize its edges, one for one, against any extension of the buffers. -/
theorem lowerEdges_forall₂ (ls : List Nat) (es : List ArrayEdge) (st : LowerState)
    (hOk : ∀ d ∈ es, edgeOk ls d = true) (dc : List Word) (dix : List Nat) :
    KernelsFor ls ((lowerEdges ls es st).2.c ++ dc) ((lowerEdges ls es st).2.ix ++ dix)
      es (lowerEdges ls es st).1 := by
  induction es generalizing st with
  | nil => trivial
  | cons e es ih =>
    obtain ⟨c2, i2, hc2, hi2⟩ := lowerEdges_extends ls es (lowerEdge ls e st).2
    simp only [lowerEdges, KernelsFor]
    refine ⟨?_, ih _ (fun d hd => hOk d (List.mem_cons_of_mem e hd))⟩
    rw [hc2, hi2, List.append_assoc, List.append_assoc]
    exact lowerEdge_kernelFor ls e st (hOk e List.mem_cons_self) (c2 ++ dc) (i2 ++ dix)

/-! ## 6. One dispatch -/

/-- With distinct destinations, the synchronous stage writes each wire from the edge that owns it. -/
theorem evalStageAux_find (entry cur : Nat → Vec) (stage : List ArrayEdge)
    (hNodup : (stage.map (·.dstWire)).Nodup) (w : Nat) :
    evalStageAux entry cur stage w =
      match stage.find? (fun d => d.dstWire == w) with
      | some d => evalArrayOp d.op (d.srcWires.map entry)
      | none   => cur w := by
  induction stage generalizing cur with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hNodup
    simp only [evalStageAux, List.find?_cons]
    rw [ih _ hNodup.2]
    by_cases hw : d.dstWire = w
    · subst hw
      have hNone : rest.find? (fun d' => d'.dstWire == d.dstWire) = none := by
        rw [List.find?_eq_none]
        intro d' hd' hEq
        exact hNodup.1 ⟨d', hd', beq_iff_eq.mp hEq⟩
      rw [hNone]
      simp only [beq_self_eq_true, stepEdgeSync, ↓reduceIte]
    · have h1 : (d.dstWire == w) = false := beq_eq_false_iff_ne.mpr hw
      have h2 : (w == d.dstWire) = false := beq_eq_false_iff_ne.mpr (Ne.symm hw)
      rcases hf : rest.find? (fun d' => d'.dstWire == w) with _ | d'
      · simp only [hf, h1, h2, stepEdgeSync, Bool.false_eq_true, ↓reduceIte]
      · simp only [hf, h1]

/-- The kernel found by the address it owns is the kernel of the edge found by the wire it writes. -/
theorem find_kernel (ls : List Nat) (c : List Word) (ix : List Nat)
    (stage : List ArrayEdge) (kernels : List Kernel)
    (hRel : KernelsFor ls c ix stage kernels)
    (hNodup : (stage.map (·.dstWire)).Nodup)
    (hOk : ∀ d ∈ stage, d.dstWire < ls.length)
    (w e : Nat) (hw : w < ls.length) (he : e < ls.getD w 0) :
    (kernels.find? (fun k => k.owns (base ls w + e)) = none ↔
      stage.find? (fun d => d.dstWire == w) = none) ∧
    (∀ k, kernels.find? (fun k => k.owns (base ls w + e)) = some k →
      ∃ d, stage.find? (fun d => d.dstWire == w) = some d ∧ KernelFor ls c ix d k ∧
        k.dstBase = base ls w ∧ d.dstWire = w) := by
  induction stage generalizing kernels with
  | nil =>
    cases kernels with
    | nil => simp
    | cons k ks => exact absurd hRel id
  | cons d stage' ih =>
    cases kernels with
    | nil => exact absurd hRel id
    | cons k kernels' =>
    obtain ⟨hdk, hRest⟩ := hRel
    simp only [List.map_cons, List.nodup_cons] at hNodup
    have hOk' : ∀ d' ∈ stage', d'.dstWire < ls.length := fun d' hd' => hOk d' (List.mem_cons_of_mem d hd')
    have hdLt := hOk d List.mem_cons_self
    by_cases hdw : d.dstWire = w
    · have he' : e < ls.getD d.dstWire 0 := by rw [hdw]; exact he
      have hOwns : k.owns (base ls w + e) = true := by
        rw [Kernel.owns, decide_eq_true_eq, hdk.1, hdk.2.1, ← hdw]
        omega
      have hEq : (d.dstWire == w) = true := beq_iff_eq.mpr hdw
      simp only [List.find?_cons, hOwns, hEq]
      refine ⟨by simp, ?_⟩
      intro k' hk'
      simp only [Option.some.injEq] at hk'
      subst hk'
      exact ⟨d, rfl, hdk, by rw [hdk.1, hdw], hdw⟩
    · have hNot : k.owns (base ls w + e) = false := by
        rw [Kernel.owns, decide_eq_false_iff_not, hdk.1, hdk.2.1]
        intro ⟨hle, hlt⟩
        exact base_disjoint ls d.dstWire w (base ls w + e - base ls d.dstWire) e hdLt hw
          (by omega) he hdw (by omega)
      have hNe : (d.dstWire == w) = false := beq_eq_false_iff_ne.mpr hdw
      simp only [List.find?_cons, hNot, hNe]
      exact ih kernels' hRest hNodup.2 hOk'

/-- **One dispatch is one synchronous stage.** -/
theorem runStage_sound (ls : List Nat) (c : List Word) (ix : List Nat)
    (stage : List ArrayEdge) (kernels : List Kernel)
    (hRel : KernelsFor ls c ix stage kernels)
    (hNodup : (stage.map (·.dstWire)).Nodup)
    (hOk : ∀ d ∈ stage, d.dstWire < ls.length)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good ls env) (hFlat : Flat ls env flat) :
    Flat ls (evalStageSync env stage) (runStage c ix flat ⟨kernels⟩) := by
  intro w e hw he
  have hFind := find_kernel ls c ix stage kernels hRel hNodup hOk w e hw he
  simp only [runStage, evalStageSync]
  rw [evalStageAux_find env env stage hNodup w]
  rcases hk : kernels.find? (fun k => k.owns (base ls w + e)) with _ | k
  · rw [hk, hFind.1.mp hk]
    exact hFlat w e hw he
  · obtain ⟨d, hd, hdk, hBase, hdw⟩ := hFind.2 k hk
    rw [hk, hd]
    show kernelValue c ix flat k (base ls w + e - k.dstBase) =
      List.getD (evalArrayOp d.op (d.srcWires.map env)) e 0#64
    rw [hBase, Nat.add_sub_cancel_left]
    exact hdk.2.2 env flat hGood hFlat e (by rw [hdk.2.1, hdw]; exact he)

theorem evalStageSync_good (ls : List Nat) (stage : List ArrayEdge)
    (hOk : ∀ d ∈ stage, edgeOk ls d = true) (env : Nat → Vec) (hGood : Good ls env) :
    Good ls (evalStageSync env stage) := by
  intro w hw
  simp only [evalStageSync]
  suffices h : ∀ (cur : Nat → Vec), Good ls cur → (evalStageAux env cur stage w).length = ls.getD w 0 from
    h env hGood
  induction stage with
  | nil => intro cur hcur; exact hcur w hw
  | cons d rest ih =>
    intro cur hcur
    simp only [evalStageAux]
    refine ih (fun d' hd' => hOk d' (List.mem_cons_of_mem d hd')) _ ?_
    intro u hu
    simp only [stepEdgeSync]
    by_cases hud : u == d.dstWire
    · rw [if_pos hud]
      have hOkd := hOk d List.mem_cons_self
      simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hOkd
      have hfw : ∀ f, d.op = .gather f → f.wf = true := by
        intro f hf
        have := hOkd.2
        simp only [hf, Bool.and_eq_true] at this
        exact this.1.1
      rw [evalArrayOp_length d.op _ hfw]
      have hLens : (d.srcWires.map env).map List.length = d.srcWires.map (ls.getD · 0) := by
        rw [List.map_map]
        exact List.map_congr_left fun s hs => hGood s (hOkd.1.1.2 s hs)
      rw [hLens, hOkd.1.2, beq_iff_eq.mp hud]
    · rw [if_neg (by simpa using hud)]
      exact hcur u hu

/-! ## 7. The program -/

theorem runStages_sound (ls : List Nat) (c : List Word) (ix : List Nat)
    (stages : List (List ArrayEdge)) (st : LowerState)
    (hOk : ∀ s ∈ stages, ∀ d ∈ s, edgeOk ls d = true)
    (hInd : stages.all ArrayHypergraph.checkStageIndependent = true)
    (dc : List Word) (dix : List Nat)
    (hc : c = (lowerStages ls stages st).2.c ++ dc) (hix : ix = (lowerStages ls stages st).2.ix ++ dix)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good ls env) (hFlat : Flat ls env flat) :
    Flat ls (evalLayeredSync env stages) (runStages c ix flat (lowerStages ls stages st).1) ∧
    Good ls (evalLayeredSync env stages) := by
  induction stages generalizing st env flat with
  | nil => exact ⟨hFlat, hGood⟩
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hInd
    have hOkS : ∀ d ∈ s, edgeOk ls d = true := hOk s List.mem_cons_self
    have hOkSS : ∀ s' ∈ ss, ∀ d ∈ s', edgeOk ls d = true := fun s' hs' => hOk s' (List.mem_cons_of_mem s hs')
    obtain ⟨c2, i2, hc2, hi2⟩ := lowerStages_extends ls ss (lowerEdges ls s st).2
    simp only [lowerStages] at hc hix ⊢
    have hcS : c = (lowerEdges ls s st).2.c ++ (c2 ++ dc) := by rw [hc, hc2, List.append_assoc]
    have hixS : ix = (lowerEdges ls s st).2.ix ++ (i2 ++ dix) := by rw [hix, hi2, List.append_assoc]
    have hRel := lowerEdges_forall₂ ls s st hOkS (c2 ++ dc) (i2 ++ dix)
    rw [← hcS, ← hixS] at hRel
    have hNodup := checkStageIndependent_nodup s hInd.1
    have hDst : ∀ d ∈ s, d.dstWire < ls.length := by
      intro d hd
      have := hOkS d hd
      simp only [edgeOk, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1.1
    have hFlat' := runStage_sound ls c ix s _ hRel hNodup hDst env flat hGood hFlat
    have hGood' := evalStageSync_good ls s hOkS env hGood
    simp only [evalLayeredSync, runStages, List.foldl_cons]
    exact ih (lowerEdges ls s st).2 hOkSS hInd.2 hc hix (evalStageSync env s)
      (runStage c ix flat ⟨(lowerEdges ls s st).1⟩) hGood' hFlat'

/-- **`lowerArrayToGpu_sound`**: on a graph whose edges and outputs are well-formed, the lowered program
run from any flattening of a good wire environment shows `evalGraph g env` on its output wires. -/
theorem lowerArrayToGpu_sound (g : ArrayGraph)
    (hOk : ∀ d ∈ g.edges, edgeOk g.lengths d = true)
    (hOut : ∀ w ∈ g.outputs, w < g.lengths.length)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good g.lengths env) (hFlat : Flat g.lengths env flat) :
    runProgram (lowerArrayToGpu g) flat = evalGraph g env := by
  have hLayer := layerGraph_sound g env
  have hOkS : ∀ s ∈ layerGraph g, ∀ d ∈ s, edgeOk g.lengths d = true := by
    intro s hs d hd
    apply hOk
    rw [← hLayer.2.1]
    exact List.mem_flatten.mpr ⟨s, hs, hd⟩
  obtain ⟨hFlat', hGood'⟩ := runStages_sound g.lengths
    (lowerStages g.lengths (layerGraph g) ⟨[], []⟩).2.c (lowerStages g.lengths (layerGraph g) ⟨[], []⟩).2.ix
    (layerGraph g) ⟨[], []⟩ hOkS hLayer.1 [] [] (List.append_nil _).symm (List.append_nil _).symm
    env flat hGood hFlat
  simp only [runProgram, lowerArrayToGpu, evalGraph]
  rw [← hLayer.2.2]
  apply List.map_congr_left
  intro w hw
  have hwLt := hOut w hw
  rw [getD_range_map g.lengths.length (base g.lengths) 0 w hwLt]
  apply List.ext_getElem
  · simp [hGood' w hwLt]
  · intro e h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have he : e < g.lengths.getD w 0 := by simpa using h1
    rw [hFlat' w e hwLt he]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! ## 8. The scalar corollary -/

theorem base_replicate_one (n w : Nat) (hw : w ≤ n) : base (List.replicate n 1) w = w := by
  induction n generalizing w with
  | zero => cases w <;> simp_all [base]
  | succ n ih =>
    cases w with
    | zero => rfl
    | succ k => simp only [List.replicate_succ, base]; rw [ih k (by omega)]; omega

/-- **`lowerHypergraphToGpu_sound`**: a scalar graph, run as its one-element instance from the scalar
environment laid out one word per wire, shows the scalar 64-bit layered evaluation on every output. -/
theorem lowerHypergraphToGpu_sound (g : StrictOpenHypergraph)
    (hOk : ∀ d ∈ (ofScalar g).edges, edgeOk (ofScalar g).lengths d = true)
    (hOut : ∀ w ∈ g.boundaryOut.table, w < g.nodeTypes.length)
    (env : Nat → Word) :
    runProgram (lowerHypergraphToGpu g) env =
      g.boundaryOut.table.map fun w => [evalLayeredStagesSyncBv env (layerHypergraph g) w] := by
  have hn : (ofScalar g).lengths.length = g.nodeTypes.length := by simp [ofScalar]
  have hGood : Good (ofScalar g).lengths (singletonEnv env) := by
    intro w hw
    rw [hn] at hw
    simp [ofScalar, singletonEnv, List.getD_eq_getElem?_getD, List.getElem?_replicate, hw]
  have hFlat : Flat (ofScalar g).lengths (singletonEnv env) env := by
    intro w e hw he
    rw [hn] at hw
    have hl : (ofScalar g).lengths = List.replicate g.nodeTypes.length 1 := rfl
    rw [hl] at he ⊢
    have he0 : e = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate] at he
      simp [hw] at he
      omega
    subst he0
    rw [base_replicate_one g.nodeTypes.length w (Nat.le_of_lt hw)]
    rfl
  have hOut' : ∀ w ∈ (ofScalar g).outputs, w < (ofScalar g).lengths.length := by
    intro w hw
    rw [hn]
    exact hOut w hw
  rw [lowerHypergraphToGpu, lowerArrayToGpu_sound (ofScalar g) hOk hOut' _ env hGood hFlat]
  simp only [evalGraph]
  rw [← (layerGraph_sound (ofScalar g) (singletonEnv env)).2.2, ofScalar_layered_sound]
  rfl

/-! ## 9. The emitter (WGSL), checked by running it -/

/-- Rules planted in the emitted text only, for the verify script's tooth. -/
inductive Plant where
  | none
  | addAsSub
  | swapMux
  deriving DecidableEq, Repr

def Plant.ofString? : String → Option Plant
  | "addAsSub" => some .addAsSub
  | "swapMux"  => some .swapMux
  | _          => Option.none

/-- Operand `i` of a map kernel at element `e`: its word, or `0` when the edge has no such source. -/
def operand (bases : List Nat) (i : Nat) : String :=
  match bases[i]? with
  | some b => s!"w[{b}u + e]"
  | Option.none => "i64(0)"

def elemExpr (p : Plant) (op : ElemOp) (bases : List Nat) : String :=
  let a (i : Nat) := operand bases i
  match op with
  | .scalar .add       => if p == .addAsSub then s!"{a 0} - {a 1}" else s!"{a 0} + {a 1}"
  | .scalar .sub       => s!"{a 0} - {a 1}"
  | .scalar .mul       => s!"{a 0} * {a 1}"
  | .scalar .mac       => s!"{a 0} * {a 1} + {a 2}"
  | .scalar .mux       =>
    if p == .swapMux then s!"select({a 1}, {a 2}, {a 0} != i64(0))"
    else s!"select({a 2}, {a 1}, {a 0} != i64(0))"
  | .scalar (.const _) => "i64(0) /* unreachable: lowered to fill */"
  | .scalar (.scale _) => "i64(0) /* unreachable: lowered to scaleBy */"
  | .ult               => s!"select(i64(0), i64(1), u64({a 0}) < u64({a 1}))"
  | .band              => s!"{a 0} & {a 1}"
  | .bor               => s!"{a 0} | {a 1}"
  | .shr               => s!"{a 0} >> u32({a 1})"
  | .shl               => s!"{a 0} << u32({a 1})"

def kernelStatement (p : Plant) (k : Kernel) : String :=
  let rhs : String :=
    match k.body with
    | .map op bases      => elemExpr p op bases
    | .fill i            => s!"c[{i}u]"
    | .scaleBy i bases   => s!"c[{i}u] * {operand bases 0}"
    | .gather ixb b      => s!"w[{b}u + ix[{ixb}u + e]]"
    | .concat b0 l0 b1   => s!"select(w[{b1}u + (e - {l0}u)], w[{b0}u + e], e < {l0}u)"
    | .const cb          => s!"c[{cb}u + e]"
  s!"w[{k.dstBase}u + e] = {rhs};"

/-- The shader of stage `k`: thread `gid.x` finds its kernel by the thread ranges laid end to end,
becomes element `e` of it, and runs its statement; threads past the last kernel idle. -/
def emitStageWgsl (p : Plant) (name : String) (k numStages : Nat) (s : GpuStage) : String :=
  let branches := (s.kernels.foldl (fun (acc : Nat × List String) kern =>
    let hi := acc.1 + kern.count
    (hi, acc.2 ++ [s!"  {if acc.2.isEmpty then "if" else "else if"} (t < {hi}u) \{ let e : u32 = t - {acc.1}u; {kernelStatement p kern} }"]))
    (0, [])).2
  String.intercalate "\n"
    ([ s!"// obend-emit-gpu: {name}, stage {k} of {numStages}: {s.kernels.length} kernels, {s.threads} threads."
     , "// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes)."
     , "@group(0) @binding(0) var<storage, read_write> w : array<i64>;"
     , "@group(0) @binding(1) var<storage, read> c : array<i64>;"
     , "@group(0) @binding(2) var<storage, read> ix : array<u32>;"
     , ""
     , s!"@compute @workgroup_size({workgroupSize})"
     , "fn main(@builtin(global_invocation_id) gid : vec3<u32>) {"
     , "  let t : u32 = gid.x;" ] ++ branches ++ [ "}", "" ])

/-- The dispatch plan the host reads: the buffer sizes, the constant and index buffers, every wire's
base and length, the boundary wires, and each stage's shader file and thread count. -/
def emitPlanJson (name : String) (p : GpuProgram) : String :=
  let nums (xs : List Nat) := String.intercalate "," (xs.map toString)
  let consts := String.intercalate "," (p.consts.map fun v => s!"\"{v.toInt}\"")
  let stages := String.intercalate ",\n    " (p.stages.zipIdx.map fun (s, i) =>
    s!"\{\"file\":\"stage_{i}.wgsl\",\"threads\":{s.threads}}")
  String.intercalate "\n"
    [ "{"
    , s!"  \"graph\": \"{name}\","
    , s!"  \"words\": {p.words},"
    , s!"  \"workgroupSize\": {workgroupSize},"
    , s!"  \"wireBase\": [{nums p.wireBase}],"
    , s!"  \"wireLen\": [{nums p.wireLen}],"
    , s!"  \"consts\": [{consts}],"
    , s!"  \"tables\": [{nums p.tables}],"
    , s!"  \"inputs\": [{nums p.inputs}],"
    , s!"  \"outputs\": [{nums p.outputs}],"
    , s!"  \"stages\": [\n    {stages}\n  ]"
    , "}"
    , "" ]

/-- The wire environment for one vector: boundary input `i` holds `vals[i]`, every other wire zeros of
its declared length. -/
def mkEnv (ls : List Nat) (inputs : List Nat) (vals : List Vec) : Nat → Vec :=
  fun w =>
    match (inputs.zip vals).find? (fun iv => iv.1 == w) with
    | some iv => iv.2
    | Option.none => List.replicate (ls.getD w 0) 0#64

end Obend.Hardware.Gpu
