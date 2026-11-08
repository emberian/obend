module
/-
# Obend.Hardware.Gpu — an array hypergraph lowered to compute shaders, one dispatch per wavefront

Rung G1 of `review/GPU-PROGRAM-20261105.md`: the first rung of the hardware tier that a GPU we own runs
(`hardware/gpu/verify_gpu.sh`, on hbox's RDNA2 card through Vulkan and on the Mac's GPU through Metal).

The source is an `ArrayGraph` (`Obend.Hardware.ArrayHypergraph`): wires carry vectors of 64-bit words,
a hyperedge is one array operation. The artifact is a `GpuProgram`: one flat storage buffer `w` with
liveness-allocated wire ranges, a constant buffer `c`, an index buffer `ix` for gathers, and one compute
shader per wavefront stage of `layerGraph` applied to `fuseGraph` of the source. Fusion first: every
map edge recomputes its elementwise producers, so a chain of elementwise edges is one kernel whose
thread runs the chain as local `let`s, and the producers nobody else reads are gone. Then the level
layering: a stage is a frontier of edges whose predecessors were all dispatched. A stage's hyperedges
become kernels; invocation `t` belongs to a kernel. A map invocation writes one element; a fold
invocation owns a segment and runs a linear accumulator loop. `kernelInvocationValues_flatten`
connects those loops to the output-address semantics. Every invocation it reads its operands from `w` as they stood when the dispatch began and
writes `w[dstBase + e]`. Stages are separate dispatches; the host orders them. `allocateLayout` recycles
buffers after their final read, and permits in-place reuse only by the sole elementwise consumer of a
source on that final read. `layoutOk` independently checks live-value preservation, bounds, and absence
of cross-thread aliases. `stageRaceFree_alias` proves any read/write overlap belongs to the same map
kernel and element; `stageRaceFree_writes` excludes writes to a common word by distinct destinations.
The program therefore lives in the apex fibre, sequential and exact modulo `2^64`; weak memory is G4.

The scalar graphs of `Obend.Hardware.OpenHypergraph` run through the same lowering as their one-element
instance (`ofScalar`): `lowerHypergraphToGpu g = lowerArrayToGpu (ofScalar g)`.

## What is proved

* `lowerArrayToGpu_sound`: for a well-formed graph and a layout passing the executable `layoutOk`
  check, any good wire environment represented on the initially live wires yields `evalGraph` on the
  outputs. Dead wires need no representation. The proof composes `fuseGraph_sound`, `layerGraph_sound`,
  and `runStages_sound`, whose invariant tracks live wires backwards from the outputs. Physical ranges
  may coincide when the wires' live intervals do not. Program kernels are simulated instruction by
  instruction (`runKCode_sim`). The allocator is an untrusted heuristic; its result is checked before
  emission, and the theorem is universal over environments satisfying this finite layout certificate.
* `lowerHypergraphToGpu_sound`: the scalar corollary, against `evalLayeredStagesSyncBv` of the scalar
  layering, through `ofScalar_layered_sound`.

## What is the gate

`emitStageWgsl` is text, like `emitModuleSV`; its faithfulness to `runProgram` is checked by running
it: `verify_gpu.sh` regenerates every committed shader and plan byte for byte (or its digest, for the
graph whose plan is too large to commit), runs every vector of every graph on the device against
`runProgram`'s expected values, and requires each planted emitter rule (`addAsSub`, `swapMux`, `mulHighZero`) to make a
comparison fail. With Mesa's RADV it also captures the final gfx1031 assembly of each shader, the
artifact rung G2 reads.

## Departures from the device, named

Storage and registers use `vec2<u32>`; carries, comparisons, shifts, and reduction use u32 operations.
`Limbs` and `LimbsShift` refine them to the original `BitVec 64` semantics. WGSL has no extended-u32
multiply builtin, so the only widened expression multiplies two explicitly u32 operands and extracts
its low/high limbs. `mul32_widen` proves that bounded primitive; RADV emits `v_mul_lo_u32` and
`v_mul_hi_u32`. This uses Naga/wgpu's SHADER_INT64 extension, not a standard WGSL integer type.
There is no general 64×64 multiply in the shader. Missing operands remain zero. Shifts handle every
64-bit count, including counts at least 64, rather than truncating the count. The workgroup source and
its G4 phase certificates live in `ArrayKernel`, `Gpu.BlockLower`, `Gpu.Workgroup`, and `Gpu.SourceProtocol`.

Expected values: a closure-based evaluator recomputed every wire on every read and was exponential in
dependency depth; `obend-emit-gpu` uses `evalGraphArr` (wires as arrays, local names in a hash map).
-/
public import Obend.Hardware.ArrayHypergraph
public import Obend.Hardware.Gpu.Limbs
@[expose] public section

namespace Obend.Hardware.Gpu
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
set_option autoImplicit false

/-! ## 1. The program -/

/-- An operand of a kernel instruction at element `e`. -/
inductive KOperand where
  /-- `w[base + e]`. -/
  | read (base : Nat)
  /-- `c[i]`. -/
  | cst (i : Nat)
  /-- the local `w`. -/
  | tmp (w : Nat)
  deriving DecidableEq, Repr

structure KInstr where
  op   : ElemOp
  args : List KOperand
  dst  : Nat
  deriving DecidableEq, Repr

/-- What one kernel's threads compute; element `e` writes `w[dstBase + e]`. -/
inductive KernelBody where
  /-- the instructions in order over locals that start at `0`; the local `out`. -/
  | prog (code : List KInstr) (out : Nat)
  /-- `w[srcBase + ix[ixBase + e]]`. -/
  | gather (ixBase srcBase : Nat)
  /-- `w[src0Base + e]` for `e < len0`, else `w[src1Base + (e - len0)]`. -/
  | concat (src0Base len0 src1Base : Nat)
  /-- `c[cBase + e]`. -/
  | const (cBase : Nat)
  /-- One invocation per segment; scans write every element of their segment. -/
  | fold (op : ReduceOp) (shape : FoldShape) (srcBase : Nat)
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

/-- Invocation count differs from output count for sequential-segment scans. -/
def Kernel.threads (k : Kernel) : Nat :=
  match k.body with
  | .fold _ shape _ => shape.segments.length
  | _ => k.count

def GpuStage.threads (s : GpuStage) : Nat := sumNatList (s.kernels.map (·.threads))

/-! ## 2. Layout -/

/-- Physical storage, in words. Dead fused wires have base zero and are never accessed. -/
structure Layout where
  bases : Array Nat
  words : Nat
  deriving Repr

def Layout.base (l : Layout) (w : Nat) : Nat := l.bases[w]?.getD 0

/-- Live before a dispatch: its reads, and values needed afterwards that it does not define. -/
def liveBefore (stage : List ArrayEdge) (after : List Nat) : List Nat :=
  stage.flatMap (·.srcWires) ++ after.filter (fun w => !(stage.any (·.dstWire == w)))

def liveAt : List (List ArrayEdge) → List Nat → List Nat
  | [], outputs => outputs
  | s :: ss, outputs => liveBefore s (liveAt ss outputs)

/-- Intervals are disjoint, including empty wires. -/
def separated (ls : List Nat) (b : Nat → Nat) (u v : Nat) : Bool :=
  ls.getD u 0 == 0 || ls.getD v 0 == 0 ||
    b u + ls.getD u 0 ≤ b v || b v + ls.getD v 0 ≤ b u

theorem separated_ne (ls : List Nat) (b : Nat → Nat) (u v i j : Nat)
    (h : separated ls b u v = true) (hi : i < ls.getD u 0) (hj : j < ls.getD v 0) :
    b u + i ≠ b v + j := by
  simp only [separated, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

/-- Every destination is disjoint from every other value live after the dispatch. In particular,
this permits overwriting a source whose last use is this dispatch. -/
def preservesLive (ls : List Nat) (b : Nat → Nat) (s : List ArrayEdge) (after : List Nat) : Bool :=
  s.all fun d => after.all fun w => d.dstWire == w || separated ls b d.dstWire w

/-- A dispatch has no write/write races and no cross-thread read/write aliases. The only allowed
read/write overlap is an elementwise kernel reading exactly its own destination range. Different
kernels sharing that source forbid takeover, even when both consumers are elementwise. -/
def stageRaceFree (ls : List Nat) (b : Nat → Nat) (s : List ArrayEdge) : Bool :=
  s.all fun d => s.all fun r =>
    (d.dstWire == r.dstWire || separated ls b d.dstWire r.dstWire) &&
    r.srcWires.all fun w => separated ls b d.dstWire w ||
      (d == r && d.isMap && b d.dstWire == b w)

/-- If a write aliases a read in an accepted dispatch, both belong to the same elementwise
kernel and the same element. This excludes gather/concat takeover and every cross-kernel alias. -/
theorem stageRaceFree_alias (ls : List Nat) (b : Nat → Nat) (stage : List ArrayEdge)
    (h : stageRaceFree ls b stage = true) (d r : ArrayEdge) (hd : d ∈ stage) (hr : r ∈ stage)
    (w : Nat) (hw : w ∈ r.srcWires) (i j : Nat)
    (hi : i < ls.getD d.dstWire 0) (hj : j < ls.getD w 0)
    (heq : b d.dstWire + i = b w + j) : d = r ∧ d.isMap = true ∧ i = j := by
  simp only [stageRaceFree, List.all_eq_true, Bool.and_eq_true] at h
  have ha := (h d hd r hr).2 w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
  rcases ha with hsep | ⟨⟨hdr, hmap⟩, hb⟩
  · exact False.elim (separated_ne ls b d.dstWire w i j hsep hi hj heq)
  · exact ⟨hdr, hmap, by omega⟩

/-- Distinct destination wires cannot share a word in an accepted dispatch. Within a kernel,
`base + i = base + j` already implies `i = j`. -/
theorem stageRaceFree_writes (ls : List Nat) (b : Nat → Nat) (stage : List ArrayEdge)
    (h : stageRaceFree ls b stage = true) (d r : ArrayEdge) (hd : d ∈ stage) (hr : r ∈ stage)
    (hne : d.dstWire ≠ r.dstWire) (i j : Nat)
    (hi : i < ls.getD d.dstWire 0) (hj : j < ls.getD r.dstWire 0) :
    b d.dstWire + i ≠ b r.dstWire + j := by
  simp only [stageRaceFree, List.all_eq_true, Bool.and_eq_true] at h
  have ha := (h d hd r hr).1
  simp only [Bool.or_eq_true, beq_iff_eq] at ha
  exact separated_ne ls b d.dstWire r.dstWire i j (ha.resolve_left hne) hi hj

def layoutStagesOk (ls : List Nat) (b : Nat → Nat) : List (List ArrayEdge) → List Nat → Bool
  | [], _ => true
  | s :: ss, outputs => preservesLive ls b s (liveAt ss outputs) &&
      stageRaceFree ls b s && layoutStagesOk ls b ss outputs

/-- Every accepted stage carries the alias certificate used by the race theorems above. -/
theorem layoutStagesOk_raceFree (ls : List Nat) (b : Nat → Nat)
    (stages : List (List ArrayEdge)) (outputs : List Nat)
    (h : layoutStagesOk ls b stages outputs = true) :
    ∀ s ∈ stages, stageRaceFree ls b s = true := by
  induction stages with
  | nil => simp
  | cons s ss ih =>
    simp only [layoutStagesOk, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.1.2
    · exact ih h.2 r hr

structure BufferSlot where
  base : Nat
  capacity : Nat
  owner : Nat
  lastStage : Nat
  deriving Repr, Inhabited

/-- Greedy whole-buffer reuse, after MLIR One-Shot Bufferization's conflict analysis:
https://mlir.llvm.org/docs/Bufferization/ (read 2026-11-06). Unlike its destination-only search, we
also recycle dead buffers. All indexing and construction here use Arrays. A slot can be taken at
its final read only by that read's sole elementwise consumer; gathers/concats never run in place. -/
def allocateLayout (lengths : List Nat) (inputs outputs : List Nat)
    (stages : List (List ArrayEdge)) : Layout := Id.run do
  let lens := lengths.toArray
  let mut last := Array.replicate lens.size 0
  let mut used := Array.replicate lens.size false
  let mut defined := Array.replicate lens.size false
  for w in inputs ++ outputs do
    used := used.set! w true
  for (s, t) in stages.zipIdx do
    for d in s do
      used := used.set! d.dstWire true
      defined := defined.set! d.dstWire true
      for w in d.srcWires do
        used := used.set! w true
        last := last.set! w (t + 1)
  for w in outputs do
    last := last.set! w (stages.length + 1)
  let mut bases := Array.replicate lens.size 0
  let mut slots : Array BufferSlot := #[]
  let mut words := 0
  for w in [:lens.size] do
    if used[w]! && (!defined[w]! || inputs.contains w) then
      bases := bases.set! w words
      slots := slots.push ⟨words, lens[w]!, w, last[w]!⟩
      words := words + lens[w]!
  for (s, t0) in stages.zipIdx do
    let t := t0 + 1
    for d in s do
      let n := lens[d.dstWire]?.getD 0
      let mut choice : Option Nat := none
      for i in [:slots.size] do
        let slot := slots[i]!
        let takeover := slot.lastStage == t && d.isMap && d.srcWires.contains slot.owner &&
          s.all (fun r => r == d || !(r.srcWires.contains slot.owner)) &&
          (lens[slot.owner]?.getD 0) == n
        if choice.isNone && n ≤ slot.capacity && (slot.lastStage < t || takeover) then
          choice := some i
      let lastStage := max t (last[d.dstWire]?.getD 0)
      match choice with
      | some i =>
        let slot := slots[i]!
        bases := bases.set! d.dstWire slot.base
        slots := slots.set! i { slot with owner := d.dstWire, lastStage := lastStage }
      | none =>
        bases := bases.set! d.dstWire words
        slots := slots.push ⟨words, n, d.dstWire, lastStage⟩
        words := words + n
  return ⟨bases, words⟩

def gpuLayout (g : ArrayGraph) : Layout :=
  allocateLayout g.lengths g.inputs g.outputs (layerGraph (fuseGraph g))

/-- Executable certificate checked before emission. Also covers host input writes, buffer bounds,
and the initially live wires, so a rejected allocator result cannot reach a device. -/
def checkLayout (g : ArrayGraph) (l : Layout) : Bool :=
  let stages := layerGraph (fuseGraph g)
  let initial := liveAt stages g.outputs ++ g.inputs
  let accessed := initial ++ stages.flatMap (fun s => s.flatMap (fun d => d.dstWire :: d.srcWires)) ++ g.outputs
  accessed.all (fun w => w < g.lengths.length && l.base w + g.lengths.getD w 0 ≤ l.words) &&
  initial.all (fun u => initial.all (fun v => u == v || separated g.lengths l.base u v)) &&
  layoutStagesOk g.lengths l.base stages g.outputs

/-- Check the allocator's result using the same certificate checker available to other planners. -/
def layoutOk (g : ArrayGraph) : Bool := checkLayout g (gpuLayout g)

/-! ## 3. Lowering -/

structure LowerState where
  c  : List Word
  ix : List Nat
  deriving Repr

/-- A name in a program: a source wire reads the buffer at its base, anything else is a local. -/
def operandOf (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (a : Nat) : KOperand :=
  if srcWires.contains a then .read (b a) else .tmp a

/-- One instruction: a scalar constant becomes `c[i] + 0`, a scale `c[i] * x`, with the constant appended
to the buffer; every other operation keeps its operands by name. -/
def lowerInstr (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (i : Instr) (st : LowerState) : KInstr × LowerState :=
  match i.op with
  | .scalar (.const v) =>
    (⟨.scalar .add, [.cst st.c.length], i.dst⟩, { st with c := st.c ++ [BitVec.ofInt 64 v] })
  | .scalar (.scale k) =>
    (⟨.scalar .mul, .cst st.c.length :: i.args.map (operandOf ls b srcWires), i.dst⟩,
      { st with c := st.c ++ [BitVec.ofInt 64 k] })
  | op => (⟨op, i.args.map (operandOf ls b srcWires), i.dst⟩, st)

def lowerCode (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) : List Instr → LowerState → List KInstr × LowerState
  | [], st => ([], st)
  | i :: is, st =>
    let r := lowerInstr ls b srcWires i st
    let rs := lowerCode ls b srcWires is r.2
    (r.1 :: rs.1, rs.2)

def lowerEdge (ls : List Nat) (b : Nat → Nat) (e : ArrayEdge) (st : LowerState) : Kernel × LowerState :=
  let len (w : Nat) := ls.getD w 0
  let dst := b e.dstWire
  let count := len e.dstWire
  match e.op with
  | .map _ p =>
    let r := lowerCode ls b e.srcWires p.code st
    (⟨dst, count, .prog r.1 p.out⟩, r.2)
  | .gather f =>
    (⟨dst, count, .gather st.ix.length (b (e.srcWires.getD 0 0))⟩, { st with ix := st.ix ++ f.table })
  | .concat =>
    (⟨dst, count, .concat (b (e.srcWires.getD 0 0)) (len (e.srcWires.getD 0 0)) (b (e.srcWires.getD 1 0))⟩, st)
  | .const vs => (⟨dst, count, .const st.c.length⟩, { st with c := st.c ++ vs })
  | .fold op shape => (⟨dst, count, .fold op shape (b (e.srcWires.getD 0 0))⟩, st)

def lowerEdges (ls : List Nat) (b : Nat → Nat) : List ArrayEdge → LowerState → List Kernel × LowerState
  | [], st => ([], st)
  | e :: es, st =>
    let r := lowerEdge ls b e st
    let rs := lowerEdges ls b es r.2
    (r.1 :: rs.1, rs.2)

def lowerStages (ls : List Nat) (b : Nat → Nat) : List (List ArrayEdge) → LowerState → List GpuStage × LowerState
  | [], st => ([], st)
  | s :: ss, st =>
    let r := lowerEdges ls b s st
    let rs := lowerStages ls b ss r.2
    (⟨r.1⟩ :: rs.1, rs.2)

/-- Fuse, layer, allocate live buffers, and lower using the resulting physical bases. -/
def lowerArrayToGpu (g : ArrayGraph) : GpuProgram :=
  let l := gpuLayout g
  let r := lowerStages g.lengths l.base (layerGraph (fuseGraph g)) ⟨[], []⟩
  { words    := l.words
  , wireBase := l.bases.toList
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

def readOperand (c : List Word) (entry : Nat → Word) (e : Nat) (loc : Nat → Word) : KOperand → Word
  | .read b => entry (b + e)
  | .cst i  => c.getD i 0#64
  | .tmp w  => loc w

def stepKInstr (c : List Word) (entry : Nat → Word) (e : Nat) (loc : Nat → Word) (i : KInstr) : Nat → Word :=
  let v := evalElemOp i.op (i.args.map (readOperand c entry e loc))
  fun w => if w == i.dst then v else loc w

def runKCode (c : List Word) (entry : Nat → Word) (e : Nat) (loc : Nat → Word) (code : List KInstr) : Nat → Word :=
  code.foldl (stepKInstr c entry e) loc

def kernelValue (c : List Word) (ix : List Nat) (entry : Nat → Word) (k : Kernel) (e : Nat) : Word :=
  match k.body with
  | .prog code out    => runKCode c entry e (fun _ => 0#64) code out
  | .gather ixb b     => entry (b + ix.getD (ixb + e) 0)
  | .concat b0 l0 b1  => if e < l0 then entry (b0 + e) else entry (b1 + (e - l0))
  | .const cb         => c.getD (cb + e) 0#64
  | .fold op shape b  => (evalFold op shape (fun i => entry (b + i))).getD e 0#64

/-- The values written by each actual invocation, in its contiguous output interval.
Ordinary kernels write one value; a fold invocation writes one entire segment. -/
def kernelInvocationValues (c : List Word) (ix : List Nat) (entry : Nat → Word) (k : Kernel) : List Vec :=
  match k.body with
  | .fold op shape b => foldThreadValues op shape (fun i => entry (b + i))
  | _ => (List.range k.count).map (fun e => [kernelValue c ix entry k e])

/-- The invocation schedule and the output-address model agree. Their contiguous ranges
partition the outputs; scan invocations may write many values, and empty segments none. -/
theorem kernelInvocationValues_flatten (c : List Word) (ix : List Nat) (entry : Nat → Word) (k : Kernel)
    (hShape : ∀ op shape b, k.body = .fold op shape b → k.count = shape.outLen) :
    (kernelInvocationValues c ix entry k).flatten =
      (List.range k.count).map (kernelValue c ix entry k) := by
  cases hb : k.body with
  | prog code out => simp [kernelInvocationValues, hb, flatten_map_singletons]
  | gather i b => simp [kernelInvocationValues, hb, flatten_map_singletons]
  | concat a n b => simp [kernelInvocationValues, hb, flatten_map_singletons]
  | const b => simp [kernelInvocationValues, hb, flatten_map_singletons]
  | fold op shape b =>
    simp only [kernelInvocationValues, hb, foldThreadValues_flatten]
    have hv : kernelValue c ix entry k = fun e =>
        (evalFold op shape (fun i => entry (b + i))).getD e 0#64 := by
      funext e
      simp only [kernelValue, hb]
    rw [hv]
    symm
    apply map_range_getD
    simpa [evalFold, FoldShape.outLen] using hShape op shape b hb

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

/-- `flat` represents just the live wires at their physical bases; dead wires may be overwritten. -/
def Flat (ls : List Nat) (b : Nat → Nat) (live : List Nat) (env : Nat → Vec) (flat : Nat → Word) : Prop :=
  ∀ w e, w ∈ live → w < ls.length → e < ls.getD w 0 → flat (b w + e) = (env w).getD e 0#64

/-- A kernel realizes an edge: it owns the destination's range and, from any good flattening, each of
its elements is the edge's value there. -/
def KernelFor (ls : List Nat) (b : Nat → Nat) (c : List Word) (ix : List Nat) (d : ArrayEdge) (k : Kernel) : Prop :=
  k.dstBase = b d.dstWire ∧ k.count = ls.getD d.dstWire 0 ∧
  ∀ (env : Nat → Vec) (flat : Nat → Word), Good ls env → Flat ls b d.srcWires env flat →
    ∀ e, e < k.count →
      kernelValue c ix flat k e = (edgeValue env d).getD e 0#64

/-- Kernels realize edges one for one. -/
def KernelsFor (ls : List Nat) (b : Nat → Nat) (c : List Word) (ix : List Nat) : List ArrayEdge → List Kernel → Prop
  | [], [] => True
  | d :: ds, k :: ks => KernelFor ls b c ix d k ∧ KernelsFor ls b c ix ds ks
  | _, _ => False

theorem lowerEdge_dst_count (ls : List Nat) (b : Nat → Nat) (d : ArrayEdge) (st : LowerState) :
    (lowerEdge ls b d st).1.dstBase = b d.dstWire ∧ (lowerEdge ls b d st).1.count = ls.getD d.dstWire 0 := by
  cases hop : d.op <;> simp [lowerEdge, hop]

/-! ### Programs, simulated instruction by instruction -/

theorem lowerInstr_extends (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (i : Instr) (st : LowerState) :
    ∃ dc, (lowerInstr ls b srcWires i st).2.c = st.c ++ dc ∧ (lowerInstr ls b srcWires i st).2.ix = st.ix := by
  cases hop : i.op with
  | scalar o => cases o <;> simp [lowerInstr, hop]
  | ult | band | bor | shr | shl => simp [lowerInstr, hop]

theorem lowerCode_extends (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (code : List Instr) (st : LowerState) :
    ∃ dc, (lowerCode ls b srcWires code st).2.c = st.c ++ dc ∧ (lowerCode ls b srcWires code st).2.ix = st.ix := by
  induction code generalizing st with
  | nil => exact ⟨[], by simp [lowerCode]⟩
  | cons i is ih =>
    obtain ⟨c1, hc1, hi1⟩ := lowerInstr_extends ls b srcWires i st
    obtain ⟨c2, hc2, hi2⟩ := ih (lowerInstr ls b srcWires i st).2
    refine ⟨c1 ++ c2, ?_, ?_⟩
    · simp only [lowerCode]; rw [hc2, hc1, List.append_assoc]
    · simp only [lowerCode]; rw [hi2, hi1]

theorem getD_append_length {α : Type} (c : List α) (x : α) (d : List α) (z : α) :
    (c ++ x :: d).getD c.length z = x := by
  have := getD_append_right c (x :: d) 0 z
  simpa using this

/-- The simulation relation between a program's local environment and the kernel's: every non-source
name agrees, every source name holds the buffer's word at its base. -/
def Sim (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (flat : Nat → Word) (el : Nat) (loc kloc : Nat → Word) : Prop :=
  (∀ w, srcWires.contains w = false → kloc w = loc w) ∧
  (∀ w, srcWires.contains w = true → loc w = flat (b w + el))

theorem operands_sim (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (c : List Word) (flat : Nat → Word) (el : Nat)
    (loc kloc : Nat → Word) (hS : Sim ls b srcWires flat el loc kloc) (args : List Nat) :
    (args.map (operandOf ls b srcWires)).map (readOperand c flat el kloc) = args.map loc := by
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_def, operandOf]
  cases hc : srcWires.contains a with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, readOperand]; exact hS.1 a hc
  | true => simp only [↓reduceIte, readOperand]; exact (hS.2 a hc).symm

theorem sim_step (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (flat : Nat → Word) (el : Nat) (loc kloc : Nat → Word)
    (hS : Sim ls b srcWires flat el loc kloc) (dst : Nat) (hdst : srcWires.contains dst = false) (v : Word) :
    Sim ls b srcWires flat el (fun w => if w == dst then v else loc w) (fun w => if w == dst then v else kloc w) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    by_cases h : w = dst
    · simp [h]
    · simp only [beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ↓reduceIte]; exact hS.1 w hw
  · intro w hw
    have h : w ≠ dst := fun h => by rw [h, hdst] at hw; exact Bool.noConfusion hw
    simp only [beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ↓reduceIte]; exact hS.2 w hw

/-- One instruction, simulated. -/
theorem lowerInstr_sim (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (i : Instr) (st : LowerState)
    (hdst : srcWires.contains i.dst = false) (dc : List Word) (flat : Nat → Word) (el : Nat)
    (loc kloc : Nat → Word) (hS : Sim ls b srcWires flat el loc kloc) :
    Sim ls b srcWires flat el (stepInstr loc i)
      (stepKInstr ((lowerInstr ls b srcWires i st).2.c ++ dc) flat el kloc (lowerInstr ls b srcWires i st).1) := by
  have hv : ∀ (c : List Word), evalElemOp i.op (i.args.map loc) =
      evalElemOp (lowerInstr ls b srcWires i st).1.op
        ((lowerInstr ls b srcWires i st).1.args.map (readOperand ((lowerInstr ls b srcWires i st).2.c ++ dc) flat el kloc)) := by
    intro _
    cases hop : i.op with
    | scalar o =>
      cases o with
      | const v =>
        simp only [lowerInstr, hop, evalElemOp, evalHypergraphOpBv, List.map_cons, List.map_nil, readOperand,
          List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
        rw [List.append_assoc, List.singleton_append, getD_append_length, BitVec.add_zero]
      | scale k =>
        simp only [lowerInstr, hop, evalElemOp, evalHypergraphOpBv, List.map_cons, readOperand,
          List.getD_cons_zero, List.getD_cons_succ]
        rw [List.append_assoc, List.singleton_append, getD_append_length,
          operands_sim ls b srcWires _ flat el loc kloc hS i.args]
      | add | sub | mul | mac | mux =>
        simp only [lowerInstr, hop]
        rw [operands_sim ls b srcWires _ flat el loc kloc hS i.args]
    | ult | band | bor | shr | shl =>
      simp only [lowerInstr, hop]
      rw [operands_sim ls b srcWires _ flat el loc kloc hS i.args]
  have hd : (lowerInstr ls b srcWires i st).1.dst = i.dst := by
    cases hop : i.op with
    | scalar o => cases o <;> simp [lowerInstr, hop]
    | ult | band | bor | shr | shl => simp [lowerInstr, hop]
  simp only [stepInstr, stepKInstr, hd]
  rw [← hv []]
  exact sim_step ls b srcWires flat el loc kloc hS i.dst hdst _

/-- **`runKCode_sim`**: a lowered program, run on the kernel's locals, simulates the program on its own,
given that no instruction writes a source name. -/
theorem runKCode_sim (ls : List Nat) (b : Nat → Nat) (srcWires : List Nat) (code : List Instr) (st : LowerState)
    (hdst : ∀ i ∈ code, srcWires.contains i.dst = false) (dc : List Word) (flat : Nat → Word) (el : Nat)
    (loc kloc : Nat → Word) (hS : Sim ls b srcWires flat el loc kloc) :
    Sim ls b srcWires flat el (runCode loc code)
      (runKCode ((lowerCode ls b srcWires code st).2.c ++ dc) flat el kloc (lowerCode ls b srcWires code st).1) := by
  induction code generalizing st loc kloc with
  | nil => exact hS
  | cons i is ih =>
    obtain ⟨c2, hc2, _⟩ := lowerCode_extends ls b srcWires is (lowerInstr ls b srcWires i st).2
    simp only [lowerCode, runCode, runKCode, List.foldl_cons] at ih ⊢
    have h1 := lowerInstr_sim ls b srcWires i st (hdst i List.mem_cons_self) (c2 ++ dc) flat el loc kloc hS
    have h2 := ih (lowerInstr ls b srcWires i st).2 (fun j hj => hdst j (List.mem_cons_of_mem _ hj)) _ _ h1
    rw [hc2, List.append_assoc] at h2 ⊢
    exact h2

theorem srcLookup_map_not_mem (f : Nat → Vec) (ws : List Nat) (u : Nat) (hu : ws.contains u = false) :
    srcLookup (ws.map fun w => (w, f w)) u = [] := by
  simp only [srcLookup]
  rw [List.find?_eq_none.mpr]
  intro p hp
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
  intro h
  have hwu : w = u := beq_iff_eq.mp h
  rw [← hwu, List.contains_iff_mem.mpr hw] at hu
  exact Bool.noConfusion hu

/-- The edge's value at `e`, read from the flat buffer, for each operation. -/
theorem lowerEdge_kernelFor (ls : List Nat) (b : Nat → Nat) (d : ArrayEdge) (st : LowerState) (hOk : edgeOk ls d = true)
    (dc : List Word) (dix : List Nat) :
    KernelFor ls b ((lowerEdge ls b d st).2.c ++ dc) ((lowerEdge ls b d st).2.ix ++ dix) d (lowerEdge ls b d st).1 := by
  simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk
  obtain ⟨⟨⟨hDst, hSrcs⟩, hLen⟩, hOp⟩ := hOk
  obtain ⟨hBase, hCount⟩ := lowerEdge_dst_count ls b d st
  refine ⟨hBase, hCount, ?_⟩
  intro env flat hGood hFlat e he
  rw [hCount] at he
  have hRead : ∀ s, s ∈ d.srcWires → ∀ i, i < ls.getD s 0 → flat (b s + i) = (env s).getD i 0#64 :=
    fun s hs i hi => hFlat s i hs (hSrcs s hs) hi
  cases hop : d.op with
  | map n p =>
    simp only [hop, ArrayOp.outLen, List.all_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at hLen hOp
    obtain ⟨⟨hSame, hNoDst⟩, hOut⟩ := hOp
    have hArr : (edgeValue env d).getD e 0#64 =
        evalProg p fun w => (srcLookup (edgeSrcs env d) w).getD e 0#64 := by
      simp only [edgeValue, hop, evalArrayOp]
      rw [getD_range_map n _ _ e (by omega)]
    rw [hArr]
    simp only [lowerEdge, hop, kernelValue, evalProg]
    obtain ⟨c2, hc2, hi2⟩ := lowerCode_extends ls b d.srcWires p.code st
    have hS0 : Sim ls b d.srcWires flat e (fun w => (srcLookup (edgeSrcs env d) w).getD e 0#64) (fun _ => 0#64) := by
      refine ⟨?_, ?_⟩
      · intro w hw
        simp only [edgeSrcs]
        rw [srcLookup_map_not_mem env d.srcWires w hw]
        rfl
      · intro w hw
        have hmem := List.contains_iff_mem.mp hw
        simp only [edgeSrcs]
        rw [srcLookup_map env d.srcWires w hmem]
        exact (hRead w hmem e (by rw [hSame w hmem]; exact he)).symm
    have hSim := runKCode_sim ls b d.srcWires p.code st hNoDst dc flat e _ _ hS0
    exact (hSim.1 p.out hOut).symm ▸ rfl
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
    have hkv : kernelValue ((lowerEdge ls b d st).2.c ++ dc) ((lowerEdge ls b d st).2.ix ++ dix) flat
        (lowerEdge ls b d st).1 e = flat (b s + f.table.getD e 0) := by
      simp only [lowerEdge, hop, kernelValue, hs, List.getD_cons_zero]
      rw [List.append_assoc, getD_append_right st.ix (f.table ++ dix) e 0, getD_append_of_lt f.table dix e 0 heTab]
    have hav : (edgeValue env d).getD e 0#64 = (env s).getD (f.table.getD e 0) 0#64 := by
      simp only [edgeValue, edgeSrcs, evalArrayOp, hop, hs, List.map_cons, List.map_nil, List.getD_cons_zero]
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
    simp only [lowerEdge, hop, kernelValue, edgeValue, edgeSrcs, evalArrayOp, hs, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    by_cases hlt : e < ls.getD s0 0
    · rw [ite_eq_left hlt, hRead s0 h0 e hlt]
      exact (getD_append_of_lt (env s0) (env s1) e 0#64 (by rw [hLen0]; exact hlt)).symm
    · rw [ite_eq_right hlt, hRead s1 h1 (e - ls.getD s0 0) (by omega)]
      have h' := getD_append_right (env s0) (env s1) (e - ls.getD s0 0) 0#64
      rw [hLen0, show ls.getD s0 0 + (e - ls.getD s0 0) = e by omega] at h'
      exact h'.symm
  | fold op shape =>
    simp only [hop, ArrayOp.outLen, Bool.and_eq_true, beq_iff_eq] at hLen hOp
    obtain ⟨hOne, hInput⟩ := hOp
    obtain ⟨s, hs⟩ : ∃ s, d.srcWires = [s] := by
      cases h : d.srcWires with
      | nil => simp [h] at hOne
      | cons s rest => cases rest with
        | nil => exact ⟨s, rfl⟩
        | cons _ _ => simp [h] at hOne
    have hsMem : s ∈ d.srcWires := by rw [hs]; exact List.mem_cons_self
    simp only [hs, List.getD_cons_zero] at hInput
    simp only [lowerEdge, hop, kernelValue, edgeValue, edgeSrcs, evalArrayOp,
      hs, List.map_cons, List.map_nil, List.getD_cons_zero]
    congr 1
    unfold evalFold
    apply List.map_congr_left
    intro r hr
    apply foldRange_congr
    intro i hi hlo
    exact hRead s hsMem i (by have := shape.ranges_bound r hr; omega)
  | const vs =>
    simp only [hop, ArrayOp.outLen] at hLen
    rw [← hLen] at he
    simp only [lowerEdge, hop, kernelValue, edgeValue, evalArrayOp]
    rw [List.append_assoc, getD_append_right st.c (vs ++ dc) e 0#64, getD_append_of_lt vs dc e 0#64 he]

/-- The static shape check supplies the invocation-schedule theorem's output-count premise. -/
theorem lowerEdge_foldShape (ls : List Nat) (bases : Nat → Nat) (d : ArrayEdge) (st : LowerState)
    (hOk : edgeOk ls d = true) (op : ReduceOp) (shape : FoldShape) (b : Nat)
    (hb : (lowerEdge ls bases d st).1.body = .fold op shape b) :
    (lowerEdge ls bases d st).1.count = shape.outLen := by
  simp only [edgeOk, Bool.and_eq_true, beq_iff_eq] at hOk
  have hLen := hOk.1.2
  cases hop : d.op with
  | map n p => simp [lowerEdge, hop] at hb
  | gather f => simp [lowerEdge, hop] at hb
  | concat => simp [lowerEdge, hop] at hb
  | const vs => simp [lowerEdge, hop] at hb
  | fold op' shape' =>
    simp only [lowerEdge, hop, KernelBody.fold.injEq] at hb
    obtain ⟨rfl, rfl, _⟩ := hb
    simpa [lowerEdge, hop, ArrayOp.outLen] using hLen.symm

/-- Lowered invocations themselves realize every output element. This includes the actual
linear scan loops and empty segments, not only the abstract output-address evaluator. -/
theorem lowerEdge_invocations_sound (ls : List Nat) (bases : Nat → Nat) (d : ArrayEdge) (st : LowerState)
    (hOk : edgeOk ls d = true) (dc : List Word) (dix : List Nat)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good ls env) (hFlat : Flat ls bases d.srcWires env flat) :
    (kernelInvocationValues ((lowerEdge ls bases d st).2.c ++ dc) ((lowerEdge ls bases d st).2.ix ++ dix)
      flat (lowerEdge ls bases d st).1).flatten =
      (List.range (ls.getD d.dstWire 0)).map (fun i => (edgeValue env d).getD i 0#64) := by
  rw [kernelInvocationValues_flatten _ _ _ _ (lowerEdge_foldShape ls bases d st hOk)]
  have hRel := lowerEdge_kernelFor ls bases d st hOk dc dix
  rw [hRel.2.1]
  apply List.map_congr_left
  intro i hi
  exact hRel.2.2 env flat hGood hFlat i (by rw [hRel.2.1]; exact List.mem_range.mp hi)

/-- Lowering only appends to the constant and index buffers. -/
theorem lowerEdge_extends (ls : List Nat) (b : Nat → Nat) (d : ArrayEdge) (st : LowerState) :
    ∃ dc dix, (lowerEdge ls b d st).2.c = st.c ++ dc ∧ (lowerEdge ls b d st).2.ix = st.ix ++ dix := by
  cases hop : d.op with
  | map n p =>
    obtain ⟨dc, hc, hi⟩ := lowerCode_extends ls b d.srcWires p.code st
    exact ⟨dc, [], by simp [lowerEdge, hop, hc, hi]⟩
  | gather f => exact ⟨[], f.table, by simp [lowerEdge, hop]⟩
  | concat => simp [lowerEdge, hop]
  | fold op shape => simp [lowerEdge, hop]
  | const vs => exact ⟨vs, [], by simp [lowerEdge, hop]⟩

theorem lowerEdges_extends (ls : List Nat) (b : Nat → Nat) (es : List ArrayEdge) (st : LowerState) :
    ∃ dc dix, (lowerEdges ls b es st).2.c = st.c ++ dc ∧ (lowerEdges ls b es st).2.ix = st.ix ++ dix := by
  induction es generalizing st with
  | nil => exact ⟨[], [], by simp [lowerEdges]⟩
  | cons e es ih =>
    obtain ⟨c1, i1, hc1, hi1⟩ := lowerEdge_extends ls b e st
    obtain ⟨c2, i2, hc2, hi2⟩ := ih (lowerEdge ls b e st).2
    refine ⟨c1 ++ c2, i1 ++ i2, ?_, ?_⟩
    · simp only [lowerEdges]; rw [hc2, hc1, List.append_assoc]
    · simp only [lowerEdges]; rw [hi2, hi1, List.append_assoc]

theorem lowerStages_extends (ls : List Nat) (b : Nat → Nat) (ss : List (List ArrayEdge)) (st : LowerState) :
    ∃ dc dix, (lowerStages ls b ss st).2.c = st.c ++ dc ∧ (lowerStages ls b ss st).2.ix = st.ix ++ dix := by
  induction ss generalizing st with
  | nil => exact ⟨[], [], by simp [lowerStages]⟩
  | cons s ss ih =>
    obtain ⟨c1, i1, hc1, hi1⟩ := lowerEdges_extends ls b s st
    obtain ⟨c2, i2, hc2, hi2⟩ := ih (lowerEdges ls b s st).2
    refine ⟨c1 ++ c2, i1 ++ i2, ?_, ?_⟩
    · simp only [lowerStages]; rw [hc2, hc1, List.append_assoc]
    · simp only [lowerStages]; rw [hi2, hi1, List.append_assoc]

/-- A lowered stage's kernels realize its edges, one for one, against any extension of the buffers. -/
theorem lowerEdges_forall₂ (ls : List Nat) (b : Nat → Nat) (es : List ArrayEdge) (st : LowerState)
    (hOk : ∀ d ∈ es, edgeOk ls d = true) (dc : List Word) (dix : List Nat) :
    KernelsFor ls b ((lowerEdges ls b es st).2.c ++ dc) ((lowerEdges ls b es st).2.ix ++ dix)
      es (lowerEdges ls b es st).1 := by
  induction es generalizing st with
  | nil => trivial
  | cons e es ih =>
    obtain ⟨c2, i2, hc2, hi2⟩ := lowerEdges_extends ls b es (lowerEdge ls b e st).2
    simp only [lowerEdges, KernelsFor]
    refine ⟨?_, ih _ (fun d hd => hOk d (List.mem_cons_of_mem e hd))⟩
    rw [hc2, hi2, List.append_assoc, List.append_assoc]
    exact lowerEdge_kernelFor ls b e st (hOk e List.mem_cons_self) (c2 ++ dc) (i2 ++ dix)

/-! ## 6. One dispatch -/

/-- With distinct destinations, the synchronous stage writes each wire from the edge that owns it. -/
theorem evalStageAux_find (entry cur : Nat → Vec) (stage : List ArrayEdge)
    (hNodup : (stage.map (·.dstWire)).Nodup) (w : Nat) :
    evalStageAux entry cur stage w =
      match stage.find? (fun d => d.dstWire == w) with
      | some d => edgeValue entry d
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
theorem find_kernel (ls : List Nat) (b : Nat → Nat) (c : List Word) (ix : List Nat)
    (stage : List ArrayEdge) (kernels : List Kernel)
    (hRel : KernelsFor ls b c ix stage kernels)
    (hNodup : (stage.map (·.dstWire)).Nodup)
    (hOk : ∀ d ∈ stage, d.dstWire < ls.length)
    (after : List Nat)
    (hSep : ∀ d ∈ stage, ∀ w ∈ after, d.dstWire ≠ w → separated ls b d.dstWire w = true)
    (w e : Nat) (hlive : w ∈ after) (hw : w < ls.length) (he : e < ls.getD w 0) :
    (kernels.find? (fun k => k.owns (b w + e)) = none ↔
      stage.find? (fun d => d.dstWire == w) = none) ∧
    (∀ k, kernels.find? (fun k => k.owns (b w + e)) = some k →
      ∃ d, stage.find? (fun d => d.dstWire == w) = some d ∧ KernelFor ls b c ix d k ∧
        k.dstBase = b w ∧ d.dstWire = w) := by
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
      have hOwns : k.owns (b w + e) = true := by
        rw [Kernel.owns, decide_eq_true_eq, hdk.1, hdk.2.1, ← hdw]
        omega
      have hEq : (d.dstWire == w) = true := beq_iff_eq.mpr hdw
      simp only [List.find?_cons, hOwns, hEq]
      refine ⟨by simp, ?_⟩
      intro k' hk'
      simp only [Option.some.injEq] at hk'
      subst hk'
      exact ⟨d, rfl, hdk, by rw [hdk.1, hdw], hdw⟩
    · have hNot : k.owns (b w + e) = false := by
        rw [Kernel.owns, decide_eq_false_iff_not, hdk.1, hdk.2.1]
        intro ⟨hle, hlt⟩
        exact separated_ne ls b d.dstWire w (b w + e - b d.dstWire) e
          (hSep d List.mem_cons_self w hlive hdw) (by omega) he (by omega)
      have hNe : (d.dstWire == w) = false := beq_eq_false_iff_ne.mpr hdw
      simp only [List.find?_cons, hNot, hNe]
      exact ih kernels' hRest hNodup.2 hOk' (fun d' hd' => hSep d' (List.mem_cons_of_mem d hd'))

/-- **One dispatch is one synchronous stage.** -/
theorem runStage_sound (ls : List Nat) (b : Nat → Nat) (c : List Word) (ix : List Nat)
    (stage : List ArrayEdge) (kernels : List Kernel)
    (hRel : KernelsFor ls b c ix stage kernels)
    (hNodup : (stage.map (·.dstWire)).Nodup)
    (hOk : ∀ d ∈ stage, d.dstWire < ls.length)
    (after : List Nat)
    (hSep : ∀ d ∈ stage, ∀ w ∈ after, d.dstWire ≠ w → separated ls b d.dstWire w = true)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good ls env) (hFlat : Flat ls b (liveBefore stage after) env flat) :
    Flat ls b after (evalStageSync env stage) (runStage c ix flat ⟨kernels⟩) := by
  intro w e hlive hw he
  have hFind := find_kernel ls b c ix stage kernels hRel hNodup hOk after hSep w e hlive hw he
  simp only [runStage, evalStageSync]
  rw [evalStageAux_find env env stage hNodup w]
  rcases hk : kernels.find? (fun k => k.owns (b w + e)) with _ | k
  · rw [hk, hFind.1.mp hk]
    apply hFlat w e _ hw he
    apply List.mem_append_right
    apply List.mem_filter.mpr
    refine ⟨hlive, ?_⟩
    simp only [Bool.not_eq_true']
    apply List.any_eq_false.mpr
    intro d hd
    exact List.find?_eq_none.mp (hFind.1.mp hk) d hd
  · obtain ⟨d, hd, hdk, hBase, hdw⟩ := hFind.2 k hk
    rw [hk, hd]
    show kernelValue c ix flat k (b w + e - k.dstBase) = List.getD (edgeValue env d) e 0#64
    rw [hBase, Nat.add_sub_cancel_left]
    have hSrcFlat : Flat ls b d.srcWires env flat := by
      intro u i hu hui hi
      apply hFlat u i _ hui hi
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨d, List.mem_of_find?_eq_some hd, hu⟩
    exact hdk.2.2 env flat hGood hSrcFlat e (by rw [hdk.2.1, hdw]; exact he)

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
    · rw [ite_eq_left hud]
      have hOkd := hOk d List.mem_cons_self
      simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hOkd
      have hfw : ∀ f, d.op = .gather f → f.wf = true := by
        intro f hf
        have := hOkd.2
        simp only [hf, Bool.and_eq_true] at this
        exact this.1.1
      simp only [edgeValue]
      rw [evalArrayOp_length d.op _ hfw]
      have hLens : ((edgeSrcs env d).map (·.2)).map List.length = d.srcWires.map (ls.getD · 0) := by
        simp only [edgeSrcs, List.map_map]
        exact List.map_congr_left fun s hs => hGood s (hOkd.1.1.2 s hs)
      rw [hLens, hOkd.1.2, beq_iff_eq.mp hud]
    · rw [ite_eq_right (by simpa using hud)]
      exact hcur u hu

/-! ## 7. The program -/

theorem runStages_sound (ls : List Nat) (b : Nat → Nat) (c : List Word) (ix : List Nat)
    (stages : List (List ArrayEdge)) (outputs : List Nat) (st : LowerState)
    (hOk : ∀ s ∈ stages, ∀ d ∈ s, edgeOk ls d = true)
    (hInd : stages.all ArrayHypergraph.checkStageIndependent = true)
    (hLayout : layoutStagesOk ls b stages outputs = true)
    (dc : List Word) (dix : List Nat)
    (hc : c = (lowerStages ls b stages st).2.c ++ dc) (hix : ix = (lowerStages ls b stages st).2.ix ++ dix)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good ls env) (hFlat : Flat ls b (liveAt stages outputs) env flat) :
    Flat ls b outputs (evalLayeredSync env stages) (runStages c ix flat (lowerStages ls b stages st).1) ∧
    Good ls (evalLayeredSync env stages) := by
  induction stages generalizing st env flat with
  | nil => exact ⟨hFlat, hGood⟩
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hInd
    simp only [layoutStagesOk, Bool.and_eq_true] at hLayout
    have hSep : ∀ d ∈ s, ∀ w ∈ liveAt ss outputs, d.dstWire ≠ w →
        separated ls b d.dstWire w = true := by
      have hp := hLayout.1.1
      simp only [preservesLive, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
      intro d hd w hw hne
      exact (hp d hd w hw).resolve_left hne
    have hOkS : ∀ d ∈ s, edgeOk ls d = true := hOk s List.mem_cons_self
    have hOkSS : ∀ s' ∈ ss, ∀ d ∈ s', edgeOk ls d = true := fun s' hs' => hOk s' (List.mem_cons_of_mem s hs')
    obtain ⟨c2, i2, hc2, hi2⟩ := lowerStages_extends ls b ss (lowerEdges ls b s st).2
    simp only [lowerStages] at hc hix ⊢
    have hcS : c = (lowerEdges ls b s st).2.c ++ (c2 ++ dc) := by rw [hc, hc2, List.append_assoc]
    have hixS : ix = (lowerEdges ls b s st).2.ix ++ (i2 ++ dix) := by rw [hix, hi2, List.append_assoc]
    have hRel := lowerEdges_forall₂ ls b s st hOkS (c2 ++ dc) (i2 ++ dix)
    rw [← hcS, ← hixS] at hRel
    have hNodup := checkStageIndependent_nodup s hInd.1
    have hDst : ∀ d ∈ s, d.dstWire < ls.length := by
      intro d hd
      have := hOkS d hd
      simp only [edgeOk, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1.1
    have hFlat' := runStage_sound ls b c ix s _ hRel hNodup hDst (liveAt ss outputs) hSep env flat hGood hFlat
    have hGood' := evalStageSync_good ls s hOkS env hGood
    simp only [evalLayeredSync, runStages, List.foldl_cons]
    exact ih (lowerEdges ls b s st).2 hOkSS hInd.2 hLayout.2 hc hix (evalStageSync env s)
      (runStage c ix flat ⟨(lowerEdges ls b s st).1⟩) hGood' hFlat'

/-- The executable checker supplies the per-stage liveness certificate. -/
theorem layoutOk_stages (g : ArrayGraph) (h : layoutOk g = true) :
    layoutStagesOk g.lengths (gpuLayout g).base (layerGraph (fuseGraph g)) g.outputs = true := by
  simp only [layoutOk, checkLayout, Bool.and_eq_true] at h
  exact h.2

/-- The emitted program's graph stages satisfy both race theorems, including in-place kernels. -/
theorem lowerArrayToGpu_raceFree (g : ArrayGraph) (h : layoutOk g = true) :
    ∀ s ∈ layerGraph (fuseGraph g), stageRaceFree g.lengths (gpuLayout g).base s = true :=
  layoutStagesOk_raceFree _ _ _ _ (layoutOk_stages g h)

/-- **Universal lowering soundness with buffer reuse.** Only live entry values need representation;
the executable certificate checks preservation and races independently of the allocator heuristic. -/
theorem lowerArrayToGpu_sound (g : ArrayGraph) (hWf : g.wf = true)
    (hLayout : layoutOk g = true)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good g.lengths env)
    (hFlat : Flat g.lengths (gpuLayout g).base
      (liveAt (layerGraph (fuseGraph g)) g.outputs) env flat) :
    runProgram (lowerArrayToGpu g) flat = evalGraph g env := by
  obtain ⟨hFuse, hOkF⟩ := fuseGraph_sound g hWf env
  have hOut := wf_outputs g hWf
  have hLayer := layerGraph_sound (fuseGraph g) env
  have hOkS : ∀ s ∈ layerGraph (fuseGraph g), ∀ d ∈ s, edgeOk g.lengths d = true := by
    intro s hs d hd
    apply hOkF
    rw [← hLayer.2.1.mem_iff]
    exact List.mem_flatten.mpr ⟨s, hs, hd⟩
  obtain ⟨hFlat', hGood'⟩ := runStages_sound g.lengths (gpuLayout g).base
    (lowerStages g.lengths (gpuLayout g).base (layerGraph (fuseGraph g)) ⟨[], []⟩).2.c
    (lowerStages g.lengths (gpuLayout g).base (layerGraph (fuseGraph g)) ⟨[], []⟩).2.ix
    (layerGraph (fuseGraph g)) g.outputs ⟨[], []⟩ hOkS hLayer.1 (layoutOk_stages g hLayout)
    [] [] (List.append_nil _).symm (List.append_nil _).symm env flat hGood hFlat
  rw [← hFuse]
  simp only [runProgram, lowerArrayToGpu, evalGraph, fuseGraph_outputs]
  rw [← hLayer.2.2]
  apply List.map_congr_left
  intro w hw
  have hwLt := hOut w hw
  have hb : (gpuLayout g).bases.toList.getD w 0 = (gpuLayout g).base w := by
    simp [Layout.base, List.getD_eq_getElem?_getD]
  rw [hb]
  apply List.ext_getElem
  · simp [hGood' w hwLt]
  · intro e h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have he : e < g.lengths.getD w 0 := by simpa using h1
    rw [hFlat' w e hw hwLt he]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! ## 8. The scalar corollary -/

/-- Scalar inputs use the same physical layout as array inputs, including reuse. -/
theorem lowerHypergraphToGpu_sound (g : StrictOpenHypergraph)
    (hWf : (ofScalar g).wf = true) (hLayout : layoutOk (ofScalar g) = true)
    (env : Nat → Word) (flat : Nat → Word)
    (hFlat : Flat (ofScalar g).lengths (gpuLayout (ofScalar g)).base
      (liveAt (layerGraph (fuseGraph (ofScalar g))) (ofScalar g).outputs) (singletonEnv env) flat) :
    runProgram (lowerHypergraphToGpu g) flat =
      g.boundaryOut.table.map fun w => [evalLayeredStagesSyncBv env (layerHypergraph g) w] := by
  have hn : (ofScalar g).lengths.length = g.nodeTypes.length := by simp [ofScalar]
  have hGood : Good (ofScalar g).lengths (singletonEnv env) := by
    intro w hw
    rw [hn] at hw
    simp [ofScalar, singletonEnv, List.getD_eq_getElem?_getD, List.getElem?_replicate, hw]
  rw [lowerHypergraphToGpu, lowerArrayToGpu_sound (ofScalar g) hWf hLayout _ flat hGood hFlat]
  simp only [evalGraph]
  rw [← (layerGraph_sound (ofScalar g) (singletonEnv env)).2.2, ofScalar_layered_sound]
  rfl

/-! ## 9. The emitter (WGSL), checked by running it -/

/-- Rules planted in the emitted text only, for the verify script's tooth. -/
inductive Plant where
  | none
  | addAsSub
  | swapMux
  | mulHighZero
  deriving DecidableEq, Repr

def Plant.ofString? : String → Option Plant
  | "addAsSub" => some .addAsSub
  | "swapMux"  => some .swapMux
  | "mulHighZero" => some .mulHighZero
  | _          => Option.none

/-- Plant a broken high product in the actual limb primitive, not its model. -/
def limbPrelude (p : Plant) : String :=
  if p == .mulHighZero then Limbs.wgslPrelude.replace "u32(product >> 32u)" "0u"
  else Limbs.wgslPrelude

def operandText : KOperand → String
  | .read b => s!"w[{b}u + e]"
  | .cst i  => s!"c[{i}u]"
  | .tmp w  => s!"v{w}"

/-- A word literal in the portable little-endian u32 representation. -/
def wordText (v : Int) : String :=
  let n := (BitVec.ofInt 64 v).toNat
  s!"vec2<u32>({n % 4294967296}u, {n / 4294967296}u)"

/-- The expression of one instruction over u32 pairs and bounded widening multiplication. -/
def elemExpr (p : Plant) (op : ElemOp) (args : List String) : String :=
  let a (i : Nat) := args.getD i "vec2<u32>(0u)"
  match op with
  | .scalar .add       => if p == .addAsSub then s!"u64_sub({a 0}, {a 1})" else s!"u64_add({a 0}, {a 1})"
  | .scalar .sub       => s!"u64_sub({a 0}, {a 1})"
  | .scalar .mul       => s!"u64_mul({a 0}, {a 1})"
  | .scalar .mac       => s!"u64_add(u64_mul({a 0}, {a 1}), {a 2})"
  | .scalar .mux       =>
    if p == .swapMux then s!"select({a 1}, {a 2}, any({a 0} != vec2<u32>(0u)))"
    else s!"select({a 2}, {a 1}, any({a 0} != vec2<u32>(0u)))"
  | .scalar (.const v) => wordText v
  | .scalar (.scale k) => s!"u64_mul({wordText k}, {a 0})"
  | .ult               => s!"vec2<u32>(select(0u, 1u, u64_lt({a 0}, {a 1})), 0u)"
  | .band              => s!"{a 0} & {a 1}"
  | .bor               => s!"{a 0} | {a 1}"
  | .shr               => s!"u64_shr({a 0}, {a 1})"
  | .shl               => s!"u64_shl({a 0}, {a 1})"

/-- Text of the lawful word monoid, including the existing planted add fault. -/
def reduceExpr (p : Plant) (op : ReduceOp) (a b : String) : String :=
  match op with
  | .add => elemExpr p (.scalar .add) [a, b]
  | .mul => elemExpr p (.scalar .mul) [a, b]
  | .band => s!"{a} & {b}"
  | .bor => s!"{a} | {b}"

/-- Linear sequential-segment schedule: invocation `e` owns segment `e`, including
its entire output interval. Empty reductions store the identity; empty scans store nothing.
The schedule's model is `foldThreadValues`, with `foldThreadValues_flatten` proving its
output-address view used by `kernelValue`. No invocation reads another's writes. -/
def foldStatements (p : Plant) (op : ReduceOp) (shape : FoldShape) (src dst : Nat) : List String :=
  let ns := shape.segments
  if ns.isEmpty then [] else
  let starts := ((ns.foldl (fun (acc : Nat × List Nat) n => (acc.1 + n, acc.1 :: acc.2)) (0, [])).2).reverse
  let nums (xs : List Nat) := String.intercalate ", " (xs.map fun n => s!"{n}u")
  let pre := [s!"let starts = array<u32, {ns.length}>({nums starts});",
    s!"let lengths = array<u32, {ns.length}>({nums ns});",
    "let start = starts[e];", "let n = lengths[e];",
    s!"var acc : vec2<u32> = {wordText op.identity.toInt};"]
  let combine := s!"acc = {reduceExpr p op "acc" s!"w[{src}u + start + j]"};"
  match shape.mode with
  | none => pre ++ ["for (var j = 0u; j < n; j = j + 1u) {", s!"  {combine}", "}",
      s!"w[{dst}u + e] = acc;"]
  | some .inclusive => pre ++ ["for (var j = 0u; j < n; j = j + 1u) {", s!"  {combine}",
      s!"  w[{dst}u + start + j] = acc;", "}"]
  | some .exclusive => pre ++ ["for (var j = 0u; j < n; j = j + 1u) {",
      s!"  w[{dst}u + start + j] = acc;", s!"  {combine}", "}"]

/-- Statements of invocation `e`: an ordinary kernel writes one element; a fold kernel
runs the accumulator loop for one segment and may write multiple outputs. -/
def kernelStatements (p : Plant) (k : Kernel) : List String :=
  match k.body with
  | .prog code out =>
    (code.map fun i => s!"let v{i.dst} : vec2<u32> = {elemExpr p i.op (i.args.map operandText)};") ++
      [s!"w[{k.dstBase}u + e] = v{out};"]
  | .gather ixb b      => [s!"w[{k.dstBase}u + e] = w[{b}u + ix[{ixb}u + e]];"]
  | .concat b0 l0 b1   =>
    [s!"if (e < {l0}u) \{ w[{k.dstBase}u + e] = w[{b0}u + e]; } else \{ w[{k.dstBase}u + e] = w[{b1}u + (e - {l0}u)]; }"]
  | .const cb          => [s!"w[{k.dstBase}u + e] = c[{cb}u + e];"]
  | .fold op shape b   => foldStatements p op shape b k.dstBase

/-- The shader of stage `k`: thread `gid.x` finds its kernel by the thread ranges laid end to end,
becomes invocation `e` of it, and runs its statements; threads past the last kernel idle. The ranges are
disjoint, so the tests are a flat sequence (an `else if` chain nests, and Metal's compiler stops at a
depth of 256). -/
def emitStageWgsl (p : Plant) (name : String) (k numStages : Nat) (s : GpuStage) : String :=
  let branches := (s.kernels.foldl (fun (acc : Nat × List String) kern =>
    let hi := acc.1 + kern.threads
    let test := if acc.1 == 0 then s!"t < {hi}u" else s!"t >= {acc.1}u && t < {hi}u"
    let body := (kernelStatements p kern).map (s!"    " ++ ·)
    (hi, acc.2 ++ [s!"  if ({test}) \{", s!"    let e : u32 = t - {acc.1}u;"] ++ body ++ ["  }"]))
    (0, [])).2
  String.intercalate "\n"
    ([ s!"// obend-emit-gpu: {name}, stage {k} of {numStages}: {s.kernels.length} kernels, {s.threads} threads."
     , "// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes)."
     , "@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;"
     , "@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;"
     , "@group(0) @binding(2) var<storage, read> ix : array<u32>;"
     , ""
     , limbPrelude p
     , s!"@compute @workgroup_size({workgroupSize})"
     , "fn main(@builtin(global_invocation_id) gid : vec3<u32>) {"
     , s!"  let t : u32 = gid.x + gid.y * {(if (s.threads + workgroupSize - 1) / workgroupSize > 65535 then 32768 else max 1 ((s.threads + workgroupSize - 1) / workgroupSize)) * workgroupSize}u;" ] ++ branches ++ [ "}", "" ])

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
