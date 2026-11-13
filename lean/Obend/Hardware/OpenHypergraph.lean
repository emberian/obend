module
/-
# Obend.Hardware.OpenHypergraph — Data-Parallel `StrictOpenHypergraph`, Wavefront Pipeline Layering & `catgrad` Syntactic `Optic` Reverse-Mode AD

Mechanizes the categorical string-diagram and hardware-compilation foundations of
`/Users/ember/hellas/open-hypergraphs` (Wilson & Zanasi, *Data-Parallel Algorithms for String Diagrams*,
`arXiv:2305.01041`) and `/Users/ember/hellas/catgrad` (categorical reverse-mode automatic differentiation
via syntactic `Optic` morphisms), bridged directly to `Obend.Hardware.HDL` and `Obend.Hardware.Compiler`:

1. **Data-Parallel `StrictOpenHypergraph` Representation (`FiniteFunction`, `IndexedCoproduct`, `StrictOpenHypergraph`)**:
   - Represents finite functions $f : A \to B$ as flat index tables (`FiniteFunction`) supporting
     identity (`id`), initial map (`initial`), sequential composition (`comp`), coproduct (`coprod`),
     monoidal parallel product (`tensor`), and symmetric braiding (`twist`),
   - Represents families of variable-arity incidence maps $\sum_{i \in X} s_i \to W$ without pointer
     indirection via segmented arrays (`IndexedCoproduct` with `sizes` and flat `values`),
   - Formalizes `StrictOpenHypergraph` over flat wire object types, operation labels (`HypergraphOp`),
     source/target `IndexedCoproduct` incidence tables, and open boundary ports (`boundaryIn`, `boundaryOut`).
2. **Topological Kahn / Coffman–Graham Wavefront Layering (`layerHypergraph`, `evalHypergraphLayered`)**:
   - Partitions hypergraph operations into synchronous hardware pipeline stages / GPU wavefronts
     (`layerHyperEdges`, `layerHypergraph`), coalescing data-independent operations into the same parallel
     wavefront while inserting synchronous register boundaries across Read-After-Write (RAW),
     Write-After-Read (WAR), and Write-After-Write (WAW) dependencies,
   - Proves **`layerHypergraph_sound`** and **`evalHypergraph_pipelined_eq_comb`**: for every
     `StrictOpenHypergraph`, every layered wavefront stage is conflict-free (`checkStageIndependent = true`),
     and synchronous multi-stage pipelined evaluation produces the exact same wire state and boundary
     outputs as single-pass combinational evaluation (`evalHypergraphComb`).
3. **`catgrad` Syntactic `Optic` Reverse-Mode Automatic Differentiation (`OpticOp`, `compileOpticAdjoint`, `evalOpticFwd`, `evalOpticRev`)**:
   - Compiles forward arithmetic and physics operations (`OpticOp`) into static forward + residual +
     backward cotangent morphisms (`OpticAdjoint`) with **zero runtime tape allocation** (all forward
     residuals are routed on static hypergraph wires),
   - Proves **`optic_reverse_ad_sound`** and **`optic_comp_chain_rule_sound`**: the reverse cotangent
     pass computes exact analytical partial derivatives $\partial L / \partial x$ and $\partial L / \partial y$
     matching forward-mode dual numbers (`DualInt`), and satisfies linear cotangent scaling and the
     2-stage categorical chain rule.
-/
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Tactic.Tooth
@[expose] public section

namespace Obend.Hardware.OpenHypergraph
open Obend.Hardware.HDL Obend.Hardware.Compiler
set_option autoImplicit false

/-! ## 1. Data-Parallel `FiniteFunction`, `IndexedCoproduct` & `StrictOpenHypergraph` (`arXiv:2305.01041`) -/

/-- A finite function $f : \{0, \dots, \text{source}-1\} \to \{0, \dots, \text{target}-1\}$ represented
as a flat data-parallel lookup table (`table : List Nat`). -/
structure FiniteFunction where
  source : Nat
  target : Nat
  table  : List Nat
  deriving DecidableEq, Repr

/-- Well-formedness check for a `FiniteFunction`:
1. `table.length == source`, and
2. Every entry $y \in \text{table}$ satisfies $y < \text{target}$. -/
def FiniteFunction.wf (f : FiniteFunction) : Bool :=
  (f.table.length == f.source) && f.table.all (fun y => decide (y < f.target))

/-- Identity finite function $\mathrm{id}_n : n \to n$. -/
def FiniteFunction.id (n : Nat) : FiniteFunction where
  source := n
  target := n
  table  := List.range n

/-- Unique initial finite function $!_b : 0 \to b$. -/
def FiniteFunction.initial (b : Nat) : FiniteFunction where
  source := 0
  target := b
  table  := []

/-- Sequential composition $g \circ f : f.\text{source} \to g.\text{target}$ via parallel gather (`map`). -/
def FiniteFunction.comp (f g : FiniteFunction) : Option FiniteFunction :=
  if f.target == g.source then
    some {
      source := f.source
      target := g.target
      table  := f.table.map (fun idx => g.table.getD idx 0)
    }
  else
    none

/-- Categorical coproduct $[f, g] : A_1 + A_2 \to B$ when $f$ and $g$ share the same target $B$. -/
def FiniteFunction.coprod (f g : FiniteFunction) : Option FiniteFunction :=
  if f.target == g.target then
    some {
      source := f.source + g.source
      target := f.target
      table  := f.table ++ g.table
    }
  else
    none

/-- Monoidal parallel product (tensor) $f \otimes g : A_1 + A_2 \to B_1 + B_2$, shifting $g$'s
codomain indices by $f.\text{target}$. -/
def FiniteFunction.tensor (f g : FiniteFunction) : FiniteFunction where
  source := f.source + g.source
  target := f.target + g.target
  table  := f.table ++ g.table.map (· + f.target)

/-- Symmetric braiding $\sigma_{a, b} : a + b \to b + a$ swapping a prefix block of length $a$
with a suffix block of length $b$. -/
def FiniteFunction.twist (a b : Nat) : FiniteFunction where
  source := a + b
  target := b + a
  table  := (List.range a).map (· + b) ++ List.range b

/-- Theorem (`finiteFunction_initial_wf`):
For every codomain size `b : Nat`, `FiniteFunction.initial b` is well-formed. -/
theorem finiteFunction_initial_wf (b : Nat) :
    (FiniteFunction.initial b).wf = true := by
  rfl

/-- Theorem (`finiteFunction_tensor_dims`):
The monoidal tensor `f.tensor g` sums both `.source` and `.target` dimensions and has table length
`f.table.length + g.table.length`. -/
theorem finiteFunction_tensor_dims (f g : FiniteFunction) :
    (f.tensor g).source = f.source + g.source ∧
    (f.tensor g).target = f.target + g.target ∧
    (f.tensor g).table.length = f.table.length + g.table.length := by
  simp [FiniteFunction.tensor]

/-- Sum of a list of natural numbers (used for segmented array offsets in `IndexedCoproduct`). -/
def sumNatList (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

/-- An `IndexedCoproduct` represents a finite family of maps $\sum_{i=0}^{k-1} s_i \to W$ as two flat
`FiniteFunction`s:
* `sizes`: maps operation index $i \in \{0, \dots, k-1\}$ to its port arity $s_i$,
* `values`: maps flat concatenated port index $p \in \{0, \dots, \sum s_i - 1\}$ to its incident wire $w \in W$. -/
structure IndexedCoproduct where
  sizes  : FiniteFunction
  values : FiniteFunction
  deriving DecidableEq, Repr

/-- Well-formedness of an `IndexedCoproduct`:
`sizes` and `values` are well-formed `FiniteFunction`s, and `values.source` equals the sum of
all segment lengths in `sizes.table`. -/
def IndexedCoproduct.wf (c : IndexedCoproduct) : Bool :=
  c.sizes.wf && c.values.wf && (c.values.source == sumNatList c.sizes.table)

/-- Extract the wire-incidence list (segment) for operation `opIdx` from an `IndexedCoproduct`. -/
def IndexedCoproduct.segment (c : IndexedCoproduct) (opIdx : Nat) : List Nat :=
  let offset := sumNatList (c.sizes.table.take opIdx)
  let len    := c.sizes.table.getD opIdx 0
  (c.values.table.drop offset).take len

/-- Construct a flat data-parallel `IndexedCoproduct` with wire codomain `numWires` from a list
of per-operation wire lists `segs : List (List Nat)`. -/
def IndexedCoproduct.fromSegments (numWires : Nat) (segs : List (List Nat)) : IndexedCoproduct :=
  let lengths := segs.map List.length
  let flat    := segs.flatten
  { sizes  := { source := segs.length, target := flat.length + 1, table := lengths }
  , values := { source := flat.length, target := numWires,        table := flat } }

/-- Monoidal parallel tensor of two `IndexedCoproduct`s (`c1` over `W_1` and `c2` over `W_2`). -/
def IndexedCoproduct.tensor (c1 c2 : IndexedCoproduct) : IndexedCoproduct where
  sizes  :=
    { source := c1.sizes.source + c2.sizes.source
    , target := max c1.sizes.target c2.sizes.target
    , table  := c1.sizes.table ++ c2.sizes.table }
  values := c1.values.tensor c2.values

/-- Hardware and arithmetic operation labels in an open hypergraph. -/
inductive HypergraphOp where
  | const (val : Int)
  | add
  | sub
  | mul
  | scale (factor : Int)
  | mac
  | mux
  deriving DecidableEq, Repr

/-- Evaluate a single `HypergraphOp` given its list of source wire values `args`. -/
def evalHypergraphOp (op : HypergraphOp) (args : List Int) : Int :=
  match op with
  | .const v => v
  | .add     => args.getD 0 0 + args.getD 1 0
  | .sub     => args.getD 0 0 - args.getD 1 0
  | .mul     => args.getD 0 0 * args.getD 1 0
  | .scale k => k * args.getD 0 0
  | .mac     => args.getD 0 0 * args.getD 1 0 + args.getD 2 0
  | .mux     => if args.getD 0 0 != 0 then args.getD 1 0 else args.getD 2 0

/-- Data-parallel **`StrictOpenHypergraph`** (`arXiv:2305.01041`):
* `nodeTypes`: bitwidth / type label for each wire $w \in \{0, \dots, |W|-1\}$,
* `ops`: operation label for each hyperedge $x \in \{0, \dots, |X|-1\}$,
* `sources`: `IndexedCoproduct` mapping each hyperedge $x$ to its ordered source wires,
* `targets`: `IndexedCoproduct` mapping each hyperedge $x$ to its ordered target wires,
* `boundaryIn`: `FiniteFunction` mapping open graph inputs $I \to W$,
* `boundaryOut`: `FiniteFunction` mapping open graph outputs $O \to W$. -/
structure StrictOpenHypergraph where
  nodeTypes   : List Nat
  ops         : List HypergraphOp
  sources     : IndexedCoproduct
  targets     : IndexedCoproduct
  boundaryIn  : FiniteFunction
  boundaryOut : FiniteFunction
  deriving DecidableEq, Repr

/-- Structural well-formedness checker for a `StrictOpenHypergraph`. -/
def StrictOpenHypergraph.wf (g : StrictOpenHypergraph) : Bool :=
  let numWires := g.nodeTypes.length
  let numOps   := g.ops.length
  g.sources.wf &&
  g.targets.wf &&
  g.boundaryIn.wf &&
  g.targets.sizes.table.all (· == 1) &&
  g.boundaryOut.wf &&
  (g.sources.sizes.source == numOps) &&
  (g.targets.sizes.source == numOps) &&
  (g.sources.values.target == numWires) &&
  (g.targets.values.target == numWires) &&
  (g.boundaryIn.target == numWires) &&
  (g.boundaryOut.target == numWires)

/-- Data-parallel monoidal product $g_1 \otimes g_2$ of two `StrictOpenHypergraph`s. -/
def StrictOpenHypergraph.tensor (g1 g2 : StrictOpenHypergraph) : StrictOpenHypergraph where
  nodeTypes   := g1.nodeTypes ++ g2.nodeTypes
  ops         := g1.ops ++ g2.ops
  sources     := g1.sources.tensor g2.sources
  targets     := g1.targets.tensor g2.targets
  boundaryIn  := g1.boundaryIn.tensor g2.boundaryIn
  boundaryOut := g1.boundaryOut.tensor g2.boundaryOut

/-- Theorem (`strictOpenHypergraph_tensor_counts`):
The parallel tensor of two `StrictOpenHypergraph`s sums wire counts, operation counts,
input boundary ports, and output boundary ports in $O(1)$ metadata operations. -/
theorem strictOpenHypergraph_tensor_counts (g1 g2 : StrictOpenHypergraph) :
    (g1.tensor g2).nodeTypes.length = g1.nodeTypes.length + g2.nodeTypes.length ∧
    (g1.tensor g2).ops.length = g1.ops.length + g2.ops.length ∧
    (g1.tensor g2).boundaryIn.source = g1.boundaryIn.source + g2.boundaryIn.source ∧
    (g1.tensor g2).boundaryOut.source = g1.boundaryOut.source + g2.boundaryOut.source := by
  simp [StrictOpenHypergraph.tensor, FiniteFunction.tensor]

/-! ## 2. Topological Kahn / Coffman–Graham Wavefront Layering (`layerHypergraph`, `evalHypergraphLayered`) -/

/-- Decoded single-output hyperedge extracted from a `StrictOpenHypergraph`. -/
structure HyperEdge where
  opIdx    : Nat
  op       : HypergraphOp
  srcWires : List Nat
  dstWire  : Nat
  deriving DecidableEq, Repr

/-- Build a `StrictOpenHypergraph` from wire count `numWires`, boundary input wires `inWires`,
boundary output wires `outWires`, and a topological list of `HyperEdge`s. -/
def mkStrictOpenHypergraph
    (numWires : Nat)
    (inWires outWires : List Nat)
    (edges : List HyperEdge) : StrictOpenHypergraph where
  nodeTypes   := List.replicate numWires 64
  ops         := edges.map (·.op)
  sources     := IndexedCoproduct.fromSegments numWires (edges.map (·.srcWires))
  targets     := IndexedCoproduct.fromSegments numWires (edges.map (fun e => [e.dstWire]))
  boundaryIn  := { source := inWires.length,  target := numWires, table := inWires }
  boundaryOut := { source := outWires.length, target := numWires, table := outWires }

/-- Linear-time recursive unpacker for `extractHyperEdges`. -/
def extractHyperEdgesAux
    (idx : Nat)
    (ops : List HypergraphOp)
    (srcSizes srcVals tgtVals : List Nat) : List HyperEdge :=
  match ops, srcSizes, tgtVals with
  | [], _, _ => []
  | op :: restOps, sLen :: restSizes, dst :: restTgts =>
    { opIdx    := idx
    , op       := op
    , srcWires := srcVals.take sLen
    , dstWire  := dst } ::
    extractHyperEdgesAux (idx + 1) restOps restSizes (srcVals.drop sLen) restTgts
  | op :: restOps, [], dst :: restTgts =>
    { opIdx := idx, op := op, srcWires := [], dstWire := dst } ::
    extractHyperEdgesAux (idx + 1) restOps [] srcVals restTgts
  | op :: restOps, sLen :: restSizes, [] =>
    { opIdx := idx, op := op, srcWires := srcVals.take sLen, dstWire := 0 } ::
    extractHyperEdgesAux (idx + 1) restOps restSizes (srcVals.drop sLen) []
  | op :: restOps, [], [] =>
    { opIdx := idx, op := op, srcWires := [], dstWire := 0 } ::
    extractHyperEdgesAux (idx + 1) restOps [] srcVals []

/-- Extract the ordered list of `HyperEdge`s from a `StrictOpenHypergraph`. -/
def extractHyperEdges (g : StrictOpenHypergraph) : List HyperEdge :=
  extractHyperEdgesAux 0 g.ops g.sources.sizes.table g.sources.values.table g.targets.values.table

/-- Evaluate a single `HyperEdge` against wire environment `env`, updating `e.dstWire`. -/
def stepHyperEdge (env : Nat → Int) (e : HyperEdge) : Nat → Int :=
  let v := evalHypergraphOp e.op (e.srcWires.map env)
  fun w => if w == e.dstWire then v else env w

/-- Single-pass combinational evaluation of a list of `HyperEdge`s. -/
def evalHyperEdgesComb (initEnv : Nat → Int) (edges : List HyperEdge) : Nat → Int :=
  edges.foldl stepHyperEdge initEnv

/-- Combinational evaluation of a `StrictOpenHypergraph`, returning the values on `boundaryOut`. -/
def evalHypergraphComb (g : StrictOpenHypergraph) (initEnv : Nat → Int) : List Int :=
  let finalEnv := evalHyperEdgesComb initEnv (extractHyperEdges g)
  g.boundaryOut.table.map finalEnv

/-- Check whether hyperedge `e` is completely data-independent of all hyperedges in `stage`:
1. No Write-After-Write (WAW) collision (`e.dstWire != s.dstWire`),
2. No Read-After-Write (RAW) hazard (`!(s.srcWires.contains e.dstWire)`),
3. No Write-After-Read (WAR) hazard (`!(e.srcWires.contains s.dstWire)`). -/
def edgeIndependentOfStage (e : HyperEdge) (stage : List HyperEdge) : Bool :=
  stage.all fun s =>
    (e.dstWire != s.dstWire) &&
    !(s.srcWires.contains e.dstWire) &&
    !(e.srcWires.contains s.dstWire)

/-- Verify that all hyperedges within a single wavefront stage are pairwise data-independent
so they can execute simultaneously in a single GPU wavefront or synchronous RTL clock cycle. -/
def checkStageIndependent : List HyperEdge → Bool
  | [] => true
  | e :: rest => edgeIndependentOfStage e rest && checkStageIndependent rest

/-- Topological Kahn / Coffman–Graham wavefront layering of a list of `HyperEdge`s:
coalesces adjacent data-independent operations into a shared parallel wavefront stage, and inserts
a synchronous pipeline stage boundary whenever a RAW, WAR, or WAW data dependency is encountered. -/
def layerHyperEdges : List HyperEdge → List (List HyperEdge)
  | [] => []
  | e :: rest =>
    match layerHyperEdges rest with
    | [] => [[e]]
    | s :: stages =>
      if edgeIndependentOfStage e s then
        (e :: s) :: stages
      else
        [e] :: s :: stages

/-- Partition a `StrictOpenHypergraph` into synchronous topological wavefront stages. -/
def layerHypergraph (g : StrictOpenHypergraph) : List (List HyperEdge) :=
  layerHyperEdges (extractHyperEdges g)

/-- Evaluate a single synchronous wavefront stage `stage` starting from wire state `env`. -/
def evalWavefrontStage (env : Nat → Int) (stage : List HyperEdge) : Nat → Int :=
  stage.foldl stepHyperEdge env

/-- Synchronous hardware step for a hyperedge `e` inside a wavefront stage:
reads all `e.srcWires` strictly from the frozen stage-entry register snapshot `stageEntryEnv`
(rather than from intermediate intra-stage writes in `curEnv`), updating `e.dstWire` in `curEnv`. -/
def stepHyperEdgeSync (stageEntryEnv : Nat → Int) (curEnv : Nat → Int) (e : HyperEdge) : Nat → Int :=
  let v := evalHypergraphOp e.op (e.srcWires.map stageEntryEnv)
  fun w => if w == e.dstWire then v else curEnv w

/-- Auxiliary fold for synchronous wavefront stage execution where every hyperedge reads
strictly from `stageEntryEnv`. -/
def evalWavefrontStageAux (stageEntryEnv : Nat → Int) (curEnv : Nat → Int) : List HyperEdge → Nat → Int
  | [] => curEnv
  | e :: rest =>
    evalWavefrontStageAux stageEntryEnv (stepHyperEdgeSync stageEntryEnv curEnv e) rest

/-- True synchronous wavefront stage evaluation (`evalWavefrontStageSync`):
all hyperedges in `stage` sample their source wires simultaneously from the stage-entry
snapshot `env` latched at the start of the clock cycle / GPU wavefront. -/
def evalWavefrontStageSync (env : Nat → Int) (stage : List HyperEdge) : Nat → Int :=
  evalWavefrontStageAux env env stage

/-- Evaluate a sequence of layered wavefront stages across synchronous pipeline registers. -/
def evalLayeredStages (initEnv : Nat → Int) (stages : List (List HyperEdge)) : Nat → Int :=
  stages.foldl evalWavefrontStage initEnv

/-- Evaluate a sequence of layered wavefront stages using true synchronous snapshot reads
(`evalWavefrontStageSync`) at each stage boundary. -/
def evalLayeredStagesSync (initEnv : Nat → Int) (stages : List (List HyperEdge)) : Nat → Int :=
  stages.foldl evalWavefrontStageSync initEnv

/-- Evaluate a `StrictOpenHypergraph` stage-by-stage using its wavefront layering `layerHypergraph g`,
returning the final values on `boundaryOut`. -/
def evalHypergraphLayered (g : StrictOpenHypergraph) (initEnv : Nat → Int) : List Int :=
  let finalEnv := evalLayeredStages initEnv (layerHypergraph g)
  g.boundaryOut.table.map finalEnv

/-- Evaluate a `StrictOpenHypergraph` stage-by-stage using true synchronous snapshot wavefronts
(`evalLayeredStagesSync`), returning the final values on `boundaryOut`. -/
def evalHypergraphLayeredSync (g : StrictOpenHypergraph) (initEnv : Nat → Int) : List Int :=
  let finalEnv := evalLayeredStagesSync initEnv (layerHypergraph g)
  g.boundaryOut.table.map finalEnv

/-- Helper lemma: updating wire `dst` does not affect `srcWires.map env` when `!(srcWires.contains dst)`. -/
theorem map_env_update_of_not_contains
    (env : Nat → Int) (dst : Nat) (v : Int) (srcWires : List Nat)
    (hNotMem : (srcWires.contains dst) = false) :
    srcWires.map (fun w => if w == dst then v else env w) = srcWires.map env := by
  induction srcWires with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at hNotMem
    have hw : (w == dst) = false := by
      cases h : w == dst
      · rfl
      · have hRev : (dst == w) = true := beq_iff_eq.mpr (beq_iff_eq.mp h).symm
        rw [hRev] at hNotMem
        exact Bool.noConfusion hNotMem.1
    simp only [List.map_cons, hw, Bool.false_eq_true, ↓reduceIte]
    exact congrArg (env w :: ·) (ih hNotMem.2)

/-- Helper lemma: when no hyperedge in `stage` reads `dst`, updating `dst` in `stageEntryEnv`
leaves `evalWavefrontStageAux` unchanged. -/
theorem evalWavefrontStageAux_shift_entry
    (stageEntryEnv curEnv : Nat → Int) (dst : Nat) (v : Int) (stage : List HyperEdge)
    (hNoRaw : stage.all (fun s => !(s.srcWires.contains dst)) = true) :
    evalWavefrontStageAux (fun w => if w == dst then v else stageEntryEnv w) curEnv stage =
      evalWavefrontStageAux stageEntryEnv curEnv stage := by
  induction stage generalizing curEnv with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hNoRaw
    simp only [evalWavefrontStageAux, stepHyperEdgeSync]
    rw [map_env_update_of_not_contains stageEntryEnv dst v s.srcWires hNoRaw.1]
    exact ih _ hNoRaw.2

/-- Helper lemma: `edgeIndependentOfStage e rest = true` implies no hyperedge in `rest` reads `e.dstWire`. -/
theorem edgeIndependentOfStage_implies_no_raw
    (e : HyperEdge) (rest : List HyperEdge)
    (hInd : edgeIndependentOfStage e rest = true) :
    rest.all (fun s => !(s.srcWires.contains e.dstWire)) = true := by
  unfold edgeIndependentOfStage at hInd
  induction rest with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hInd ⊢
    exact ⟨hInd.1.1.2, ih hInd.2⟩

/-- **Theorem (`evalWavefrontStageSync_eq_evalWavefrontStage`)**:
Whenever a wavefront stage is conflict-free (`checkStageIndependent stage = true`),
true synchronous parallel evaluation (`evalWavefrontStageSync`, where all operations read
simultaneously from the stage-entry snapshot `env`) produces the **exact same** wire environment
as sequential stage evaluation (`evalWavefrontStage`). -/
theorem evalWavefrontStageSync_eq_evalWavefrontStage
    (env : Nat → Int) (stage : List HyperEdge)
    (hInd : checkStageIndependent stage = true) :
    evalWavefrontStageSync env stage = evalWavefrontStage env stage := by
  induction stage generalizing env with
  | nil => rfl
  | cons e rest ih =>
    simp only [checkStageIndependent, Bool.and_eq_true] at hInd
    have hNoRaw := edgeIndependentOfStage_implies_no_raw e rest hInd.1
    unfold evalWavefrontStageSync
    dsimp only [evalWavefrontStageAux, evalWavefrontStage, List.foldl_cons]
    have hStepEq : stepHyperEdgeSync env env e = stepHyperEdge env e := rfl
    rw [hStepEq]
    have hShift := evalWavefrontStageAux_shift_entry
      env (stepHyperEdge env e) e.dstWire (evalHypergraphOp e.op (e.srcWires.map env)) rest hNoRaw
    dsimp only [stepHyperEdge] at hShift ⊢
    rw [← hShift]
    exact ih (stepHyperEdge env e) hInd.2

/-- Lemma (`evalLayeredStagesSync_eq_evalLayeredStages`):
For any list of stages where every stage satisfies `checkStageIndependent`,
`evalLayeredStagesSync` equals `evalLayeredStages`. -/
theorem evalLayeredStagesSync_eq_evalLayeredStages
    (initEnv : Nat → Int) (stages : List (List HyperEdge))
    (hAll : stages.all checkStageIndependent = true) :
    evalLayeredStagesSync initEnv stages = evalLayeredStages initEnv stages := by
  induction stages generalizing initEnv with
  | nil => rfl
  | cons stage rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hAll
    simp only [evalLayeredStagesSync, evalLayeredStages, List.foldl_cons]
    rw [evalWavefrontStageSync_eq_evalWavefrontStage initEnv stage hAll.1]
    exact ih (evalWavefrontStage initEnv stage) hAll.2

/-- Lemma (`layerHyperEdges_flatten`):
Wavefront layering preserves the exact topological order of operations (`(layerHyperEdges edges).flatten = edges`). -/
theorem layerHyperEdges_flatten (edges : List HyperEdge) :
    (layerHyperEdges edges).flatten = edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    dsimp only [layerHyperEdges]
    cases hLayers : layerHyperEdges rest with
    | nil =>
      rw [hLayers] at ih
      simp only [List.flatten_nil] at ih
      subst ih
      rfl
    | cons s stages =>
      rw [hLayers] at ih
      by_cases hInd : edgeIndependentOfStage e s = true
      · simp only [hInd, ↓reduceIte, List.flatten_cons, List.cons_append]
        exact congrArg (e :: ·) ih
      · simp only [hInd, Bool.false_eq_true, ↓reduceIte, List.flatten_cons, List.singleton_append]
        exact congrArg (e :: ·) ih

/-- Lemma (`layerHyperEdges_all_stages_independent`):
Every wavefront stage produced by `layerHyperEdges` is conflict-free (`checkStageIndependent = true`),
guaranteeing zero intra-stage RAW, WAR, or WAW hazards. -/
theorem layerHyperEdges_all_stages_independent (edges : List HyperEdge) :
    (layerHyperEdges edges).all checkStageIndependent = true := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    dsimp only [layerHyperEdges]
    cases hLayers : layerHyperEdges rest with
    | nil =>
      rfl
    | cons s stages =>
      rw [hLayers] at ih
      simp only [List.all_cons, Bool.and_eq_true] at ih
      by_cases hInd : edgeIndependentOfStage e s = true
      · simp [hInd, checkStageIndependent, ih.1, ih.2]
      · simp only [hInd, Bool.false_eq_true, ↓reduceIte]
        simp [checkStageIndependent, edgeIndependentOfStage, ih.1, ih.2]

/-- Lemma (`evalLayeredStages_eq_evalHyperEdgesComb_flatten`):
Evaluating any sequence of wavefront stages `stages` sequentially across pipeline stage boundaries
equals single-pass combinational evaluation of `stages.flatten`. -/
theorem evalLayeredStages_eq_evalHyperEdgesComb_flatten
    (initEnv : Nat → Int) (stages : List (List HyperEdge)) :
    evalLayeredStages initEnv stages =
      evalHyperEdgesComb initEnv stages.flatten := by
  induction stages generalizing initEnv with
  | nil => rfl
  | cons stage rest ih =>
    simp only [evalLayeredStages, List.foldl_cons, List.flatten_cons,
      evalHyperEdgesComb, List.foldl_append]
    exact ih (evalWavefrontStage initEnv stage)

/-- **Theorem (`layerHypergraph_sound`)**:
For EVERY `StrictOpenHypergraph` `g` and initial wire environment `initEnv : Nat → Int`:
1. Every wavefront stage in `layerHypergraph g` is intra-stage data-independent
   (`(layerHypergraph g).all checkStageIndependent = true`),
2. Flattening the layered wavefronts recovers the exact extracted hyperedge DAG,
3. Evaluating `g` stage-by-stage via `evalLayeredStages` produces the exact same wire environment
   as `evalHyperEdgesComb`, and
4. True synchronous snapshot evaluation (`evalLayeredStagesSync`, where all operations in each
   stage read from the frozen stage-entry register snapshot) produces the exact same wire
   environment as `evalHyperEdgesComb`! -/
theorem layerHypergraph_sound (g : StrictOpenHypergraph) (initEnv : Nat → Int) :
    (layerHypergraph g).all checkStageIndependent = true ∧
    (layerHypergraph g).flatten = extractHyperEdges g ∧
    evalLayeredStages initEnv (layerHypergraph g) =
      evalHyperEdgesComb initEnv (extractHyperEdges g) ∧
    evalLayeredStagesSync initEnv (layerHypergraph g) =
      evalHyperEdgesComb initEnv (extractHyperEdges g) := by
  unfold layerHypergraph
  have hInd := layerHyperEdges_all_stages_independent (extractHyperEdges g)
  have hFlat := layerHyperEdges_flatten (extractHyperEdges g)
  have hSeq : evalLayeredStages initEnv (layerHyperEdges (extractHyperEdges g)) =
      evalHyperEdgesComb initEnv (extractHyperEdges g) := by
    rw [evalLayeredStages_eq_evalHyperEdgesComb_flatten, hFlat]
  refine ⟨hInd, hFlat, hSeq, ?_⟩
  rw [evalLayeredStagesSync_eq_evalLayeredStages initEnv _ hInd, hSeq]

/-- **Theorem (`evalHypergraph_pipelined_eq_comb`)**:
For EVERY `StrictOpenHypergraph` `g` and initial wire environment `initEnv : Nat → Int`,
both sequential-stage (`evalHypergraphLayered g initEnv`) and true synchronous snapshot
(`evalHypergraphLayeredSync g initEnv`) wavefront evaluation produce the EXACT same boundary
output vector as unpipelined combinational evaluation (`evalHypergraphComb g initEnv`). -/
theorem evalHypergraph_pipelined_eq_comb (g : StrictOpenHypergraph) (initEnv : Nat → Int) :
    evalHypergraphLayered g initEnv = evalHypergraphComb g initEnv ∧
    evalHypergraphLayeredSync g initEnv = evalHypergraphComb g initEnv := by
  unfold evalHypergraphLayered evalHypergraphLayeredSync evalHypergraphComb
  rw [(layerHypergraph_sound g initEnv).2.2.1, (layerHypergraph_sound g initEnv).2.2.2]
  exact ⟨rfl, rfl⟩

/-- Golden 4-operation diamond hypergraph computing $(x_0 + x_1) \cdot (x_2 + x_3) + 10$:
* Wires `0..3`: boundary inputs $x_0, x_1, x_2, x_3$,
* Edge 0 (Stage 0): $w_4 := w_0 + w_1$,
* Edge 1 (Stage 0, parallel with Edge 0!): $w_5 := w_2 + w_3$,
* Edge 2 (Stage 1, depends on $w_4, w_5$): $w_6 := w_4 \cdot w_5$,
* Edge 3 (Stage 2, depends on $w_6$): $w_7 := 10$,
* Edge 4 (Stage 2, depends on $w_6, w_7$): $w_8 := w_6 + w_7$. -/
def goldenDiamondHypergraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 9 [0, 1, 2, 3] [8]
    [ { opIdx := 0, op := .add,      srcWires := [0, 1], dstWire := 4 }
    , { opIdx := 1, op := .add,      srcWires := [2, 3], dstWire := 5 }
    , { opIdx := 2, op := .mul,      srcWires := [4, 5], dstWire := 6 }
    , { opIdx := 3, op := .const 10, srcWires := [],     dstWire := 7 }
    , { opIdx := 4, op := .add,      srcWires := [6, 7], dstWire := 8 } ]

/-- Theorem (`golden_diamond_hypergraph_wavefronts_verified`):
Verifies that `goldenDiamondHypergraph` is well-formed (`wf = true`), that `layerHypergraph`
packs the independent additions (`op 0` and `op 1`) plus constant load (`op 3`) into earlier parallel
wavefronts across 3 synchronous pipeline stages (`[2, 2, 1]` ops per stage), and that
`evalHypergraphLayered`, `evalHypergraphLayeredSync`, and `evalHypergraphComb` all evaluate
$(3 + 4) \cdot (5 + 6) + 10 = 87$. -/
theorem golden_diamond_hypergraph_wavefronts_verified :
    let initEnv : Nat → Int := fun w =>
      match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | _ => 0
    goldenDiamondHypergraph.wf = true ∧
    (layerHypergraph goldenDiamondHypergraph).length = 3 ∧
    ((layerHypergraph goldenDiamondHypergraph).map List.length) = [2, 2, 1] ∧
    evalHypergraphLayered goldenDiamondHypergraph initEnv = [87] ∧
    evalHypergraphLayeredSync goldenDiamondHypergraph initEnv = [87] ∧
    evalHypergraphComb goldenDiamondHypergraph initEnv = [87] := by
  decide +kernel

/-! ## 3. `catgrad` Syntactic `Optic` Reverse-Mode AD (`OpticOp`, `compileOpticAdjoint`, `evalOpticFwd`, `evalOpticRev`) -/

/-- Forward-mode Dual Number $x + \dot{x}\varepsilon$ ($\varepsilon^2 = 0$) over exact integers,
used as the mathematical reference specification for analytical partial derivatives. -/
structure DualInt where
  primal  : Int
  tangent : Int
  deriving DecidableEq, Repr

/-- Dual number addition $(a + \dot{a}\varepsilon) + (b + \dot{b}\varepsilon) = (a + b) + (\dot{a} + \dot{b})\varepsilon$. -/
def DualInt.add (a b : DualInt) : DualInt where
  primal  := a.primal + b.primal
  tangent := a.tangent + b.tangent

/-- Dual number subtraction $(a + \dot{a}\varepsilon) - (b + \dot{b}\varepsilon) = (a - b) + (\dot{a} - \dot{b})\varepsilon$. -/
def DualInt.sub (a b : DualInt) : DualInt where
  primal  := a.primal - b.primal
  tangent := a.tangent - b.tangent

/-- Dual number multiplication (Leibniz product rule):
$(a + \dot{a}\varepsilon)(b + \dot{b}\varepsilon) = (a b) + (\dot{a} b + a \dot{b})\varepsilon$. -/
def DualInt.mul (a b : DualInt) : DualInt where
  primal  := a.primal * b.primal
  tangent := a.tangent * b.primal + a.primal * b.tangent

/-- Differentiable operations in `catgrad`'s `Optic` reverse-mode AD calculus. -/
inductive OpticOp where
  | add                   -- f(x, y) = x + y
  | sub                   -- f(x, y) = x - y
  | mul                   -- f(x, y) = x * y
  | scale     (k : Int)   -- f(x, y) = k * x
  | square                -- f(x, y) = x * x
  | linearMac (w : Int)   -- f(x, y) = w * x + y
  | bilinear  (c : Int)   -- f(x, y) = c * (x * y)
  deriving DecidableEq, Repr

/-- Reference forward-mode dual evaluation `evalOpticDual` for any `OpticOp`. -/
def evalOpticDual (op : OpticOp) (dx dy : DualInt) : DualInt :=
  match op with
  | .add         => DualInt.add dx dy
  | .sub         => DualInt.sub dx dy
  | .mul         => DualInt.mul dx dy
  | .scale k     => DualInt.mul ⟨k, 0⟩ dx
  | .square      => DualInt.mul dx dx
  | .linearMac w => DualInt.add (DualInt.mul ⟨w, 0⟩ dx) dy
  | .bilinear c  => DualInt.mul ⟨c, 0⟩ (DualInt.mul dx dy)

/-- Static residual wire descriptor and backward cotangent rule produced by `compileOpticAdjoint`:
In `catgrad`, an `Optic` morphism $\langle \text{fwd}, \text{rev} \rangle : (A, \Delta A) \to (B, \Delta B)$
routes static residual wires $M$ from the forward hypergraph directly into the reverse cotangent
hypergraph with **zero runtime dynamic tape allocation**! -/
structure OpticAdjoint where
  op                : OpticOp
  numResidualWires  : Nat
  usesInputResiduals : Bool
  deriving DecidableEq, Repr

/-- Syntactically compile a forward `OpticOp` into its static `OpticAdjoint` descriptor:
linear operations (`add`, `sub`, `scale`, `linearMac`) require `0` residual wires, while nonlinear
multiplicative operations (`mul`, `square`, `bilinear`) route `1` or `2` static input wires into
the reverse pass. -/
def compileOpticAdjoint (op : OpticOp) : OpticAdjoint :=
  match op with
  | .add         => { op := op, numResidualWires := 0, usesInputResiduals := false }
  | .sub         => { op := op, numResidualWires := 0, usesInputResiduals := false }
  | .scale _     => { op := op, numResidualWires := 0, usesInputResiduals := false }
  | .linearMac _ => { op := op, numResidualWires := 0, usesInputResiduals := false }
  | .square      => { op := op, numResidualWires := 1, usesInputResiduals := true }
  | .mul         => { op := op, numResidualWires := 2, usesInputResiduals := true }
  | .bilinear _  => { op := op, numResidualWires := 2, usesInputResiduals := true }

/-- Forward pass of an `OpticOp`: computes `(primalOut, (resWire0, resWire1))`, where `(resWire0, resWire1)`
are the static residual wires routed to the backward cotangent pass (zero for linear ops). -/
def evalOpticFwd (op : OpticOp) (x y : Int) : Int × (Int × Int) :=
  match op with
  | .add         => (x + y,       (0, 0))
  | .sub         => (x - y,       (0, 0))
  | .mul         => (x * y,       (x, y))
  | .scale k     => (k * x,       (0, 0))
  | .square      => (x * x,       (x, 0))
  | .linearMac w => (w * x + y,   (0, 0))
  | .bilinear c  => (c * (x * y), (x, y))

/-- Reverse cotangent pass of a compiled `OpticAdjoint`: given the static residual wires
`res = (r0, r1)` from `evalOpticFwd` and the upstream output cotangent `dOut = ∂L/∂z`, computes
the exact input cotangents `(dx, dy) = (∂L/∂x, ∂L/∂y)`. -/
def evalOpticRev (adj : OpticAdjoint) (res : Int × Int) (dOut : Int) : Int × Int :=
  let (r0, r1) := res
  match adj.op with
  | .add         => (dOut, dOut)
  | .sub         => (dOut, -dOut)
  | .mul         => (r1 * dOut, r0 * dOut)
  | .scale k     => (k * dOut, 0)
  | .square      => ((r0 + r0) * dOut, 0)
  | .linearMac w => (w * dOut, dOut)
  | .bilinear c  => ((c * r1) * dOut, (c * r0) * dOut)

/-- **Theorem (`optic_reverse_ad_sound`)**:
For EVERY `op : OpticOp` and EVERY input pair `(x, y : Int)`:
1. The forward pass `evalOpticFwd op x y` computes the exact primal value of `evalOpticDual`,
2. Seeding the compiled reverse cotangent pass `evalOpticRev (compileOpticAdjoint op) res 1`
   with unit output cotangent `dOut = 1` computes the **exact analytical partial derivatives**
   $\left(\frac{\partial f}{\partial x}, \frac{\partial f}{\partial y}\right)$ matching forward-mode
   dual numbers `(evalOpticDual op ⟨x, 1⟩ ⟨y, 0⟩).tangent` and `(evalOpticDual op ⟨x, 0⟩ ⟨y, 1⟩).tangent`,
3. For any upstream cotangent `dOut : Int`, `evalOpticRev` scales both partial derivatives linearly
   by `dOut` (`dx = (∂f/∂x) * dOut` and `dy = (∂f/∂y) * dOut`). -/
theorem optic_reverse_ad_sound (op : OpticOp) (x y dOut : Int) :
    let (z, res) := evalOpticFwd op x y
    let adj := compileOpticAdjoint op
    let (gx, gy) := evalOpticRev adj res 1
    let (dx, dy) := evalOpticRev adj res dOut
    z = (evalOpticDual op ⟨x, 1⟩ ⟨y, 0⟩).primal ∧
    gx = (evalOpticDual op ⟨x, 1⟩ ⟨y, 0⟩).tangent ∧
    gy = (evalOpticDual op ⟨x, 0⟩ ⟨y, 1⟩).tangent ∧
    dx = gx * dOut ∧
    dy = gy * dOut := by
  cases op with
  | add =>
    dsimp only [evalOpticFwd, compileOpticAdjoint, evalOpticRev, evalOpticDual, DualInt.add]
    refine ⟨rfl, by omega, by omega, by omega, by omega⟩
  | sub =>
    dsimp only [evalOpticFwd, compileOpticAdjoint, evalOpticRev, evalOpticDual, DualInt.sub]
    refine ⟨rfl, by omega, by omega, by omega, by omega⟩
  | mul =>
    dsimp only [evalOpticFwd, compileOpticAdjoint, evalOpticRev, evalOpticDual, DualInt.mul]
    simp [Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add]
  | scale k =>
    dsimp only [evalOpticFwd, compileOpticAdjoint, evalOpticRev, evalOpticDual, DualInt.mul]
    simp [Int.mul_one, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add]
  | square =>
    dsimp only [evalOpticFwd, compileOpticAdjoint, evalOpticRev, evalOpticDual, DualInt.mul]
    simp [Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero]
  | linearMac w =>
    dsimp only [evalOpticFwd, compileOpticAdjoint, evalOpticRev, evalOpticDual, DualInt.add, DualInt.mul]
    simp [Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add]
  | bilinear c =>
    dsimp only [evalOpticFwd, compileOpticAdjoint, evalOpticRev, evalOpticDual, DualInt.mul]
    simp [Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add]

/-- Composed 2-stage Optic hypergraph $L(x, y) = \text{op}_2(\text{op}_1(x, y), y)$ where variable $y$
fans out to both stage 1 and stage 2 (so the backward pass accumulates $y$'s cotangents via addition
$\Delta y = \Delta y_1 + \Delta y_2$, the dual of forward wire fanout/copying in `catgrad`!). -/
def evalOpticChain2Fwd (op1 op2 : OpticOp) (x y : Int) : Int × ((Int × Int) × (Int × Int)) :=
  let (u, res1) := evalOpticFwd op1 x y
  let (z, res2) := evalOpticFwd op2 u y
  (z, (res1, res2))

/-- Reverse pass of the 2-stage Optic composition $L(x, y) = \text{op}_2(\text{op}_1(x, y), y)$:
propagates `dOut` backward through `op2` to obtain `(du, dy2)`, then propagates `du` backward
through `op1` to obtain `(dx, dy1)`, and sums the fanout cotangent `dy = dy1 + dy2`. -/
def evalOpticChain2Rev
    (adj1 adj2 : OpticAdjoint)
    (res : (Int × Int) × (Int × Int))
    (dOut : Int) : Int × Int :=
  let (res1, res2) := res
  let (du, dy2) := evalOpticRev adj2 res2 dOut
  let (dx, dy1) := evalOpticRev adj1 res1 du
  (dx, dy1 + dy2)

/-- **Theorem (`optic_comp_chain_rule_sound`)**:
For EVERY pair of operations `op1 op2 : OpticOp` and EVERY input `(x, y : Int)`, the 2-stage
`catgrad` Optic composition (`evalOpticChain2Fwd` followed by `evalOpticChain2Rev` with fanout
cotangent accumulation $\Delta y = \Delta y_1 + \Delta y_2$) computes the exact composed analytical
gradient $\left(\frac{\partial L}{\partial x}, \frac{\partial L}{\partial y}\right)$ matching
forward-mode dual numbers! -/
theorem optic_comp_chain_rule_sound (op1 op2 : OpticOp) (x y : Int) :
    let (z, res) := evalOpticChain2Fwd op1 op2 x y
    let (gx, gy) := evalOpticChain2Rev (compileOpticAdjoint op1) (compileOpticAdjoint op2) res 1
    let dualX := evalOpticDual op2 (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩) ⟨y, 0⟩
    let dualY := evalOpticDual op2 (evalOpticDual op1 ⟨x, 0⟩ ⟨y, 1⟩) ⟨y, 1⟩
    z = dualX.primal ∧
    gx = dualX.tangent ∧
    gy = dualY.tangent := by
  have h1 := optic_reverse_ad_sound op1 x y 1
  dsimp only at h1
  let u := (evalOpticFwd op1 x y).1
  let res1 := (evalOpticFwd op1 x y).2
  let du_dx := (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩).tangent
  let du_dy := (evalOpticDual op1 ⟨x, 0⟩ ⟨y, 1⟩).tangent
  have h2 := optic_reverse_ad_sound op2 u y 1
  dsimp only at h2
  let res2 := (evalOpticFwd op2 u y).2
  let dz_du := (evalOpticRev (compileOpticAdjoint op2) res2 1).1
  let dz_dy2 := (evalOpticRev (compileOpticAdjoint op2) res2 1).2
  have h1_scaled := optic_reverse_ad_sound op1 x y dz_du
  dsimp only at h1_scaled
  dsimp only [evalOpticChain2Fwd, evalOpticChain2Rev]
  rw [h1_scaled.2.2.2.1, h1_scaled.2.2.2.2]
  rw [h1.2.1, h1.2.2.1]
  have hPrimal1Y : (evalOpticDual op1 ⟨x, 0⟩ ⟨y, 1⟩).primal = u := by
    cases op1 <;> rfl
  have hPrimal1X : (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩).primal = u := h1.1.symm
  refine ⟨?_, ?_, ?_⟩
  · change (evalOpticFwd op2 u y).1 = (evalOpticDual op2 (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩) ⟨y, 0⟩).primal
    rw [h2.1]
    cases hDual1 : evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩ with
    | mk p1 t1 =>
      have hp1 : p1 = u := by
        rw [← hPrimal1X, hDual1]
      rw [hp1]
      cases op2 <;> rfl
  · change du_dx * dz_du = (evalOpticDual op2 (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩) ⟨y, 0⟩).tangent
    dsimp only [dz_du, res2]
    rw [h2.2.1]
    cases hDual1 : evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩ with
    | mk p1 t1 =>
      have hp1 : p1 = u := by rw [← hPrimal1X, hDual1]
      have ht1 : t1 = du_dx := by dsimp [du_dx]; rw [hDual1]
      rw [hp1, ht1]
      cases op2 with
      | add | sub =>
        dsimp only [evalOpticDual, DualInt.add, DualInt.sub, DualInt.mul]
        omega
      | mul =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp [Int.mul_zero, Int.add_zero]
      | scale k =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp [Int.mul_one, Int.zero_mul, Int.zero_add, Int.mul_comm]
      | square =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp [Int.add_mul, Int.mul_comm]
      | linearMac w =>
        dsimp only [evalOpticDual, DualInt.add, DualInt.mul]
        simp [Int.mul_one, Int.zero_mul, Int.zero_add, Int.add_zero, Int.mul_comm]
      | bilinear c =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp only [Int.zero_mul, Int.one_mul, Int.mul_zero, Int.add_zero, Int.zero_add]
        rw [← Int.mul_assoc du_dx c y, Int.mul_comm du_dx c, Int.mul_assoc c du_dx y]
  · change du_dy * dz_du + dz_dy2 = (evalOpticDual op2 (evalOpticDual op1 ⟨x, 0⟩ ⟨y, 1⟩) ⟨y, 1⟩).tangent
    dsimp only [dz_du, dz_dy2, res2]
    rw [h2.2.1, h2.2.2.1]
    cases hDual1 : evalOpticDual op1 ⟨x, 0⟩ ⟨y, 1⟩ with
    | mk p1 t1 =>
      have hp1 : p1 = u := by rw [← hPrimal1Y, hDual1]
      have ht1 : t1 = du_dy := by dsimp [du_dy]; rw [hDual1]
      rw [hp1, ht1]
      cases op2 with
      | add | sub =>
        dsimp only [evalOpticDual, DualInt.add, DualInt.sub, DualInt.mul]
        omega
      | mul =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp [Int.mul_one]
      | scale k =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp [Int.mul_one, Int.zero_mul, Int.zero_add, Int.add_zero, Int.mul_comm]
      | square =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp [Int.add_zero, Int.add_mul, Int.mul_comm]
      | linearMac w =>
        dsimp only [evalOpticDual, DualInt.add, DualInt.mul]
        simp [Int.mul_one, Int.zero_mul, Int.zero_add, Int.mul_comm]
      | bilinear c =>
        dsimp only [evalOpticDual, DualInt.mul]
        simp only [Int.zero_mul, Int.one_mul, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_one]
        rw [Int.mul_add c (du_dy * y) u]
        have hComm : du_dy * (c * y) = c * (du_dy * y) := by
          rw [← Int.mul_assoc du_dy c y, Int.mul_comm du_dy c, Int.mul_assoc c du_dy y]
        rw [hComm]

/-- **Theorem (`golden_optic_ad_and_empty_hypergraph_verified`)**:
1. Verifies the empty-hypergraph boundary case (`ops = []`): `layerHypergraph` produces `[]` stages
   and `evalHypergraphLayered` passes open input wires straight to open output ports,
2. Verifies `catgrad` 2-stage Optic AD on $L(x, y) = (3x + y) \cdot y$ at $(x, y) = (4, 5)$, confirming
   primal $L(4, 5) = 85$ and exact analytical partial derivatives
   $\left(\frac{\partial L}{\partial x}, \frac{\partial L}{\partial y}\right) = (3y,\; 3x + 2y) = (15, 22)$
   with zero dynamic tape allocation. -/
theorem golden_optic_ad_and_empty_hypergraph_verified :
    let emptyG := mkStrictOpenHypergraph 2 [0, 1] [1, 0] []
    let initEnv : Nat → Int := fun w => if w == 0 then 11 else 29
    let (z, res) := evalOpticChain2Fwd (.linearMac 3) .mul 4 5
    let (gx, gy) := evalOpticChain2Rev (compileOpticAdjoint (.linearMac 3)) (compileOpticAdjoint .mul) res 1
    emptyG.wf = true ∧
    layerHypergraph emptyG = [] ∧
    evalHypergraphLayered emptyG initEnv = [29, 11] ∧
    z = 85 ∧
    gx = 15 ∧
    gy = 22 := by
  decide +kernel

/-! ## 4. Static `OpticOp → StrictOpenHypergraph` Compilation & `Obend.Hardware.HDL` RTL Bridge -/

/-- Compile a differentiable `OpticOp` into a static 9-wire `StrictOpenHypergraph`
with open boundary inputs `[0, 1, 2]` (`x`, `y`, `dOut`), static internal residual wires `6..8`
(zero runtime tape allocation!), and open boundary outputs `[3, 4, 5]` (`[z, dx, dy]`). -/
def compileOpticToHypergraph (op : OpticOp) : StrictOpenHypergraph :=
  let edges : List HyperEdge :=
    match op with
    | .add =>
      [ { opIdx := 0, op := .add,        srcWires := [0, 1], dstWire := 3 }
      , { opIdx := 1, op := .scale 1,    srcWires := [2],    dstWire := 4 }
      , { opIdx := 2, op := .scale 1,    srcWires := [2],    dstWire := 5 } ]
    | .sub =>
      [ { opIdx := 0, op := .sub,        srcWires := [0, 1], dstWire := 3 }
      , { opIdx := 1, op := .scale 1,    srcWires := [2],    dstWire := 4 }
      , { opIdx := 2, op := .scale (-1), srcWires := [2],    dstWire := 5 } ]
    | .mul =>
      [ { opIdx := 0, op := .mul,        srcWires := [0, 1], dstWire := 3 }
      , { opIdx := 1, op := .mul,        srcWires := [1, 2], dstWire := 4 }
      , { opIdx := 2, op := .mul,        srcWires := [0, 2], dstWire := 5 } ]
    | .scale k =>
      [ { opIdx := 0, op := .scale k,    srcWires := [0],    dstWire := 3 }
      , { opIdx := 1, op := .scale k,    srcWires := [2],    dstWire := 4 }
      , { opIdx := 2, op := .const 0,    srcWires := [],     dstWire := 5 } ]
    | .square =>
      [ { opIdx := 0, op := .mul,        srcWires := [0, 0], dstWire := 3 }
      , { opIdx := 1, op := .add,        srcWires := [0, 0], dstWire := 6 }
      , { opIdx := 2, op := .mul,        srcWires := [6, 2], dstWire := 4 }
      , { opIdx := 3, op := .const 0,    srcWires := [],     dstWire := 5 } ]
    | .linearMac w =>
      [ { opIdx := 0, op := .scale w,    srcWires := [0],    dstWire := 6 }
      , { opIdx := 1, op := .add,        srcWires := [6, 1], dstWire := 3 }
      , { opIdx := 2, op := .scale w,    srcWires := [2],    dstWire := 4 }
      , { opIdx := 3, op := .scale 1,    srcWires := [2],    dstWire := 5 } ]
    | .bilinear c =>
      [ { opIdx := 0, op := .mul,        srcWires := [0, 1], dstWire := 6 }
      , { opIdx := 1, op := .scale c,    srcWires := [6],    dstWire := 3 }
      , { opIdx := 2, op := .scale c,    srcWires := [1],    dstWire := 7 }
      , { opIdx := 3, op := .mul,        srcWires := [7, 2], dstWire := 4 }
      , { opIdx := 4, op := .scale c,    srcWires := [0],    dstWire := 8 }
      , { opIdx := 5, op := .mul,        srcWires := [8, 2], dstWire := 5 } ]
  mkStrictOpenHypergraph 9 [0, 1, 2] [3, 4, 5] edges

/-- **Theorem (`compileOpticToHypergraph_wf`)**:
For every `op : OpticOp`, the synthesized forward+backward `StrictOpenHypergraph` is well-formed. -/
theorem compileOpticToHypergraph_wf (op : OpticOp) :
    (compileOpticToHypergraph op).wf = true := by
  cases op <;> rfl

/-- Initial wire environment binding wire `0 ↦ x`, wire `1 ↦ y`, and wire `2 ↦ dOut`. -/
def opticHypergraphInitEnv (x y dOut : Int) (w : Nat) : Int :=
  match w with
  | 0 => x
  | 1 => y
  | 2 => dOut
  | _ => 0

/-- **Theorem (`compileOpticToHypergraph_sound`)**:
For EVERY `op : OpticOp` and EVERY `(x, y, dOut : Int)`, evaluating the static
`StrictOpenHypergraph` `compileOpticToHypergraph op` via combinational evaluation
(`evalHypergraphComb`), sequential wavefront evaluation (`evalHypergraphLayered`), or
true synchronous snapshot wavefront evaluation (`evalHypergraphLayeredSync`) produces the
exact 3-output vector `[z, dx, dy]` matching `evalOpticFwd` and `evalOpticRev`! -/
theorem compileOpticToHypergraph_sound (op : OpticOp) (x y dOut : Int) :
    let g := compileOpticToHypergraph op
    let env := opticHypergraphInitEnv x y dOut
    let (z, res) := evalOpticFwd op x y
    let (dx, dy) := evalOpticRev (compileOpticAdjoint op) res dOut
    evalHypergraphComb g env = [z, dx, dy] ∧
    evalHypergraphLayered g env = [z, dx, dy] ∧
    evalHypergraphLayeredSync g env = [z, dx, dy] := by
  have hPipe := evalHypergraph_pipelined_eq_comb (compileOpticToHypergraph op) (opticHypergraphInitEnv x y dOut)
  have hComb :
      evalHypergraphComb (compileOpticToHypergraph op) (opticHypergraphInitEnv x y dOut) =
        [ (evalOpticFwd op x y).1
        , (evalOpticRev (compileOpticAdjoint op) (evalOpticFwd op x y).2 dOut).1
        , (evalOpticRev (compileOpticAdjoint op) (evalOpticFwd op x y).2 dOut).2 ] := by
    cases op with
    | add =>
      change [x + y, 1 * dOut, 1 * dOut] = [x + y, dOut, dOut]
      simp [Int.one_mul]
    | sub =>
      change [x - y, 1 * dOut, (-1) * dOut] = [x - y, dOut, -dOut]
      simp [Int.one_mul, Int.neg_one_mul]
    | linearMac w =>
      change [w * x + y, w * dOut, 1 * dOut] = [w * x + y, w * dOut, dOut]
      simp [Int.one_mul]
    | mul | scale _ | square | bilinear _ =>
      rfl
  dsimp only
  refine ⟨hComb, ?_, ?_⟩
  · rw [hPipe.1, hComb]
  · rw [hPipe.2, hComb]

/-- 64-bit hardware `BitVec 64` evaluation semantics for `HypergraphOp`, matching `Obend.Hardware.HDL.evalRtlExpr`. -/
def evalHypergraphOpBv (op : HypergraphOp) (args : List (BitVec 64)) : BitVec 64 :=
  let a0 := args.getD 0 0#64
  let a1 := args.getD 1 0#64
  let a2 := args.getD 2 0#64
  match op with
  | .const v => BitVec.ofInt 64 v
  | .add     => a0 + a1
  | .sub     => a0 - a1
  | .mul     => a0 * a1
  | .scale k => BitVec.ofInt 64 k * a0
  | .mac     => a0 * a1 + a2
  | .mux     => if a0 != 0#64 then a1 else a2

theorem map_getD_eq_getElem? {α : Type} (xs : List α) (f : α → BitVec 64) (i : Nat) :
    (xs.map f).getD i 0#64 =
      match xs[i]? with
      | some u => f u
      | none   => 0#64 := by
  simp only [List.getD, List.getElem?_map]
  cases xs[i]? <;> rfl

/-- Lower a `HypergraphOp` applied to operand expressions `args` to an `Obend.Hardware.HDL.RtlExpr`; a
missing operand is `0`, as in `evalHypergraphOpBv`. The pipelined compiler below reads a stage's entry
(`stageEntryExpr`) through it, and `Obend.Hardware.Square.elemOpToRtl` an element of an array wire. -/
def compileHypergraphOpExpr (op : HypergraphOp) (args : List RtlExpr) : RtlExpr :=
  let a (i : Nat) : RtlExpr := args.getD i (.const 0#64)
  match op with
  | .const v => .const (BitVec.ofInt 64 v)
  | .add     => .alu .add (a 0) (a 1)
  | .sub     => .alu .sub (a 0) (a 1)
  | .mul     => .alu .mul (a 0) (a 1)
  | .scale k => .alu .mul (.const (BitVec.ofInt 64 k)) (a 0)
  | .mac     => .alu .add (.alu .mul (a 0) (a 1)) (a 2)
  | .mux     => .mux (a 0) (a 1) (a 2)

theorem evalRtlExpr_getD_const (inputs wires regs : Nat → BitVec 64) (args : List RtlExpr) (i : Nat) :
    evalRtlExpr inputs wires regs (args.getD i (.const 0#64)) =
      (args.map (evalRtlExpr inputs wires regs)).getD i 0#64 := by
  rw [map_getD_eq_getElem?]
  simp only [List.getD_eq_getElem?_getD]
  cases args[i]? <;> rfl

/-- **`evalRtlExpr_compileHypergraphOpExpr`**: for every operation and every operand list, the lowered
expression evaluates to `evalHypergraphOpBv` of the evaluated operands. -/
theorem evalRtlExpr_compileHypergraphOpExpr (op : HypergraphOp) (args : List RtlExpr)
    (inputs wires regs : Nat → BitVec 64) :
    evalRtlExpr inputs wires regs (compileHypergraphOpExpr op args) =
      evalHypergraphOpBv op (args.map (evalRtlExpr inputs wires regs)) := by
  cases op <;>
    simp only [compileHypergraphOpExpr, evalRtlExpr, evalAluOp, evalHypergraphOpBv, evalRtlExpr_getD_const]

/- The combinational lowering of a whole graph is `Obend.Hardware.Square.compileHypergraphToRtl`, the
scalar graph as the one-element instance (`ofScalar`) of `compileArrayGraphToRtl`. -/

/-! ## 5. Whole-Graph Functorial Reverse-AD (`compileGraphAdjoint`, `compileGraphAdjoint_multiEdge_sound`) -/

/-- State of the whole-graph reverse-mode cotangent compiler:
* `cotMap`: maps each primal wire $w$ that has received at least one downstream cotangent contribution
  to the SSA wire index holding its accumulated cotangent $\Delta w$,
* `nextWire`: next fresh wire index in the augmented hypergraph,
* `revEdges`: reverse-pass cotangent pullback and fanout-accumulation hyperedges emitted so far. -/
structure CotangentBuilderState where
  cotMap   : List (Nat × Nat)
  nextWire : Nat
  revEdges : List HyperEdge
  deriving DecidableEq, Repr

/-- Update or insert `(w, cotWire)` in a cotangent wire map. -/
def setCotWire (w cotWire : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(w, cotWire)]
  | (k, v) :: rest =>
    if k == w then (w, cotWire) :: rest
    else (k, v) :: setCotWire w cotWire rest

/-- Single-pass lookup-and-update on `cotMap`:
* If `w` is not present, appends `(w, deltaWire)` and returns `(none, cotMap')`;
* If `(w, prevWire)` is present, updates it in-place to `(w, sumWire)` and returns `(some prevWire, cotMap')`. -/
def upsertCotWire (w deltaWire sumWire : Nat) :
    List (Nat × Nat) → Option Nat × List (Nat × Nat)
  | [] => (none, [(w, deltaWire)])
  | (k, v) :: rest =>
    if k == w then
      (some v, (w, sumWire) :: rest)
    else
      match upsertCotWire w deltaWire sumWire rest with
      | (res, rest') => (res, (k, v) :: rest')

/-- Emit a single reverse-pass `HyperEdge` with a freshly allocated destination wire. -/
def emitRevEdge (op : HypergraphOp) (srcWires : List Nat) :
    CotangentBuilderState → Nat × CotangentBuilderState
  | ⟨cotMap, nextWire, revEdges⟩ =>
    let edge : HyperEdge :=
      { opIdx := 0, op := op, srcWires := srcWires, dstWire := nextWire }
    (nextWire, ⟨cotMap, nextWire + 1, revEdges ++ [edge]⟩)

/-- Accumulate a cotangent contribution on wire `deltaWire` into primal wire `w`:
* If `w` has no prior cotangent wire in `st.cotMap`, binds `w ↦ deltaWire` directly;
* If `w` already has a cotangent wire `prevWire` (because `w` fans out to multiple downstream consumers
  or is used twice in the same operation), emits a `.add` hyperedge summing `[prevWire, deltaWire]`
  into a fresh wire and updates `st.cotMap`! -/
def accumWireCotangent (w deltaWire : Nat) : CotangentBuilderState → CotangentBuilderState
  | ⟨cotMap, nextWire, revEdges⟩ =>
    match upsertCotWire w deltaWire nextWire cotMap with
    | (none, cotMap') =>
      ⟨cotMap', nextWire, revEdges⟩
    | (some prevWire, cotMap') =>
      let addEdge : HyperEdge :=
        { opIdx := 0, op := .add, srcWires := [prevWire, deltaWire], dstWire := nextWire }
      ⟨cotMap', nextWire + 1, revEdges ++ [addEdge]⟩

/-- Emit a reverse-pass `HyperEdge` `(op, srcWires)` and immediately accumulate its output wire into
primal wire `w` (emitting a `.add` fanout accumulator edge if `w` already has a cotangent wire). -/
def emitAndAccum (w : Nat) (op : HypergraphOp) (srcWires : List Nat) :
    CotangentBuilderState → CotangentBuilderState
  | ⟨cotMap, nextWire, revEdges⟩ =>
    let e1 : HyperEdge :=
      { opIdx := 0, op := op, srcWires := srcWires, dstWire := nextWire }
    match upsertCotWire w nextWire (nextWire + 1) cotMap with
    | (none, cotMap') =>
      ⟨cotMap', nextWire + 1, revEdges ++ [e1]⟩
    | (some prevWire, cotMap') =>
      let e2 : HyperEdge :=
        { opIdx := 0, op := .add, srcWires := [prevWire, nextWire], dstWire := nextWire + 1 }
      ⟨cotMap', nextWire + 2, revEdges ++ [e1, e2]⟩

/-- Total structural wire index lookup (`wireAt ws i`), avoiding typeclass `GetElem?` indirection. -/
def wireAt : List Nat → Nat → Nat
  | [], _ => 0
  | w :: _, 0 => w
  | _ :: rest, i + 1 => wireAt rest i

/-- Emit the reverse-mode cotangent pullback edges for a single forward `HyperEdge` `e`,
routing forward primal wires directly as static residuals with zero runtime tape allocation. -/
def pullbackHyperEdge (e : HyperEdge) : CotangentBuilderState → CotangentBuilderState
  | ⟨cotMap, nextWire, revEdges⟩ =>
    match cotMap.lookup e.dstWire with
    | none => ⟨cotMap, nextWire, revEdges⟩
    | some dOut =>
      let st : CotangentBuilderState := ⟨cotMap, nextWire, revEdges⟩
      match e.op with
      | .const _ => st
      | .add =>
        let w0 := wireAt e.srcWires 0
        let w1 := wireAt e.srcWires 1
        emitAndAccum w1 (.scale 1) [dOut]
          (emitAndAccum w0 (.scale 1) [dOut] st)
      | .sub =>
        let w0 := wireAt e.srcWires 0
        let w1 := wireAt e.srcWires 1
        emitAndAccum w1 (.scale (-1)) [dOut]
          (emitAndAccum w0 (.scale 1) [dOut] st)
      | .mul =>
        let w0 := wireAt e.srcWires 0
        let w1 := wireAt e.srcWires 1
        emitAndAccum w1 .mul [w0, dOut]
          (emitAndAccum w0 .mul [w1, dOut] st)
      | .scale k =>
        let w0 := wireAt e.srcWires 0
        emitAndAccum w0 (.scale k) [dOut] st
      | .mac =>
        let w0 := wireAt e.srcWires 0
        let w1 := wireAt e.srcWires 1
        let w2 := wireAt e.srcWires 2
        emitAndAccum w2 (.scale 1) [dOut]
          (emitAndAccum w1 .mul [w0, dOut]
            (emitAndAccum w0 .mul [w1, dOut] st))
      | .mux =>
        let c  := wireAt e.srcWires 0
        let w1 := wireAt e.srcWires 1
        let w2 := wireAt e.srcWires 2
        match emitRevEdge (.const 0) [] st with
        | (zWire, st1) =>
          emitAndAccum w2 .mux [c, zWire, dOut]
            (emitAndAccum w1 .mux [c, dOut, zWire] st1)

/-- Resolve the final cotangent wire for each open input wire $w \in \text{inWires}$, emitting a
`.const 0` wire if $w$ did not contribute to any output. -/
def resolveInputCotWires : List Nat → CotangentBuilderState → List Nat × CotangentBuilderState
  | [], st => ([], st)
  | w :: rest, ⟨cotMap, nextWire, revEdges⟩ =>
    match cotMap.lookup w with
    | some cw =>
      match resolveInputCotWires rest ⟨cotMap, nextWire, revEdges⟩ with
      | (restWires, st') => (cw :: restWires, st')
    | none =>
      let e0 : HyperEdge := { opIdx := 0, op := .const 0, srcWires := [], dstWire := nextWire }
      let st1 : CotangentBuilderState := ⟨setCotWire w nextWire cotMap, nextWire + 1, revEdges ++ [e0]⟩
      match resolveInputCotWires rest st1 with
      | (restWires, st2) => (nextWire :: restWires, st2)

/-- Linear-time recursive helper for `reindexHyperEdges`. -/
def reindexHyperEdgesAux : Nat → List HyperEdge → List HyperEdge
  | _, [] => []
  | idx, ⟨_, op, srcWires, dstWire⟩ :: rest =>
    ⟨idx, op, srcWires, dstWire⟩ :: reindexHyperEdgesAux (idx + 1) rest

/-- Re-number the `opIdx` fields of a list of `HyperEdge`s sequentially `0, 1, 2, ...`. -/
def reindexHyperEdges (edges : List HyperEdge) : List HyperEdge :=
  reindexHyperEdgesAux 0 edges

/-- Seed the initial `CotangentBuilderState` with output cotangent wires `seedWire, seedWire + 1, ...`. -/
def seedCotangentStateAux : Nat → List Nat → CotangentBuilderState → CotangentBuilderState
  | _, [], st => st
  | seedWire, wOut :: rest, st =>
    seedCotangentStateAux (seedWire + 1) rest (accumWireCotangent wOut seedWire st)

/-- Generate `count` consecutive wire indices starting at `startWire`. -/
def makeSeedWires : Nat → Nat → List Nat
  | _, 0 => []
  | startWire, k + 1 => startWire :: makeSeedWires (startWire + 1) k

/-- Build `(allOutWires, finalNextWire, rawAllEdges)` for `compileGraphAdjointAux`. -/
def buildGraphAdjointState
    (numPrimal : Nat) (inWires outWires : List Nat) (fwdEdges : List HyperEdge) :
    List Nat × Nat × List HyperEdge :=
  let numOuts := outWires.length
  let initSt : CotangentBuilderState :=
    seedCotangentStateAux numPrimal outWires
      { cotMap := [], nextWire := numPrimal + numOuts, revEdges := [] }
  let afterPullback :=
    fwdEdges.reverse.foldl (fun st e => pullbackHyperEdge e st) initSt
  match resolveInputCotWires inWires afterPullback with
  | (inCotWires, ⟨_, finalNextWire, finalRevEdges⟩) =>
    (outWires ++ inCotWires, finalNextWire, fwdEdges ++ finalRevEdges)

/-- Auxiliary builder for `compileGraphAdjoint` operating on unpacked boundary tables and forward edges. -/
def compileGraphAdjointAux
    (numPrimal : Nat) (inWires outWires : List Nat) (fwdEdges : List HyperEdge) :
    StrictOpenHypergraph :=
  let state := buildGraphAdjointState numPrimal inWires outWires fwdEdges
  let seedWires := makeSeedWires numPrimal outWires.length
  mkStrictOpenHypergraph
    state.2.1
    (inWires ++ seedWires)
    state.1
    (reindexHyperEdges state.2.2)

/-- **Whole-Graph Functorial Reverse-AD (`compileGraphAdjoint`)**:
Takes an arbitrary multi-edge `StrictOpenHypergraph` `g` and constructs the joint forward+backward
`StrictOpenHypergraph`:
1. Preserves all forward primal wires `0 .. |W|-1` and forward hyperedges `extractHyperEdges g`,
2. Allocates upstream output cotangent seed wires `|W| .. |W| + |O| - 1` (appended to `boundaryIn`),
3. Traverses `(extractHyperEdges g).reverse` in reverse topological order, emitting cotangent pullback
   hyperedges and accumulating fanout cotangents with `.add` whenever a primal wire feeds multiple
   downstream consumers,
4. Exposes `g.boundaryOut ++ inCotWires` as `boundaryOut` (the primal outputs followed by the exact
   input gradients $\partial L / \partial x_i$). -/
def compileGraphAdjoint (g : StrictOpenHypergraph) : StrictOpenHypergraph :=
  compileGraphAdjointAux g.nodeTypes.length g.boundaryIn.table g.boundaryOut.table (extractHyperEdges g)

/-- Emit the forward `HyperEdge`s for an `OpticOp` reading from `(in0, in1)` and writing its primal
output to `outWire` (using `scratchWire` if an internal intermediate wire is needed). -/
def opticFwdHyperEdges (op : OpticOp) (in0 in1 outWire scratchWire : Nat) : List HyperEdge :=
  match op with
  | .add =>
    [{ opIdx := 0, op := .add, srcWires := [in0, in1], dstWire := outWire }]
  | .sub =>
    [{ opIdx := 0, op := .sub, srcWires := [in0, in1], dstWire := outWire }]
  | .mul =>
    [{ opIdx := 0, op := .mul, srcWires := [in0, in1], dstWire := outWire }]
  | .scale k =>
    [{ opIdx := 0, op := .scale k, srcWires := [in0], dstWire := outWire }]
  | .square =>
    [{ opIdx := 0, op := .mul, srcWires := [in0, in0], dstWire := outWire }]
  | .linearMac w =>
    [ { opIdx := 0, op := .scale w, srcWires := [in0],          dstWire := scratchWire }
    , { opIdx := 1, op := .add,     srcWires := [scratchWire, in1], dstWire := outWire } ]
  | .bilinear c =>
    [ { opIdx := 0, op := .mul,     srcWires := [in0, in1],     dstWire := scratchWire }
    , { opIdx := 1, op := .scale c, srcWires := [scratchWire],  dstWire := outWire } ]

/-- Construct the multi-edge forward `StrictOpenHypergraph` for the 2-stage composition
$L(x, y) = \text{op}_2(\text{op}_1(x, y), y)$ where:
* Wire `0`: boundary input $x$,
* Wire `1`: boundary input $y$ (which fans out to BOTH stage 1 and stage 2!),
* Wire `2`: stage-1 primal output $u = \text{op}_1(x, y)$ (using scratch wire `4` if needed),
* Wire `3`: stage-2 primal output $z = \text{op}_2(u, y)$ (using scratch wire `5` if needed). -/
def compileOpticChain2FwdHypergraph (op1 op2 : OpticOp) : StrictOpenHypergraph :=
  let edges1 := opticFwdHyperEdges op1 0 1 2 4
  let edges2 := opticFwdHyperEdges op2 2 1 3 5
  mkStrictOpenHypergraph 6 [0, 1] [3] (reindexHyperEdges (edges1 ++ edges2))

/-- Initial wire environment for `compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2)`
binding wire `0 ↦ x`, wire `1 ↦ y`, and the output cotangent seed wire `6 ↦ dOut`. -/
def opticChain2AdjointInitEnv (x y dOut : Int) (w : Nat) : Int :=
  match w with
  | 0 => x
  | 1 => y
  | 6 => dOut
  | _ => 0

theorem extractHyperEdgesAux_reindexHyperEdgesAux
    (idx : Nat) (edges : List HyperEdge) :
    extractHyperEdgesAux idx
      ((reindexHyperEdgesAux idx edges).map (·.op))
      (((reindexHyperEdgesAux idx edges).map (·.srcWires)).map List.length)
      (((reindexHyperEdgesAux idx edges).map (·.srcWires)).flatten)
      (((reindexHyperEdgesAux idx edges).map (fun e => [e.dstWire])).flatten) =
      reindexHyperEdgesAux idx edges := by
  induction edges generalizing idx with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨_, op, srcWires, dstWire⟩
    simp only [reindexHyperEdgesAux, List.map_cons, List.flatten_cons, List.cons_append,
      List.nil_append, extractHyperEdgesAux, List.take_left, List.drop_left, ih (idx + 1)]

@[simp] theorem extractHyperEdges_mkStrictOpenHypergraph
    (numWires : Nat) (inWires outWires : List Nat) (edges : List HyperEdge) :
    extractHyperEdges (mkStrictOpenHypergraph numWires inWires outWires (reindexHyperEdges edges)) =
      reindexHyperEdges edges :=
  extractHyperEdgesAux_reindexHyperEdgesAux 0 edges

theorem evalHyperEdgesComb_reindexHyperEdgesAux
    (idx : Nat) (edges : List HyperEdge) (initEnv : Nat → Int) :
    evalHyperEdgesComb initEnv (reindexHyperEdgesAux idx edges) =
      evalHyperEdgesComb initEnv edges := by
  induction edges generalizing idx initEnv with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨_, op, srcWires, dstWire⟩
    dsimp only [reindexHyperEdgesAux, evalHyperEdgesComb, List.foldl_cons, stepHyperEdge]
    exact ih (idx + 1) _

@[simp] theorem evalHyperEdgesComb_reindexHyperEdges
    (initEnv : Nat → Int) (edges : List HyperEdge) :
    evalHyperEdgesComb initEnv (reindexHyperEdges edges) =
      evalHyperEdgesComb initEnv edges :=
  evalHyperEdgesComb_reindexHyperEdgesAux 0 edges initEnv

theorem evalHypergraphComb_mkStrictOpenHypergraph_reindex
    (numWires : Nat) (inWires outWires : List Nat) (edges : List HyperEdge) (initEnv : Nat → Int) :
    evalHypergraphComb (mkStrictOpenHypergraph numWires inWires outWires (reindexHyperEdges edges)) initEnv =
      outWires.map (evalHyperEdgesComb initEnv edges) := by
  unfold evalHypergraphComb
  rw [extractHyperEdges_mkStrictOpenHypergraph, evalHyperEdgesComb_reindexHyperEdges]
  rfl

/-- Direct combinational evaluator for `buildGraphAdjointState` bypassing `IndexedCoproduct` roundtrips. -/
def evalBuildGraphAdjointComb
    (numPrimal : Nat) (inWires outWires : List Nat) (fwdEdges : List HyperEdge) (initEnv : Nat → Int) :
    List Int :=
  match buildGraphAdjointState numPrimal inWires outWires fwdEdges with
  | (allOuts, _, rawEdges) => allOuts.map (evalHyperEdgesComb initEnv rawEdges)

theorem evalHypergraphComb_compileGraphAdjointAux
    (numPrimal : Nat) (inWires outWires : List Nat) (fwdEdges : List HyperEdge) (initEnv : Nat → Int) :
    evalHypergraphComb (compileGraphAdjointAux numPrimal inWires outWires fwdEdges) initEnv =
      evalBuildGraphAdjointComb numPrimal inWires outWires fwdEdges initEnv := by
  unfold compileGraphAdjointAux evalBuildGraphAdjointComb
  rw [evalHypergraphComb_mkStrictOpenHypergraph_reindex]

theorem compileGraphAdjoint_chain2_eq (op1 op2 : OpticOp) :
    compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2) =
      compileGraphAdjointAux 6 [0, 1] [3]
        (reindexHyperEdges (opticFwdHyperEdges op1 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5)) := by
  unfold compileGraphAdjoint compileOpticChain2FwdHypergraph
  change compileGraphAdjointAux (List.replicate 6 64).length [0, 1] [3]
    (extractHyperEdges (mkStrictOpenHypergraph 6 [0, 1] [3]
      (reindexHyperEdges (opticFwdHyperEdges op1 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5)))) = _
  rw [List.length_replicate, extractHyperEdges_mkStrictOpenHypergraph]

@[simp] theorem list_getD_zero_cons {α : Type} (x : α) (xs : List α) (d : α) :
    (x :: xs).getD 0 d = x := rfl

@[simp] theorem list_getD_one_cons {α : Type} (x y : α) (xs : List α) (d : α) :
    (x :: y :: xs).getD 1 d = y := rfl

@[simp] theorem list_getD_two_cons {α : Type} (x y z : α) (xs : List α) (d : α) :
    (x :: y :: z :: xs).getD 2 d = z := rfl

@[simp] theorem list_getD_nil {α : Type} (i : Nat) (d : α) :
    ([] : List α).getD i d = d := rfl

set_option maxHeartbeats 1600000 in
theorem compileGraphAdjoint_chain2_comb (op1 op2 : OpticOp) (x y dOut : Int) :
    evalHypergraphComb (compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2))
      (opticChain2AdjointInitEnv x y dOut) =
    [ (evalOpticChain2Fwd op1 op2 x y).1
    , (evalOpticChain2Rev (compileOpticAdjoint op1) (compileOpticAdjoint op2)
        (evalOpticChain2Fwd op1 op2 x y).2 dOut).1
    , (evalOpticChain2Rev (compileOpticAdjoint op1) (compileOpticAdjoint op2)
        (evalOpticChain2Fwd op1 op2 x y).2 dOut).2 ] := by
  rw [compileGraphAdjoint_chain2_eq, evalHypergraphComb_compileGraphAdjointAux]
  cases op1 <;> cases op2 <;>
    dsimp [evalBuildGraphAdjointComb, buildGraphAdjointState,
      opticFwdHyperEdges, reindexHyperEdges, reindexHyperEdgesAux,
      seedCotangentStateAux, accumWireCotangent, emitAndAccum, upsertCotWire,
      pullbackHyperEdge, wireAt, emitRevEdge, resolveInputCotWires, setCotWire,
      evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp, opticChain2AdjointInitEnv,
      evalOpticChain2Fwd, evalOpticChain2Rev, evalOpticFwd, evalOpticRev, compileOpticAdjoint,
      List.reverse, List.reverseAux, List.foldl, List.map, List.lookup,
      list_getD_zero_cons, list_getD_one_cons, list_getD_two_cons, list_getD_nil] <;>
    grind

set_option maxHeartbeats 1600000 in
/-- **Theorem (`compileGraphAdjoint_multiEdge_sound`)**:
1. **Universal 2-Stage Composed Multi-Edge Functorial AD Soundness**:
   For EVERY pair of operations `op1 op2 : OpticOp` and EVERY `(x, y, dOut : Int)`:
   - The whole-graph adjoint `compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2)` is
     structurally well-formed (`wf = true`),
   - Evaluating `compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2)` via combinational
     evaluation (`evalHypergraphComb`), sequential wavefront evaluation (`evalHypergraphLayered`),
     or true synchronous snapshot wavefront evaluation (`evalHypergraphLayeredSync`) produces the
     exact 3-output vector `[z, dx, dy]` matching `evalOpticChain2Fwd` and `evalOpticChain2Rev`
     (including automatic `.add` fanout cotangent accumulation on wire `1` across stages and within `.square`!),
   - At unit output seed `dOut = 1`, `evalHypergraphComb` computes the exact analytical partial
     derivatives $\left(L(x,y),\; \frac{\partial L}{\partial x},\; \frac{\partial L}{\partial y}\right)$
     matching forward-mode dual numbers `DualInt`!
2. **Whole-Graph Adjoint of the 5-Edge `goldenDiamondHypergraph`**:
   Compiling the 5-edge 4-input diamond hypergraph $f(x_0, x_1, x_2, x_3) = (x_0 + x_1)(x_2 + x_3) + 10$
   through `compileGraphAdjoint` produces a well-formed 21-wire, 14-edge hypergraph whose evaluation
   at $(3, 4, 5, 6)$ with `dOut = 1` returns `[87, 11, 11, 7, 7]`
   ($f = 87$, $\partial f / \partial x_0 = \partial f / \partial x_1 = 5 + 6 = 11$,
   $\partial f / \partial x_2 = \partial f / \partial x_3 = 3 + 4 = 7$). -/
theorem compileGraphAdjoint_multiEdge_sound (op1 op2 : OpticOp) (x y dOut : Int) :
    let gFwd := compileOpticChain2FwdHypergraph op1 op2
    let gAdj := compileGraphAdjoint gFwd
    let env  := opticChain2AdjointInitEnv x y dOut
    let (z, res) := evalOpticChain2Fwd op1 op2 x y
    let (dx, dy) := evalOpticChain2Rev (compileOpticAdjoint op1) (compileOpticAdjoint op2) res dOut
    let envUnit := opticChain2AdjointInitEnv x y 1
    let dualX := evalOpticDual op2 (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩) ⟨y, 0⟩
    let dualY := evalOpticDual op2 (evalOpticDual op1 ⟨x, 0⟩ ⟨y, 1⟩) ⟨y, 1⟩
    let diamondAdj := compileGraphAdjoint goldenDiamondHypergraph
    let diamondEnv : Nat → Int := fun w =>
      match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 9 => 1 | _ => 0
    gAdj.wf = true ∧
    evalHypergraphComb gAdj env = [z, dx, dy] ∧
    evalHypergraphLayered gAdj env = [z, dx, dy] ∧
    evalHypergraphLayeredSync gAdj env = [z, dx, dy] ∧
    evalHypergraphComb gAdj envUnit = [dualX.primal, dualX.tangent, dualY.tangent] ∧
    diamondAdj.wf = true ∧
    evalHypergraphComb diamondAdj diamondEnv = [87, 11, 11, 7, 7] := by
  have hWf : (compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2)).wf = true := by
    rw [compileGraphAdjoint_chain2_eq]
    cases op1 <;> cases op2 <;>
      dsimp [compileGraphAdjointAux, buildGraphAdjointState,
        opticFwdHyperEdges, reindexHyperEdges, reindexHyperEdgesAux,
        seedCotangentStateAux, makeSeedWires, accumWireCotangent, emitAndAccum, upsertCotWire,
        pullbackHyperEdge, wireAt, emitRevEdge, resolveInputCotWires, setCotWire,
        mkStrictOpenHypergraph, StrictOpenHypergraph.wf, IndexedCoproduct.wf,
        IndexedCoproduct.fromSegments, FiniteFunction.wf, sumNatList,
        List.reverse, List.reverseAux, List.foldl, List.map, List.lookup,
        List.flatten, List.all, List.replicate, List.length] <;>
      rfl
  have hComb := compileGraphAdjoint_chain2_comb op1 op2 x y dOut
  have hPipe := evalHypergraph_pipelined_eq_comb
    (compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2))
    (opticChain2AdjointInitEnv x y dOut)
  have hCombUnit :
      evalHypergraphComb (compileGraphAdjoint (compileOpticChain2FwdHypergraph op1 op2))
        (opticChain2AdjointInitEnv x y 1) =
      [ (evalOpticDual op2 (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩) ⟨y, 0⟩).primal
      , (evalOpticDual op2 (evalOpticDual op1 ⟨x, 1⟩ ⟨y, 0⟩) ⟨y, 0⟩).tangent
      , (evalOpticDual op2 (evalOpticDual op1 ⟨x, 0⟩ ⟨y, 1⟩) ⟨y, 1⟩).tangent ] := by
    rw [compileGraphAdjoint_chain2_comb op1 op2 x y 1]
    have hChain := optic_comp_chain_rule_sound op1 op2 x y
    dsimp only at hChain
    rw [hChain.1, hChain.2.1, hChain.2.2]
  have hDiamond :
      (compileGraphAdjoint goldenDiamondHypergraph).wf = true ∧
      evalHypergraphComb (compileGraphAdjoint goldenDiamondHypergraph)
        (fun w => match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 9 => 1 | _ => 0) =
        [87, 11, 11, 7, 7] := by
    decide +kernel
  dsimp only
  refine ⟨hWf, hComb, ?_, ?_, hCombUnit, hDiamond.1, hDiamond.2⟩
  · rw [hPipe.1, hComb]
  · rw [hPipe.2, hComb]

/-! ### 5.1 Universal Whole-DAG Reverse-Mode AD Pullback Specification & Soundness (`compileGraphAdjoint_dag_sound`) -/

/-- Mathematical local cotangent contributions `[(srcWire, deltaCot), ...]` for a single forward
`HyperEdge` `e` given the forward primal wire environment `fwdEnv : Nat → Int` and the downstream
cotangent `dOut : Int` on `e.dstWire`. -/
def specEdgeLocalPullback (fwdEnv : Nat → Int) (e : HyperEdge) (dOut : Int) : List (Nat × Int) :=
  match e.op with
  | .const _ => []
  | .add =>
    let w0 := wireAt e.srcWires 0
    let w1 := wireAt e.srcWires 1
    [(w0, 1 * dOut), (w1, 1 * dOut)]
  | .sub =>
    let w0 := wireAt e.srcWires 0
    let w1 := wireAt e.srcWires 1
    [(w0, 1 * dOut), (w1, (-1) * dOut)]
  | .mul =>
    let w0 := wireAt e.srcWires 0
    let w1 := wireAt e.srcWires 1
    [(w0, fwdEnv w1 * dOut), (w1, fwdEnv w0 * dOut)]
  | .scale k =>
    let w0 := wireAt e.srcWires 0
    [(w0, k * dOut)]
  | .mac =>
    let w0 := wireAt e.srcWires 0
    let w1 := wireAt e.srcWires 1
    let w2 := wireAt e.srcWires 2
    [(w0, fwdEnv w1 * dOut), (w1, fwdEnv w0 * dOut), (w2, 1 * dOut)]
  | .mux =>
    let c  := wireAt e.srcWires 0
    let w1 := wireAt e.srcWires 1
    let w2 := wireAt e.srcWires 2
    [ (w1, if fwdEnv c != 0 then dOut else 0)
    , (w2, if fwdEnv c != 0 then 0 else dOut) ]

/-- Accumulate a single `(targetWire, deltaCot)` contribution into a cotangent map `cot : Nat → Int`. -/
def addSpecCotangent (targetWire : Nat) (delta : Int) (cot : Nat → Int) (w : Nat) : Int :=
  if w == targetWire then cot w + delta else cot w

/-- Accumulate a list of `(wire, deltaCot)` contributions into a mathematical cotangent map `specCot : Nat → Int`. -/
def accumSpecCotangents (contribs : List (Nat × Int)) (specCot : Nat → Int) : Nat → Int :=
  contribs.foldl (fun cot (u, delta) => addSpecCotangent u delta cot) specCot

/-- Single-edge mathematical reverse-mode AD pullback step on `specCot : Nat → Int`. -/
def specGradEdgeStep (fwdEnv : Nat → Int) (e : HyperEdge) (specCot : Nat → Int) : Nat → Int :=
  accumSpecCotangents (specEdgeLocalPullback fwdEnv e (specCot e.dstWire)) specCot

/-- Left-to-right fold of `specGradEdgeStep` over an already-reversed forward edge list `revFwd`. -/
def specGradRevOrder (fwdEnv : Nat → Int) (revFwd : List HyperEdge) (initCot : Nat → Int) : Nat → Int :=
  revFwd.foldl (fun cot e => specGradEdgeStep fwdEnv e cot) initCot

/-- Whole-DAG mathematical reverse-mode AD pullback specification (`specGradEdges`):
folds `specGradEdgeStep` right-to-left over `edges : List HyperEdge` (i.e. left-to-right over `edges.reverse`). -/
def specGradEdges (fwdEnv : Nat → Int) (edges : List HyperEdge) (initCot : Nat → Int) : Nat → Int :=
  specGradRevOrder fwdEnv edges.reverse initCot

@[simp] theorem addSpecCotangent_zero (targetWire : Nat) (cot : Nat → Int) :
    addSpecCotangent targetWire 0 cot = cot := by
  funext w
  unfold addSpecCotangent
  split <;> omega

theorem accumSpecCotangents_localPullback_zero
    (fwdEnv : Nat → Int) (e : HyperEdge) (specCot : Nat → Int) :
    accumSpecCotangents (specEdgeLocalPullback fwdEnv e 0) specCot = specCot := by
  cases hOp : e.op <;>
    simp [specEdgeLocalPullback, hOp, accumSpecCotangents, addSpecCotangent_zero]

/-- A forward `HyperEdge` `e` has all source wire lookups within the primal wire range `0 .. numPrimal - 1`. -/
def EdgeSrcBounded (numPrimal : Nat) (e : HyperEdge) : Prop :=
  ∀ i, wireAt e.srcWires i < numPrimal

/-- Representation invariant relating `st : CotangentBuilderState` to the forward primal wire
environment `fwdEnv : Nat → Int` and the mathematical cotangent specification `specCot : Nat → Int`:
1. `numPrimal ≤ st.nextWire`,
2. Every primal wire `u < numPrimal` retains its forward value: `evalHyperEdgesComb fwdEnv st.revEdges u = fwdEnv u`,
3. Every wire `w` with `st.cotMap.lookup w = none` has `specCot w = 0`,
4. Every wire `w` with `st.cotMap.lookup w = some cw` has `cw < st.nextWire` and
   `evalHyperEdgesComb fwdEnv st.revEdges cw = specCot w`. -/
structure CotStateInvariant
    (numPrimal : Nat) (fwdEnv : Nat → Int) (specCot : Nat → Int) (st : CotangentBuilderState) : Prop where
  primal_le_next : numPrimal ≤ st.nextWire
  primal_preserved : ∀ u, u < numPrimal → evalHyperEdgesComb fwdEnv st.revEdges u = fwdEnv u
  lookup_none : ∀ w, st.cotMap.lookup w = none → specCot w = 0
  lookup_some : ∀ w cw, st.cotMap.lookup w = some cw →
    cw < st.nextWire ∧ evalHyperEdgesComb fwdEnv st.revEdges cw = specCot w

theorem evalHyperEdgesComb_append (initEnv : Nat → Int) (es1 es2 : List HyperEdge) :
    evalHyperEdgesComb initEnv (es1 ++ es2) =
      evalHyperEdgesComb (evalHyperEdgesComb initEnv es1) es2 := by
  unfold evalHyperEdgesComb
  exact List.foldl_append

@[simp] theorem evalHyperEdgesComb_nil (initEnv : Nat → Int) :
    evalHyperEdgesComb initEnv [] = initEnv := rfl

@[simp] theorem evalHyperEdgesComb_cons (initEnv : Nat → Int) (e : HyperEdge) (rest : List HyperEdge) :
    evalHyperEdgesComb initEnv (e :: rest) = evalHyperEdgesComb (stepHyperEdge initEnv e) rest := rfl

theorem stepHyperEdge_eq_self (env : Nat → Int) (e : HyperEdge) :
    stepHyperEdge env e e.dstWire = evalHypergraphOp e.op (e.srcWires.map env) := by
  simp [stepHyperEdge]

theorem stepHyperEdge_ne (env : Nat → Int) (e : HyperEdge) (u : Nat) (hne : u ≠ e.dstWire) :
    stepHyperEdge env e u = env u := by
  unfold stepHyperEdge
  have hbeq : (u == e.dstWire) = false := beq_false_of_ne hne
  simp [hbeq]

theorem upsertCotWire_fst (w deltaWire sumWire : Nat) (cotMap : List (Nat × Nat)) :
    (upsertCotWire w deltaWire sumWire cotMap).1 = cotMap.lookup w := by
  induction cotMap with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [upsertCotWire, List.lookup]
    have hcomm : (k == w) = (w == k) := by grind
    rw [hcomm]
    cases (w == k) <;> simp [ih]

theorem upsertCotWire_snd_lookup_self (w deltaWire sumWire : Nat) (cotMap : List (Nat × Nat)) :
    ((upsertCotWire w deltaWire sumWire cotMap).2).lookup w =
      match cotMap.lookup w with
      | none => some deltaWire
      | some _ => some sumWire := by
  induction cotMap with
  | nil =>
    simp [upsertCotWire, List.lookup]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [upsertCotWire, List.lookup]
    have hcomm : (k == w) = (w == k) := by grind
    rw [hcomm]
    cases hwk : (w == k)
    · simp [List.lookup, hwk, ih]
    · simp [List.lookup]

theorem upsertCotWire_snd_lookup_ne (w u deltaWire sumWire : Nat) (cotMap : List (Nat × Nat))
    (hne : (u == w) = false) :
    ((upsertCotWire w deltaWire sumWire cotMap).2).lookup u = cotMap.lookup u := by
  induction cotMap with
  | nil =>
    simp [upsertCotWire, List.lookup, hne]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [upsertCotWire, List.lookup]
    cases hkw : (k == w)
    · simp [List.lookup, ih]
    · have huk : (u == k) = false := by grind
      simp [List.lookup, hne, huk]

theorem setCotWire_lookup_self (w cw : Nat) (cotMap : List (Nat × Nat)) :
    (setCotWire w cw cotMap).lookup w = some cw := by
  induction cotMap with
  | nil => simp [setCotWire]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [setCotWire]
    have hcomm : (k == w) = (w == k) := by grind
    rw [hcomm]
    cases hwk : (w == k) <;> simp [List.lookup, hwk, ih]

theorem setCotWire_lookup_ne (w u cw : Nat) (cotMap : List (Nat × Nat))
    (hne : (u == w) = false) :
    (setCotWire w cw cotMap).lookup u = cotMap.lookup u := by
  induction cotMap with
  | nil => simp [setCotWire, List.lookup, hne]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [setCotWire, List.lookup]
    cases hkw : (k == w)
    · simp [List.lookup, ih]
    · have huk : (u == k) = false := by grind
      simp [List.lookup, hne, huk]

theorem emitAndAccum_cotMap
    (w : Nat) (op : HypergraphOp) (srcWires : List Nat) (st : CotangentBuilderState) :
    (emitAndAccum w op srcWires st).cotMap =
      (upsertCotWire w st.nextWire (st.nextWire + 1) st.cotMap).2 := by
  rcases st with ⟨cotMap, nextWire, revEdges⟩
  unfold emitAndAccum
  cases hUp : upsertCotWire w nextWire (nextWire + 1) cotMap with
  | mk opt cotMap' =>
    cases opt <;> simp [hUp]

theorem emitAndAccum_nextWire_le
    (w : Nat) (op : HypergraphOp) (srcWires : List Nat) (st : CotangentBuilderState) :
    st.nextWire ≤ (emitAndAccum w op srcWires st).nextWire := by
  rcases st with ⟨cotMap, nextWire, revEdges⟩
  unfold emitAndAccum
  cases hUp : upsertCotWire w nextWire (nextWire + 1) cotMap with
  | mk opt cotMap' =>
    cases opt <;> simp [hUp] <;> omega

theorem emitAndAccum_preserves_below_nextWire
    (fwdEnv : Nat → Int) (w : Nat) (op : HypergraphOp) (srcWires : List Nat)
    (st : CotangentBuilderState) (u : Nat) (hu : u < st.nextWire) :
    evalHyperEdgesComb fwdEnv (emitAndAccum w op srcWires st).revEdges u =
      evalHyperEdgesComb fwdEnv st.revEdges u := by
  rcases st with ⟨cotMap, nextWire, revEdges⟩
  dsimp at hu
  unfold emitAndAccum
  cases hUp : upsertCotWire w nextWire (nextWire + 1) cotMap with
  | mk opt cotMap' =>
    cases opt with
    | none =>
      simp only [hUp, evalHyperEdgesComb_append, evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
      exact stepHyperEdge_ne _ _ u (by dsimp; omega)
    | some prevWire =>
      simp only [hUp, evalHyperEdgesComb_append, evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
      rw [stepHyperEdge_ne _ _ u (by dsimp; omega), stepHyperEdge_ne _ _ u (by dsimp; omega)]

/-- **Lemma (`emitAndAccum_preserves_invariant`)**:
Emitting a local cotangent edge `(op, srcWires)` and accumulating its output into primal wire `w`
preserves `CotStateInvariant` while updating the mathematical cotangent map by
`addSpecCotangent w (evalHypergraphOp op (srcWires.map curEnv)) specCot`. -/
theorem emitAndAccum_preserves_invariant
    (numPrimal : Nat) (fwdEnv : Nat → Int) (specCot : Nat → Int)
    (w : Nat) (op : HypergraphOp) (srcWires : List Nat) (st : CotangentBuilderState)
    (hInv : CotStateInvariant numPrimal fwdEnv specCot st) :
    let curEnv := evalHyperEdgesComb fwdEnv st.revEdges
    let delta  := evalHypergraphOp op (srcWires.map curEnv)
    CotStateInvariant numPrimal fwdEnv (addSpecCotangent w delta specCot) (emitAndAccum w op srcWires st) := by
  intro curEnv delta
  have hNextLe := emitAndAccum_nextWire_le w op srcWires st
  have hBelow := emitAndAccum_preserves_below_nextWire fwdEnv w op srcWires st
  refine
    { primal_le_next := Nat.le_trans hInv.primal_le_next hNextLe
    , primal_preserved := fun u hu => by
        rw [hBelow u (Nat.lt_of_lt_of_le hu hInv.primal_le_next)]
        exact hInv.primal_preserved u hu
    , lookup_none := ?_
    , lookup_some := ?_ }
  · intro u hNone
    rw [emitAndAccum_cotMap] at hNone
    cases huw : (u == w)
    · rw [upsertCotWire_snd_lookup_ne w u st.nextWire (st.nextWire + 1) st.cotMap huw] at hNone
      unfold addSpecCotangent
      simp [huw, hInv.lookup_none u hNone]
    · have huEq : u = w := LawfulBEq.eq_of_beq huw
      subst huEq
      rw [upsertCotWire_snd_lookup_self] at hNone
      cases hLook : st.cotMap.lookup u <;> rw [hLook] at hNone <;> contradiction
  · intro u cw hSome
    cases huw : (u == w)
    · rw [emitAndAccum_cotMap, upsertCotWire_snd_lookup_ne w u st.nextWire (st.nextWire + 1) st.cotMap huw] at hSome
      obtain ⟨hcwLt, hcwVal⟩ := hInv.lookup_some u cw hSome
      refine ⟨Nat.lt_of_lt_of_le hcwLt hNextLe, ?_⟩
      rw [hBelow cw hcwLt, hcwVal]
      unfold addSpecCotangent
      simp [huw]
    · have huEq : u = w := LawfulBEq.eq_of_beq huw
      subst huEq
      rcases st with ⟨cotMap, nextWire, revEdges⟩
      unfold emitAndAccum at hSome ⊢
      cases hUp : upsertCotWire u nextWire (nextWire + 1) cotMap with
      | mk opt cotMap' =>
        cases opt with
        | none =>
          have hFst : (upsertCotWire u nextWire (nextWire + 1) cotMap).1 = none :=
            congrArg Prod.fst hUp
          rw [upsertCotWire_fst] at hFst
          have hSnd : (upsertCotWire u nextWire (nextWire + 1) cotMap).2 = cotMap' :=
            congrArg Prod.snd hUp
          simp only [hUp] at hSome ⊢
          rw [← hSnd, upsertCotWire_snd_lookup_self, hFst] at hSome
          injection hSome with hcwEq
          subst hcwEq
          have hSpec0 : specCot u = 0 := hInv.lookup_none u hFst
          refine ⟨by omega, ?_⟩
          rw [evalHyperEdgesComb_append]
          simp only [evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
          change stepHyperEdge curEnv { opIdx := 0, op := op, srcWires := srcWires, dstWire := nextWire } nextWire =
            addSpecCotangent u delta specCot u
          rw [stepHyperEdge_eq_self]
          unfold addSpecCotangent
          simp [hSpec0, delta]
        | some prevWire =>
          have hFst : (upsertCotWire u nextWire (nextWire + 1) cotMap).1 = some prevWire :=
            congrArg Prod.fst hUp
          rw [upsertCotWire_fst] at hFst
          have hSnd : (upsertCotWire u nextWire (nextWire + 1) cotMap).2 = cotMap' :=
            congrArg Prod.snd hUp
          simp only [hUp] at hSome ⊢
          rw [← hSnd, upsertCotWire_snd_lookup_self, hFst] at hSome
          injection hSome with hcwEq
          subst hcwEq
          obtain ⟨hPrevLt, hPrevVal⟩ := hInv.lookup_some u prevWire hFst
          dsimp at hPrevLt hPrevVal
          refine ⟨by omega, ?_⟩
          rw [evalHyperEdgesComb_append]
          simp only [evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
          let e1 : HyperEdge := { opIdx := 0, op := op, srcWires := srcWires, dstWire := nextWire }
          let e2 : HyperEdge := { opIdx := 0, op := .add, srcWires := [prevWire, nextWire], dstWire := nextWire + 1 }
          change stepHyperEdge (stepHyperEdge curEnv e1) e2 (nextWire + 1) = addSpecCotangent u delta specCot u
          rw [stepHyperEdge_eq_self]
          have hPrevAfterE1 : stepHyperEdge curEnv e1 prevWire = specCot u := by
            rw [stepHyperEdge_ne curEnv e1 prevWire (by dsimp [e1]; omega)]
            exact hPrevVal
          have hNextAfterE1 : stepHyperEdge curEnv e1 nextWire = delta :=
            stepHyperEdge_eq_self curEnv e1
          unfold addSpecCotangent
          simp [e2, evalHypergraphOp, hPrevAfterE1, hNextAfterE1]

theorem emitRevEdge_const_zero_sound
    (numPrimal : Nat) (fwdEnv : Nat → Int) (specCot : Nat → Int) (st : CotangentBuilderState)
    (hInv : CotStateInvariant numPrimal fwdEnv specCot st) :
    let res := emitRevEdge (.const 0) [] st
    CotStateInvariant numPrimal fwdEnv specCot res.2 ∧
    st.nextWire < res.2.nextWire ∧
    res.1 = st.nextWire ∧
    evalHyperEdgesComb fwdEnv res.2.revEdges res.1 = 0 ∧
    (∀ u, u < st.nextWire → evalHyperEdgesComb fwdEnv res.2.revEdges u = evalHyperEdgesComb fwdEnv st.revEdges u) := by
  rcases st with ⟨cotMap, nextWire, revEdges⟩
  dsimp [emitRevEdge]
  have hBelow :
      ∀ u, u < nextWire →
        evalHyperEdgesComb fwdEnv (revEdges ++ [{ opIdx := 0, op := .const 0, srcWires := [], dstWire := nextWire }]) u =
          evalHyperEdgesComb fwdEnv revEdges u := by
    intro u hu
    rw [evalHyperEdgesComb_append]
    simp only [evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
    exact stepHyperEdge_ne _ _ u (by dsimp; omega)
  refine ⟨?_, by omega, rfl, ?_, hBelow⟩
  · refine
      { primal_le_next := by
          have := hInv.primal_le_next
          dsimp at this ⊢
          omega
      , primal_preserved := fun u hu => by
          have hPrimalLe := hInv.primal_le_next
          dsimp at hPrimalLe
          rw [hBelow u (Nat.lt_of_lt_of_le hu hPrimalLe)]
          exact hInv.primal_preserved u hu
      , lookup_none := hInv.lookup_none
      , lookup_some := fun w cw hSome => by
          obtain ⟨hcwLt, hcwVal⟩ := hInv.lookup_some w cw hSome
          dsimp at hcwLt hcwVal
          refine ⟨by dsimp; omega, ?_⟩
          rw [hBelow cw hcwLt, hcwVal] }
  · rw [evalHyperEdgesComb_append]
    simp only [evalHyperEdgesComb_cons, evalHyperEdgesComb_nil, stepHyperEdge, evalHypergraphOp, beq_self_eq_true, ↓reduceIte]

/-- **Theorem (`pullbackHyperEdge_sound`)**:
For every forward `e : HyperEdge` with `EdgeSrcBounded numPrimal e` (covering all 7 `HypergraphOp`
constructors: `.const`, `.add`, `.sub`, `.mul`, `.scale`, `.mac`, `.mux`), executing
`pullbackHyperEdge e st` from a state satisfying `CotStateInvariant numPrimal fwdEnv specCot st`
produces a state satisfying `CotStateInvariant numPrimal fwdEnv (specGradEdgeStep fwdEnv e specCot) (pullbackHyperEdge e st)`. -/
theorem pullbackHyperEdge_sound
    (numPrimal : Nat) (fwdEnv : Nat → Int) (specCot : Nat → Int)
    (e : HyperEdge) (st : CotangentBuilderState)
    (hEdge : EdgeSrcBounded numPrimal e)
    (hInv : CotStateInvariant numPrimal fwdEnv specCot st) :
    CotStateInvariant numPrimal fwdEnv (specGradEdgeStep fwdEnv e specCot) (pullbackHyperEdge e st) ∧
    st.nextWire ≤ (pullbackHyperEdge e st).nextWire ∧
    (∀ u, u < st.nextWire →
      evalHyperEdgesComb fwdEnv (pullbackHyperEdge e st).revEdges u =
        evalHyperEdgesComb fwdEnv st.revEdges u) := by
  rcases st with ⟨cotMap, nextWire, revEdges⟩
  rcases e with ⟨opIdx, op, srcWires, dstWire⟩
  let st0 : CotangentBuilderState := ⟨cotMap, nextWire, revEdges⟩
  let e0 : HyperEdge := ⟨opIdx, op, srcWires, dstWire⟩
  unfold pullbackHyperEdge
  cases hLook : cotMap.lookup dstWire with
  | none =>
    simp only [hLook]
    have hSpec0 : specCot dstWire = 0 := hInv.lookup_none dstWire hLook
    have hStepEq : specGradEdgeStep fwdEnv e0 specCot = specCot := by
      unfold specGradEdgeStep
      change accumSpecCotangents (specEdgeLocalPullback fwdEnv e0 (specCot dstWire)) specCot = specCot
      rw [hSpec0, accumSpecCotangents_localPullback_zero]
    rw [hStepEq]
    exact ⟨hInv, Nat.le_refl _, fun _ _ => trivial⟩
  | some dOut =>
    simp only [hLook]
    obtain ⟨hdOutLt, hdOutVal⟩ := hInv.lookup_some dstWire dOut hLook
    dsimp at hdOutLt hdOutVal
    have hwLt : ∀ i, wireAt srcWires i < st0.nextWire := fun i =>
      Nat.lt_of_lt_of_le (hEdge i) hInv.primal_le_next
    have hwVal : ∀ i, evalHyperEdgesComb fwdEnv st0.revEdges (wireAt srcWires i) = fwdEnv (wireAt srcWires i) :=
      fun i => hInv.primal_preserved (wireAt srcWires i) (hEdge i)
    cases op with
    | const v =>
      simp only
      have hStepEq : specGradEdgeStep fwdEnv ⟨opIdx, .const v, srcWires, dstWire⟩ specCot = specCot := by
        simp [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents]
      rw [hStepEq]
      exact ⟨hInv, Nat.le_refl _, fun _ _ => trivial⟩
    | scale k =>
      simp only
      let w0 := wireAt srcWires 0
      have hInv1 := emitAndAccum_preserves_invariant numPrimal fwdEnv specCot w0 (.scale k) [dOut] st0 hInv
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons] at hInv1
      rw [hdOutVal] at hInv1
      have hStepEq :
          specGradEdgeStep fwdEnv ⟨opIdx, .scale k, srcWires, dstWire⟩ specCot =
            addSpecCotangent w0 (k * specCot dstWire) specCot := by
        simp [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, w0]
      rw [hStepEq]
      exact ⟨hInv1, emitAndAccum_nextWire_le w0 (.scale k) [dOut] st0,
        emitAndAccum_preserves_below_nextWire fwdEnv w0 (.scale k) [dOut] st0⟩
    | add =>
      simp only
      let w0 := wireAt srcWires 0
      let w1 := wireAt srcWires 1
      let st1 := emitAndAccum w0 (.scale 1) [dOut] st0
      have hInv1 := emitAndAccum_preserves_invariant numPrimal fwdEnv specCot w0 (.scale 1) [dOut] st0 hInv
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons] at hInv1
      rw [hdOutVal] at hInv1
      have hNext1 := emitAndAccum_nextWire_le w0 (.scale 1) [dOut] st0
      have hBelow1 := emitAndAccum_preserves_below_nextWire fwdEnv w0 (.scale 1) [dOut] st0
      have hdOutVal1 : evalHyperEdgesComb fwdEnv st1.revEdges dOut = specCot dstWire := by
        rw [hBelow1 dOut hdOutLt, hdOutVal]
      have hInv2 := emitAndAccum_preserves_invariant numPrimal fwdEnv
        (addSpecCotangent w0 (1 * specCot dstWire) specCot) w1 (.scale 1) [dOut] st1 hInv1
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons] at hInv2
      rw [hdOutVal1] at hInv2
      have hNext2 := emitAndAccum_nextWire_le w1 (.scale 1) [dOut] st1
      have hBelow2 := emitAndAccum_preserves_below_nextWire fwdEnv w1 (.scale 1) [dOut] st1
      have hStepEq :
          specGradEdgeStep fwdEnv ⟨opIdx, .add, srcWires, dstWire⟩ specCot =
            addSpecCotangent w1 (1 * specCot dstWire)
              (addSpecCotangent w0 (1 * specCot dstWire) specCot) := by
        simp [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, w0, w1]
      rw [hStepEq]
      refine ⟨hInv2, Nat.le_trans hNext1 hNext2, fun u hu => ?_⟩
      change evalHyperEdgesComb fwdEnv (emitAndAccum w1 (.scale 1) [dOut] st1).revEdges u =
        evalHyperEdgesComb fwdEnv st0.revEdges u
      rw [hBelow2 u (Nat.lt_of_lt_of_le hu hNext1), hBelow1 u hu]
    | sub =>
      simp only
      let w0 := wireAt srcWires 0
      let w1 := wireAt srcWires 1
      let st1 := emitAndAccum w0 (.scale 1) [dOut] st0
      have hInv1 := emitAndAccum_preserves_invariant numPrimal fwdEnv specCot w0 (.scale 1) [dOut] st0 hInv
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons] at hInv1
      rw [hdOutVal] at hInv1
      have hNext1 := emitAndAccum_nextWire_le w0 (.scale 1) [dOut] st0
      have hBelow1 := emitAndAccum_preserves_below_nextWire fwdEnv w0 (.scale 1) [dOut] st0
      have hdOutVal1 : evalHyperEdgesComb fwdEnv st1.revEdges dOut = specCot dstWire := by
        rw [hBelow1 dOut hdOutLt, hdOutVal]
      have hInv2 := emitAndAccum_preserves_invariant numPrimal fwdEnv
        (addSpecCotangent w0 (1 * specCot dstWire) specCot) w1 (.scale (-1)) [dOut] st1 hInv1
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons] at hInv2
      rw [hdOutVal1] at hInv2
      have hNext2 := emitAndAccum_nextWire_le w1 (.scale (-1)) [dOut] st1
      have hBelow2 := emitAndAccum_preserves_below_nextWire fwdEnv w1 (.scale (-1)) [dOut] st1
      have hStepEq :
          specGradEdgeStep fwdEnv ⟨opIdx, .sub, srcWires, dstWire⟩ specCot =
            addSpecCotangent w1 ((-1) * specCot dstWire)
              (addSpecCotangent w0 (1 * specCot dstWire) specCot) := by
        simp [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, w0, w1]
      rw [hStepEq]
      refine ⟨hInv2, Nat.le_trans hNext1 hNext2, fun u hu => ?_⟩
      change evalHyperEdgesComb fwdEnv (emitAndAccum w1 (.scale (-1)) [dOut] st1).revEdges u =
        evalHyperEdgesComb fwdEnv st0.revEdges u
      rw [hBelow2 u (Nat.lt_of_lt_of_le hu hNext1), hBelow1 u hu]
    | mul =>
      simp only
      let w0 := wireAt srcWires 0
      let w1 := wireAt srcWires 1
      let st1 := emitAndAccum w0 .mul [w1, dOut] st0
      have hInv1 := emitAndAccum_preserves_invariant numPrimal fwdEnv specCot w0 .mul [w1, dOut] st0 hInv
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons, list_getD_one_cons] at hInv1
      rw [hwVal 1, hdOutVal] at hInv1
      have hNext1 := emitAndAccum_nextWire_le w0 .mul [w1, dOut] st0
      have hBelow1 := emitAndAccum_preserves_below_nextWire fwdEnv w0 .mul [w1, dOut] st0
      have hw0Val1 : evalHyperEdgesComb fwdEnv st1.revEdges w0 = fwdEnv w0 := by
        rw [hBelow1 w0 (hwLt 0), hwVal 0]
      have hdOutVal1 : evalHyperEdgesComb fwdEnv st1.revEdges dOut = specCot dstWire := by
        rw [hBelow1 dOut hdOutLt, hdOutVal]
      have hInv2 := emitAndAccum_preserves_invariant numPrimal fwdEnv
        (addSpecCotangent w0 (fwdEnv w1 * specCot dstWire) specCot) w1 .mul [w0, dOut] st1 hInv1
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons, list_getD_one_cons] at hInv2
      rw [hw0Val1, hdOutVal1] at hInv2
      have hNext2 := emitAndAccum_nextWire_le w1 .mul [w0, dOut] st1
      have hBelow2 := emitAndAccum_preserves_below_nextWire fwdEnv w1 .mul [w0, dOut] st1
      have hStepEq :
          specGradEdgeStep fwdEnv ⟨opIdx, .mul, srcWires, dstWire⟩ specCot =
            addSpecCotangent w1 (fwdEnv w0 * specCot dstWire)
              (addSpecCotangent w0 (fwdEnv w1 * specCot dstWire) specCot) := by
        simp [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, w0, w1]
      rw [hStepEq]
      refine ⟨hInv2, Nat.le_trans hNext1 hNext2, fun u hu => ?_⟩
      change evalHyperEdgesComb fwdEnv (emitAndAccum w1 .mul [w0, dOut] st1).revEdges u =
        evalHyperEdgesComb fwdEnv st0.revEdges u
      rw [hBelow2 u (Nat.lt_of_lt_of_le hu hNext1), hBelow1 u hu]
    | mac =>
      simp only
      let w0 := wireAt srcWires 0
      let w1 := wireAt srcWires 1
      let w2 := wireAt srcWires 2
      let st1 := emitAndAccum w0 .mul [w1, dOut] st0
      have hInv1 := emitAndAccum_preserves_invariant numPrimal fwdEnv specCot w0 .mul [w1, dOut] st0 hInv
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons, list_getD_one_cons] at hInv1
      rw [hwVal 1, hdOutVal] at hInv1
      have hNext1 := emitAndAccum_nextWire_le w0 .mul [w1, dOut] st0
      have hBelow1 := emitAndAccum_preserves_below_nextWire fwdEnv w0 .mul [w1, dOut] st0
      have hw0Val1 : evalHyperEdgesComb fwdEnv st1.revEdges w0 = fwdEnv w0 := by
        rw [hBelow1 w0 (hwLt 0), hwVal 0]
      have hdOutVal1 : evalHyperEdgesComb fwdEnv st1.revEdges dOut = specCot dstWire := by
        rw [hBelow1 dOut hdOutLt, hdOutVal]
      let cot1 := addSpecCotangent w0 (fwdEnv w1 * specCot dstWire) specCot
      let st2 := emitAndAccum w1 .mul [w0, dOut] st1
      have hInv2 := emitAndAccum_preserves_invariant numPrimal fwdEnv cot1 w1 .mul [w0, dOut] st1 hInv1
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons, list_getD_one_cons] at hInv2
      rw [hw0Val1, hdOutVal1] at hInv2
      have hNext2 := emitAndAccum_nextWire_le w1 .mul [w0, dOut] st1
      have hBelow2 := emitAndAccum_preserves_below_nextWire fwdEnv w1 .mul [w0, dOut] st1
      have hdOutVal2 : evalHyperEdgesComb fwdEnv st2.revEdges dOut = specCot dstWire := by
        rw [hBelow2 dOut (Nat.lt_of_lt_of_le hdOutLt hNext1), hdOutVal1]
      let cot2 := addSpecCotangent w1 (fwdEnv w0 * specCot dstWire) cot1
      have hInv3 := emitAndAccum_preserves_invariant numPrimal fwdEnv cot2 w2 (.scale 1) [dOut] st2 hInv2
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons] at hInv3
      rw [hdOutVal2] at hInv3
      have hNext3 := emitAndAccum_nextWire_le w2 (.scale 1) [dOut] st2
      have hBelow3 := emitAndAccum_preserves_below_nextWire fwdEnv w2 (.scale 1) [dOut] st2
      have hStepEq :
          specGradEdgeStep fwdEnv ⟨opIdx, .mac, srcWires, dstWire⟩ specCot =
            addSpecCotangent w2 (1 * specCot dstWire) cot2 := by
        simp [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, w0, w1, w2, cot1, cot2]
      rw [hStepEq]
      refine ⟨hInv3, Nat.le_trans (Nat.le_trans hNext1 hNext2) hNext3, fun u hu => ?_⟩
      have hu1 : u < st1.nextWire := Nat.lt_of_lt_of_le hu hNext1
      have hu2 : u < st2.nextWire := Nat.lt_of_lt_of_le hu1 hNext2
      change evalHyperEdgesComb fwdEnv (emitAndAccum w2 (.scale 1) [dOut] st2).revEdges u =
        evalHyperEdgesComb fwdEnv st0.revEdges u
      rw [hBelow3 u hu2, hBelow2 u hu1, hBelow1 u hu]
    | mux =>
      simp only
      let c  := wireAt srcWires 0
      let w1 := wireAt srcWires 1
      let w2 := wireAt srcWires 2
      obtain ⟨hInvZ, hNextZ, hzEq, hzVal, hBelowZ⟩ := emitRevEdge_const_zero_sound numPrimal fwdEnv specCot st0 hInv
      let zWire := (emitRevEdge (.const 0) [] st0).1
      let st1   := (emitRevEdge (.const 0) [] st0).2
      have hzLt1 : zWire < st1.nextWire := by
        change (emitRevEdge (.const 0) [] st0).1 < st1.nextWire
        rw [hzEq]
        exact hNextZ
      have hcLt1 : c < st1.nextWire := Nat.lt_trans (hwLt 0) hNextZ
      have hdOutLt1 : dOut < st1.nextWire := Nat.lt_trans hdOutLt hNextZ
      have hcVal1 : evalHyperEdgesComb fwdEnv st1.revEdges c = fwdEnv c := by
        rw [hBelowZ c (hwLt 0), hwVal 0]
      have hdOutVal1 : evalHyperEdgesComb fwdEnv st1.revEdges dOut = specCot dstWire := by
        rw [hBelowZ dOut hdOutLt, hdOutVal]
      let st2 := emitAndAccum w1 .mux [c, dOut, zWire] st1
      have hInv2 := emitAndAccum_preserves_invariant numPrimal fwdEnv specCot w1 .mux [c, dOut, zWire] st1 hInvZ
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons, list_getD_one_cons, list_getD_two_cons] at hInv2
      rw [hcVal1, hdOutVal1, hzVal] at hInv2
      have hNext2 := emitAndAccum_nextWire_le w1 .mux [c, dOut, zWire] st1
      have hBelow2 := emitAndAccum_preserves_below_nextWire fwdEnv w1 .mux [c, dOut, zWire] st1
      have hcVal2 : evalHyperEdgesComb fwdEnv st2.revEdges c = fwdEnv c := by
        rw [hBelow2 c hcLt1, hcVal1]
      have hzVal2 : evalHyperEdgesComb fwdEnv st2.revEdges zWire = 0 := by
        rw [hBelow2 zWire hzLt1, hzVal]
      have hdOutVal2 : evalHyperEdgesComb fwdEnv st2.revEdges dOut = specCot dstWire := by
        rw [hBelow2 dOut hdOutLt1, hdOutVal1]
      let cot1 := addSpecCotangent w1 (if (fwdEnv c != 0) = true then specCot dstWire else 0) specCot
      have hInv3 := emitAndAccum_preserves_invariant numPrimal fwdEnv cot1 w2 .mux [c, zWire, dOut] st2 hInv2
      dsimp only [List.map, evalHypergraphOp, list_getD_zero_cons, list_getD_one_cons, list_getD_two_cons] at hInv3
      rw [hcVal2, hzVal2, hdOutVal2] at hInv3
      have hNext3 := emitAndAccum_nextWire_le w2 .mux [c, zWire, dOut] st2
      have hBelow3 := emitAndAccum_preserves_below_nextWire fwdEnv w2 .mux [c, zWire, dOut] st2
      have hStepEq :
          specGradEdgeStep fwdEnv ⟨opIdx, .mux, srcWires, dstWire⟩ specCot =
            addSpecCotangent w2 (if (fwdEnv c != 0) = true then 0 else specCot dstWire) cot1 := by
        simp [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, c, w1, w2, cot1]
      rw [hStepEq]
      refine ⟨hInv3, Nat.le_trans (Nat.le_trans (Nat.le_of_lt hNextZ) hNext2) hNext3, fun u hu => ?_⟩
      have hu1 : u < st1.nextWire := Nat.lt_trans hu hNextZ
      have hu2 : u < st2.nextWire := Nat.lt_of_lt_of_le hu1 hNext2
      change evalHyperEdgesComb fwdEnv (emitAndAccum w2 .mux [c, zWire, dOut] st2).revEdges u =
        evalHyperEdgesComb fwdEnv st0.revEdges u
      rw [hBelow3 u hu2, hBelow2 u hu1, hBelowZ u hu]

/-- Structural induction over any reversed forward edge list `revFwd : List HyperEdge` establishing
that `revFwd.foldl (fun st e => pullbackHyperEdge e st) initSt` maintains `CotStateInvariant` for
`specGradRevOrder fwdEnv revFwd initCot`. -/
theorem pullbackHyperEdges_foldl_sound
    (numPrimal : Nat) (fwdEnv : Nat → Int) (revFwd : List HyperEdge)
    (initCot : Nat → Int) (initSt : CotangentBuilderState)
    (hEdges : ∀ e ∈ revFwd, EdgeSrcBounded numPrimal e)
    (hInv : CotStateInvariant numPrimal fwdEnv initCot initSt) :
    let finalSt := revFwd.foldl (fun st e => pullbackHyperEdge e st) initSt
    CotStateInvariant numPrimal fwdEnv (specGradRevOrder fwdEnv revFwd initCot) finalSt ∧
    initSt.nextWire ≤ finalSt.nextWire ∧
    (∀ u, u < initSt.nextWire →
      evalHyperEdgesComb fwdEnv finalSt.revEdges u = evalHyperEdgesComb fwdEnv initSt.revEdges u) := by
  induction revFwd generalizing initCot initSt with
  | nil =>
    exact ⟨hInv, Nat.le_refl _, fun _ _ => rfl⟩
  | cons e rest ih =>
    dsimp only [List.foldl_cons, specGradRevOrder]
    have hHeadEdge : EdgeSrcBounded numPrimal e := hEdges e List.mem_cons_self
    have hRestEdges : ∀ e' ∈ rest, EdgeSrcBounded numPrimal e' :=
      fun e' he' => hEdges e' (List.mem_cons_of_mem e he')
    obtain ⟨hInv1, hNext1, hBelow1⟩ :=
      pullbackHyperEdge_sound numPrimal fwdEnv initCot e initSt hHeadEdge hInv
    obtain ⟨hInvRest, hNextRest, hBelowRest⟩ :=
      ih (specGradEdgeStep fwdEnv e initCot) (pullbackHyperEdge e initSt) hRestEdges hInv1
    refine ⟨hInvRest, Nat.le_trans hNext1 hNextRest, fun u hu => ?_⟩
    rw [hBelowRest u (Nat.lt_of_lt_of_le hu hNext1), hBelow1 u hu]

theorem resolveInputCotWires_sound
    (numPrimal : Nat) (fwdEnv : Nat → Int) (specCot : Nat → Int)
    (inWires : List Nat) (st : CotangentBuilderState)
    (hInv : CotStateInvariant numPrimal fwdEnv specCot st) :
    CotStateInvariant numPrimal fwdEnv specCot (resolveInputCotWires inWires st).2 ∧
    st.nextWire ≤ (resolveInputCotWires inWires st).2.nextWire ∧
    (∀ u, u < st.nextWire →
      evalHyperEdgesComb fwdEnv (resolveInputCotWires inWires st).2.revEdges u =
        evalHyperEdgesComb fwdEnv st.revEdges u) ∧
    (resolveInputCotWires inWires st).1.map
      (evalHyperEdgesComb fwdEnv (resolveInputCotWires inWires st).2.revEdges) =
      inWires.map specCot := by
  induction inWires generalizing st with
  | nil =>
    exact ⟨hInv, Nat.le_refl _, fun _ _ => rfl, rfl⟩
  | cons w rest ih =>
    rcases st with ⟨cotMap, nextWire, revEdges⟩
    unfold resolveInputCotWires
    cases hLook : cotMap.lookup w with
    | some cw =>
      simp only
      obtain ⟨hcwLt, hcwVal⟩ := hInv.lookup_some w cw hLook
      dsimp at hcwLt hcwVal
      obtain ⟨hInvRest, hNextRest, hBelowRest, hMapRest⟩ := ih ⟨cotMap, nextWire, revEdges⟩ hInv
      refine ⟨hInvRest, hNextRest, hBelowRest, ?_⟩
      simp only [List.map_cons]
      rw [hBelowRest cw hcwLt, hcwVal, hMapRest]
    | none =>
      simp only
      have hSpec0 : specCot w = 0 := hInv.lookup_none w hLook
      let e0 : HyperEdge := { opIdx := 0, op := .const 0, srcWires := [], dstWire := nextWire }
      let st1 : CotangentBuilderState := ⟨setCotWire w nextWire cotMap, nextWire + 1, revEdges ++ [e0]⟩
      have hBelow1 : ∀ u, u < nextWire → evalHyperEdgesComb fwdEnv st1.revEdges u = evalHyperEdgesComb fwdEnv revEdges u := by
        intro u hu
        dsimp [st1]
        rw [evalHyperEdgesComb_append]
        simp only [evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
        exact stepHyperEdge_ne _ _ u (by dsimp [e0]; omega)
      have hValNext : evalHyperEdgesComb fwdEnv st1.revEdges nextWire = specCot w := by
        dsimp [st1]
        rw [evalHyperEdgesComb_append]
        simp only [evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
        change stepHyperEdge (evalHyperEdgesComb fwdEnv revEdges) e0 e0.dstWire = specCot w
        rw [stepHyperEdge_eq_self]
        simp [e0, evalHypergraphOp, hSpec0]
      have hInv1 : CotStateInvariant numPrimal fwdEnv specCot st1 := by
        refine
          { primal_le_next := by
              have hPrimalLe := hInv.primal_le_next
              dsimp at hPrimalLe
              dsimp [st1]
              omega
          , primal_preserved := fun u hu => by
              have hPrimalLe := hInv.primal_le_next
              dsimp at hPrimalLe
              rw [hBelow1 u (Nat.lt_of_lt_of_le hu hPrimalLe)]
              exact hInv.primal_preserved u hu
          , lookup_none := fun u hNone => by
              dsimp [st1] at hNone
              cases huw : (u == w)
              · rw [setCotWire_lookup_ne w u nextWire cotMap huw] at hNone
                exact hInv.lookup_none u hNone
              · have huEq : u = w := LawfulBEq.eq_of_beq huw
                subst huEq
                rw [setCotWire_lookup_self] at hNone
                contradiction
          , lookup_some := fun u cw hSome => by
              dsimp [st1] at hSome ⊢
              cases huw : (u == w)
              · rw [setCotWire_lookup_ne w u nextWire cotMap huw] at hSome
                obtain ⟨hcwLt, hcwVal⟩ := hInv.lookup_some u cw hSome
                dsimp at hcwLt hcwVal
                refine ⟨by omega, ?_⟩
                rw [hBelow1 cw hcwLt, hcwVal]
              · have huEq : u = w := LawfulBEq.eq_of_beq huw
                subst huEq
                rw [setCotWire_lookup_self] at hSome
                injection hSome with hcwEq
                subst hcwEq
                exact ⟨by omega, hValNext⟩ }
      obtain ⟨hInvRest, hNextRest, hBelowRest, hMapRest⟩ := ih st1 hInv1
      have hNext1 : nextWire < st1.nextWire := by dsimp [st1]; omega
      refine ⟨hInvRest, Nat.le_trans (Nat.le_of_lt hNext1) hNextRest, fun u hu => ?_, ?_⟩
      · rw [hBelowRest u (Nat.lt_trans hu hNext1), hBelow1 u hu]
      · simp only [List.map_cons]
        change evalHyperEdgesComb fwdEnv (resolveInputCotWires rest st1).2.revEdges nextWire ::
          List.map (evalHyperEdgesComb fwdEnv (resolveInputCotWires rest st1).2.revEdges)
            (resolveInputCotWires rest st1).1 =
          specCot w :: List.map specCot rest
        rw [hBelowRest nextWire hNext1, hValNext, hMapRest]

/-- **Theorem (`compileGraphAdjoint_dag_sound`)**:
Universal Whole-DAG Reverse-Mode AD Pullback Soundness by structural induction on `edges : List HyperEdge`:
1. For ANY primal wire count `numPrimal`, ANY forward DAG `edges : List HyperEdge` whose source wires lie
   in `0 .. numPrimal - 1` (`∀ e ∈ edges, EdgeSrcBounded numPrimal e`), ANY forward wire environment
   `fwdEnv : Nat → Int`, ANY initial cotangent map `initCot : Nat → Int`, and ANY initial builder state
   `initSt : CotangentBuilderState` satisfying `CotStateInvariant numPrimal fwdEnv initCot initSt`:
   - Folding `pullbackHyperEdge` right-to-left over `edges` (`edges.reverse.foldl`) maintains
     `CotStateInvariant numPrimal fwdEnv (specGradEdges fwdEnv edges initCot) afterPullback`,
   - Resolving any boundary input wire list `inWires : List Nat` via `resolveInputCotWires` preserves
     all primal wires `u < numPrimal` (`evalHyperEdgesComb fwdEnv finalSt.revEdges u = fwdEnv u`) and
     evaluates the resolved input cotangent wires `inCotWires` to the exact whole-DAG reverse-mode
     gradients `inWires.map (specGradEdges fwdEnv edges initCot)`! -/
theorem compileGraphAdjoint_dag_sound
    (numPrimal : Nat) (fwdEnv : Nat → Int) (edges : List HyperEdge) (inWires : List Nat)
    (initCot : Nat → Int) (initSt : CotangentBuilderState)
    (hEdges : ∀ e ∈ edges, EdgeSrcBounded numPrimal e)
    (hInv : CotStateInvariant numPrimal fwdEnv initCot initSt) :
    let afterPullback := edges.reverse.foldl (fun st e => pullbackHyperEdge e st) initSt
    let resolved := resolveInputCotWires inWires afterPullback
    let inCotWires := resolved.1
    let finalSt := resolved.2
    CotStateInvariant numPrimal fwdEnv (specGradEdges fwdEnv edges initCot) afterPullback ∧
    CotStateInvariant numPrimal fwdEnv (specGradEdges fwdEnv edges initCot) finalSt ∧
    (∀ u, u < numPrimal → evalHyperEdgesComb fwdEnv finalSt.revEdges u = fwdEnv u) ∧
    inCotWires.map (evalHyperEdgesComb fwdEnv finalSt.revEdges) =
      inWires.map (specGradEdges fwdEnv edges initCot) := by
  have hRevEdges : ∀ e ∈ edges.reverse, EdgeSrcBounded numPrimal e := by
    intro e he
    exact hEdges e (List.mem_reverse.mp he)
  obtain ⟨hInvAfter, _, _⟩ :=
    pullbackHyperEdges_foldl_sound numPrimal fwdEnv edges.reverse initCot initSt hRevEdges hInv
  change CotStateInvariant numPrimal fwdEnv (specGradEdges fwdEnv edges initCot) _ at hInvAfter
  obtain ⟨hInvFinal, _, _, hMapFinal⟩ :=
    resolveInputCotWires_sound numPrimal fwdEnv (specGradEdges fwdEnv edges initCot)
      inWires (edges.reverse.foldl (fun st e => pullbackHyperEdge e st) initSt) hInvAfter
  refine ⟨hInvAfter, hInvFinal, hInvFinal.primal_preserved, hMapFinal⟩

/-! ## 6. Pipelined Wavefront RTL Compilation (`compileHypergraphToRtlPipelined`; its whole-module theorem is `compileHypergraphToRtlPipelined_sound`, §8c) -/

/-- Synchronous 64-bit hardware step for a hyperedge `e` inside a wavefront stage, reading all
`e.srcWires` from the frozen stage-entry snapshot `stageEntryEnv : Nat → BitVec 64`. -/
def stepHyperEdgeSyncBv (stageEntryEnv : Nat → BitVec 64) (curEnv : Nat → BitVec 64) (e : HyperEdge) :
    Nat → BitVec 64 :=
  let v := evalHypergraphOpBv e.op (e.srcWires.map stageEntryEnv)
  fun w => if w == e.dstWire then v else curEnv w

/-- Auxiliary fold for 64-bit synchronous wavefront stage execution. -/
def evalWavefrontStageAuxBv (stageEntryEnv : Nat → BitVec 64) (curEnv : Nat → BitVec 64) :
    List HyperEdge → Nat → BitVec 64
  | [] => curEnv
  | e :: rest =>
    evalWavefrontStageAuxBv stageEntryEnv (stepHyperEdgeSyncBv stageEntryEnv curEnv e) rest

/-- 64-bit synchronous wavefront stage evaluation (`evalWavefrontStageSyncBv`). -/
def evalWavefrontStageSyncBv (env : Nat → BitVec 64) (stage : List HyperEdge) : Nat → BitVec 64 :=
  evalWavefrontStageAuxBv env env stage

/-- Evaluate a sequence of wavefront stages over 64-bit bitvectors using synchronous snapshot reads. -/
def evalLayeredStagesSyncBv (initEnv : Nat → BitVec 64) (stages : List (List HyperEdge)) :
    Nat → BitVec 64 :=
  stages.foldl evalWavefrontStageSyncBv initEnv

/-- `RtlExpr` reading the stage-entry snapshot of hypergraph wire `u` at wavefront stage `stageIdx`:
* Stage `0` reads from `.inputPort u`,
* Stage `stageIdx > 0` reads from the previous wavefront stage's pipeline register
  `.regRead ((stageIdx - 1) * numWires + u)`. -/
def stageEntryExpr (numWires stageIdx u : Nat) : RtlExpr :=
  if stageIdx == 0 then .inputPort u
  else .regRead ((stageIdx - 1) * numWires + u)

/-- Lower a `HypergraphOp` inside wavefront stage `stageIdx` to an `RtlExpr` reading its operands
from the stage-entry register boundary `stageEntryExpr numWires stageIdx`. -/
def compileHypergraphStageOpToRtl
    (numWires stageIdx : Nat) (op : HypergraphOp) (srcWires : List Nat) : RtlExpr :=
  compileHypergraphOpExpr op (srcWires.map (stageEntryExpr numWires stageIdx))

/-- Auxiliary fold constructing the next-state `RtlExpr` for each hypergraph wire `w` across the
operations of wavefront stage `stageIdx`. -/
def compileWavefrontStageAuxExpr
    (numWires stageIdx : Nat) (curExpr : Nat → RtlExpr) :
    List HyperEdge → Nat → RtlExpr
  | [] => curExpr
  | e :: rest =>
    let vExpr := compileHypergraphStageOpToRtl numWires stageIdx e.op e.srcWires
    compileWavefrontStageAuxExpr numWires stageIdx
      (fun w => if w == e.dstWire then vExpr else curExpr w) rest

/-- Construct the stage-exit `RtlExpr` for wire `w` at the end of wavefront stage `stageIdx`. -/
def compileWavefrontStageExpr
    (numWires stageIdx : Nat) (stage : List HyperEdge) (w : Nat) : RtlExpr :=
  compileWavefrontStageAuxExpr numWires stageIdx (stageEntryExpr numWires stageIdx) stage w

/-- **Pipelined Wavefront RTL Compiler (`compileHypergraphToRtlPipelined`)**:
Lowers a `StrictOpenHypergraph` `g` into a deeply pipelined synchronous `Obend.Hardware.HDL.RtlModule`
by partitioning `g` into Kahn topological wavefront layers `stages := layerHypergraph g` and inserting
a bank of synchronous pipeline stage `RegSpec`s (`pipe_s{s}_w{w}`) between every wavefront layer! -/
def compileHypergraphToRtlPipelined (name : String) (g : StrictOpenHypergraph) : RtlModule :=
  let numWires  := g.nodeTypes.length
  let stages    := layerHypergraph g
  let numStages := stages.length
  let stageWires : List WireAssign :=
    (stages.zipIdx.map fun (stage, s) =>
      (List.range numWires).map fun w =>
        { wireIdx := s * numWires + w
        , name    := s!"w_s{s}_w{w}"
        , expr    := compileWavefrontStageExpr numWires s stage w }).flatten
  let stageRegs : List RegSpec :=
    (stages.zipIdx.map fun (stage, s) =>
      (List.range numWires).map fun w =>
        { regIdx         := s * numWires + w
        , name           := s!"pipe_s{s}_w{w}"
        , domain         := .coreClk
        , resetKind      := .resetFree
        , isSynchronizer := false
        , nextExpr       := compileWavefrontStageExpr numWires s stage w }).flatten
  let outPorts : List OutputPort :=
    g.boundaryOut.table.map fun w =>
      { name := s!"out_w{w}"
      , expr :=
          if numStages == 0 then .inputPort w
          else .regRead ((numStages - 1) * numWires + w) }
  { name       := name
  , inputNames := (List.range numWires).map (fun w => s!"in_w{w}")
  , wires      := stageWires
  , regs       := stageRegs
  , outputs    := outPorts }

theorem evalRtlExpr_stageEntryExpr
    (numWires stageIdx u : Nat)
    (inputs wireEnv regState : Nat → BitVec 64) :
    evalRtlExpr inputs wireEnv regState (stageEntryExpr numWires stageIdx u) =
      (if stageIdx == 0 then inputs else fun k => regState ((stageIdx - 1) * numWires + k)) u := by
  unfold stageEntryExpr
  by_cases h : stageIdx == 0 <;> simp [h, evalRtlExpr]

theorem compileHypergraphStageOpToRtl_sound
    (numWires stageIdx : Nat) (op : HypergraphOp) (srcWires : List Nat)
    (inputs wireEnv regState : Nat → BitVec 64) :
    let entryEnv := if stageIdx == 0 then inputs else fun u => regState ((stageIdx - 1) * numWires + u)
    evalRtlExpr inputs wireEnv regState (compileHypergraphStageOpToRtl numWires stageIdx op srcWires) =
      evalHypergraphOpBv op (srcWires.map entryEnv) := by
  intro entryEnv
  rw [compileHypergraphStageOpToRtl, evalRtlExpr_compileHypergraphOpExpr, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  exact evalRtlExpr_stageEntryExpr numWires stageIdx u inputs wireEnv regState

theorem compileWavefrontStageAuxExpr_sound
    (numWires stageIdx : Nat) (stage : List HyperEdge)
    (inputs wireEnv regState : Nat → BitVec 64)
    (curExpr : Nat → RtlExpr) (curEnv : Nat → BitVec 64)
    (hCur : ∀ w, evalRtlExpr inputs wireEnv regState (curExpr w) = curEnv w) :
    let entryEnv := if stageIdx == 0 then inputs else fun u => regState ((stageIdx - 1) * numWires + u)
    ∀ w,
      evalRtlExpr inputs wireEnv regState (compileWavefrontStageAuxExpr numWires stageIdx curExpr stage w) =
        evalWavefrontStageAuxBv entryEnv curEnv stage w := by
  intro entryEnv
  induction stage generalizing curExpr curEnv with
  | nil =>
    intro w
    exact hCur w
  | cons e rest ih =>
    intro w
    dsimp only [compileWavefrontStageAuxExpr, evalWavefrontStageAuxBv]
    apply ih
    intro u
    by_cases hu : u == e.dstWire
    · simp only [hu, ↓reduceIte, stepHyperEdgeSyncBv]
      exact compileHypergraphStageOpToRtl_sound numWires stageIdx e.op e.srcWires inputs wireEnv regState
    · simp only [hu, Bool.false_eq_true, ↓reduceIte, stepHyperEdgeSyncBv]
      exact hCur u

/-- **Theorem (`compileWavefrontStageExpr_sound`)**:
For EVERY wavefront stage `stage : List HyperEdge`, stage index `stageIdx`, wire count `numWires`,
and wire index `w : Nat`, evaluating the lowered pipeline stage register expression
`compileWavefrontStageExpr numWires stageIdx stage w` equals the synchronous wavefront stage
evaluation `evalWavefrontStageSyncBv entryEnv stage w`! -/
theorem compileWavefrontStageExpr_sound
    (numWires stageIdx : Nat) (stage : List HyperEdge)
    (inputs wireEnv regState : Nat → BitVec 64) (w : Nat) :
    let entryEnv := if stageIdx == 0 then inputs else fun u => regState ((stageIdx - 1) * numWires + u)
    evalRtlExpr inputs wireEnv regState (compileWavefrontStageExpr numWires stageIdx stage w) =
      evalWavefrontStageSyncBv entryEnv stage w := by
  unfold compileWavefrontStageExpr evalWavefrontStageSyncBv
  exact compileWavefrontStageAuxExpr_sound numWires stageIdx stage inputs wireEnv regState
    (stageEntryExpr numWires stageIdx)
    (if stageIdx == 0 then inputs else fun u => regState ((stageIdx - 1) * numWires + u))
    (fun u => evalRtlExpr_stageEntryExpr numWires stageIdx u inputs wireEnv regState)
    w

/-- Predicate identifying arithmetic `HypergraphOp`s (whose 64-bit `BitVec` semantics is a ring
homomorphism of `Int` modulo $2^{64}$ via `BitVec.ofInt 64`). -/
def HypergraphOp.isArithmetic : HypergraphOp → Bool
  | .mux => false
  | _    => true

theorem map_ofInt_getD (args : List Int) (i : Nat) :
    (args.map (BitVec.ofInt 64)).getD i 0#64 = BitVec.ofInt 64 (args.getD i 0) := by
  rw [map_getD_eq_getElem?]
  simp only [List.getD]
  cases args[i]? <;> rfl

theorem bitvec_ofInt_sub_64 (a b : Int) :
    BitVec.ofInt 64 a - BitVec.ofInt 64 b = BitVec.ofInt 64 (a - b) := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem evalHypergraphOpBv_ofInt (op : HypergraphOp) (args : List Int)
    (hArith : op.isArithmetic = true) :
    evalHypergraphOpBv op (args.map (BitVec.ofInt 64)) =
      BitVec.ofInt 64 (evalHypergraphOp op args) := by
  cases op with
  | const v => rfl
  | add =>
    dsimp only [evalHypergraphOpBv, evalHypergraphOp]
    rw [map_ofInt_getD, map_ofInt_getD, BitVec.ofInt_add]
  | sub =>
    dsimp only [evalHypergraphOpBv, evalHypergraphOp]
    rw [map_ofInt_getD, map_ofInt_getD, bitvec_ofInt_sub_64]
  | mul =>
    dsimp only [evalHypergraphOpBv, evalHypergraphOp]
    rw [map_ofInt_getD, map_ofInt_getD, BitVec.ofInt_mul]
  | scale k =>
    dsimp only [evalHypergraphOpBv, evalHypergraphOp]
    rw [map_ofInt_getD, BitVec.ofInt_mul]
  | mac =>
    dsimp only [evalHypergraphOpBv, evalHypergraphOp]
    rw [map_ofInt_getD, map_ofInt_getD, map_ofInt_getD, BitVec.ofInt_add, BitVec.ofInt_mul]
  | mux =>
    simp [HypergraphOp.isArithmetic] at hArith

theorem evalWavefrontStageAuxBv_ofInt
    (stageEntryEnv curEnv : Nat → Int) (stage : List HyperEdge)
    (hArith : stage.all (fun e => e.op.isArithmetic) = true) :
    ∀ w,
      evalWavefrontStageAuxBv (fun u => BitVec.ofInt 64 (stageEntryEnv u))
        (fun u => BitVec.ofInt 64 (curEnv u)) stage w =
      BitVec.ofInt 64 (evalWavefrontStageAux stageEntryEnv curEnv stage w) := by
  induction stage generalizing curEnv with
  | nil =>
    intro w
    rfl
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hArith
    intro w
    dsimp only [evalWavefrontStageAuxBv, evalWavefrontStageAux]
    have hStep :
        stepHyperEdgeSyncBv (fun u => BitVec.ofInt 64 (stageEntryEnv u))
          (fun u => BitVec.ofInt 64 (curEnv u)) e =
        fun u => BitVec.ofInt 64 (stepHyperEdgeSync stageEntryEnv curEnv e u) := by
      funext u
      dsimp only [stepHyperEdgeSyncBv, stepHyperEdgeSync]
      by_cases hu : u == e.dstWire
      · simp only [hu, ↓reduceIte]
        have hMap :
            e.srcWires.map (fun k => BitVec.ofInt 64 (stageEntryEnv k)) =
              (e.srcWires.map stageEntryEnv).map (BitVec.ofInt 64) := by
          simp [List.map_map]
        rw [hMap, evalHypergraphOpBv_ofInt e.op _ hArith.1]
      · simp [hu]
    rw [hStep]
    exact ih (stepHyperEdgeSync stageEntryEnv curEnv e) hArith.2 w

theorem evalWavefrontStageSyncBv_ofInt
    (env : Nat → Int) (stage : List HyperEdge)
    (hArith : stage.all (fun e => e.op.isArithmetic) = true) :
    evalWavefrontStageSyncBv (fun u => BitVec.ofInt 64 (env u)) stage =
      fun w => BitVec.ofInt 64 (evalWavefrontStageSync env stage w) := by
  funext w
  exact evalWavefrontStageAuxBv_ofInt env env stage hArith w

theorem evalLayeredStagesSyncBv_ofInt
    (initEnv : Nat → Int) (stages : List (List HyperEdge))
    (hArith : stages.all (fun s => s.all (fun e => e.op.isArithmetic)) = true) :
    evalLayeredStagesSyncBv (fun u => BitVec.ofInt 64 (initEnv u)) stages =
      fun w => BitVec.ofInt 64 (evalLayeredStagesSync initEnv stages w) := by
  induction stages generalizing initEnv with
  | nil => rfl
  | cons stage rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hArith
    simp only [evalLayeredStagesSyncBv, evalLayeredStagesSync, List.foldl_cons]
    rw [evalWavefrontStageSyncBv_ofInt initEnv stage hArith.1]
    exact ih (evalWavefrontStageSync initEnv stage) hArith.2

/-- **Theorem (`compileGraphAdjoint_diamond_symbolic_sound`)**:
For EVERY symbolic integer assignment `(x0 x1 x2 x3 dOut : Int)` to the 5-edge
`goldenDiamondHypergraph` ($f(x_0, x_1, x_2, x_3) = (x_0 + x_1)(x_2 + x_3) + 10$),
evaluating `compileGraphAdjoint goldenDiamondHypergraph` via `evalHypergraphComb`,
`evalHypergraphLayered`, or `evalHypergraphLayeredSync` produces the exact symbolic primal
output and partial derivatives:
`[(x0 + x1) * (x2 + x3) + 10, (x2 + x3) * dOut, (x2 + x3) * dOut, (x0 + x1) * dOut, (x0 + x1) * dOut]`. -/
theorem compileGraphAdjoint_diamond_symbolic_sound (x0 x1 x2 x3 dOut : Int) :
    let gAdj := compileGraphAdjoint goldenDiamondHypergraph
    let env : Nat → Int := fun w =>
      match w with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 9 => dOut | _ => 0
    let expected :=
      [ (x0 + x1) * (x2 + x3) + 10
      , (x2 + x3) * dOut
      , (x2 + x3) * dOut
      , (x0 + x1) * dOut
      , (x0 + x1) * dOut ]
    evalHypergraphComb gAdj env = expected ∧
    evalHypergraphLayered gAdj env = expected ∧
    evalHypergraphLayeredSync gAdj env = expected := by
  have hComb :
      evalHypergraphComb (compileGraphAdjoint goldenDiamondHypergraph)
        (fun w => match w with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 9 => dOut | _ => 0) =
      [ (x0 + x1) * (x2 + x3) + 10
      , (x2 + x3) * dOut
      , (x2 + x3) * dOut
      , (x0 + x1) * dOut
      , (x0 + x1) * dOut ] := by
    change [ (x0 + x1) * (x2 + x3) + 10
           , 1 * ((x2 + x3) * (1 * dOut))
           , 1 * ((x2 + x3) * (1 * dOut))
           , 1 * ((x0 + x1) * (1 * dOut))
           , 1 * ((x0 + x1) * (1 * dOut)) ] = _
    simp [Int.one_mul]
  have hPipe := evalHypergraph_pipelined_eq_comb
    (compileGraphAdjoint goldenDiamondHypergraph)
    (fun w => match w with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 9 => dOut | _ => 0)
  exact ⟨hComb, hPipe.1.trans hComb, hPipe.2.trans hComb⟩

/-! ## 8b. The Single Pass at 64 Bits (`evalHyperEdgesCombBv`)

`evalHyperEdgesComb` with the operations read at 64 bits: the scalar meaning the RTL lowerings are
stated against (`Obend.Hardware.Square.compileHypergraphToRtl_sound`), and over `Int` modulo `2^64`
for graphs without `mux` (`evalHyperEdgesCombBv_ofInt`). A specification, not run. -/

/-- Combinational 64-bit step of one hyperedge: `stepHyperEdge` over `BitVec 64`. -/
def stepHyperEdgeBv (env : Nat → BitVec 64) (e : HyperEdge) : Nat → BitVec 64 :=
  let v := evalHypergraphOpBv e.op (e.srcWires.map env)
  fun w => if w == e.dstWire then v else env w

/-- Single-pass 64-bit combinational evaluation of a list of `HyperEdge`s. -/
def evalHyperEdgesCombBv (initEnv : Nat → BitVec 64) (edges : List HyperEdge) : Nat → BitVec 64 :=
  edges.foldl stepHyperEdgeBv initEnv

theorem evalHyperEdgesCombBv_ofInt (env : Nat → Int) (edges : List HyperEdge)
    (hArith : edges.all (fun e => e.op.isArithmetic) = true) :
    evalHyperEdgesCombBv (fun u => BitVec.ofInt 64 (env u)) edges =
      fun w => BitVec.ofInt 64 (evalHyperEdgesComb env edges w) := by
  induction edges generalizing env with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hArith
    simp only [evalHyperEdgesCombBv, evalHyperEdgesComb, List.foldl_cons] at ih ⊢
    have hStep : stepHyperEdgeBv (fun u => BitVec.ofInt 64 (env u)) e =
        fun u => BitVec.ofInt 64 (stepHyperEdge env e u) := by
      funext u
      dsimp only [stepHyperEdgeBv, stepHyperEdge]
      by_cases hu : u == e.dstWire
      · simp only [hu, ↓reduceIte]
        have hMap : e.srcWires.map (fun k => BitVec.ofInt 64 (env k)) =
            (e.srcWires.map env).map (BitVec.ofInt 64) := by
          simp [List.map_map]
        rw [hMap, evalHypergraphOpBv_ofInt e.op _ hArith.1]
      · simp [hu]
    rw [hStep]
    exact ih (stepHyperEdge env e) hArith.2

/-! ## 8c. The Whole Pipelined Module (`compileHypergraphToRtlPipelined_sound`)

The pipelined module's register bank has slot `s * n + w` for stage `s` and wire `w < n`, written by
stage `s` alone (`pipe_slot_inj`); a clock edge writes every slot from the previous bank
(`compileWavefrontStageExpr_sound`), so after `t` edges with the inputs held, bank `s < t` holds the
synchronous evaluation of the first `s + 1` wavefront stages (`pipelined_bank`), and after one edge per
stage the outputs read the last bank: `evalLayeredStagesSyncBv` of the whole layering. The
hypotheses are that the graph's wires are below `n` (every source and every boundary output), which
`ArrayGraph.wf` of the one-element instance gives (`Obend.Hardware.Square.pipelined_eq_comb`). -/

theorem pipe_slot_inj (n s w s' w' : Nat) (hw : w < n) (hw' : w' < n)
    (h : s * n + w = s' * n + w') : s = s' ∧ w = w' := by
  have hd : ∀ a b, b < n → (a * n + b) / n = a := by
    intro a b hb
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb]
    omega
  have hm : ∀ a b, b < n → (a * n + b) % n = b := by
    intro a b hb
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have h1 := hd s w hw
  have h2 := hd s' w' hw'
  have h3 := hm s w hw
  have h4 := hm s' w' hw'
  rw [h] at h1 h3
  omega

/-- The register-bank update of `stepModuleRegs_eq_foldl_next`, its values abstracted. -/
def bankStep (val : RegSpec → BitVec 64) (f : Nat → BitVec 64) (r : RegSpec) : Nat → BitVec 64 :=
  fun i => if i == r.regIdx then val r else f i

/-- One stage's registers, folded: its slots take their values, every other slot is untouched. -/
theorem foldl_bank_stage (val : RegSpec → BitVec 64) (n s : Nat) (mk : Nat → RegSpec)
    (hIdx : ∀ w, (mk w).regIdx = s * n + w) (f0 : Nat → BitVec 64) (m : Nat) :
    (∀ w, w < m → ((List.range m).foldl (fun f w => bankStep val f (mk w)) f0) (s * n + w) = val (mk w)) ∧
    (∀ j, (∀ w, w < m → j ≠ s * n + w) →
      ((List.range m).foldl (fun f w => bankStep val f (mk w)) f0) j = f0 j) := by
  induction m with
  | zero => exact ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨ihOn, ihOff⟩ := ih
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨?_, ?_⟩
    · intro w hw
      simp only [bankStep, hIdx]
      by_cases hwm : w = m
      · subst hwm
        simp
      · rw [ite_eq_right (by simp; omega)]
        exact ihOn w (by omega)
    · intro j hj
      simp only [bankStep, hIdx]
      rw [ite_eq_right (by simpa using hj m (Nat.lt_succ_self m))]
      exact ihOff j (fun w hw => hj w (by omega))

/-- Every stage's registers, folded from stage `s0` on: the slots of stages below `s0` are untouched,
the slot of stage `s0 + k`, wire `w` holds the value of its register. -/
theorem foldl_bank_stages (val : RegSpec → BitVec 64) (n : Nat) (mk : Nat → List HyperEdge → Nat → RegSpec)
    (hIdx : ∀ s stage w, (mk s stage w).regIdx = s * n + w)
    (L : List (List HyperEdge)) (s0 : Nat) (f0 : Nat → BitVec 64) :
    (∀ s w, w < n → s < s0 →
      ((L.zipIdx s0).foldl (fun acc (p : List HyperEdge × Nat) =>
        (List.range n).foldl (fun f w => bankStep val f (mk p.2 p.1 w)) acc) f0) (s * n + w) =
      f0 (s * n + w)) ∧
    (∀ k w, w < n → (hk : k < L.length) →
      ((L.zipIdx s0).foldl (fun acc (p : List HyperEdge × Nat) =>
        (List.range n).foldl (fun f w => bankStep val f (mk p.2 p.1 w)) acc) f0) ((s0 + k) * n + w) =
      val (mk (s0 + k) L[k] w)) := by
  induction L generalizing s0 f0 with
  | nil => exact ⟨fun _ _ _ _ => rfl, fun k _ _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | cons stage rest ih =>
    simp only [List.zipIdx_cons, List.foldl_cons]
    obtain ⟨hB1, hB2⟩ := foldl_bank_stage val n s0 (mk s0 stage) (hIdx s0 stage) f0 n
    obtain ⟨hC1, hC2⟩ := ih (s0 + 1)
      ((List.range n).foldl (fun f w => bankStep val f (mk s0 stage w)) f0)
    refine ⟨?_, ?_⟩
    · intro s w hw hs
      rw [hC1 s w hw (by omega)]
      apply hB2
      intro w' hw' h
      have := (pipe_slot_inj n s w s0 w' hw hw' h).1
      omega
    · intro k w hw hk
      cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hC1 s0 w hw (by omega)]
        exact hB1 w hw
      | succ k =>
        rw [show s0 + (k + 1) = s0 + 1 + k by omega]
        have := hC2 k w hw (by simpa using hk)
        simpa using this

/-- The pipelined module's register for stage `s`, wire `w`. -/
def pipeReg (numWires s : Nat) (stage : List HyperEdge) (w : Nat) : RegSpec :=
  { regIdx         := s * numWires + w
  , name           := s!"pipe_s{s}_w{w}"
  , domain         := .coreClk
  , resetKind      := .resetFree
  , isSynchronizer := false
  , nextExpr       := compileWavefrontStageExpr numWires s stage w }

theorem compileHypergraphToRtlPipelined_regs (name : String) (g : StrictOpenHypergraph) :
    (compileHypergraphToRtlPipelined name g).regs =
      ((layerHypergraph g).zipIdx.map fun (stage, s) =>
        (List.range g.nodeTypes.length).map (pipeReg g.nodeTypes.length s stage)).flatten := rfl

/-- One clock edge: slot `s * n + w` takes stage `s` of the previous bank (stage `0` of the inputs). -/
theorem pipelined_step (name : String) (g : StrictOpenHypergraph) (ins st : Nat → BitVec 64)
    (s w : Nat) (hw : w < g.nodeTypes.length) (hs : s < (layerHypergraph g).length) :
    stepModuleRegs (compileHypergraphToRtlPipelined name g) false ins st (s * g.nodeTypes.length + w) =
      evalWavefrontStageSyncBv
        (if s == 0 then ins else fun u => st ((s - 1) * g.nodeTypes.length + u))
        (layerHypergraph g)[s] w := by
  rw [stepModuleRegs_eq_foldl_next, compileHypergraphToRtlPipelined_regs, List.foldl_flatten, List.foldl_map]
  have hF : (fun (acc : Nat → BitVec 64) (p : List HyperEdge × Nat) =>
      ((List.range g.nodeTypes.length).map (pipeReg g.nodeTypes.length p.2 p.1)).foldl
        (fun (nextSt : Nat → BitVec 64) r => fun i =>
          if i == r.regIdx then
            regNextValue false ins (evalWireTable ins st (compileHypergraphToRtlPipelined name g).wires) st r
          else nextSt i) acc) =
      fun acc p => (List.range g.nodeTypes.length).foldl
        (fun f w => bankStep
          (regNextValue false ins (evalWireTable ins st (compileHypergraphToRtlPipelined name g).wires) st)
          f (pipeReg g.nodeTypes.length p.2 p.1 w)) acc := by
    funext acc p
    rw [List.foldl_map]
    rfl
  rw [hF]
  have := (foldl_bank_stages
    (regNextValue false ins (evalWireTable ins st (compileHypergraphToRtlPipelined name g).wires) st)
    g.nodeTypes.length (pipeReg g.nodeTypes.length) (fun _ _ _ => rfl) (layerHypergraph g) 0 st).2 s w hw hs
  rw [Nat.zero_add] at this
  rw [this]
  simp only [regNextValue, pipeReg]
  exact compileWavefrontStageExpr_sound g.nodeTypes.length s (layerHypergraph g)[s] ins _ st w

theorem evalWavefrontStageAuxBv_congr (n : Nat) (E1 E2 C1 C2 : Nat → BitVec 64) (stage : List HyperEdge)
    (hSrc : ∀ e ∈ stage, ∀ u ∈ e.srcWires, u < n)
    (hE : ∀ u, u < n → E1 u = E2 u) (hC : ∀ u, u < n → C1 u = C2 u) :
    ∀ w, w < n → evalWavefrontStageAuxBv E1 C1 stage w = evalWavefrontStageAuxBv E2 C2 stage w := by
  induction stage generalizing C1 C2 with
  | nil => exact hC
  | cons e rest ih =>
    intro w hw
    simp only [evalWavefrontStageAuxBv]
    refine ih _ _ (fun e' he' => hSrc e' (List.mem_cons_of_mem e he')) ?_ w hw
    intro u hu
    simp only [stepHyperEdgeSyncBv]
    by_cases hud : u == e.dstWire
    · simp only [hud, ↓reduceIte]
      congr 1
      apply List.map_congr_left
      intro v hv
      exact hE v (hSrc e List.mem_cons_self v hv)
    · simp only [hud, Bool.false_eq_true, ↓reduceIte]
      exact hC u hu

/-- A stage reads only wires below `n`: two entry environments that agree there give the same stage. -/
theorem evalWavefrontStageSyncBv_congr (n : Nat) (E1 E2 : Nat → BitVec 64) (stage : List HyperEdge)
    (hSrc : ∀ e ∈ stage, ∀ u ∈ e.srcWires, u < n) (hE : ∀ u, u < n → E1 u = E2 u) :
    ∀ w, w < n → evalWavefrontStageSyncBv E1 stage w = evalWavefrontStageSyncBv E2 stage w :=
  evalWavefrontStageAuxBv_congr n E1 E2 E1 E2 stage hSrc hE hE

theorem evalLayeredStagesSyncBv_take_succ (ins : Nat → BitVec 64) (stages : List (List HyperEdge))
    (s : Nat) (hs : s < stages.length) :
    evalLayeredStagesSyncBv ins (stages.take (s + 1)) =
      evalWavefrontStageSyncBv (evalLayeredStagesSyncBv ins (stages.take s)) stages[s] := by
  simp only [evalLayeredStagesSyncBv]
  rw [List.take_succ_eq_append_getElem hs, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem runModuleTrace_replicate_succ (m : RtlModule) (initRegs : Nat → BitVec 64)
    (x : Bool × (Nat → BitVec 64)) (t : Nat) :
    runModuleTrace m initRegs (List.replicate (t + 1) x) =
      stepModuleRegs m x.1 x.2 (runModuleTrace m initRegs (List.replicate t x)) := by
  simp only [runModuleTrace, List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- After `t` edges with `ins` held, bank `s < t` holds the first `s + 1` stages of the layering. -/
theorem pipelined_bank (name : String) (g : StrictOpenHypergraph)
    (hSrc : ∀ e ∈ extractHyperEdges g, ∀ u ∈ e.srcWires, u < g.nodeTypes.length)
    (ins initRegs : Nat → BitVec 64) (t : Nat) :
    ∀ s w, w < g.nodeTypes.length → s < t → s < (layerHypergraph g).length →
      runModuleTrace (compileHypergraphToRtlPipelined name g) initRegs (List.replicate t (false, ins))
          (s * g.nodeTypes.length + w) =
        evalLayeredStagesSyncBv ins ((layerHypergraph g).take (s + 1)) w := by
  have hStageSrc : ∀ stage ∈ layerHypergraph g, ∀ e ∈ stage, ∀ u ∈ e.srcWires, u < g.nodeTypes.length := by
    intro stage hst e he
    apply hSrc
    rw [← layerHyperEdges_flatten (extractHyperEdges g)]
    exact List.mem_flatten.mpr ⟨stage, hst, he⟩
  induction t with
  | zero => intro s w _ hs; exact absurd hs (Nat.not_lt_zero _)
  | succ t ih =>
    intro s w hw hst hsK
    rw [runModuleTrace_replicate_succ, pipelined_step name g ins _ s w hw hsK]
    cases s with
    | zero =>
      simp only [beq_self_eq_true, ↓reduceIte, evalLayeredStagesSyncBv, List.take_succ_eq_append_getElem hsK,
        List.take_zero, List.nil_append, List.foldl_cons, List.foldl_nil]
    | succ s' =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel]
      rw [evalLayeredStagesSyncBv_take_succ ins _ (s' + 1) hsK]
      apply evalWavefrontStageSyncBv_congr g.nodeTypes.length _ _ _
        (hStageSrc _ (List.getElem_mem hsK)) _ w hw
      intro u hu
      exact ih s' u hu (by omega) (by omega)

/-- **`compileHypergraphToRtlPipelined_sound`**: for every scalar open hypergraph whose wires are
below its wire count (every source and every boundary output) and every input, holding the inputs
for one clock edge per wavefront stage from any initial register state, the pipelined module's
output ports show the synchronous layered evaluation of the whole graph. -/
theorem compileHypergraphToRtlPipelined_sound (name : String) (g : StrictOpenHypergraph)
    (hSrc : ∀ e ∈ extractHyperEdges g, ∀ u ∈ e.srcWires, u < g.nodeTypes.length)
    (hOut : ∀ w ∈ g.boundaryOut.table, w < g.nodeTypes.length)
    (ins initRegs : Nat → BitVec 64) :
    (evalModuleOutputs (compileHypergraphToRtlPipelined name g) ins
        (runModuleTrace (compileHypergraphToRtlPipelined name g) initRegs
          (List.replicate (layerHypergraph g).length (false, ins)))).map Prod.snd =
      g.boundaryOut.table.map (evalLayeredStagesSyncBv ins (layerHypergraph g)) := by
  have hOuts : (compileHypergraphToRtlPipelined name g).outputs =
      g.boundaryOut.table.map fun w =>
        ({ name := s!"out_w{w}"
         , expr :=
            if (layerHypergraph g).length == 0 then .inputPort w
            else .regRead (((layerHypergraph g).length - 1) * g.nodeTypes.length + w) } : OutputPort) := rfl
  simp only [evalModuleOutputs]
  rw [hOuts]
  simp only [List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_def]
  cases hK : (layerHypergraph g).length with
  | zero =>
    have hNil : layerHypergraph g = [] := List.eq_nil_of_length_eq_zero hK
    simp only [beq_self_eq_true, ↓reduceIte, evalRtlExpr, hNil, evalLayeredStagesSyncBv, List.foldl_nil]
  | succ K' =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte, evalRtlExpr, Nat.add_sub_cancel]
    rw [← hK, pipelined_bank name g hSrc ins initRegs _ K' w (hOut w hw) (by omega) (by omega)]
    rw [show K' + 1 = (layerHypergraph g).length from hK.symm, List.take_length]

/-! ## 9. Data-Parallel CSR `IndexedCoproduct` Algebra (`FiniteFunction.converse`, `IndexedCoproduct.flatmap`, `operationAdjacencyCsr`, `layerHypergraphCsr`) (`arXiv:2305.01041`) -/

/-- Length of the lookup table of a `FiniteFunction`. -/
def FiniteFunction.length (f : FiniteFunction) : Nat :=
  f.table.length

/-- Evaluate a `FiniteFunction` at domain index `i : Nat`, returning `some (f(i))` when
`i < f.table.length`, or `none` otherwise. -/
def FiniteFunction.eval (f : FiniteFunction) (i : Nat) : Option Nat :=
  f.table[i]?

/-- Number of segments in an `IndexedCoproduct`. -/
def IndexedCoproduct.numSegments (c : IndexedCoproduct) : Nat :=
  c.sizes.table.length

/-- Ordered list of domain indices `offset + k` where `xs[k]? = some w`. -/
def preimageIndicesAux (offset w : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    if x == w then
      offset :: preimageIndicesAux (offset + 1) w xs
    else
      preimageIndicesAux (offset + 1) w xs

/-- Ordered preimage indices $i \in \{0, \dots, |f.\text{table}|-1\}$ mapped to codomain element $w$ by $f$. -/
def FiniteFunction.preimageSegment (f : FiniteFunction) (w : Nat) : List Nat :=
  preimageIndicesAux 0 w f.table

/-- **Relational Converse / Preimage Family (`FiniteFunction.converse`, `arXiv:2305.01041`)**:
Given a finite function $f : \{0, \dots, s-1\} \to \{0, \dots, t-1\}$, computes its relational
converse / preimage family $\sum_{w \in \{0, \dots, t-1\}} f^{-1}(w) \to \{0, \dots, s-1\}$ as a
CSR `IndexedCoproduct` whose `sizes` array has length `t` (`sizes[w] = count of i with f(i) = w`)
and whose flat `values` array lists the preimage indices in ascending order for each $w = 0, \dots, t-1$. -/
def FiniteFunction.converse (f : FiniteFunction) : IndexedCoproduct :=
  IndexedCoproduct.fromSegments f.source
    ((List.range f.target).map (fun w => f.preimageSegment w))

theorem foldl_add_eq_add_sumNatList (acc : Nat) (xs : List Nat) :
    xs.foldl (· + ·) acc = acc + sumNatList xs := by
  induction xs generalizing acc with
  | nil =>
    simp [sumNatList]
  | cons x rest ih =>
    simp only [List.foldl_cons, sumNatList]
    rw [ih (acc + x), ih (0 + x)]
    omega

theorem sumNatList_nil : sumNatList [] = 0 := rfl

theorem sumNatList_cons (x : Nat) (xs : List Nat) :
    sumNatList (x :: xs) = x + sumNatList xs := by
  unfold sumNatList
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_add_eq_add_sumNatList x xs

theorem sumNatList_append (xs ys : List Nat) :
    sumNatList (xs ++ ys) = sumNatList xs + sumNatList ys := by
  induction xs with
  | nil =>
    simp [sumNatList_nil]
  | cons x rest ih =>
    simp only [List.cons_append, sumNatList_cons, ih]
    omega

theorem drop_add_length_append {α : Type} (s : List α) (rest : List α) (n : Nat) :
    (s ++ rest).drop (s.length + n) = rest.drop n := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    change (xs ++ rest).drop (xs.length + n) = rest.drop n
    exact ih

theorem take_length_append {α : Type} (s : List α) (rest : List α) :
    (s ++ rest).take s.length = s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change x :: ((xs ++ rest).take xs.length) = x :: xs
    exact congrArg (x :: ·) ih

theorem segment_fromSegments_aux (segs : List (List Nat)) (k : Nat) :
    (segs.flatten.drop (sumNatList ((segs.map List.length).take k))).take
      ((segs.map List.length).getD k 0) = segs.getD k [] := by
  induction segs generalizing k with
  | nil =>
    simp [List.getD]
  | cons s rest ih =>
    cases k with
    | zero =>
      exact take_length_append s rest.flatten
    | succ k' =>
      change ((s ++ rest.flatten).drop (sumNatList (s.length :: (rest.map List.length).take k'))).take
        ((rest.map List.length).getD k' 0) = rest.getD k' []
      rw [sumNatList_cons, drop_add_length_append]
      exact ih k'

/-- Extracting segment `k` from `IndexedCoproduct.fromSegments numWires segs` returns `segs.getD k []`. -/
theorem segment_fromSegments (numWires : Nat) (segs : List (List Nat)) (k : Nat) :
    (IndexedCoproduct.fromSegments numWires segs).segment k = segs.getD k [] := by
  unfold IndexedCoproduct.fromSegments IndexedCoproduct.segment
  exact segment_fromSegments_aux segs k

theorem getD_map_range {α : Type} (n : Nat) (f : Nat → α) (k : Nat) (d : α) (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp only [List.getD, List.getElem?_map]
  have hRange : (List.range n)[k]? = some k := List.getElem?_range hk
  rw [hRange]
  rfl

theorem getD_of_le_length {α : Type} (xs : List α) (k : Nat) (d : α) (hk : xs.length ≤ k) :
    xs.getD k d = d := by
  simp only [List.getD]
  have hNone : xs[k]? = none := List.getElem?_eq_none hk
  rw [hNone]
  rfl

theorem preimageIndicesAux_length (offset w : Nat) (xs : List Nat) :
    (preimageIndicesAux offset w xs).length = (xs.filter (· == w)).length := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [preimageIndicesAux, List.filter]
    by_cases h : (x == w) = true
    · simp [h, ih (offset + 1)]
    · have hf : (x == w) = false := Bool.eq_false_iff.mpr h
      simp [hf, ih (offset + 1)]

theorem filter_lt_zero_nil (xs : List Nat) :
    xs.filter (fun x => decide (x < 0)) = [] := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [List.filter, ih]

theorem filter_lt_succ_length (xs : List Nat) (t : Nat) :
    (xs.filter (fun x => decide (x < t + 1))).length =
      (xs.filter (fun x => decide (x < t))).length + (xs.filter (· == t)).length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.filter]
    by_cases h1 : x < t
    · have h2 : x < t + 1 := by omega
      have h3 : (x == t) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp [decide_eq_true h1, decide_eq_true h2, h3, ih]
      omega
    · by_cases hEq : x = t
      · subst hEq
        have h2 : x < x + 1 := by omega
        have h3 : (x == x) = true := beq_self_eq_true x
        simp [decide_eq_false h1, decide_eq_true h2, h3, ih]
        omega
      · have h2 : ¬(x < t + 1) := by omega
        have h3 : (x == t) = false := beq_eq_false_iff_ne.mpr hEq
        simp [decide_eq_false h1, decide_eq_false h2, h3, ih]

theorem sum_filter_beq_range (xs : List Nat) (t : Nat) :
    sumNatList ((List.range t).map (fun w => (xs.filter (· == w)).length)) =
      (xs.filter (fun x => decide (x < t))).length := by
  induction t with
  | zero =>
    rw [filter_lt_zero_nil]
    rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, sumNatList_append, ih, filter_lt_succ_length]
    simp [sumNatList_cons, sumNatList_nil]

/-- **Theorem (`converse_wellFormed`)**:
For EVERY `f : FiniteFunction`:
1. `f.converse.sizes.length = f.target` and `f.converse.sizes.table.length = f.target`,
2. `f.converse.numSegments = f.target`, and
3. `sumNatList f.converse.sizes.table = (f.table.filter (· < f.target)).length`! -/
theorem converse_wellFormed (f : FiniteFunction) :
    f.converse.sizes.length = f.target ∧
    f.converse.sizes.table.length = f.target ∧
    f.converse.numSegments = f.target ∧
    sumNatList f.converse.sizes.table = (f.table.filter (fun y => decide (y < f.target))).length := by
  have hLen : f.converse.sizes.table.length = f.target := by
    simp [FiniteFunction.converse, IndexedCoproduct.fromSegments]
  refine ⟨hLen, hLen, hLen, ?_⟩
  dsimp only [FiniteFunction.converse, IndexedCoproduct.fromSegments]
  rw [List.map_map]
  have hMap :
      List.map (List.length ∘ fun w => f.preimageSegment w) (List.range f.target) =
        (List.range f.target).map (fun w => (f.table.filter (· == w)).length) := by
    apply List.map_congr_left
    intro w _
    exact preimageIndicesAux_length 0 w f.table
  rw [hMap]
  exact sum_filter_beq_range f.table f.target

theorem mem_preimageIndicesAux_ge (offset w i : Nat) (xs : List Nat)
    (hMem : i ∈ preimageIndicesAux offset w xs) :
    offset ≤ i := by
  induction xs generalizing offset with
  | nil =>
    cases hMem
  | cons x rest ih =>
    dsimp only [preimageIndicesAux] at hMem
    split at hMem
    · cases List.mem_cons.mp hMem with
      | inl hEq => omega
      | inr hRest =>
        have hGe := ih (offset + 1) hRest
        omega
    · have hGe := ih (offset + 1) hMem
      omega

theorem mem_preimageIndicesAux_iff (offset w i : Nat) (xs : List Nat) :
    i ∈ preimageIndicesAux offset w xs ↔ offset ≤ i ∧ xs[i - offset]? = some w := by
  induction xs generalizing offset with
  | nil =>
    simp [preimageIndicesAux]
  | cons x rest ih =>
    dsimp only [preimageIndicesAux]
    by_cases hLt : i < offset
    · constructor
      · intro hMem
        have hGe := mem_preimageIndicesAux_ge offset w i (x :: rest) hMem
        omega
      · rintro ⟨hGe, _⟩
        omega
    · by_cases hEq : i = offset
      · subst hEq
        have hSub : i - i = 0 := Nat.sub_self i
        rw [hSub]
        change i ∈ (if x == w then i :: preimageIndicesAux (i + 1) w rest else preimageIndicesAux (i + 1) w rest) ↔
          i ≤ i ∧ some x = some w
        by_cases hxw : (x == w) = true
        · have hxEq : x = w := beq_iff_eq.mp hxw
          simp [hxEq]
        · have hxf : (x == w) = false := Bool.eq_false_iff.mpr hxw
          have hxNe : x ≠ w := beq_eq_false_iff_ne.mp hxf
          simp only [hxf, Bool.false_eq_true, ↓reduceIte, Nat.le_refl, true_and, Option.some.injEq]
          constructor
          · intro hMem
            have hGe := mem_preimageIndicesAux_ge (i + 1) w i rest hMem
            omega
          · intro hContra
            exact absurd hContra hxNe
      · have hGt : offset + 1 ≤ i := by omega
        have hNe : i ≠ offset := hEq
        have hMemStep :
            i ∈ (if x == w then offset :: preimageIndicesAux (offset + 1) w rest else preimageIndicesAux (offset + 1) w rest) ↔
              i ∈ preimageIndicesAux (offset + 1) w rest := by
          by_cases hxw : (x == w) = true
          · simp [hxw, hNe]
          · have hxf : (x == w) = false := Bool.eq_false_iff.mpr hxw
            simp [hxf]
        rw [hMemStep, ih (offset + 1)]
        have hSubSucc : i - offset = (i - (offset + 1)) + 1 := by omega
        rw [hSubSucc]
        change (offset + 1 ≤ i ∧ rest[i - (offset + 1)]? = some w) ↔
          (offset ≤ i ∧ rest[i - (offset + 1)]? = some w)
        constructor
        · rintro ⟨_, hSome⟩
          exact ⟨by omega, hSome⟩
        · rintro ⟨_, hSome⟩
          exact ⟨hGt, hSome⟩

/-- **Theorem (`mem_converse_segment_iff`)**:
For any `f : FiniteFunction`, codomain element $w < f.\text{target}$, and domain index $i$
(including all $i < f.\text{source}$), $i$ appears in segment $w$ of `f.converse`
**if and only if** `f.eval i = some w`! -/
theorem mem_converse_segment_iff (f : FiniteFunction) (w i : Nat) (hw : w < f.target) :
    i ∈ f.converse.segment w ↔ f.eval i = some w := by
  unfold FiniteFunction.converse
  rw [segment_fromSegments, getD_map_range f.target (fun u => f.preimageSegment u) w [] hw]
  unfold FiniteFunction.preimageSegment FiniteFunction.eval
  rw [mem_preimageIndicesAux_iff 0 w i f.table]
  simp

/-- **CSR Segmented `IndexedCoproduct.flatmap` (`arXiv:2305.01041`)**:
Given a segmented CSR array `c` with values in $\{0, \dots, \text{sub.numSegments}-1\}$, replaces
each element $w$ in segment $e$ of `c` with the entire segment `sub.segment w`, producing a new
CSR `IndexedCoproduct` with `c.sizes.length` segments over codomain `sub.values.target`. -/
def IndexedCoproduct.flatmap (c : IndexedCoproduct) (sub : IndexedCoproduct) : IndexedCoproduct :=
  IndexedCoproduct.fromSegments sub.values.target
    ((List.range c.sizes.table.length).map (fun e =>
      ((c.segment e).map (fun w => sub.segment w)).flatten))

/-- **Theorem (`flatmap_numSegments`)**:
For EVERY pair of CSR `IndexedCoproduct`s `c` and `sub`, `c.flatmap sub` preserves the exact
number of segments:
`(c.flatmap sub).sizes.length = c.sizes.length` and `(c.flatmap sub).numSegments = c.numSegments`. -/
theorem flatmap_numSegments (c sub : IndexedCoproduct) :
    (c.flatmap sub).sizes.length = c.sizes.length ∧
    (c.flatmap sub).sizes.table.length = c.sizes.table.length ∧
    (c.flatmap sub).numSegments = c.numSegments := by
  simp [IndexedCoproduct.flatmap, IndexedCoproduct.fromSegments,
    FiniteFunction.length, IndexedCoproduct.numSegments]

theorem segment_flatmap_eq (c sub : IndexedCoproduct) (e : Nat) :
    (c.flatmap sub).segment e = ((c.segment e).map (fun w => sub.segment w)).flatten := by
  unfold IndexedCoproduct.flatmap
  rw [segment_fromSegments]
  by_cases he : e < c.sizes.table.length
  · exact getD_map_range c.sizes.table.length
      (fun u => ((c.segment u).map (fun w => sub.segment w)).flatten) e [] he
  · have hLe : c.sizes.table.length ≤ e := by omega
    have hMapLe : ((List.range c.sizes.table.length).map
        (fun u => ((c.segment u).map (fun w => sub.segment w)).flatten)).length ≤ e := by
      simp [hLe]
    rw [getD_of_le_length _ e [] hMapLe]
    have hSegEmpty : c.segment e = [] := by
      unfold IndexedCoproduct.segment
      rw [getD_of_le_length c.sizes.table e 0 hLe]
      rfl
    rw [hSegEmpty]
    rfl

/-- **Theorem (`mem_flatmap_segment_iff`)**:
For EVERY pair of CSR `IndexedCoproduct`s `c, sub` and EVERY segment index `e` and value `j`:
$$j \in (c.\text{flatmap } \text{sub}).\text{segment } e \iff \exists w \in c.\text{segment } e,\; j \in \text{sub.segment } w.$$ -/
theorem mem_flatmap_segment_iff (c sub : IndexedCoproduct) (e j : Nat) :
    j ∈ (c.flatmap sub).segment e ↔ ∃ w ∈ c.segment e, j ∈ sub.segment w := by
  rw [segment_flatmap_eq, List.mem_flatten]
  simp only [List.mem_map]
  constructor
  · rintro ⟨l, ⟨w, hw, rfl⟩, hj⟩
    exact ⟨w, hw, hj⟩
  · rintro ⟨w, hw, hj⟩
    exact ⟨sub.segment w, ⟨w, hw, rfl⟩, hj⟩

/-- CSR segmented array mapping each hyperedge index $e \in \{0, \dots, |E|-1\}$ to its source wires. -/
def sourcesCsr (numWires : Nat) (edges : List HyperEdge) : IndexedCoproduct :=
  IndexedCoproduct.fromSegments numWires (edges.map (·.srcWires))

/-- CSR segmented array mapping each hyperedge index $e \in \{0, \dots, |E|-1\}$ to its target wire(s). -/
def targetsCsr (numWires : Nat) (edges : List HyperEdge) : IndexedCoproduct :=
  IndexedCoproduct.fromSegments numWires (edges.map (fun e => [e.dstWire]))

/-- Flat port-to-hyperedge owner table mapping each flat input port $p \in \sum_e |e.\text{srcWires}|$
to the index $e \in \{0, \dots, |E|-1\}$ of its owning consumer hyperedge. -/
def sourcePortOwnerTable (edges : List HyperEdge) : List Nat :=
  (edges.zipIdx.map (fun (e, idx) => List.replicate e.srcWires.length idx)).flatten

/-- CSR `IndexedCoproduct` mapping each wire $w \in \{0, \dots, \text{numWires}-1\}$ to the producer
hyperedges $e_1$ that write $w$, computed directly as `(targetsCsr numWires edges).values.converse`. -/
def wireProducersCsr (numWires : Nat) (edges : List HyperEdge) : IndexedCoproduct :=
  (targetsCsr numWires edges).values.converse

/-- CSR `IndexedCoproduct` mapping each wire $w \in \{0, \dots, \text{numWires}-1\}$ to the consumer
hyperedges $e_2$ that read $w$, computed by composing `(sourcesCsr numWires edges).values.converse`
with `sourcePortOwnerTable edges`. -/
def wireConsumersCsr (numWires : Nat) (edges : List HyperEdge) : IndexedCoproduct :=
  let portConv := (sourcesCsr numWires edges).values.converse
  { sizes  := portConv.sizes
  , values :=
      { source := portConv.values.source
      , target := edges.length
      , table  := portConv.values.table.map (fun p => (sourcePortOwnerTable edges).getD p 0) } }

/-- **CSR Operation Predecessor Table (`operationPredecessorsCsr`)**:
Maps each consumer hyperedge $e_2$ to the flat segment of producer hyperedges $e_1$ that write a
wire read by $e_2$, computed via `IndexedCoproduct.flatmap` and `FiniteFunction.converse`:
`(sourcesCsr numWires edges).flatmap (wireProducersCsr numWires edges)`. -/
def operationPredecessorsCsr (numWires : Nat) (edges : List HyperEdge) : IndexedCoproduct :=
  (sourcesCsr numWires edges).flatmap (wireProducersCsr numWires edges)

/-- **CSR Operation Adjacency Table (`operationAdjacencyCsr`)**:
Maps each producer hyperedge $e_1$ to the flat segment of consumer hyperedges $e_2$ that read a
wire written by $e_1$, computed via `IndexedCoproduct.flatmap` and `FiniteFunction.converse`:
`(targetsCsr numWires edges).flatmap (wireConsumersCsr numWires edges)`. -/
def operationAdjacencyCsr (numWires : Nat) (edges : List HyperEdge) : IndexedCoproduct :=
  (targetsCsr numWires edges).flatmap (wireConsumersCsr numWires edges)

theorem drop_map_eq {α β : Type} (f : α → β) (xs : List α) (n : Nat) :
    (xs.map f).drop n = (xs.drop n).map f := by
  induction xs generalizing n with
  | nil =>
    cases n <;> rfl
  | cons x rest ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

theorem take_map_eq {α β : Type} (f : α → β) (xs : List α) (n : Nat) :
    (xs.map f).take n = (xs.take n).map f := by
  induction xs generalizing n with
  | nil =>
    cases n <;> rfl
  | cons x rest ih =>
    cases n with
    | zero => rfl
    | succ k =>
      change f x :: ((rest.map f).take k) = f x :: ((rest.take k).map f)
      exact congrArg (f x :: ·) (ih k)

theorem segment_wireConsumersCsr (numWires : Nat) (edges : List HyperEdge) (w : Nat) :
    (wireConsumersCsr numWires edges).segment w =
      (((sourcesCsr numWires edges).values.converse).segment w).map
        (fun p => (sourcePortOwnerTable edges).getD p 0) := by
  unfold wireConsumersCsr IndexedCoproduct.segment
  dsimp only
  rw [drop_map_eq, take_map_eq]

/-- **Theorem (`operationAdjacencyCsr_sound`)**:
1. **Universal CSR Producer-to-Consumer Adjacency Characterization**:
   For EVERY `numWires : Nat`, `edges : List HyperEdge`, and hyperedge indices `e1, e2 : Nat`,
   $e_2 \in (\text{operationAdjacencyCsr numWires edges}).\text{segment } e_1$ iff there exists a
   written wire $w \in (\text{targetsCsr numWires edges}).\text{segment } e_1$ and a flat input
   port $p \in ((\text{sourcesCsr numWires edges}).\text{values.converse}).\text{segment } w$
   owned by $e_2$ (`(sourcePortOwnerTable edges).getD p 0 = e2`).
2. **Universal CSR Consumer-to-Producer Predecessor Characterization**:
   For EVERY `numWires : Nat`, `edges : List HyperEdge`, and `e1, e2 : Nat`,
   $e_1 \in (\text{operationPredecessorsCsr numWires edges}).\text{segment } e_2$ iff there exists a
   source wire $w \in (\text{sourcesCsr numWires edges}).\text{segment } e_2$ such that
   $e_1 \in ((\text{targetsCsr numWires edges}).\text{values.converse}).\text{segment } w$.
3. **Concrete Kernel Verification on `goldenDiamondHypergraph`**:
   `operationAdjacencyCsr` and `operationPredecessorsCsr` recover the exact diamond DAG adjacency
   (`0 → [2]`, `1 → [2]`, `2 → [4]`, `3 → [4]`, `4 → []`) and predecessor segments
   (`0 ← []`, `1 ← []`, `2 ← [0, 1]`, `3 ← []`, `4 ← [2, 3]`)! -/
theorem operationAdjacencyCsr_sound
    (numWires : Nat) (edges : List HyperEdge) (e1 e2 : Nat) :
    (e2 ∈ (operationAdjacencyCsr numWires edges).segment e1 ↔
      ∃ w ∈ (targetsCsr numWires edges).segment e1,
        ∃ p ∈ ((sourcesCsr numWires edges).values.converse).segment w,
          (sourcePortOwnerTable edges).getD p 0 = e2) ∧
    (e1 ∈ (operationPredecessorsCsr numWires edges).segment e2 ↔
      ∃ w ∈ (sourcesCsr numWires edges).segment e2,
        e1 ∈ ((targetsCsr numWires edges).values.converse).segment w) ∧
    (let dEdges := extractHyperEdges goldenDiamondHypergraph
     let adj := operationAdjacencyCsr 9 dEdges
     let preds := operationPredecessorsCsr 9 dEdges
     [adj.segment 0, adj.segment 1, adj.segment 2, adj.segment 3, adj.segment 4] =
       [[2], [2], [4], [4], []] ∧
     [preds.segment 0, preds.segment 1, preds.segment 2, preds.segment 3, preds.segment 4] =
       [[], [], [0, 1], [], [2, 3]]) := by
  have hAdj :
      e2 ∈ (operationAdjacencyCsr numWires edges).segment e1 ↔
        ∃ w ∈ (targetsCsr numWires edges).segment e1,
          ∃ p ∈ ((sourcesCsr numWires edges).values.converse).segment w,
            (sourcePortOwnerTable edges).getD p 0 = e2 := by
    unfold operationAdjacencyCsr
    rw [mem_flatmap_segment_iff]
    constructor
    · rintro ⟨w, hw, he2⟩
      rw [segment_wireConsumersCsr, List.mem_map] at he2
      rcases he2 with ⟨p, hp, rfl⟩
      exact ⟨w, hw, p, hp, rfl⟩
    · rintro ⟨w, hw, p, hp, rfl⟩
      refine ⟨w, hw, ?_⟩
      rw [segment_wireConsumersCsr, List.mem_map]
      exact ⟨p, hp, rfl⟩
  have hPreds :
      e1 ∈ (operationPredecessorsCsr numWires edges).segment e2 ↔
        ∃ w ∈ (sourcesCsr numWires edges).segment e2,
          e1 ∈ ((targetsCsr numWires edges).values.converse).segment w := by
    unfold operationPredecessorsCsr wireProducersCsr
    exact mem_flatmap_segment_iff (sourcesCsr numWires edges) ((targetsCsr numWires edges).values.converse) e2 e1
  refine ⟨hAdj, hPreds, by decide +kernel⟩

/-- Check whether hyperedge `idx` has all its CSR producer hyperedges already in `scheduled`. -/
def csrEdgeReady (predsCsr : IndexedCoproduct) (scheduled : List Nat) (idx : Nat) : Bool :=
  (predsCsr.segment idx).all (fun p => (p == idx) || scheduled.contains p)

/-- Filter ready frontier edges into a conflict-free parallel wavefront stage (`picked`) and
remaining deferred edges (`deferred`), guaranteeing `checkStageIndependent (picked.map Prod.fst) = true`. -/
def filterIndependentWavefront :
    List (HyperEdge × Nat) → List (HyperEdge × Nat) × List (HyperEdge × Nat)
  | [] => ([], [])
  | (e, idx) :: rest =>
    let (picked, deferred) := filterIndependentWavefront rest
    if edgeIndependentOfStage e (picked.map Prod.fst) then
      ((e, idx) :: picked, deferred)
    else
      (picked, (e, idx) :: deferred)

/-- Peel one parallel CSR wavefront stage from `remaining` unscheduled hyperedges:
all unscheduled edges whose CSR producer edges are already scheduled (and that have no WAW/WAR
hazard with earlier unscheduled edges) fire simultaneously in the current wavefront. -/
def peelCsrWavefrontStage
    (predsCsr : IndexedCoproduct)
    (scheduled : List Nat)
    (remaining : List (HyperEdge × Nat)) :
    List HyperEdge × List Nat × List (HyperEdge × Nat) :=
  let (readyRaw, blocked) :=
    remaining.partition (fun (e, idx) =>
      csrEdgeReady predsCsr scheduled idx &&
      edgeIndependentOfStage e ((remaining.takeWhile (fun (_, j) => j != idx)).map Prod.fst))
  let (picked, deferred) := filterIndependentWavefront readyRaw
  match picked with
  | [] =>
    match remaining with
    | [] => ([], scheduled, [])
    | (e, idx) :: rest => ([e], idx :: scheduled, rest)
  | _ =>
    (picked.map Prod.fst, (picked.map Prod.snd) ++ scheduled, deferred ++ blocked)

/-- Fuel-bounded CSR parallel frontier-peeling loop. -/
def layerHyperEdgesCsrAux
    (predsCsr : IndexedCoproduct)
    (scheduled : List Nat) :
    Nat → List (HyperEdge × Nat) → List (List HyperEdge)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, remaining@(_ :: _) =>
    let (stage, scheduled', remaining') := peelCsrWavefrontStage predsCsr scheduled remaining
    stage :: layerHyperEdgesCsrAux predsCsr scheduled' fuel remaining'

/-- Compute wavefront stages from CSR producer/in-degree tables by parallel frontier peeling. -/
def layerHyperEdgesCsr (numWires : Nat) (edges : List HyperEdge) : List (List HyperEdge) :=
  let predsCsr := operationPredecessorsCsr numWires edges
  layerHyperEdgesCsrAux predsCsr [] edges.length edges.zipIdx

/-- **Data-Parallel CSR Wavefront Layering (`layerHypergraphCsr`)**:
Computes synchronous wavefront stages from the CSR in-degree/producer tables
(`operationPredecessorsCsr`) by parallel frontier peeling. -/
def layerHypergraphCsr (g : StrictOpenHypergraph) : List (List HyperEdge) :=
  layerHyperEdgesCsr g.nodeTypes.length (extractHyperEdges g)

/-- Evaluate a `StrictOpenHypergraph` stage-by-stage using CSR wavefront layering (`layerHypergraphCsr`). -/
def evalHypergraphLayeredCsr (g : StrictOpenHypergraph) (initEnv : Nat → Int) : List Int :=
  let finalEnv := evalLayeredStages initEnv (layerHypergraphCsr g)
  g.boundaryOut.table.map finalEnv

/-- Evaluate a `StrictOpenHypergraph` stage-by-stage using CSR wavefront layering and true
synchronous stage-entry register snapshots (`evalLayeredStagesSync`). -/
def evalHypergraphLayeredCsrSync (g : StrictOpenHypergraph) (initEnv : Nat → Int) : List Int :=
  let finalEnv := evalLayeredStagesSync initEnv (layerHypergraphCsr g)
  g.boundaryOut.table.map finalEnv

theorem filterIndependentWavefront_independent (xs : List (HyperEdge × Nat)) :
    checkStageIndependent ((filterIndependentWavefront xs).1.map Prod.fst) = true := by
  induction xs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨e, idx⟩
    dsimp only [filterIndependentWavefront]
    by_cases hInd : edgeIndependentOfStage e ((filterIndependentWavefront rest).1.map Prod.fst) = true
    · simp [hInd, checkStageIndependent, ih]
    · simp [hInd, ih]

theorem peelCsrWavefrontStage_independent
    (predsCsr : IndexedCoproduct)
    (scheduled : List Nat)
    (remaining : List (HyperEdge × Nat)) :
    checkStageIndependent (peelCsrWavefrontStage predsCsr scheduled remaining).1 = true := by
  unfold peelCsrWavefrontStage
  dsimp only
  have hFilt := filterIndependentWavefront_independent
    ((remaining.partition (fun (e, idx) =>
      csrEdgeReady predsCsr scheduled idx &&
      edgeIndependentOfStage e ((remaining.takeWhile (fun (_, j) => j != idx)).map Prod.fst))).1)
  cases hPicked : (filterIndependentWavefront
    ((remaining.partition (fun (e, idx) =>
      csrEdgeReady predsCsr scheduled idx &&
      edgeIndependentOfStage e ((remaining.takeWhile (fun (_, j) => j != idx)).map Prod.fst))).1)).1 with
  | nil =>
    cases remaining with
    | nil => rfl
    | cons hd tl =>
      rcases hd with ⟨e, idx⟩
      rfl
  | cons p ps =>
    rw [hPicked] at hFilt
    exact hFilt

theorem layerHyperEdgesCsrAux_all_independent
    (predsCsr : IndexedCoproduct)
    (scheduled : List Nat)
    (fuel : Nat)
    (remaining : List (HyperEdge × Nat)) :
    (layerHyperEdgesCsrAux predsCsr scheduled fuel remaining).all checkStageIndependent = true := by
  induction fuel generalizing scheduled remaining with
  | zero => rfl
  | succ k ih =>
    cases remaining with
    | nil => rfl
    | cons hd tl =>
      dsimp only [layerHyperEdgesCsrAux, List.all_cons]
      rw [peelCsrWavefrontStage_independent, Bool.true_and]
      exact ih _ _

/-- **Theorem (`layerHypergraphCsr_sound_and_agrees`)**:
1. **Universal CSR Wavefront Stage Independence & Synchronous Equivalence**:
   For EVERY `StrictOpenHypergraph` `g` and EVERY initial wire environment `initEnv : Nat → Int`:
   - Every wavefront stage produced by `layerHypergraphCsr g` is conflict-free
     (`(layerHypergraphCsr g).all checkStageIndependent = true`),
   - True synchronous stage-entry snapshot evaluation (`evalLayeredStagesSync initEnv (layerHypergraphCsr g)`)
     equals sequential stage evaluation (`evalLayeredStages initEnv (layerHypergraphCsr g)`), and
   - `evalHypergraphLayeredCsrSync g initEnv = evalHypergraphLayeredCsr g initEnv`.
2. **Symbolic & Concrete Agreement with `layerHypergraph` and `evalHypergraphComb` on `goldenDiamondHypergraph`
   and Multi-Stage Reverse-AD Pipelines (`compileGraphAdjoint goldenDiamondHypergraph`)**:
   - On `goldenDiamondHypergraph`, `layerHypergraphCsr` peels 3 wavefront stages of sizes `[3, 1, 1]`
     (coalescing `op 0`, `op 1`, and constant `op 3` into Wavefront 0), and for EVERY symbolic environment
     `initEnv : Nat → Int`:
     `evalHypergraphLayeredCsr goldenDiamondHypergraph initEnv = evalHypergraphLayered goldenDiamondHypergraph initEnv`
     and `evalHypergraphLayeredCsr goldenDiamondHypergraph initEnv = evalHypergraphComb goldenDiamondHypergraph initEnv`!
   - On the 12-operation multi-stage reverse-mode AD pipeline `compileGraphAdjoint goldenDiamondHypergraph`,
     `evalHypergraphLayeredCsr` and `evalHypergraphLayeredCsrSync` agree with `evalHypergraphLayered`
     and `evalHypergraphComb` (`[87, 11, 11, 7, 7]`)! -/
theorem layerHypergraphCsr_sound_and_agrees
    (g : StrictOpenHypergraph) (initEnv : Nat → Int) :
    let diamondEnv : Nat → Int := fun w =>
      match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 9 => 1 | _ => 0
    (layerHypergraphCsr g).all checkStageIndependent = true ∧
    evalLayeredStagesSync initEnv (layerHypergraphCsr g) =
      evalLayeredStages initEnv (layerHypergraphCsr g) ∧
    evalHypergraphLayeredCsrSync g initEnv =
      evalHypergraphLayeredCsr g initEnv ∧
    ((layerHypergraphCsr goldenDiamondHypergraph).map List.length = [3, 1, 1]) ∧
    evalHypergraphLayeredCsr goldenDiamondHypergraph initEnv =
      evalHypergraphLayered goldenDiamondHypergraph initEnv ∧
    evalHypergraphLayeredCsr goldenDiamondHypergraph initEnv =
      evalHypergraphComb goldenDiamondHypergraph initEnv ∧
    evalHypergraphLayeredCsr (compileGraphAdjoint goldenDiamondHypergraph) diamondEnv =
      evalHypergraphComb (compileGraphAdjoint goldenDiamondHypergraph) diamondEnv ∧
    evalHypergraphLayeredCsrSync (compileGraphAdjoint goldenDiamondHypergraph) diamondEnv =
      [87, 11, 11, 7, 7] := by
  have hInd : (layerHypergraphCsr g).all checkStageIndependent = true :=
    layerHyperEdgesCsrAux_all_independent _ [] _ _
  have hSync :
      evalLayeredStagesSync initEnv (layerHypergraphCsr g) =
        evalLayeredStages initEnv (layerHypergraphCsr g) :=
    evalLayeredStagesSync_eq_evalLayeredStages initEnv (layerHypergraphCsr g) hInd
  have hOutSync :
      evalHypergraphLayeredCsrSync g initEnv = evalHypergraphLayeredCsr g initEnv := by
    unfold evalHypergraphLayeredCsrSync evalHypergraphLayeredCsr
    rw [hSync]
  have hDiamondComb :
      evalHypergraphLayeredCsr goldenDiamondHypergraph initEnv =
        evalHypergraphComb goldenDiamondHypergraph initEnv := rfl
  have hDiamondLay :
      evalHypergraphLayeredCsr goldenDiamondHypergraph initEnv =
        evalHypergraphLayered goldenDiamondHypergraph initEnv := rfl
  refine ⟨hInd, hSync, hOutSync, by decide +kernel, hDiamondLay, hDiamondComb, by decide +kernel, by decide +kernel⟩

end Obend.Hardware.OpenHypergraph
end

