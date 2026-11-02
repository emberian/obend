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

/-- Theorem (`finiteFunction_twist_involution_2_3`):
Composing the symmetric braiding `twist 2 3` with `twist 3 2` recovers `FiniteFunction.id 5`. -/
theorem finiteFunction_twist_involution_2_3 :
    FiniteFunction.comp (FiniteFunction.twist 2 3) (FiniteFunction.twist 3 2) =
      some (FiniteFunction.id 5) := by
  decide +kernel

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

/-- Extract the ordered list of `HyperEdge`s from a `StrictOpenHypergraph`. -/
def extractHyperEdges (g : StrictOpenHypergraph) : List HyperEdge :=
  (List.range g.ops.length).map fun idx =>
    { opIdx    := idx
    , op       := g.ops.getD idx (.const 0)
    , srcWires := g.sources.segment idx
    , dstWire  := (g.targets.segment idx).getD 0 0 }

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

/-- Lower a `HypergraphOp` with source wire indices `srcWires` directly to an `Obend.Hardware.HDL.RtlExpr`. -/
def compileHypergraphOpToRtl (op : HypergraphOp) (srcWires : List Nat) : RtlExpr :=
  let w (i : Nat) : RtlExpr := .inputPort (srcWires.getD i 0)
  match op with
  | .const v => .const (BitVec.ofInt 64 v)
  | .add     => .alu .add (w 0) (w 1)
  | .sub     => .alu .sub (w 0) (w 1)
  | .mul     => .alu .mul (w 0) (w 1)
  | .scale k => .alu .mul (.const (BitVec.ofInt 64 k)) (w 0)
  | .mac     => .alu .add (.alu .mul (w 0) (w 1)) (w 2)
  | .mux     => .mux (w 0) (w 1) (w 2)

/-- **Theorem (`compileHypergraphOpToRtl_sound`)**:
For EVERY `op : HypergraphOp` and source wire triple `(w0, w1, w2 : Nat)`, evaluating the lowered
`RtlExpr` `compileHypergraphOpToRtl op [w0, w1, w2]` via `Obend.Hardware.HDL.evalRtlExpr` produces
the exact same 64-bit value as `evalHypergraphOpBv op [inputs w0, inputs w1, inputs w2]`. -/
theorem compileHypergraphOpToRtl_sound
    (op : HypergraphOp) (w0 w1 w2 : Nat)
    (inputs wires regs : Nat → BitVec 64) :
    evalRtlExpr inputs wires regs (compileHypergraphOpToRtl op [w0, w1, w2]) =
      evalHypergraphOpBv op [inputs w0, inputs w1, inputs w2] := by
  cases op <;> rfl

/-- Lower a `HypergraphOp` reading from internal combinational hypergraph wires (`.wireRef`)
to an `Obend.Hardware.HDL.RtlExpr`. -/
def compileHypergraphWireOpToRtl (op : HypergraphOp) (srcWires : List Nat) : RtlExpr :=
  let w (i : Nat) : RtlExpr := .wireRef (srcWires.getD i 0)
  match op with
  | .const v => .const (BitVec.ofInt 64 v)
  | .add     => .alu .add (w 0) (w 1)
  | .sub     => .alu .sub (w 0) (w 1)
  | .mul     => .alu .mul (w 0) (w 1)
  | .scale k => .alu .mul (.const (BitVec.ofInt 64 k)) (w 0)
  | .mac     => .alu .add (.alu .mul (w 0) (w 1)) (w 2)
  | .mux     => .mux (w 0) (w 1) (w 2)

/-- **Theorem (`compileHypergraphWireOpToRtl_sound`)**:
Evaluating `compileHypergraphWireOpToRtl op [w0, w1, w2]` over internal combinational wire nets
`wires` produces `evalHypergraphOpBv op [wires w0, wires w1, wires w2]`. -/
theorem compileHypergraphWireOpToRtl_sound
    (op : HypergraphOp) (w0 w1 w2 : Nat)
    (inputs wires regs : Nat → BitVec 64) :
    evalRtlExpr inputs wires regs (compileHypergraphWireOpToRtl op [w0, w1, w2]) =
      evalHypergraphOpBv op [wires w0, wires w1, wires w2] := by
  cases op <;> rfl

/-- Lower an entire `StrictOpenHypergraph` into a complete `Obend.Hardware.HDL.RtlModule`
where open input boundary wires are bound from `inputNames`, each `HyperEdge` in `extractHyperEdges g`
defines a topological `WireAssign` in `wires`, and open output boundary wires drive `outputs`. -/
def compileHypergraphToRtl (name : String) (g : StrictOpenHypergraph) : RtlModule where
  name       := name
  inputNames := g.boundaryIn.table.map (fun w => s!"in_w{w}")
  wires      :=
    (g.boundaryIn.table.zipIdx.map (fun (w, idx) =>
      { wireIdx := w, name := s!"w_{w}", expr := RtlExpr.inputPort idx })) ++
    ((extractHyperEdges g).map (fun e =>
      { wireIdx := e.dstWire, name := s!"w_{e.dstWire}", expr := compileHypergraphWireOpToRtl e.op e.srcWires }))
  regs       := []
  outputs    := g.boundaryOut.table.map (fun w => { name := s!"out_w{w}", expr := RtlExpr.wireRef w })

end Obend.Hardware.OpenHypergraph
end
