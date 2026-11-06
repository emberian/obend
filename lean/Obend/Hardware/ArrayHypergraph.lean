module
/-
# Obend.Hardware.ArrayHypergraph — open hypergraphs whose wires carry arrays

The scalar `StrictOpenHypergraph` of `Obend.Hardware.OpenHypergraph` has one 64-bit word per wire and
one operation per hyperedge. On a GPU that is one thread per hyperedge, a gate and not a computation.
Here a wire carries a vector of words and a hyperedge is one array operation: an elementwise map of a
scalar operation (every element a thread), a gather along a `FiniteFunction` (Wilson–Zanasi's
data-parallel permutation datum, `arXiv:2305.01041`), a concatenation, or a constant array. The
wavefront layering and its theorems are the scalar ones restated over array environments: a stage's
operations are pairwise independent, and the synchronous stage-by-stage evaluation equals the
single-pass combinational one.

The scalar graphs are the one-element instance: `ofScalar` maps every hyperedge to the elementwise map
of its operation over length-one wires, and `ofScalar_layered_sound` says the array evaluation of the
image is the scalar 64-bit evaluation (`evalLayeredStagesSyncBv`), wire by wire as a singleton. That is
the sense in which shape-indexed wires generalize the scalar language rather than sit beside it.

Elementwise operations are the scalar `HypergraphOp`s plus the bit operations a Goldilocks field
multiply needs (`Obend.Apps.ZkNtt.glMul`): unsigned comparison, and, or, logical shifts. All arithmetic
is modulo `2^64`, as `BitVec 64` and WGSL `i64` are.
-/
public import Obend.Hardware.OpenHypergraph
@[expose] public section

namespace Obend.Hardware.ArrayHypergraph
open Obend.Hardware.OpenHypergraph
set_option autoImplicit false

abbrev Word := BitVec 64
abbrev Vec := List Word

/-! ## 1. Operations -/

/-- One element's operation: a scalar `HypergraphOp`, or a bit operation. Operands are elements of the
source wires at the same index; a missing operand is `0`, as in `evalHypergraphOpBv`. -/
inductive ElemOp where
  | scalar (op : HypergraphOp)
  | ult
  | band
  | bor
  | shr
  | shl
  deriving DecidableEq, Repr

def evalElemOp (op : ElemOp) (args : List Word) : Word :=
  let a0 := args.getD 0 0#64
  let a1 := args.getD 1 0#64
  match op with
  | .scalar o => evalHypergraphOpBv o args
  | .ult      => if BitVec.ult a0 a1 then 1#64 else 0#64
  | .band     => a0 &&& a1
  | .bor      => a0 ||| a1
  | .shr      => a0 >>> a1.toNat
  | .shl      => a0 <<< a1.toNat

/-- One hyperedge's operation on whole wires. -/
inductive ArrayOp where
  /-- `n` elements, element `e` is `op` of the sources' elements `e`. -/
  | map (n : Nat) (op : ElemOp)
  /-- element `e` is element `f.table[e]` of the one source; length `f.source`. -/
  | gather (f : FiniteFunction)
  /-- the first source followed by the second. -/
  | concat
  /-- a constant array. -/
  | const (vals : Vec)
  deriving DecidableEq, Repr

def evalArrayOp (op : ArrayOp) (args : List Vec) : Vec :=
  match op with
  | .map n o   => (List.range n).map fun e => evalElemOp o (args.map fun a => a.getD e 0#64)
  | .gather f  => f.table.map fun i => (args.getD 0 []).getD i 0#64
  | .concat    => args.getD 0 [] ++ args.getD 1 []
  | .const vs  => vs

/-- The length an operation's result has, from the operation alone or its sources' lengths. -/
def ArrayOp.outLen (op : ArrayOp) (srcLens : List Nat) : Nat :=
  match op with
  | .map n _  => n
  | .gather f => f.source
  | .concat   => srcLens.getD 0 0 + srcLens.getD 1 0
  | .const vs => vs.length

theorem evalArrayOp_length (op : ArrayOp) (args : List Vec) (hf : ∀ f, op = .gather f → f.wf = true) :
    (evalArrayOp op args).length = op.outLen (args.map List.length) := by
  cases op with
  | map n o => simp [evalArrayOp, ArrayOp.outLen]
  | gather f =>
    have h := hf f rfl
    simp only [FiniteFunction.wf, Bool.and_eq_true, beq_iff_eq] at h
    simp [evalArrayOp, ArrayOp.outLen, h.1]
  | concat =>
    simp only [evalArrayOp, ArrayOp.outLen, List.length_append]
    cases args with
    | nil => rfl
    | cons a rest => cases rest <;> simp
  | const vs => simp [evalArrayOp, ArrayOp.outLen]

/-! ## 2. Graphs -/

structure ArrayEdge where
  opIdx    : Nat
  op       : ArrayOp
  srcWires : List Nat
  dstWire  : Nat
  deriving DecidableEq, Repr

/-- `lengths w` is the declared length of wire `w`; `inputs` and `outputs` the boundary wires; `edges`
in a topological order. -/
structure ArrayGraph where
  lengths : List Nat
  inputs  : List Nat
  outputs : List Nat
  edges   : List ArrayEdge
  deriving Repr

/-- One edge's static check: wires exist, the declared result length is the destination's, a map's
sources share the destination's length, a gather's table is well-formed and targets its one source's
length, a concatenation has two sources, a constant none. -/
def edgeOk (ls : List Nat) (e : ArrayEdge) : Bool :=
  let len (w : Nat) := ls.getD w 0
  e.dstWire < ls.length && e.srcWires.all (· < ls.length) &&
  (e.op.outLen (e.srcWires.map len) == len e.dstWire) &&
  (match e.op with
   | .map _ _  => e.srcWires.all (fun s => len s == len e.dstWire)
   | .gather f => f.wf && e.srcWires.length == 1 && (f.target == len (e.srcWires.getD 0 0))
   | .concat   => e.srcWires.length == 2
   | .const _  => e.srcWires.isEmpty)

/-- Static well-formedness: the boundary wires exist, every edge passes `edgeOk`, every destination is
written once. -/
def ArrayGraph.wf (g : ArrayGraph) : Bool :=
  let nw := g.lengths.length
  g.inputs.all (· < nw) && g.outputs.all (· < nw) &&
  g.edges.all (edgeOk g.lengths) &&
  (g.edges.map (·.dstWire)).Nodup

instance : DecidablePred (fun l : List Nat => l.Nodup) := fun l => List.nodupDecidable l

theorem wf_edgeOk (g : ArrayGraph) (h : g.wf = true) : ∀ d ∈ g.edges, edgeOk g.lengths d = true := by
  simp only [ArrayGraph.wf, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2

theorem wf_outputs (g : ArrayGraph) (h : g.wf = true) : ∀ w ∈ g.outputs, w < g.lengths.length := by
  simp only [ArrayGraph.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-! ## 3. Semantics -/

def stepEdge (env : Nat → Vec) (e : ArrayEdge) : Nat → Vec :=
  let v := evalArrayOp e.op (e.srcWires.map env)
  fun w => if w == e.dstWire then v else env w

/-- Single-pass combinational evaluation. -/
def evalComb (env : Nat → Vec) (es : List ArrayEdge) : Nat → Vec :=
  es.foldl stepEdge env

def evalGraph (g : ArrayGraph) (env : Nat → Vec) : List Vec :=
  g.outputs.map (evalComb env g.edges)

/-- Synchronous step: sources read from the stage-entry snapshot. -/
def stepEdgeSync (entry cur : Nat → Vec) (e : ArrayEdge) : Nat → Vec :=
  let v := evalArrayOp e.op (e.srcWires.map entry)
  fun w => if w == e.dstWire then v else cur w

def evalStageAux (entry cur : Nat → Vec) : List ArrayEdge → Nat → Vec
  | [] => cur
  | e :: rest => evalStageAux entry (stepEdgeSync entry cur e) rest

def evalStageSync (env : Nat → Vec) (stage : List ArrayEdge) : Nat → Vec :=
  evalStageAux env env stage

def evalStage (env : Nat → Vec) (stage : List ArrayEdge) : Nat → Vec :=
  stage.foldl stepEdge env

def evalLayeredSync (env : Nat → Vec) (stages : List (List ArrayEdge)) : Nat → Vec :=
  stages.foldl evalStageSync env

def evalLayered (env : Nat → Vec) (stages : List (List ArrayEdge)) : Nat → Vec :=
  stages.foldl evalStage env

/-! ## 4. Wavefront layering -/

def edgeIndependentOfStage (e : ArrayEdge) (stage : List ArrayEdge) : Bool :=
  stage.all fun s =>
    (e.dstWire != s.dstWire) &&
    !(s.srcWires.contains e.dstWire) &&
    !(e.srcWires.contains s.dstWire)

def checkStageIndependent : List ArrayEdge → Bool
  | [] => true
  | e :: rest => edgeIndependentOfStage e rest && checkStageIndependent rest

def layerEdges : List ArrayEdge → List (List ArrayEdge)
  | [] => []
  | e :: rest =>
    match layerEdges rest with
    | [] => [[e]]
    | s :: stages =>
      if edgeIndependentOfStage e s then (e :: s) :: stages else [e] :: s :: stages

def layerGraph (g : ArrayGraph) : List (List ArrayEdge) := layerEdges g.edges

theorem map_env_update_of_not_contains
    (env : Nat → Vec) (dst : Nat) (v : Vec) (srcWires : List Nat)
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

theorem evalStageAux_shift_entry
    (entry cur : Nat → Vec) (dst : Nat) (v : Vec) (stage : List ArrayEdge)
    (hNoRaw : stage.all (fun s => !(s.srcWires.contains dst)) = true) :
    evalStageAux (fun w => if w == dst then v else entry w) cur stage =
      evalStageAux entry cur stage := by
  induction stage generalizing cur with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hNoRaw
    simp only [evalStageAux, stepEdgeSync]
    rw [map_env_update_of_not_contains entry dst v s.srcWires hNoRaw.1]
    exact ih _ hNoRaw.2

theorem edgeIndependentOfStage_implies_no_raw
    (e : ArrayEdge) (rest : List ArrayEdge)
    (hInd : edgeIndependentOfStage e rest = true) :
    rest.all (fun s => !(s.srcWires.contains e.dstWire)) = true := by
  unfold edgeIndependentOfStage at hInd
  induction rest with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hInd ⊢
    exact ⟨hInd.1.1.2, ih hInd.2⟩

theorem evalStageSync_eq_evalStage
    (env : Nat → Vec) (stage : List ArrayEdge)
    (hInd : checkStageIndependent stage = true) :
    evalStageSync env stage = evalStage env stage := by
  induction stage generalizing env with
  | nil => rfl
  | cons e rest ih =>
    simp only [checkStageIndependent, Bool.and_eq_true] at hInd
    have hNoRaw := edgeIndependentOfStage_implies_no_raw e rest hInd.1
    unfold evalStageSync
    dsimp only [evalStageAux, evalStage, List.foldl_cons]
    have hStepEq : stepEdgeSync env env e = stepEdge env e := rfl
    rw [hStepEq]
    have hShift := evalStageAux_shift_entry
      env (stepEdge env e) e.dstWire (evalArrayOp e.op (e.srcWires.map env)) rest hNoRaw
    dsimp only [stepEdge] at hShift ⊢
    rw [← hShift]
    exact ih (stepEdge env e) hInd.2

theorem evalLayeredSync_eq_evalLayered
    (env : Nat → Vec) (stages : List (List ArrayEdge))
    (hAll : stages.all checkStageIndependent = true) :
    evalLayeredSync env stages = evalLayered env stages := by
  induction stages generalizing env with
  | nil => rfl
  | cons stage rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hAll
    simp only [evalLayeredSync, evalLayered, List.foldl_cons]
    rw [evalStageSync_eq_evalStage env stage hAll.1]
    exact ih (evalStage env stage) hAll.2

theorem layerEdges_flatten (edges : List ArrayEdge) : (layerEdges edges).flatten = edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    dsimp only [layerEdges]
    cases hLayers : layerEdges rest with
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

theorem layerEdges_all_stages_independent (edges : List ArrayEdge) :
    (layerEdges edges).all checkStageIndependent = true := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    dsimp only [layerEdges]
    cases hLayers : layerEdges rest with
    | nil => rfl
    | cons s stages =>
      rw [hLayers] at ih
      simp only [List.all_cons, Bool.and_eq_true] at ih
      by_cases hInd : edgeIndependentOfStage e s = true
      · simp [hInd, checkStageIndependent, ih.1, ih.2]
      · simp only [hInd, Bool.false_eq_true, ↓reduceIte]
        simp [checkStageIndependent, edgeIndependentOfStage, ih.1, ih.2]

theorem evalLayered_eq_evalComb_flatten (env : Nat → Vec) (stages : List (List ArrayEdge)) :
    evalLayered env stages = evalComb env stages.flatten := by
  induction stages generalizing env with
  | nil => rfl
  | cons stage rest ih =>
    simp only [evalLayered, List.foldl_cons, List.flatten_cons, evalComb, List.foldl_append]
    exact ih (evalStage env stage)

/-- **`layerGraph_sound`**: every stage of the layering is independent, the layering flattens back to
the edges, and the synchronous stage-by-stage evaluation is the single-pass one. -/
theorem layerGraph_sound (g : ArrayGraph) (env : Nat → Vec) :
    (layerGraph g).all checkStageIndependent = true ∧
    (layerGraph g).flatten = g.edges ∧
    evalLayeredSync env (layerGraph g) = evalComb env g.edges := by
  unfold layerGraph
  have hInd := layerEdges_all_stages_independent g.edges
  have hFlat := layerEdges_flatten g.edges
  refine ⟨hInd, hFlat, ?_⟩
  rw [evalLayeredSync_eq_evalLayered env _ hInd, evalLayered_eq_evalComb_flatten, hFlat]

theorem checkStageIndependent_nodup (es : List ArrayEdge) (h : checkStageIndependent es = true) :
    (es.map (·.dstWire)).Nodup := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    simp only [checkStageIndependent, Bool.and_eq_true] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih h.2⟩
    rintro ⟨s, hs, hEq⟩
    have hAll := h.1
    simp only [edgeIndependentOfStage, List.all_eq_true] at hAll
    have := hAll s hs
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.1.1 hEq.symm

/-! ## 5. The scalar graphs as the one-element instance -/

def liftEdge (e : HyperEdge) : ArrayEdge :=
  { opIdx := e.opIdx, op := .map 1 (.scalar e.op), srcWires := e.srcWires, dstWire := e.dstWire }

/-- A scalar graph as an array graph: every wire of length one, every hyperedge the elementwise map of
its operation. -/
def ofScalar (g : StrictOpenHypergraph) : ArrayGraph :=
  { lengths := List.replicate g.nodeTypes.length 1
  , inputs  := g.boundaryIn.table
  , outputs := g.boundaryOut.table
  , edges   := (extractHyperEdges g).map liftEdge }

/-- A scalar environment as singleton wires. -/
def singletonEnv (env : Nat → Word) : Nat → Vec := fun w => [env w]

theorem evalArrayOp_lift (op : HypergraphOp) (srcs : List Nat) (env : Nat → Word) :
    evalArrayOp (.map 1 (.scalar op)) (srcs.map (singletonEnv env)) =
      [evalHypergraphOpBv op (srcs.map env)] := by
  simp [evalArrayOp, evalElemOp, singletonEnv, List.map_map, Function.comp_def]

theorem stepEdgeSync_lift (entry cur : Nat → Word) (e : HyperEdge) :
    stepEdgeSync (singletonEnv entry) (singletonEnv cur) (liftEdge e) =
      singletonEnv (stepHyperEdgeSyncBv entry cur e) := by
  funext w
  simp only [stepEdgeSync, liftEdge, stepHyperEdgeSyncBv, singletonEnv, evalArrayOp_lift]
  split <;> rfl

theorem evalStageAux_lift (entry cur : Nat → Word) (stage : List HyperEdge) :
    evalStageAux (singletonEnv entry) (singletonEnv cur) (stage.map liftEdge) =
      singletonEnv (evalWavefrontStageAuxBv entry cur stage) := by
  induction stage generalizing cur with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, evalStageAux, evalWavefrontStageAuxBv, stepEdgeSync_lift]
    exact ih _

theorem edgeIndependentOfStage_lift (e : HyperEdge) (stage : List HyperEdge) :
    edgeIndependentOfStage (liftEdge e) (stage.map liftEdge) =
      OpenHypergraph.edgeIndependentOfStage e stage := by
  unfold edgeIndependentOfStage OpenHypergraph.edgeIndependentOfStage
  rw [List.all_map]
  rfl

/-- Layering commutes with the lift: independence reads only wires. -/
theorem layerEdges_lift (edges : List HyperEdge) :
    layerEdges (edges.map liftEdge) = (layerHyperEdges edges).map (·.map liftEdge) := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, layerEdges, layerHyperEdges, ih]
    cases layerHyperEdges rest with
    | nil => rfl
    | cons s stages =>
      simp only [List.map_cons, edgeIndependentOfStage_lift]
      split <;> simp

theorem evalLayeredSync_lift (env : Nat → Word) (stages : List (List HyperEdge)) :
    evalLayeredSync (singletonEnv env) (stages.map (·.map liftEdge)) =
      singletonEnv (evalLayeredStagesSyncBv env stages) := by
  induction stages generalizing env with
  | nil => rfl
  | cons stage rest ih =>
    simp only [List.map_cons, evalLayeredSync, evalLayeredStagesSyncBv, List.foldl_cons]
    have h : evalStageSync (singletonEnv env) (stage.map liftEdge) =
        singletonEnv (evalWavefrontStageSyncBv env stage) := by
      simp only [evalStageSync, evalWavefrontStageSyncBv]
      exact evalStageAux_lift env env stage
    rw [h]
    exact ih _

/-- **`ofScalar_layered_sound`**: on the one-element instance, the array evaluation of a scalar graph's
layering is the scalar 64-bit evaluation, wire by wire. -/
theorem ofScalar_layered_sound (g : StrictOpenHypergraph) (env : Nat → Word) :
    evalLayeredSync (singletonEnv env) (layerGraph (ofScalar g)) =
      singletonEnv (evalLayeredStagesSyncBv env (layerHypergraph g)) := by
  simp only [layerGraph, ofScalar, layerHypergraph, layerEdges_lift]
  exact evalLayeredSync_lift env _

end Obend.Hardware.ArrayHypergraph
