module
/-
# Obend.Hardware.ArrayHypergraph — open hypergraphs whose wires carry arrays

The scalar `StrictOpenHypergraph` of `Obend.Hardware.OpenHypergraph` has one 64-bit word per wire and
one operation per hyperedge. On a GPU that is one thread per hyperedge, a gate and not a computation.
Here a wire carries a vector of words and a hyperedge is one array operation: an elementwise program
(every element a thread), a gather along a `FiniteFunction` (Wilson–Zanasi's data-parallel permutation
datum, `arXiv:2305.01041`), a concatenation, or a constant array.

An elementwise program (`ElemProg`) is a list of instructions `dst := op args` over names that are wires:
its local environment starts at the elements of the edge's source wires and the value is the name `out`.
A graph as built is *primitive*, one instruction per map edge (`ArrayEdge.primitive`); fusion (section
6) is what makes longer programs.

## Layering (section 4)

`layerEdges` is the frontier algorithm of Wilson–Zanasi's `open-hypergraphs` crate (`strict/graph.rs`,
`kahn`): round by round, the operations whose predecessors have all been visited form the next layer. A
predecessor here is an earlier edge with a hazard (it writes a wire this one reads, reads a wire this one
writes, or writes the same wire); on a graph in SSA form that is their operation adjacency. Each stage is
pairwise independent (`checkStageIndependent`), the stages flatten to a permutation of the edges, and the
synchronous stage-by-stage evaluation equals the single-pass one (`layerGraph_sound`); the permutation
is sound because independent edges commute (`stepEdge_comm`). The scalar module's `layerHyperEdges` is
the older greedy layering (an edge joins the most recent stage if independent, else opens one) and stays
there as its own; `ofScalar_layered_sound` bridges the two through the combinational evaluation.

## Fusion (section 6)

`fuseGraph` is Halide's `compute_inline` and TVM's elementwise fusion over this language: every map edge
recomputes the elementwise producers of its sources instead of reading their wires (its program is the
producers' instructions, deduplicated, followed by its own, its sources the producers' sources), and a
map edge nobody but a map edge reads, and no output names, is dropped. `fuseGraph_sound`: for a
well-formed graph (`ArrayGraph.wf`: every edge passes `edgeOk`, destinations are written once, no edge
writes a wire an earlier or the same edge reads, map edges are primitive) the fused graph has the same
outputs, and its edges pass `edgeOk`. Chains of elementwise edges therefore lower to one kernel per
element computing a chain, and the layering sees only the producers that are read by a gather, a
concatenation or an output.

Expected values on the evaluator with wires stored (`evalGraphArr`, `evalGraphArr_eq`): the closure-based
model, compiled, re-evaluates an edge on every read and is exponential in dependency depth; and a local
environment of closures for a program is quadratic in its length, so `evalProgExec` runs it on a hash map.

Elementwise operations are the scalar `HypergraphOp`s plus the bit operations a Goldilocks field
multiply needs (`Obend.Apps.ZkNtt.glMul`): unsigned comparison, and, or, logical shifts. All arithmetic
is modulo `2^64`, as `BitVec 64` and WGSL `i64` are.
-/
public import Obend.Hardware.OpenHypergraph
public import Std.Data.HashMap
public import Obend.Hardware.ArrayFold
@[expose] public section

namespace Obend.Hardware.ArrayHypergraph
open Obend.Hardware.OpenHypergraph
set_option autoImplicit false


theorem beq_symm_nat (a b : Nat) : (a == b) = (b == a) := by
  cases h : a == b
  · cases h' : b == a
    · rfl
    · exact absurd (beq_iff_eq.mp h').symm (fun e => by simp [e] at h)
  · rw [beq_iff_eq.mp h]; simp

theorem getD_append_of_lt {α : Type} (c d : List α) (k : Nat) (z : α) (hk : k < c.length) :
    (c ++ d).getD k z = c.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_append_right {α : Type} (c d : List α) (k : Nat) (z : α) :
    (c ++ d).getD (c.length + k) z = d.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem getD_range_map {α : Type} (n : Nat) (f : Nat → α) (z : α) (e : Nat) (he : e < n) :
    ((List.range n).map f).getD e z = f e := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]

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
  | .shr      => wordShr a0 a1
  | .shl      => wordShl a0 a1

/-- One instruction of an elementwise program: `dst := op args`, every name a wire. -/
structure Instr where
  op   : ElemOp
  args : List Nat
  dst  : Nat
  deriving DecidableEq, Repr

/-- An elementwise program: its instructions in order over a local environment of named words that
starts at the source wires' elements (every other name `0`); the value is the name `out`. -/
structure ElemProg where
  code : List Instr
  out  : Nat
  deriving DecidableEq, Repr

/-- The one-instruction program `dst := op srcs`. -/
def ElemProg.single (op : ElemOp) (srcs : List Nat) (dst : Nat) : ElemProg := ⟨[⟨op, srcs, dst⟩], dst⟩

def stepInstr (loc : Nat → Word) (i : Instr) : Nat → Word :=
  let v := evalElemOp i.op (i.args.map loc)
  fun w => if w == i.dst then v else loc w

def runCode (loc : Nat → Word) (code : List Instr) : Nat → Word := code.foldl stepInstr loc

def evalProg (p : ElemProg) (loc : Nat → Word) : Word := runCode loc p.code p.out

theorem evalProg_single (op : ElemOp) (srcs : List Nat) (dst : Nat) (loc : Nat → Word) :
    evalProg (ElemProg.single op srcs dst) loc = evalElemOp op (srcs.map loc) := by
  simp [evalProg, ElemProg.single, runCode, stepInstr]

/-- One hyperedge's operation on whole wires. -/
inductive ArrayOp where
  /-- `n` elements, element `e` is the program over the sources' elements `e`. -/
  | map (n : Nat) (prog : ElemProg)
  /-- element `e` is element `f.table[e]` of the one source; length `f.source`. -/
  | gather (f : FiniteFunction)
  /-- the first source followed by the second. -/
  | concat
  /-- a constant array. -/
  | const (vals : Vec)
  /-- Associative reduction or scan, optionally segmented. -/
  | fold (op : ReduceOp) (shape : FoldShape)
  deriving DecidableEq, Repr

/-- Reduce a wire, producing a singleton (the identity when `n = 0`). -/
def ArrayOp.reduce (op : ReduceOp) (n : Nat) : ArrayOp := .fold op (.reduce n)
/-- Length-preserving scan with an explicit inclusive/exclusive convention. -/
def ArrayOp.scan (op : ReduceOp) (n : Nat) (mode : ScanMode) : ArrayOp := .fold op (.scan n mode)
def ArrayOp.segReduce (op : ReduceOp) (lengths : List Nat) : ArrayOp := .fold op (.segReduce lengths)
def ArrayOp.segScan (op : ReduceOp) (lengths : List Nat) (mode : ScanMode) : ArrayOp :=
  .fold op (.segScan lengths mode)

/-- The sources of an edge are named: a program reads them by wire. The first pair of a name wins. -/
def srcLookup (srcs : List (Nat × Vec)) (w : Nat) : Vec :=
  match srcs.find? (·.1 == w) with
  | some p => p.2
  | none => []

theorem srcLookup_map (f : Nat → Vec) (ws : List Nat) (u : Nat) (hu : u ∈ ws) :
    srcLookup (ws.map fun w => (w, f w)) u = f u := by
  induction ws with
  | nil => simp at hu
  | cons w ws ih =>
    simp only [List.map_cons, srcLookup, List.find?_cons]
    by_cases h : w = u
    · subst h; simp
    · have hb : (w == u) = false := beq_eq_false_iff_ne.mpr h
      simp only [hb]
      have hu' : u ∈ ws := by
        rcases List.mem_cons.mp hu with h' | h'
        · exact absurd h'.symm h
        · exact h'
      simpa [srcLookup] using ih hu'

def evalArrayOp (op : ArrayOp) (srcs : List (Nat × Vec)) : Vec :=
  let args := srcs.map (·.2)
  match op with
  | .map n p   => (List.range n).map fun e => evalProg p fun w => (srcLookup srcs w).getD e 0#64
  | .gather f  => f.table.map fun i => (args.getD 0 []).getD i 0#64
  | .concat    => args.getD 0 [] ++ args.getD 1 []
  | .const vs  => vs
  | .fold op shape => evalFold op shape (fun i => (args.getD 0 []).getD i 0#64)

/-- The length an operation's result has, from the operation alone or its sources' lengths. -/
def ArrayOp.outLen (op : ArrayOp) (srcLens : List Nat) : Nat :=
  match op with
  | .map n _  => n
  | .gather f => f.source
  | .concat   => srcLens.getD 0 0 + srcLens.getD 1 0
  | .const vs => vs.length
  | .fold _ shape => shape.outLen

theorem evalArrayOp_length (op : ArrayOp) (srcs : List (Nat × Vec)) (hf : ∀ f, op = .gather f → f.wf = true) :
    (evalArrayOp op srcs).length = op.outLen ((srcs.map (·.2)).map List.length) := by
  cases op with
  | map n o => simp [evalArrayOp, ArrayOp.outLen]
  | gather f =>
    have h := hf f rfl
    simp only [FiniteFunction.wf, Bool.and_eq_true, beq_iff_eq] at h
    simp [evalArrayOp, ArrayOp.outLen, h.1]
  | concat =>
    simp only [evalArrayOp, ArrayOp.outLen, List.length_append]
    cases srcs with
    | nil => rfl
    | cons a rest => cases rest <;> simp
  | const vs => simp [evalArrayOp, ArrayOp.outLen]
  | fold op shape => simp [evalArrayOp, ArrayOp.outLen, evalFold, FoldShape.outLen]

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

def ArrayEdge.isMap (e : ArrayEdge) : Bool :=
  match e.op with
  | .map _ _ => true
  | _ => false

/-- A map edge whose program is the one instruction over its own sources into its own destination; every
other edge counts as primitive. -/
def ArrayEdge.primitive (e : ArrayEdge) : Bool :=
  match e.op with
  | .map _ p =>
    match p.code with
    | [i] => i.args == e.srcWires && i.dst == e.dstWire && p.out == e.dstWire
    | _ => false
  | _ => true

/-- One edge's static check: wires exist, the declared result length is the destination's, a map's
sources share the destination's length and its program never writes a source nor reads an unwritten
name as its value, a gather's table is well-formed and targets its one source's length, a concatenation
has two sources, a constant none. -/
def edgeOk (ls : List Nat) (e : ArrayEdge) : Bool :=
  let len (w : Nat) := ls.getD w 0
  e.dstWire < ls.length && e.srcWires.all (· < ls.length) &&
  (e.op.outLen (e.srcWires.map len) == len e.dstWire) &&
  (match e.op with
   | .map _ p  =>
     e.srcWires.all (fun s => len s == len e.dstWire) &&
     p.code.all (fun i => !(e.srcWires.contains i.dst)) && !(e.srcWires.contains p.out)
   | .gather f => f.wf && e.srcWires.length == 1 && (f.target == len (e.srcWires.getD 0 0))
   | .concat   => e.srcWires.length == 2
   | .const _  => e.srcWires.isEmpty
   | .fold _ shape => e.srcWires.length == 1 && shape.inputLen == len (e.srcWires.getD 0 0))

/-- No edge writes a wire that it or an earlier edge reads. -/
def noWriteAfterRead : List ArrayEdge → Bool
  | [] => true
  | e :: rest => (e :: rest).all (fun d => !(e.srcWires.contains d.dstWire)) && noWriteAfterRead rest

/-- Static well-formedness: the boundary wires exist, every edge passes `edgeOk`, every destination is
written once and after every read of it, every map edge is primitive. -/
def ArrayGraph.wf (g : ArrayGraph) : Bool :=
  let nw := g.lengths.length
  g.inputs.all (· < nw) && g.outputs.all (· < nw) &&
  g.edges.all (edgeOk g.lengths) &&
  (g.edges.map (·.dstWire)).Nodup &&
  noWriteAfterRead g.edges &&
  g.edges.all (·.primitive)

instance : DecidablePred (fun l : List Nat => l.Nodup) := fun l => List.nodupDecidable l

theorem wf_edgeOk (g : ArrayGraph) (h : g.wf = true) : ∀ d ∈ g.edges, edgeOk g.lengths d = true := by
  simp only [ArrayGraph.wf, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.2

theorem wf_outputs (g : ArrayGraph) (h : g.wf = true) : ∀ w ∈ g.outputs, w < g.lengths.length := by
  simp only [ArrayGraph.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

theorem wf_nodup (g : ArrayGraph) (h : g.wf = true) : (g.edges.map (·.dstWire)).Nodup := by
  simp only [ArrayGraph.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem wf_noWriteAfterRead (g : ArrayGraph) (h : g.wf = true) : noWriteAfterRead g.edges = true := by
  simp only [ArrayGraph.wf, Bool.and_eq_true] at h
  exact h.1.2

theorem wf_primitive (g : ArrayGraph) (h : g.wf = true) : ∀ d ∈ g.edges, d.primitive = true := by
  simp only [ArrayGraph.wf, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

/-! ## 3. Semantics -/

def edgeSrcs (env : Nat → Vec) (e : ArrayEdge) : List (Nat × Vec) := e.srcWires.map fun w => (w, env w)

def edgeValue (env : Nat → Vec) (e : ArrayEdge) : Vec := evalArrayOp e.op (edgeSrcs env e)

def stepEdge (env : Nat → Vec) (e : ArrayEdge) : Nat → Vec :=
  let v := edgeValue env e
  fun w => if w == e.dstWire then v else env w

/-- Single-pass combinational evaluation. -/
def evalComb (env : Nat → Vec) (es : List ArrayEdge) : Nat → Vec :=
  es.foldl stepEdge env

def evalGraph (g : ArrayGraph) (env : Nat → Vec) : List Vec :=
  g.outputs.map (evalComb env g.edges)

/-- Updating a wire no source names leaves an edge's sources as they were. -/
theorem edgeSrcs_update (env : Nat → Vec) (dst : Nat) (v : Vec) (e : ArrayEdge)
    (hNotMem : (e.srcWires.contains dst) = false) :
    edgeSrcs (fun w => if w == dst then v else env w) e = edgeSrcs env e := by
  simp only [edgeSrcs]
  apply List.map_congr_left
  intro w hw
  have hne : w ≠ dst := by
    intro h; subst h
    rw [List.contains_iff_mem.mpr hw] at hNotMem
    exact Bool.noConfusion hNotMem
  simp [beq_eq_false_iff_ne.mpr hne]

theorem edgeValue_update (env : Nat → Vec) (dst : Nat) (v : Vec) (e : ArrayEdge)
    (hNotMem : (e.srcWires.contains dst) = false) :
    edgeValue (fun w => if w == dst then v else env w) e = edgeValue env e := by
  simp only [edgeValue, edgeSrcs_update env dst v e hNotMem]

/-- Two environments agreeing on an edge's sources give it the same value. -/
theorem edgeValue_congr (env env' : Nat → Vec) (e : ArrayEdge) (h : ∀ s ∈ e.srcWires, env' s = env s) :
    edgeValue env' e = edgeValue env e := by
  simp only [edgeValue, edgeSrcs]
  congr 1
  exact List.map_congr_left fun s hs => by rw [h s hs]

/-- Synchronous step: sources read from the stage-entry snapshot. -/
def stepEdgeSync (entry cur : Nat → Vec) (e : ArrayEdge) : Nat → Vec :=
  let v := edgeValue entry e
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

/-! ### Running it: the wires as arrays, the local environment as a hash map

`evalComb` closes over the environment; compiled, every read of a wire re-evaluates its edge, which is
exponential in dependency depth. `evalCombArr` stores the wires as arrays of words, and `evalProgExec`
runs a program's local environment on a hash map; `evalGraphArr_eq` says it is `evalGraph` read through
the arrays, and `obend-emit-gpu` computes expected values with it. -/

abbrev AVec := Array Word

def evalProgExec (p : ElemProg) (loc : Std.HashMap Nat Word) : Word :=
  (p.code.foldl (fun m i => m.insert i.dst (evalElemOp i.op (i.args.map fun a => m.getD a 0#64))) loc).getD
    p.out 0#64

theorem runCode_hashMap (code : List Instr) (m : Std.HashMap Nat Word) (w : Nat) :
    (code.foldl (fun m i => m.insert i.dst (evalElemOp i.op (i.args.map fun a => m.getD a 0#64))) m).getD w 0#64 =
      runCode (fun u => m.getD u 0#64) code w := by
  induction code generalizing m with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons, runCode] at ih ⊢
    rw [ih]
    have hloc : (fun u => (m.insert i.dst (evalElemOp i.op (i.args.map fun a => m.getD a 0#64))).getD u 0#64) =
        stepInstr (fun a => m.getD a 0#64) i := by
      funext u
      simp only [stepInstr, Std.HashMap.getD_insert, beq_symm_nat u i.dst]
    rw [hloc]

theorem evalProgExec_eq (p : ElemProg) (m : Std.HashMap Nat Word) :
    evalProgExec p m = evalProg p (fun u => m.getD u 0#64) := by
  simp only [evalProgExec, evalProg]
  exact runCode_hashMap p.code m p.out

/-- The local environment of element `e`: the sources' elements, the first pair of a name winning. -/
def localEnv (srcs : List (Nat × AVec)) (e : Nat) : Std.HashMap Nat Word :=
  srcs.foldr (fun p m => m.insert p.1 (p.2.getD e 0#64)) ∅

theorem getD_toList (a : AVec) (i : Nat) : a.toList.getD i 0#64 = a.getD i 0#64 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

theorem localEnv_getD (srcs : List (Nat × AVec)) (e w : Nat) :
    (localEnv srcs e).getD w 0#64 = (srcLookup (srcs.map fun p => (p.1, p.2.toList)) w).getD e 0#64 := by
  induction srcs with
  | nil => simp [localEnv, srcLookup, Std.HashMap.getD_empty]
  | cons p rest ih =>
    simp only [localEnv, List.foldr_cons, Std.HashMap.getD_insert, List.map_cons, srcLookup, List.find?_cons]
    by_cases h : p.1 = w
    · simp [h]
    · have hb : (p.1 == w) = false := beq_eq_false_iff_ne.mpr h
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      simpa [localEnv, srcLookup] using ih

def evalArrayOpExec (op : ArrayOp) (srcs : List (Nat × AVec)) : AVec :=
  let args := srcs.map (·.2)
  match op with
  | .map n p   => (Array.range n).map fun e => evalProgExec p (localEnv srcs e)
  | .gather f  => f.table.toArray.map fun i => (args.getD 0 #[]).getD i 0#64
  | .concat    => args.getD 0 #[] ++ args.getD 1 #[]
  | .const vs  => vs.toArray
  | .fold op shape => evalFoldExec op shape (fun i => (args.getD 0 #[]).getD i 0#64)

theorem getD_map_toList (xs : List AVec) (i : Nat) : (xs.map Array.toList).getD i [] = (xs.getD i #[]).toList := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ k => simp only [List.map_cons, List.getD_cons_succ]; exact ih k

theorem evalArrayOpExec_toList (op : ArrayOp) (srcs : List (Nat × AVec)) :
    (evalArrayOpExec op srcs).toList = evalArrayOp op (srcs.map fun p => (p.1, p.2.toList)) := by
  have hargs : (srcs.map fun p => (p.1, p.2.toList)).map (·.2) = (srcs.map (·.2)).map Array.toList := by
    simp [List.map_map, Function.comp_def]
  cases op with
  | map n p =>
    simp only [evalArrayOpExec, evalArrayOp, Array.toList_map, Array.toList_range]
    apply List.map_congr_left
    intro e _
    rw [evalProgExec_eq]
    congr 1
    funext w
    exact localEnv_getD srcs e w
  | gather f =>
    simp only [evalArrayOpExec, evalArrayOp, Array.toList_map, hargs, getD_map_toList, getD_toList]
  | concat =>
    simp only [evalArrayOpExec, evalArrayOp, Array.toList_append, hargs, getD_map_toList]
  | const vs => simp [evalArrayOpExec, evalArrayOp]
  | fold op shape =>
    simp only [evalArrayOpExec, evalArrayOp, evalFoldExec_toList, hargs, getD_map_toList, getD_toList]

def stepEdgeArr (a : Array AVec) (e : ArrayEdge) : Array AVec :=
  a.setIfInBounds e.dstWire (evalArrayOpExec e.op (e.srcWires.map fun w => (w, a.getD w #[])))

def evalCombArr (a : Array AVec) (es : List ArrayEdge) : Array AVec := es.foldl stepEdgeArr a

def evalGraphArr (g : ArrayGraph) (a : Array AVec) : List Vec :=
  g.outputs.map fun w => ((evalCombArr a g.edges).getD w #[]).toList

theorem stepEdgeArr_getD (a : Array AVec) (e : ArrayEdge) (hdst : e.dstWire < a.size) (w : Nat) :
    ((stepEdgeArr a e).getD w #[]).toList = stepEdge (fun u => (a.getD u #[]).toList) e w := by
  simp only [stepEdgeArr, stepEdge, edgeValue, edgeSrcs]
  by_cases hw : w = e.dstWire
  · subst hw
    simp only [beq_self_eq_true, ↓reduceIte, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt hdst, Option.getD_some]
    rw [evalArrayOpExec_toList]
    simp [List.map_map, Function.comp_def]
  · have h1 : (w == e.dstWire) = false := beq_eq_false_iff_ne.mpr hw
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm hw), h1]

theorem evalCombArr_getD (a : Array AVec) (es : List ArrayEdge) (h : ∀ e ∈ es, e.dstWire < a.size) (w : Nat) :
    ((evalCombArr a es).getD w #[]).toList = evalComb (fun u => (a.getD u #[]).toList) es w := by
  induction es generalizing a with
  | nil => rfl
  | cons e rest ih =>
    simp only [evalCombArr, evalComb, List.foldl_cons]
    have hdst := h e List.mem_cons_self
    have hsize : (stepEdgeArr a e).size = a.size := by simp [stepEdgeArr]
    have hrest : ∀ e' ∈ rest, e'.dstWire < (stepEdgeArr a e).size := by
      intro e' he'; rw [hsize]; exact h e' (List.mem_cons_of_mem e he')
    have hfun : (fun u => ((stepEdgeArr a e).getD u #[]).toList) = stepEdge (fun u => (a.getD u #[]).toList) e := by
      funext u; exact stepEdgeArr_getD a e hdst u
    have := ih (stepEdgeArr a e) hrest
    simp only [evalCombArr, evalComb] at this
    rw [hfun] at this
    exact this

/-- **`evalGraphArr_eq`**: the array evaluation is the model's, on a graph whose destinations exist. -/
theorem evalGraphArr_eq (g : ArrayGraph) (a : Array AVec) (hsize : a.size = g.lengths.length)
    (h : ∀ e ∈ g.edges, e.dstWire < g.lengths.length) :
    evalGraphArr g a = evalGraph g (fun u => (a.getD u #[]).toList) := by
  simp only [evalGraphArr, evalGraph]
  apply List.map_congr_left
  intro w _
  exact evalCombArr_getD a g.edges (fun e he => by rw [hsize]; exact h e he) w

/-! ## 4. Layering by frontiers -/

/-- `e` and `s` can share a stage: they write different wires and neither reads the other's. -/
def indep (e s : ArrayEdge) : Bool :=
  (e.dstWire != s.dstWire) && !(s.srcWires.contains e.dstWire) && !(e.srcWires.contains s.dstWire)

theorem indep_symm (e s : ArrayEdge) : indep e s = indep s e := by
  simp only [indep, bne, beq_symm_nat e.dstWire s.dstWire]
  cases s.srcWires.contains e.dstWire <;> cases e.srcWires.contains s.dstWire <;> simp

def edgeIndependentOfStage (e : ArrayEdge) (stage : List ArrayEdge) : Bool :=
  stage.all (indep e)

def checkStageIndependent : List ArrayEdge → Bool
  | [] => true
  | e :: rest => edgeIndependentOfStage e rest && checkStageIndependent rest

/-- The frontier of `es` after the edges `before`: the edges of `es` independent of every edge before
them (in `before` or earlier in `es`), and the rest, each in order. -/
def frontier : List ArrayEdge → List ArrayEdge → List ArrayEdge × List ArrayEdge
  | _, [] => ([], [])
  | before, e :: es =>
    let r := frontier (e :: before) es
    if edgeIndependentOfStage e before then (e :: r.1, r.2) else (r.1, e :: r.2)

theorem frontier_length (before es : List ArrayEdge) : (frontier before es).2.length ≤ es.length := by
  induction es generalizing before with
  | nil => simp [frontier]
  | cons e es ih =>
    simp only [frontier]
    split
    · simp only [List.length_cons]
      exact Nat.le_succ_of_le (ih _)
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih _)

theorem frontier_perm (before es : List ArrayEdge) : es.Perm ((frontier before es).1 ++ (frontier before es).2) := by
  induction es generalizing before with
  | nil => simp [frontier]
  | cons e es ih =>
    simp only [frontier]
    split
    · simp only [List.cons_append]
      exact (ih _).cons e
    · exact List.perm_cons_append_cons e (ih _)

/-- Every frontier edge is independent of every edge before the list. -/
theorem frontier_indep_before (before es : List ArrayEdge) :
    ∀ x ∈ (frontier before es).1, edgeIndependentOfStage x before = true := by
  induction es generalizing before with
  | nil => simp [frontier]
  | cons e es ih =>
    intro x hx
    simp only [frontier] at hx
    split at hx
    · rename_i hInd
      rcases List.mem_cons.mp hx with h | h
      · subst h; exact hInd
      · have := ih (e :: before) x h
        simp only [edgeIndependentOfStage, List.all_cons, Bool.and_eq_true] at this
        exact this.2
    · have := ih (e :: before) x hx
      simp only [edgeIndependentOfStage, List.all_cons, Bool.and_eq_true] at this
      exact this.2

theorem frontier_stage_indep (before es : List ArrayEdge) : checkStageIndependent (frontier before es).1 = true := by
  induction es generalizing before with
  | nil => simp [frontier, checkStageIndependent]
  | cons e es ih =>
    simp only [frontier]
    split
    · simp only [checkStageIndependent, Bool.and_eq_true]
      refine ⟨?_, ih _⟩
      simp only [edgeIndependentOfStage, List.all_eq_true]
      intro x hx
      have := frontier_indep_before (e :: before) es x hx
      simp only [edgeIndependentOfStage, List.all_cons, Bool.and_eq_true] at this
      rw [indep_symm]; exact this.1
    · exact ih _

/-- Independent edges commute. -/
theorem stepEdge_comm (env : Nat → Vec) (e x : ArrayEdge) (h : indep x e = true) :
    stepEdge (stepEdge env e) x = stepEdge (stepEdge env x) e := by
  simp only [indep, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hne, hxe⟩, hex⟩ := h
  have hve : edgeValue (stepEdge env x) e = edgeValue env e := by
    simp only [stepEdge]; exact edgeValue_update env x.dstWire _ e hxe
  have hvx : edgeValue (stepEdge env e) x = edgeValue env x := by
    simp only [stepEdge]; exact edgeValue_update env e.dstWire _ x hex
  funext w
  simp only [stepEdge] at hve hvx ⊢
  rw [hve, hvx]
  by_cases hwx : w = x.dstWire
  · subst hwx
    simp [hne]
  · simp [beq_eq_false_iff_ne.mpr hwx]

theorem evalComb_cons_comm (env : Nat → Vec) (e : ArrayEdge) (xs ys : List ArrayEdge)
    (h : ∀ x ∈ xs, indep x e = true) :
    evalComb env (e :: xs ++ ys) = evalComb env (xs ++ e :: ys) := by
  induction xs generalizing env with
  | nil => rfl
  | cons x xs ih =>
    simp only [evalComb, List.cons_append, List.foldl_cons] at ih ⊢
    rw [stepEdge_comm env e x (h x List.mem_cons_self)]
    exact ih (stepEdge env x) (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem frontier_evalComb (before es : List ArrayEdge) (env : Nat → Vec) :
    evalComb env es = evalComb env ((frontier before es).1 ++ (frontier before es).2) := by
  induction es generalizing before env with
  | nil => rfl
  | cons e es ih =>
    simp only [frontier]
    split
    · simp only [List.cons_append, evalComb, List.foldl_cons]
      exact ih _ _
    · have hStep : evalComb env (e :: es) = evalComb env (e :: ((frontier (e :: before) es).1 ++ (frontier (e :: before) es).2)) := by
        simp only [evalComb, List.foldl_cons]
        exact ih _ _
      rw [hStep]
      apply evalComb_cons_comm
      intro x hx
      have := frontier_indep_before (e :: before) es x hx
      simp only [edgeIndependentOfStage, List.all_cons, Bool.and_eq_true] at this
      exact this.1

/-- Frontier by frontier; the first edge is always in the first frontier. -/
def layerEdges : List ArrayEdge → List (List ArrayEdge)
  | [] => []
  | e :: es =>
    let r := frontier [e] es
    (e :: r.1) :: layerEdges r.2
termination_by es => es.length
decreasing_by
  simp_wf
  have := frontier_length [e] es
  omega

/-- Induction along the frontiers. -/
theorem layerEdges_ind (P : List ArrayEdge → Prop) (h0 : P [])
    (h1 : ∀ e es f r, frontier [e] es = (f, r) → P r → P (e :: es)) : ∀ es, P es := by
  suffices h : ∀ n es, es.length ≤ n → P es from fun es => h es.length es (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro es hes
    cases es with
    | nil => exact h0
    | cons _ _ => simp at hes
  | succ n ih =>
    intro es hes
    cases es with
    | nil => exact h0
    | cons e es' =>
      obtain ⟨f, r, hfr⟩ : ∃ f r, frontier [e] es' = (f, r) := ⟨_, _, rfl⟩
      apply h1 e es' f r hfr
      apply ih r
      have := frontier_length [e] es'
      rw [hfr] at this
      simp only [List.length_cons] at hes this
      omega

def layerGraph (g : ArrayGraph) : List (List ArrayEdge) := layerEdges g.edges

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
    rw [edgeValue_update entry dst v s hNoRaw.1]
    exact ih _ hNoRaw.2

theorem edgeIndependentOfStage_implies_no_raw
    (e : ArrayEdge) (rest : List ArrayEdge)
    (hInd : edgeIndependentOfStage e rest = true) :
    rest.all (fun s => !(s.srcWires.contains e.dstWire)) = true := by
  unfold edgeIndependentOfStage at hInd
  induction rest with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true, indep] at hInd ⊢
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
    have hShift := evalStageAux_shift_entry env (stepEdge env e) e.dstWire (edgeValue env e) rest hNoRaw
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

theorem layerEdges_flatten_perm (edges : List ArrayEdge) : (layerEdges edges).flatten.Perm edges := by
  induction edges using layerEdges_ind with
  | h0 => simp [layerEdges]
  | h1 e es f r h ih =>
    simp only [layerEdges, h, List.flatten_cons, List.cons_append]
    apply List.Perm.cons
    have hp := frontier_perm [e] es
    rw [h] at hp
    exact (ih.append_left f).trans hp.symm

theorem layerEdges_all_stages_independent (edges : List ArrayEdge) :
    (layerEdges edges).all checkStageIndependent = true := by
  induction edges using layerEdges_ind with
  | h0 => simp [layerEdges]
  | h1 e es f r h ih =>
    simp only [layerEdges, h, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih⟩
    simp only [checkStageIndependent, Bool.and_eq_true]
    have hs := frontier_stage_indep [e] es
    have hb := frontier_indep_before [e] es
    rw [h] at hs hb
    refine ⟨?_, hs⟩
    simp only [edgeIndependentOfStage, List.all_eq_true]
    intro x hx
    have := hb x hx
    simp only [edgeIndependentOfStage, List.all_cons, List.all_nil, Bool.and_true] at this
    rw [indep_symm]; exact this

theorem layerEdges_evalLayered (env : Nat → Vec) (edges : List ArrayEdge) :
    evalLayered env (layerEdges edges) = evalComb env edges := by
  induction edges using layerEdges_ind generalizing env with
  | h0 => simp [layerEdges, evalLayered, evalComb]
  | h1 e es f r h ih =>
    simp only [layerEdges, h, evalLayered, List.foldl_cons]
    have hfr := frontier_evalComb [e] es (stepEdge env e)
    rw [h] at hfr
    simp only [evalLayered] at ih
    rw [ih, evalStage, List.foldl_cons, evalComb, ← List.foldl_append]
    simp only [evalComb] at hfr
    rw [← hfr]
    rfl

theorem evalLayered_eq_evalComb_flatten (env : Nat → Vec) (stages : List (List ArrayEdge)) :
    evalLayered env stages = evalComb env stages.flatten := by
  induction stages generalizing env with
  | nil => rfl
  | cons stage rest ih =>
    simp only [evalLayered, List.foldl_cons, List.flatten_cons, evalComb, List.foldl_append]
    exact ih (evalStage env stage)

/-- **`layerGraph_sound`**: every stage of the layering is independent, the layering flattens to a
permutation of the edges, and the synchronous stage-by-stage evaluation is the single-pass one. -/
theorem layerGraph_sound (g : ArrayGraph) (env : Nat → Vec) :
    (layerGraph g).all checkStageIndependent = true ∧
    (layerGraph g).flatten.Perm g.edges ∧
    evalLayeredSync env (layerGraph g) = evalComb env g.edges := by
  unfold layerGraph
  have hInd := layerEdges_all_stages_independent g.edges
  refine ⟨hInd, layerEdges_flatten_perm g.edges, ?_⟩
  rw [evalLayeredSync_eq_evalLayered env _ hInd, layerEdges_evalLayered]

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
    simp only [indep, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.1.1 hEq.symm

/-! ## 5. The scalar graphs as the one-element instance -/

def liftEdge (e : HyperEdge) : ArrayEdge :=
  { opIdx := e.opIdx, op := .map 1 (ElemProg.single (.scalar e.op) e.srcWires e.dstWire)
  , srcWires := e.srcWires, dstWire := e.dstWire }

/-- A scalar graph as an array graph: every wire of length one, every hyperedge the elementwise map of
its operation. -/
def ofScalar (g : StrictOpenHypergraph) : ArrayGraph :=
  { lengths := List.replicate g.nodeTypes.length 1
  , inputs  := g.boundaryIn.table
  , outputs := g.boundaryOut.table
  , edges   := (extractHyperEdges g).map liftEdge }

/-- A scalar environment as singleton wires. -/
def singletonEnv (env : Nat → Word) : Nat → Vec := fun w => [env w]

theorem edgeValue_lift (env : Nat → Word) (e : HyperEdge) :
    edgeValue (singletonEnv env) (liftEdge e) = [evalHypergraphOpBv e.op (e.srcWires.map env)] := by
  simp only [edgeValue, edgeSrcs, liftEdge, evalArrayOp, List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, evalProg_single, evalElemOp]
  congr 2
  apply List.map_congr_left
  intro s hs
  rw [srcLookup_map (singletonEnv env) e.srcWires s hs]
  rfl

theorem stepEdge_lift (env : Nat → Word) (e : HyperEdge) :
    stepEdge (singletonEnv env) (liftEdge e) = singletonEnv (stepHyperEdgeSyncBv env env e) := by
  funext w
  simp only [stepEdge, stepHyperEdgeSyncBv, singletonEnv, edgeValue_lift]
  simp only [liftEdge]
  by_cases h : w = e.dstWire <;> simp [h]

theorem stepEdgeSync_lift (entry cur : Nat → Word) (e : HyperEdge) :
    stepEdgeSync (singletonEnv entry) (singletonEnv cur) (liftEdge e) =
      singletonEnv (stepHyperEdgeSyncBv entry cur e) := by
  funext w
  simp only [stepEdgeSync, stepHyperEdgeSyncBv, singletonEnv, edgeValue_lift]
  simp only [liftEdge]
  by_cases h : w = e.dstWire <;> simp [h]

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

theorem checkStageIndependent_lift (stage : List HyperEdge) :
    checkStageIndependent (stage.map liftEdge) = OpenHypergraph.checkStageIndependent stage := by
  induction stage with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, checkStageIndependent, OpenHypergraph.checkStageIndependent,
      edgeIndependentOfStage_lift, ih]

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
layering is the scalar 64-bit evaluation of the scalar module's own layering, wire by wire. Both sides
are the combinational evaluation: ours by `layerGraph_sound`, the scalar one lifted stage by stage
(its stages are independent and flatten to the edges, `layerHyperEdges_all_stages_independent`,
`layerHyperEdges_flatten`). -/
theorem ofScalar_layered_sound (g : StrictOpenHypergraph) (env : Nat → Word) :
    evalLayeredSync (singletonEnv env) (layerGraph (ofScalar g)) =
      singletonEnv (evalLayeredStagesSyncBv env (layerHypergraph g)) := by
  rw [(layerGraph_sound (ofScalar g) (singletonEnv env)).2.2, ← evalLayeredSync_lift, layerHypergraph]
  have hInd : ((layerHyperEdges (extractHyperEdges g)).map (·.map liftEdge)).all checkStageIndependent = true := by
    rw [List.all_map]
    have h := layerHyperEdges_all_stages_independent (extractHyperEdges g)
    simp only [List.all_eq_true] at h ⊢
    intro s hs
    simp only [Function.comp_def, checkStageIndependent_lift]
    exact h s hs
  rw [evalLayeredSync_eq_evalLayered _ _ hInd, evalLayered_eq_evalComb_flatten]
  simp only [ofScalar]
  congr 1
  rw [← List.map_flatten, layerHyperEdges_flatten]

/-! ## 6. Fusion of elementwise chains -/

/-- What a map edge has become: the wires its program reads, its program's instructions. -/
structure Def where
  wire : Nat
  srcs : List Nat
  code : List Instr
  deriving Repr

/-- Keep the first instruction of each destination. -/
def dedupeCode (seen : List Nat) : List Instr → List Instr
  | [] => []
  | i :: rest => if seen.contains i.dst then dedupeCode seen rest else i :: dedupeCode (i.dst :: seen) rest

/-- Fuse one edge against the producers so far: a map edge inlines every source a map edge wrote (the
producer's sources become its sources, the producer's instructions precede its own); other edges pass. -/
def fuseEdge (defs : List Def) (e : ArrayEdge) : ArrayEdge × List Def :=
  match e.op with
  | .map n p =>
    let found := e.srcWires.filterMap fun s => defs.find? (·.wire == s)
    let roots := ((e.srcWires.filter fun s => (defs.find? (·.wire == s)).isNone) ++ found.flatMap (·.srcs)).eraseDups
    let code := dedupeCode [] (found.flatMap (·.code)) ++ p.code
    ({ e with op := .map n ⟨code, p.out⟩, srcWires := roots }, ⟨e.dstWire, roots, code⟩ :: defs)
  | _ => (e, defs)

def fuseEdges (defs : List Def) : List ArrayEdge → List ArrayEdge
  | [] => []
  | e :: es =>
    let r := fuseEdge defs e
    r.1 :: fuseEdges r.2 es

/-- Kept after fusion: not a map edge, or an output, or read by an edge that is not a map. -/
def live (outputs : List Nat) (es : List ArrayEdge) (e : ArrayEdge) : Bool :=
  !e.isMap || outputs.contains e.dstWire || es.any fun d => !d.isMap && d.srcWires.contains e.dstWire

def fuseGraph (g : ArrayGraph) : ArrayGraph :=
  let fused := fuseEdges [] g.edges
  { g with edges := fused.filter (live g.outputs fused) }

/-! ### Programs that read what was written -/

/-- Every instruction reads names that are defined: a source, or an earlier destination. -/
def closedFrom (defined : List Nat) : List Instr → Bool
  | [] => true
  | i :: rest => i.args.all defined.contains && closedFrom (i.dst :: defined) rest

theorem closedFrom_mono (S S' : List Nat) (l : List Instr) (h : closedFrom S l = true)
    (hS : ∀ x ∈ S, x ∈ S') : closedFrom S' l = true := by
  induction l generalizing S S' with
  | nil => rfl
  | cons i rest ih =>
    simp only [closedFrom, Bool.and_eq_true, List.all_eq_true] at h ⊢
    refine ⟨?_, ih _ _ h.2 ?_⟩
    · intro a ha
      exact List.contains_iff_mem.mpr (hS a (List.contains_iff_mem.mp (h.1 a ha)))
    · intro x hx
      rcases List.mem_cons.mp hx with h' | h'
      · exact h' ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS x h')

theorem closedFrom_append (S S' : List Nat) (A B : List Instr) (hA : closedFrom S A = true)
    (hB : closedFrom S' B = true) (hS' : ∀ x ∈ S', x ∈ S ∨ x ∈ A.map (·.dst)) :
    closedFrom S (A ++ B) = true := by
  induction A generalizing S with
  | nil =>
    simp only [List.nil_append]
    exact closedFrom_mono S' S B hB fun x hx => by
      rcases hS' x hx with h | h
      · exact h
      · simp at h
  | cons i A ih =>
    simp only [closedFrom, Bool.and_eq_true, List.cons_append] at hA ⊢
    refine ⟨hA.1, ih _ hA.2 ?_⟩
    intro x hx
    rcases hS' x hx with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl (h ▸ List.mem_cons_self)
      · exact Or.inr h

theorem closedFrom_dedupe (S seen : List Nat) (l : List Instr) (h : closedFrom S l = true)
    (hseen : ∀ s ∈ seen, s ∈ S) : closedFrom S (dedupeCode seen l) = true := by
  induction l generalizing S seen with
  | nil => rfl
  | cons i rest ih =>
    simp only [closedFrom, Bool.and_eq_true] at h
    simp only [dedupeCode]
    split
    · rename_i hc
      have hd : i.dst ∈ S := hseen _ (List.contains_iff_mem.mp hc)
      exact ih S seen (closedFrom_mono _ _ _ h.2 fun x hx => by
        rcases List.mem_cons.mp hx with h' | h'
        · exact h' ▸ hd
        · exact h') hseen
    · simp only [closedFrom, Bool.and_eq_true]
      refine ⟨h.1, ih (i.dst :: S) (i.dst :: seen) h.2 ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with h' | h'
      · exact h' ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hseen s h')

theorem mem_dedupe (seen : List Nat) (l : List Instr) (i : Instr) (h : i ∈ dedupeCode seen l) : i ∈ l := by
  induction l generalizing seen with
  | nil => simp [dedupeCode] at h
  | cons j rest ih =>
    simp only [dedupeCode] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih _ h)
    · rcases List.mem_cons.mp h with h' | h'
      · exact h' ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ h')

theorem dst_mem_dedupe (seen : List Nat) (l : List Instr) (x : Nat) (h : x ∈ l.map (·.dst)) :
    x ∈ seen ∨ x ∈ (dedupeCode seen l).map (·.dst) := by
  induction l generalizing seen with
  | nil => simp at h
  | cons j rest ih =>
    simp only [List.map_cons, List.mem_cons] at h
    simp only [dedupeCode]
    split
    · rename_i hc
      rcases h with h | h
      · exact Or.inl (h ▸ List.contains_iff_mem.mp hc)
      · exact ih seen h
    · simp only [List.map_cons, List.mem_cons]
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · rcases ih (j.dst :: seen) h with h' | h'
        · rcases List.mem_cons.mp h' with h'' | h''
          · exact Or.inr (Or.inl h'')
          · exact Or.inl h''
        · exact Or.inr (Or.inr h')

theorem closedFrom_flatMap (R : List Nat) (found : List Def)
    (h : ∀ df ∈ found, closedFrom df.srcs df.code = true ∧ ∀ r ∈ df.srcs, r ∈ R) :
    closedFrom R (found.flatMap (·.code)) = true := by
  induction found with
  | nil => rfl
  | cons df rest ih =>
    simp only [List.flatMap_cons]
    have hdf := h df List.mem_cons_self
    refine closedFrom_append R R _ _ ?_ ?_ (fun x hx => Or.inl hx)
    · exact closedFrom_mono _ _ _ hdf.1 hdf.2
    · exact ih fun d hd => h d (List.mem_cons_of_mem _ hd)

/-- Local values agree with the wires' elements on a set of names. -/
def AgreesOn (loc : Nat → Word) (env : Nat → Vec) (el : Nat) (S : List Nat) : Prop :=
  ∀ w ∈ S, loc w = (env w).getD el 0#64

/-- The wire an instruction names holds, at element `el`, the instruction over its arguments' elements. -/
def ConsistentInstr (env : Nat → Vec) (el : Nat) (i : Instr) : Prop :=
  (env i.dst).getD el 0#64 = evalElemOp i.op (i.args.map fun a => (env a).getD el 0#64)

/-- Running closed code whose instructions the wires satisfy keeps the local values true, and makes
every destination true. -/
theorem runCode_agrees (env : Nat → Vec) (el : Nat) (code : List Instr) (loc : Nat → Word) (S : List Nat)
    (hA : AgreesOn loc env el S) (hC : closedFrom S code = true) (hI : ∀ i ∈ code, ConsistentInstr env el i) :
    ∀ w, w ∈ S ∨ w ∈ code.map (·.dst) → runCode loc code w = (env w).getD el 0#64 := by
  induction code generalizing loc S with
  | nil =>
    intro w hw
    simp only [List.map_nil, List.not_mem_nil, or_false] at hw
    exact hA w hw
  | cons i rest ih =>
    simp only [closedFrom, Bool.and_eq_true, List.all_eq_true] at hC
    have hStep : AgreesOn (stepInstr loc i) env el (i.dst :: S) := by
      intro w hw
      simp only [stepInstr]
      by_cases hwd : w = i.dst
      · subst hwd
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [hI i List.mem_cons_self]
        congr 1
        exact List.map_congr_left fun a ha => hA a (List.contains_iff_mem.mp (hC.1 a ha))
      · simp only [beq_eq_false_iff_ne.mpr hwd, Bool.false_eq_true, ↓reduceIte]
        rcases List.mem_cons.mp hw with h | h
        · exact absurd h hwd
        · exact hA w h
    intro w hw
    simp only [runCode, List.foldl_cons]
    refine ih (stepInstr loc i) (i.dst :: S) hStep hC.2 (fun j hj => hI j (List.mem_cons_of_mem _ hj)) w ?_
    simp only [List.map_cons, List.mem_cons] at hw ⊢
    rcases hw with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

/-! ### The invariant of fusion -/

/-- A producer's record is right, for the lengths `ls`, the whole edge list `all` and the processed
prefix `pre`. -/
structure DefOk (ls : List Nat) (all pre : List ArrayEdge) (df : Def) : Prop where
  closed  : closedFrom df.srcs df.code = true
  outDst  : df.wire ∈ df.code.map (·.dst)
  instrs  : ∀ i ∈ df.code, ∃ d ∈ pre, d.srcWires = i.args ∧ d.dstWire = i.dst ∧
              d.op = .map (ls.getD i.dst 0) (ElemProg.single i.op i.args i.dst)
  lenCode : ∀ i ∈ df.code, ls.getD i.dst 0 = ls.getD df.wire 0
  lenSrcs : ∀ r ∈ df.srcs, ls.getD r 0 = ls.getD df.wire 0
  srcsLt  : ∀ r ∈ df.srcs, r < ls.length
  roots   : ∀ r ∈ df.srcs, ∀ d ∈ all, d.isMap = true → d.dstWire ≠ r

/-- Every processed map edge is a fixpoint of the environment. -/
def Consistent (pre : List ArrayEdge) (env : Nat → Vec) : Prop :=
  ∀ d ∈ pre, d.isMap = true → env d.dstWire = edgeValue env d

structure FuseInv (ls : List Nat) (all pre : List ArrayEdge) (defs : List Def) (env : Nat → Vec) : Prop where
  cons   : Consistent pre env
  defsOk : ∀ df ∈ defs, DefOk ls all pre df
  found  : ∀ d ∈ pre, d.isMap = true → ∃ df ∈ defs, df.wire = d.dstWire

/-- The hypotheses on the whole list: well-formed, destinations written once, no write after a read of
the wire, map edges primitive. -/
structure Hyps (ls : List Nat) (all : List ArrayEdge) : Prop where
  ok    : ∀ d ∈ all, edgeOk ls d = true
  prim  : ∀ d ∈ all, d.primitive = true
  nodup : (all.map (·.dstWire)).Nodup
  nwar  : all.Pairwise fun a b => a.srcWires.contains b.dstWire = false
  self  : ∀ d ∈ all, d.srcWires.contains d.dstWire = false

theorem noWriteAfterRead_pairwise (es : List ArrayEdge) (h : noWriteAfterRead es = true) :
    es.Pairwise (fun a b => a.srcWires.contains b.dstWire = false) ∧
    ∀ d ∈ es, d.srcWires.contains d.dstWire = false := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    simp only [noWriteAfterRead, Bool.and_eq_true, List.all_cons, List.all_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hself, hrest⟩, h2⟩ := h
    obtain ⟨ihp, ihs⟩ := ih h2
    refine ⟨List.pairwise_cons.mpr ⟨hrest, ihp⟩, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with h' | h'
    · exact h' ▸ hself
    · exact ihs d h'

theorem DefOk.mono (ls : List Nat) (all pre : List ArrayEdge) (e : ArrayEdge) (df : Def)
    (h : DefOk ls all pre df) : DefOk ls all (pre ++ [e]) df := by
  have hi : ∀ i ∈ df.code, ∃ d ∈ pre ++ [e], d.srcWires = i.args ∧ d.dstWire = i.dst ∧
      d.op = .map (ls.getD i.dst 0) (ElemProg.single i.op i.args i.dst) := by
    intro i hi
    obtain ⟨d, hd, hrest⟩ := h.instrs i hi
    exact ⟨d, List.mem_append_left _ hd, hrest⟩
  exact { h with instrs := hi }

/-- A primitive map edge, read off. -/
theorem primitive_map (e : ArrayEdge) (n : Nat) (p : ElemProg) (hop : e.op = .map n p) (hp : e.primitive = true) :
    ∃ op, p = ElemProg.single op e.srcWires e.dstWire := by
  simp only [ArrayEdge.primitive, hop] at hp
  cases hc : p.code with
  | nil => simp [hc] at hp
  | cons i rest =>
    cases rest with
    | nil =>
      simp only [hc, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      refine ⟨i.op, ?_⟩
      cases p; cases i
      simp only at hc h1 h2 h3
      subst hc h1 h2 h3
      rfl
    | cons _ _ => simp [hc] at hp

theorem edgeValue_single (env : Nat → Vec) (e : ArrayEdge) (n : Nat) (op : ElemOp)
    (hop : e.op = .map n (ElemProg.single op e.srcWires e.dstWire)) :
    edgeValue env e = (List.range n).map fun el => evalElemOp op (e.srcWires.map fun s => (env s).getD el 0#64) := by
  simp only [edgeValue, hop, evalArrayOp, evalProg_single]
  apply List.map_congr_left
  intro el _
  congr 1
  apply List.map_congr_left
  intro s hs
  simp only [edgeSrcs]
  rw [srcLookup_map env e.srcWires s hs]

/-- From a consistent environment, every recorded instruction holds elementwise. -/
theorem consistent_instr (ls : List Nat) (pre : List ArrayEdge) (env : Nat → Vec) (hC : Consistent pre env)
    (i : Instr) (d : ArrayEdge) (hd : d ∈ pre) (hs : d.srcWires = i.args) (hdst : d.dstWire = i.dst)
    (hop : d.op = .map (ls.getD i.dst 0) (ElemProg.single i.op i.args i.dst))
    (el : Nat) (hel : el < ls.getD i.dst 0) : ConsistentInstr env el i := by
  have hmap : d.isMap = true := by simp [ArrayEdge.isMap, hop]
  have hv := hC d hd hmap
  rw [edgeValue_single env d _ i.op (by rw [hop, hs, hdst])] at hv
  simp only [ConsistentInstr]
  rw [← hdst, hv, getD_range_map _ _ _ el hel, hs]

/-- The fused edge computes what the edge computed. -/
theorem fuseEdge_value (ls : List Nat) (all pre : List ArrayEdge) (defs : List Def) (env : Nat → Vec)
    (hInv : FuseInv ls all pre defs env) (e : ArrayEdge) (hOk : edgeOk ls e = true) (hPrim : e.primitive = true) :
    edgeValue env (fuseEdge defs e).1 = edgeValue env e := by
  cases hop : e.op with
  | map n p =>
    obtain ⟨op, hp⟩ := primitive_map e n p hop hPrim
    subst hp
    simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk
    obtain ⟨⟨⟨_, _⟩, hLen⟩, hOp⟩ := hOk
    simp only [hop, ArrayOp.outLen, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hLen hOp
    obtain ⟨⟨hSame, _⟩, _⟩ := hOp
    simp only [fuseEdge, hop]
    rw [edgeValue_single env e n op hop]
    simp only [edgeValue, evalArrayOp, edgeSrcs]
    apply List.map_congr_left
    intro el hel
    have hel' : el < n := List.mem_range.mp hel
    -- the found producers
    simp only [ElemProg.single]
    generalize hfound : e.srcWires.filterMap (fun s => defs.find? (·.wire == s)) = found
    generalize hroots : ((e.srcWires.filter fun s => (defs.find? (·.wire == s)).isNone) ++ found.flatMap (·.srcs)).eraseDups = roots
    generalize hC : dedupeCode [] (found.flatMap (·.code)) = C
    have hfoundOk : ∀ df ∈ found, DefOk ls all pre df ∧ df.wire ∈ e.srcWires := by
      intro df hdf
      rw [← hfound, List.mem_filterMap] at hdf
      obtain ⟨s, hs, hfind⟩ := hdf
      have hw : df.wire = s := by simpa using List.find?_some hfind
      exact ⟨hInv.defsOk df (List.mem_of_find?_eq_some hfind), hw ▸ hs⟩
    have hrootsSub : ∀ df ∈ found, ∀ r ∈ df.srcs, r ∈ roots := by
      intro df hdf r hr
      rw [← hroots, List.mem_eraseDups, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨df, hdf, hr⟩)
    have hClosedC : closedFrom roots C = true := by
      rw [← hC]
      apply closedFrom_dedupe _ [] _ _ (by simp)
      exact closedFrom_flatMap roots found fun df hdf => ⟨(hfoundOk df hdf).1.closed, hrootsSub df hdf⟩
    have hConsC : ∀ i ∈ C, ConsistentInstr env el i := by
      intro i hi
      have hi' := mem_dedupe _ _ _ (by rw [hC]; exact hi)
      obtain ⟨df, hdf, hidf⟩ := List.mem_flatMap.mp hi'
      obtain ⟨hdfOk, hdfSrc⟩ := hfoundOk df hdf
      obtain ⟨d, hd, hs, hdst, hop'⟩ := hdfOk.instrs i hidf
      apply consistent_instr ls pre env hInv.cons i d hd hs hdst hop' el
      rw [hdfOk.lenCode i hidf, hSame df.wire hdfSrc, ← hLen]
      exact hel'
    let loc : Nat → Word := fun w => (srcLookup (roots.map fun w => (w, env w)) w).getD el 0#64
    have hA : AgreesOn loc env el roots := by
      intro w hw
      simp only [loc]
      rw [srcLookup_map env roots w hw]
    have hRun := runCode_agrees env el C loc roots hA hClosedC hConsC
    -- the consumer's instruction, last
    simp only [evalProg, runCode, List.foldl_append, List.foldl_cons, List.foldl_nil, stepInstr,
      beq_self_eq_true, ↓reduceIte]
    congr 1
    apply List.map_congr_left
    intro s hs
    show runCode loc C s = (env s).getD el 0#64
    apply hRun s
    cases hf : defs.find? (·.wire == s) with
    | none =>
      left
      rw [← hroots, List.mem_eraseDups, List.mem_append]
      exact Or.inl (List.mem_filter.mpr ⟨hs, by simp [hf]⟩)
    | some df =>
      right
      have hdf : df ∈ found := by
        rw [← hfound, List.mem_filterMap]
        exact ⟨s, hs, hf⟩
      have hw : df.wire = s := by simpa using List.find?_some hf
      have hout := (hfoundOk df hdf).1.outDst
      rw [hw] at hout
      have hmem : s ∈ (found.flatMap (·.code)).map (·.dst) := by
        rw [List.map_flatMap]; exact List.mem_flatMap.mpr ⟨df, hdf, hout⟩
      rcases dst_mem_dedupe [] _ s hmem with h | h
      · simp at h
      · rw [← hC]; exact h
  | gather f => simp [fuseEdge, hop]
  | concat => simp [fuseEdge, hop]
  | const vs => simp [fuseEdge, hop]
  | fold op shape => simp [fuseEdge, hop]

theorem fuseEdge_dst (defs : List Def) (e : ArrayEdge) : (fuseEdge defs e).1.dstWire = e.dstWire := by
  cases h : e.op <;> simp [fuseEdge, h]

theorem fuseEdge_isMap (defs : List Def) (e : ArrayEdge) : (fuseEdge defs e).1.isMap = e.isMap := by
  cases h : e.op <;> simp [fuseEdge, h, ArrayEdge.isMap]

/-- Stepping an environment that every processed map edge is a fixpoint of, by an edge that writes no
wire they read, keeps them fixpoints. -/
theorem consistent_step (pre : List ArrayEdge) (env : Nat → Vec) (e : ArrayEdge) (hC : Consistent pre env)
    (hDst : ∀ d ∈ pre, d.dstWire ≠ e.dstWire) (hRead : ∀ d ∈ pre, d.srcWires.contains e.dstWire = false)
    (hSelf : e.srcWires.contains e.dstWire = false) :
    Consistent (pre ++ [e]) (stepEdge env e) := by
  intro d hd hmap
  rcases List.mem_append.mp hd with h | h
  · have hv := hC d h hmap
    simp only [stepEdge]
    rw [edgeValue_update env e.dstWire _ d (hRead d h), beq_eq_false_iff_ne.mpr (hDst d h)]
    simpa using hv
  · simp only [List.mem_singleton] at h
    subst h
    simp only [stepEdge, beq_self_eq_true, ↓reduceIte]
    rw [edgeValue_update env d.dstWire _ d hSelf]

theorem fuseEdges_main (ls : List Nat) (all : List ArrayEdge) (hH : Hyps ls all) :
    ∀ (rest pre : List ArrayEdge) (defs : List Def) (env : Nat → Vec), all = pre ++ rest →
      FuseInv ls all pre defs env →
      evalComb env (fuseEdges defs rest) = evalComb env rest ∧
      ∀ e' ∈ fuseEdges defs rest, edgeOk ls e' = true ∧
        (e'.isMap = true → ∀ r ∈ e'.srcWires, ∀ d ∈ all, d.isMap = true → d.dstWire ≠ r) := by
  intro rest
  induction rest with
  | nil => intro pre defs env _ _; simp [fuseEdges, evalComb]
  | cons e rest ih =>
    intro pre defs env hAll hInv
    have heAll : e ∈ all := by rw [hAll]; exact List.mem_append_right _ List.mem_cons_self
    have hOk := hH.ok e heAll
    have hPrim := hH.prim e heAll
    have hSelf := hH.self e heAll
    -- order facts from the whole list
    have hAll' : all = (pre ++ [e]) ++ rest := by rw [hAll, List.append_assoc, List.singleton_append]
    have hPre : ∀ d ∈ pre, d.srcWires.contains e.dstWire = false ∧ d.dstWire ≠ e.dstWire := by
      intro d hd
      have hp := hH.nwar
      rw [hAll, List.pairwise_append] at hp
      refine ⟨hp.2.2 d hd e List.mem_cons_self, ?_⟩
      have hn := hH.nodup
      rw [hAll, List.map_append, List.nodup_append] at hn
      intro heq
      exact hn.2.2 _ (List.mem_map.mpr ⟨d, hd, rfl⟩) _ (List.mem_map.mpr ⟨e, List.mem_cons_self, rfl⟩) heq
    have hRest : ∀ b ∈ rest, e.srcWires.contains b.dstWire = false := by
      intro b hb
      have hp := hH.nwar
      rw [hAll, List.pairwise_append, List.pairwise_cons] at hp
      exact hp.2.1.1 b hb
    have hStepEq : stepEdge env (fuseEdge defs e).1 = stepEdge env e := by
      funext w
      simp only [stepEdge, fuseEdge_value ls all pre defs env hInv e hOk hPrim, fuseEdge_dst]
    have hCons' : Consistent (pre ++ [e]) (stepEdge env e) :=
      consistent_step pre env e hInv.cons (fun d hd => (hPre d hd).2) (fun d hd => (hPre d hd).1) hSelf
    cases hop : e.op with
    | map n p =>
      obtain ⟨op, hp⟩ := primitive_map e n p hop hPrim
      subst hp
      have hOk' := hOk
      simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk'
      obtain ⟨⟨⟨hDstLt, hSrcLt⟩, hLen⟩, hOp⟩ := hOk'
      simp only [hop, ArrayOp.outLen, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hLen hOp
      obtain ⟨⟨hSame, _⟩, _⟩ := hOp
      have hmap : e.isMap = true := by simp [ArrayEdge.isMap, hop]
      -- the fused edge's pieces
      simp only [fuseEdges, fuseEdge, hop, ElemProg.single]
      generalize hfound : e.srcWires.filterMap (fun s => defs.find? (·.wire == s)) = found
      generalize hroots : ((e.srcWires.filter fun s => (defs.find? (·.wire == s)).isNone) ++ found.flatMap (·.srcs)).eraseDups = roots
      generalize hC : dedupeCode [] (found.flatMap (·.code)) = C
      have hfoundOk : ∀ df ∈ found, DefOk ls all pre df ∧ df.wire ∈ e.srcWires := by
        intro df hdf
        rw [← hfound, List.mem_filterMap] at hdf
        obtain ⟨s, hs, hfind⟩ := hdf
        have hw : df.wire = s := by simpa using List.find?_some hfind
        exact ⟨hInv.defsOk df (List.mem_of_find?_eq_some hfind), hw ▸ hs⟩
      have hrootsSub : ∀ df ∈ found, ∀ r ∈ df.srcs, r ∈ roots := by
        intro df hdf r hr
        rw [← hroots, List.mem_eraseDups, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨df, hdf, hr⟩)
      have hClosedC : closedFrom roots C = true := by
        rw [← hC]
        apply closedFrom_dedupe _ [] _ _ (by simp)
        exact closedFrom_flatMap roots found fun df hdf => ⟨(hfoundOk df hdf).1.closed, hrootsSub df hdf⟩
      -- membership of roots
      have hrootsMem : ∀ r ∈ roots, (r ∈ e.srcWires ∧ defs.find? (·.wire == r) = none) ∨ ∃ df ∈ found, r ∈ df.srcs := by
        intro r hr
        rw [← hroots, List.mem_eraseDups, List.mem_append] at hr
        rcases hr with h | h
        · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
          exact Or.inl ⟨h1, by simpa using h2⟩
        · exact Or.inr (List.mem_flatMap.mp h)
      have hrootsLen : ∀ r ∈ roots, ls.getD r 0 = ls.getD e.dstWire 0 := by
        intro r hr
        rcases hrootsMem r hr with ⟨h, _⟩ | ⟨df, hdf, h⟩
        · exact hSame r h
        · obtain ⟨hdfOk, hdfSrc⟩ := hfoundOk df hdf
          rw [hdfOk.lenSrcs r h]; exact hSame df.wire hdfSrc
      have hrootsLt : ∀ r ∈ roots, r < ls.length := by
        intro r hr
        rcases hrootsMem r hr with ⟨h, _⟩ | ⟨df, hdf, h⟩
        · exact hSrcLt r h
        · exact (hfoundOk df hdf).1.srcsLt r h
      have hrootsNoMap : ∀ r ∈ roots, ∀ d ∈ all, d.isMap = true → d.dstWire ≠ r := by
        intro r hr d hd hdmap
        rcases hrootsMem r hr with ⟨hrs, hnone⟩ | ⟨df, hdf, h⟩
        · intro heq
          rw [hAll, List.mem_append, List.mem_cons] at hd
          rcases hd with hd | hd | hd
          · obtain ⟨df, hdf, hw⟩ := hInv.found d hd hdmap
            rw [List.find?_eq_none] at hnone
            exact hnone df hdf (beq_iff_eq.mpr (hw.trans heq))
          · subst hd
            rw [heq, List.contains_iff_mem.mpr hrs] at hSelf
            exact Bool.noConfusion hSelf
          · have := hRest d hd
            rw [heq, List.contains_iff_mem.mpr hrs] at this
            exact Bool.noConfusion this
        · exact (hfoundOk df hdf).1.roots r h d hd hdmap
      -- instructions of the new code are map instructions of the prefix plus the edge
      have hInstrs : ∀ i ∈ C ++ [⟨op, e.srcWires, e.dstWire⟩], ∃ d ∈ pre ++ [e], d.srcWires = i.args ∧ d.dstWire = i.dst ∧
          d.op = .map (ls.getD i.dst 0) (ElemProg.single i.op i.args i.dst) := by
        intro i hi
        rcases List.mem_append.mp hi with h | h
        · obtain ⟨df, hdf, hidf⟩ := List.mem_flatMap.mp (mem_dedupe _ _ _ (by rw [hC]; exact h))
          obtain ⟨d, hd, hr⟩ := (hfoundOk df hdf).1.instrs i hidf
          exact ⟨d, List.mem_append_left _ hd, hr⟩
        · simp only [List.mem_singleton] at h
          subst h
          exact ⟨e, List.mem_append_right _ List.mem_cons_self, rfl, rfl, by rw [hop, hLen]⟩
      have hCodeLen : ∀ i ∈ C ++ [⟨op, e.srcWires, e.dstWire⟩], ls.getD i.dst 0 = ls.getD e.dstWire 0 := by
        intro i hi
        rcases List.mem_append.mp hi with h | h
        · obtain ⟨df, hdf, hidf⟩ := List.mem_flatMap.mp (mem_dedupe _ _ _ (by rw [hC]; exact h))
          obtain ⟨hdfOk, hdfSrc⟩ := hfoundOk df hdf
          rw [hdfOk.lenCode i hidf]; exact hSame df.wire hdfSrc
        · simp only [List.mem_singleton] at h
          subst h; rfl
      have hCodeDstMap : ∀ i ∈ C ++ [⟨op, e.srcWires, e.dstWire⟩], ∃ d ∈ all, d.isMap = true ∧ d.dstWire = i.dst := by
        intro i hi
        obtain ⟨d, hd, _, hdst, hop'⟩ := hInstrs i hi
        refine ⟨d, ?_, by simp [ArrayEdge.isMap, hop'], hdst⟩
        rw [hAll']; exact List.mem_append_left _ hd
      have hNoRootDst : ∀ i ∈ C ++ [⟨op, e.srcWires, e.dstWire⟩], roots.contains i.dst = false := by
        intro i hi
        obtain ⟨d, hd, hdmap, hdst⟩ := hCodeDstMap i hi
        cases hc : roots.contains i.dst with
        | false => rfl
        | true => exact absurd hdst (hrootsNoMap i.dst (List.contains_iff_mem.mp hc) d hd hdmap)
      have hClosed : closedFrom roots (C ++ [⟨op, e.srcWires, e.dstWire⟩]) = true := by
        refine closedFrom_append roots e.srcWires C [⟨op, e.srcWires, e.dstWire⟩] hClosedC ?_ ?_
        · simp [closedFrom]
        · intro s hs
          cases hf : defs.find? (·.wire == s) with
          | none =>
            left
            rw [← hroots, List.mem_eraseDups, List.mem_append]
            exact Or.inl (List.mem_filter.mpr ⟨hs, by simp [hf]⟩)
          | some df =>
            right
            have hdf : df ∈ found := by rw [← hfound, List.mem_filterMap]; exact ⟨s, hs, hf⟩
            have hw : df.wire = s := by simpa using List.find?_some hf
            have hout := (hfoundOk df hdf).1.outDst
            rw [hw] at hout
            have hmem : s ∈ (found.flatMap (·.code)).map (·.dst) := by
              rw [List.map_flatMap]; exact List.mem_flatMap.mpr ⟨df, hdf, hout⟩
            rcases dst_mem_dedupe [] _ s hmem with h | h
            · simp at h
            · rw [← hC]; exact h
      -- the new producer record
      have hNewDef : DefOk ls all (pre ++ [e]) ⟨e.dstWire, roots, C ++ [⟨op, e.srcWires, e.dstWire⟩]⟩ :=
        { closed := hClosed
        , outDst := by simp
        , instrs := hInstrs
        , lenCode := hCodeLen
        , lenSrcs := hrootsLen
        , srcsLt := hrootsLt
        , roots := hrootsNoMap }
      have hInv' : FuseInv ls all (pre ++ [e]) (⟨e.dstWire, roots, C ++ [⟨op, e.srcWires, e.dstWire⟩]⟩ :: defs) (stepEdge env e) :=
        { cons := hCons'
        , defsOk := fun df hdf => by
            rcases List.mem_cons.mp hdf with h | h
            · exact h ▸ hNewDef
            · exact DefOk.mono ls all pre e df (hInv.defsOk df h)
        , found := fun d hd hdm => by
            rcases List.mem_append.mp hd with h | h
            · obtain ⟨df, hdf, hw⟩ := hInv.found d h hdm
              exact ⟨df, List.mem_cons_of_mem _ hdf, hw⟩
            · simp only [List.mem_singleton] at h
              subst h
              exact ⟨_, List.mem_cons_self, rfl⟩ }
      obtain ⟨ihEval, ihOk⟩ := ih (pre ++ [e]) _ (stepEdge env e) hAll' hInv'
      -- the fused edge is well-formed
      have hOkFused : edgeOk ls { e with op := .map n ⟨C ++ [⟨op, e.srcWires, e.dstWire⟩], e.dstWire⟩, srcWires := roots } = true := by
        simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, ArrayOp.outLen, decide_eq_true_eq,
          Bool.not_eq_true']
        refine ⟨⟨⟨hDstLt, hrootsLt⟩, hLen⟩, ⟨hrootsLen, hNoRootDst⟩, ?_⟩
        exact hNoRootDst ⟨op, e.srcWires, e.dstWire⟩ (List.mem_append_right _ List.mem_cons_self)
      refine ⟨?_, ?_⟩
      · simp only [evalComb, List.foldl_cons] at ihEval ⊢
        have hv : stepEdge env { e with op := .map n ⟨C ++ [⟨op, e.srcWires, e.dstWire⟩], e.dstWire⟩, srcWires := roots } = stepEdge env e := by
          have := hStepEq
          simp only [fuseEdge, hop, ElemProg.single] at this
          rw [hfound, hroots, hC] at this
          exact this
        rw [hv]
        exact ihEval
      · intro e' he'
        rcases List.mem_cons.mp he' with h | h
        · subst h
          exact ⟨hOkFused, fun _ => hrootsNoMap⟩
        · exact ihOk e' h
    | gather f =>
      simp only [fuseEdges, fuseEdge, hop]
      have hInv' : FuseInv ls all (pre ++ [e]) defs (stepEdge env e) :=
        { cons := hCons'
        , defsOk := fun df hdf => DefOk.mono ls all pre e df (hInv.defsOk df hdf)
        , found := fun d hd hdm => by
            rcases List.mem_append.mp hd with h | h
            · exact hInv.found d h hdm
            · simp only [List.mem_singleton] at h; subst h; simp [ArrayEdge.isMap, hop] at hdm }
      obtain ⟨ihEval, ihOk⟩ := ih (pre ++ [e]) defs (stepEdge env e) hAll' hInv'
      refine ⟨?_, ?_⟩
      · simp only [evalComb, List.foldl_cons] at ihEval ⊢; exact ihEval
      · intro e' he'
        rcases List.mem_cons.mp he' with h | h
        · subst h; exact ⟨hOk, fun hm => by simp [ArrayEdge.isMap, hop] at hm⟩
        · exact ihOk e' h
    | concat =>
      simp only [fuseEdges, fuseEdge, hop]
      have hInv' : FuseInv ls all (pre ++ [e]) defs (stepEdge env e) :=
        { cons := hCons'
        , defsOk := fun df hdf => DefOk.mono ls all pre e df (hInv.defsOk df hdf)
        , found := fun d hd hdm => by
            rcases List.mem_append.mp hd with h | h
            · exact hInv.found d h hdm
            · simp only [List.mem_singleton] at h; subst h; simp [ArrayEdge.isMap, hop] at hdm }
      obtain ⟨ihEval, ihOk⟩ := ih (pre ++ [e]) defs (stepEdge env e) hAll' hInv'
      refine ⟨?_, ?_⟩
      · simp only [evalComb, List.foldl_cons] at ihEval ⊢; exact ihEval
      · intro e' he'
        rcases List.mem_cons.mp he' with h | h
        · subst h; exact ⟨hOk, fun hm => by simp [ArrayEdge.isMap, hop] at hm⟩
        · exact ihOk e' h
    | fold op shape =>
      simp only [fuseEdges, fuseEdge, hop]
      have hInv' : FuseInv ls all (pre ++ [e]) defs (stepEdge env e) :=
        { cons := hCons'
        , defsOk := fun df hdf => DefOk.mono ls all pre e df (hInv.defsOk df hdf)
        , found := fun d hd hdm => by
            rcases List.mem_append.mp hd with h | h
            · exact hInv.found d h hdm
            · simp only [List.mem_singleton] at h; subst h; simp [ArrayEdge.isMap, hop] at hdm }
      obtain ⟨ihEval, ihOk⟩ := ih (pre ++ [e]) defs (stepEdge env e) hAll' hInv'
      refine ⟨?_, ?_⟩
      · simp only [evalComb, List.foldl_cons] at ihEval ⊢; exact ihEval
      · intro e' he'
        rcases List.mem_cons.mp he' with h | h
        · subst h; exact ⟨hOk, fun hm => by simp [ArrayEdge.isMap, hop] at hm⟩
        · exact ihOk e' h
    | const vs =>
      simp only [fuseEdges, fuseEdge, hop]
      have hInv' : FuseInv ls all (pre ++ [e]) defs (stepEdge env e) :=
        { cons := hCons'
        , defsOk := fun df hdf => DefOk.mono ls all pre e df (hInv.defsOk df hdf)
        , found := fun d hd hdm => by
            rcases List.mem_append.mp hd with h | h
            · exact hInv.found d h hdm
            · simp only [List.mem_singleton] at h; subst h; simp [ArrayEdge.isMap, hop] at hdm }
      obtain ⟨ihEval, ihOk⟩ := ih (pre ++ [e]) defs (stepEdge env e) hAll' hInv'
      refine ⟨?_, ?_⟩
      · simp only [evalComb, List.foldl_cons] at ihEval ⊢; exact ihEval
      · intro e' he'
        rcases List.mem_cons.mp he' with h | h
        · subst h; exact ⟨hOk, fun hm => by simp [ArrayEdge.isMap, hop] at hm⟩
        · exact ihOk e' h

/-! ### Dropping what nobody reads -/

/-- Two environments differing only at a wire no edge reads evaluate alike away from it. -/
theorem evalComb_unread (x : Nat) (es : List ArrayEdge) (hNo : ∀ d ∈ es, d.srcWires.contains x = false) :
    ∀ (env env' : Nat → Vec), (∀ u, u ≠ x → env' u = env u) →
      ∀ u, u ≠ x → evalComb env' es u = evalComb env es u := by
  induction es with
  | nil => intro env env' h u hu; exact h u hu
  | cons d rest ih =>
    intro env env' h u hu
    simp only [evalComb, List.foldl_cons]
    apply ih (fun d' hd' => hNo d' (List.mem_cons_of_mem _ hd')) (stepEdge env d) (stepEdge env' d) _ u hu
    intro v hv
    simp only [stepEdge]
    have hval : edgeValue env' d = edgeValue env d := by
      apply edgeValue_congr
      intro s hs
      apply h s
      intro heq
      have := hNo d List.mem_cons_self
      rw [← heq, List.contains_iff_mem.mpr hs] at this
      exact Bool.noConfusion this
    rw [hval]
    split
    · rfl
    · exact h v hv

theorem evalComb_filter (keep : ArrayEdge → Bool) (safe : List Nat) (es : List ArrayEdge)
    (hDrop : ∀ p ∈ es, keep p = false → p.dstWire ∉ safe ∧ ∀ d ∈ es, d.srcWires.contains p.dstWire = false) :
    ∀ (env : Nat → Vec), ∀ u ∈ safe, evalComb env (es.filter keep) u = evalComb env es u := by
  induction es with
  | nil => intros; rfl
  | cons p rest ih =>
    intro env u hu
    have hDrop' : ∀ q ∈ rest, keep q = false → q.dstWire ∉ safe ∧ ∀ d ∈ rest, d.srcWires.contains q.dstWire = false :=
      fun q hq hk => ⟨(hDrop q (List.mem_cons_of_mem _ hq) hk).1,
        fun d hd => (hDrop q (List.mem_cons_of_mem _ hq) hk).2 d (List.mem_cons_of_mem _ hd)⟩
    cases hk : keep p with
    | true =>
      rw [List.filter_cons, hk]
      simp only [↓reduceIte]
      show evalComb (stepEdge env p) (rest.filter keep) u = evalComb (stepEdge env p) rest u
      exact ih hDrop' (stepEdge env p) u hu
    | false =>
      rw [List.filter_cons, hk]
      simp only [Bool.false_eq_true, ↓reduceIte]
      show evalComb env (rest.filter keep) u = evalComb (stepEdge env p) rest u
      obtain ⟨hsafe, hno⟩ := hDrop p List.mem_cons_self hk
      have hne : u ≠ p.dstWire := fun h => hsafe (h ▸ hu)
      rw [ih hDrop' env u hu]
      exact (evalComb_unread p.dstWire rest (fun d hd => hno d (List.mem_cons_of_mem _ hd)) env (stepEdge env p)
        (fun v hv => by simp [stepEdge, hv]) u hne).symm

/-- **`fuseGraph_sound`**: on a well-formed graph the fused graph has the same outputs, and its edges
pass `edgeOk`. -/
theorem fuseGraph_sound (g : ArrayGraph) (hWf : g.wf = true) (env : Nat → Vec) :
    evalGraph (fuseGraph g) env = evalGraph g env ∧
    ∀ e ∈ (fuseGraph g).edges, edgeOk g.lengths e = true := by
  have hH : Hyps g.lengths g.edges :=
    { ok := wf_edgeOk g hWf
    , prim := wf_primitive g hWf
    , nodup := wf_nodup g hWf
    , nwar := (noWriteAfterRead_pairwise g.edges (wf_noWriteAfterRead g hWf)).1
    , self := (noWriteAfterRead_pairwise g.edges (wf_noWriteAfterRead g hWf)).2 }
  have hInv0 : FuseInv g.lengths g.edges [] [] env :=
    { cons := fun d hd => by simp at hd
    , defsOk := fun df hdf => by simp at hdf
    , found := fun d hd => by simp at hd }
  obtain ⟨hEval, hOk⟩ := fuseEdges_main g.lengths g.edges hH g.edges [] [] env (by simp) hInv0
  have hMapDst : ∀ e ∈ fuseEdges [] g.edges, e.isMap = true → ∃ d ∈ g.edges, d.isMap = true ∧ d.dstWire = e.dstWire := by
    -- fused edges keep destinations and kinds, one for one
    have : ∀ (defs : List Def) (es : List ArrayEdge), ∀ e ∈ fuseEdges defs es, ∃ d ∈ es, d.isMap = e.isMap ∧ d.dstWire = e.dstWire := by
      intro defs es
      induction es generalizing defs with
      | nil => simp [fuseEdges]
      | cons d rest ih =>
        intro e he
        simp only [fuseEdges, List.mem_cons] at he
        rcases he with h | h
        · exact ⟨d, List.mem_cons_self, by rw [h, fuseEdge_isMap], by rw [h, fuseEdge_dst]⟩
        · obtain ⟨d', hd', hr⟩ := ih _ e h
          exact ⟨d', List.mem_cons_of_mem _ hd', hr⟩
    intro e he hm
    obtain ⟨d, hd, hk, hdst⟩ := this [] g.edges e he
    exact ⟨d, hd, hk.trans hm, hdst⟩
  refine ⟨?_, fun e he => (hOk e (List.mem_filter.mp he).1).1⟩
  simp only [evalGraph, fuseGraph]
  rw [← hEval]
  apply List.map_congr_left
  intro w hw
  apply evalComb_filter (live g.outputs (fuseEdges [] g.edges)) g.outputs (fuseEdges [] g.edges) _ env w hw
  intro p hp hk
  simp only [live, Bool.or_eq_false_iff, Bool.not_eq_false', List.any_eq_false, Bool.and_eq_true,
    Bool.not_eq_true'] at hk
  obtain ⟨⟨hpm, hout⟩, hnon⟩ := hk
  refine ⟨fun h => by rw [List.contains_iff_mem.mpr h] at hout; exact Bool.noConfusion hout, ?_⟩
  intro d hd
  cases hdm : d.isMap with
  | false =>
    cases hc : d.srcWires.contains p.dstWire with
    | false => rfl
    | true => exact absurd ⟨hdm, hc⟩ (hnon d hd)
  | true =>
    obtain ⟨_, hdOk⟩ := hOk d hd
    obtain ⟨q, hq, hqm, hqd⟩ := hMapDst p hp hpm
    cases hc : d.srcWires.contains p.dstWire with
    | false => rfl
    | true => exact absurd hqd (hdOk hdm p.dstWire (List.contains_iff_mem.mp hc) q hq hqm)

theorem fuseGraph_lengths (g : ArrayGraph) : (fuseGraph g).lengths = g.lengths := rfl
theorem fuseGraph_outputs (g : ArrayGraph) : (fuseGraph g).outputs = g.outputs := rfl

end Obend.Hardware.ArrayHypergraph
