module
/-
# Shape and element typing for array hypergraphs

Referents: Accelerate's `Array sh e` and row-major shape representation
(https://www.acceleratehs.org/documentation/users-guide/language.html), and Futhark PLDI 2017,
§§2–3 (https://elsman.com/pdf/pldi17.pdf). Shapes are finite index sets; a gather is contravariant
reindexing. Equal storage sizes do not make `[2,3]` and `[6]` interchangeable in a map.

The physical representation is still a 64-bit word. `fixed q` records a binary scale, not a claim
that overflowing arithmetic computes exact rationals: multiplying scales q and r produces q+r;
rescaling must be explicit. Floating point has no constructor. `predicate` carries canonical 0/1.

A typing derivation contains shape/element compatibility and the structural premises of the graph
rules. Its erasure theorem derives `ArrayGraph.wf`; callers retain this proof rather than deciding
`wf` again at every downstream stage. The checker is a trust boundary, not a theorem about a fixture.
-/
public import Obend.Hardware.Gpu
@[expose] public section

namespace Obend.Hardware.ArrayTyping
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
set_option autoImplicit false

inductive ElemType where
  | word
  | predicate
  | fixed (fractionBits : Nat)
  deriving DecidableEq, Repr

abbrev Shape := List Nat

def Shape.size (s : Shape) : Nat := s.prod

structure TensorType where
  shape : Shape
  elem : ElemType
  deriving DecidableEq, Repr

def TensorType.size (t : TensorType) : Nat := t.shape.size

def defaultType : TensorType := ⟨[0], .word⟩

def wireType (types : List TensorType) (w : Nat) : TensorType := types.getD w defaultType

/-- A shape map selects source indices for the target tensor. -/
abbrev ShapeMap (target source : Shape) := Fin target.size → Fin source.size

abbrev Tensor (shape : Shape) := Fin shape.size → Word

def reindex {target source : Shape} (f : ShapeMap target source) (a : Tensor source) :
    Tensor target := a ∘ f

theorem reindex_id (s : Shape) (a : Tensor s) : reindex id a = a := rfl

theorem reindex_comp {a b c : Shape} (f : ShapeMap a b) (g : ShapeMap b c) (v : Tensor c) :
    reindex f (reindex g v) = reindex (g ∘ f) v := rfl

/-- Numeric signatures follow the physical word arithmetic. A fixed-point product retains its
full binary scale; there is no hidden rounding or rescaling operation. -/
def numeric (t : ElemType) : Bool := match t with
  | .predicate => false
  | _ => true

def productType (a b : ElemType) : Option ElemType := match a, b with
  | .word, .word => some .word
  | .fixed q, .fixed r => some (.fixed (q + r))
  | _, _ => none

def elemSignature (op : ElemOp) (args : List ElemType) (result : ElemType) : Bool :=
  match op, args with
  | .scalar (.const v), [] =>
      result != .predicate || v == 0 || v == 1
  | .scalar .add, [a,b] | .scalar .sub, [a,b] => a == b && result == a && numeric a
  | .scalar .mul, [a,b] => productType a b == some result
  | .scalar (.scale _), [a] => result == a && numeric a
  | .scalar .mac, [a,b,c] => productType a b == some c && result == c
  | .scalar .mux, [p,a,b] => (p == .predicate || p == .word) && a == b && result == a
  | .ult, [.word,.word] => result == .predicate || result == .word
  | .band, [.word,.word] | .bor, [.word,.word] => result == .word
  | .shr, [.word,.word] | .shl, [.word,.word] => result == .word
  | _, _ => false

/-- Shape and element rules, beyond the representation's length discipline. -/
def signatureOk (types : List TensorType) (e : ArrayEdge) : Bool :=
  let dst := wireType types e.dstWire
  let src := e.srcWires.map (wireType types)
  match e.op with
  | .map _ p =>
      src.all (fun t => t.shape == dst.shape) &&
      match p.code with
      | [i] => elemSignature i.op (src.map (·.elem)) dst.elem
      | _ => false
  | .gather _ => src.all (fun t => t.elem == dst.elem)
  | .concat =>
      src.all (fun t => t.elem == dst.elem && t.shape == [t.size]) && dst.shape == [dst.size]
  | .fold _ _ => src.all (fun t => t.elem == .word) && dst.elem == .word
  | .const values =>
      dst.elem != .predicate || values.all (fun x => x == 0#64 || x == 1#64)

/-- The operation's structural rule. Kept separate from `edgeOk` so the derivation exposes every
premise consumed by the erasure theorem. -/
def operationRule (ls : List Nat) (e : ArrayEdge) : Prop :=
  match e.op with
  | .map _ p =>
      (∀ s ∈ e.srcWires, ls.getD s 0 = ls.getD e.dstWire 0) ∧
      (∀ i ∈ p.code, i.dst ∉ e.srcWires) ∧ p.out ∉ e.srcWires
  | .gather f => f.wf = true ∧ e.srcWires.length = 1 ∧ f.target = ls.getD (e.srcWires.getD 0 0) 0
  | .concat => e.srcWires.length = 2
  | .const _ => e.srcWires = []
  | .fold _ shape => e.srcWires.length = 1 ∧ shape.inputLen = ls.getD (e.srcWires.getD 0 0) 0

instance (ls : List Nat) (e : ArrayEdge) : Decidable (operationRule ls e) := by
  unfold operationRule
  split <;> infer_instance

/-- A local typing rule includes wire scope and the result's representation size. -/
def EdgeTyping (types : List TensorType) (ls : List Nat) (e : ArrayEdge) : Prop :=
  e.dstWire < ls.length ∧
  (∀ s ∈ e.srcWires, s < ls.length) ∧
  e.op.outLen (e.srcWires.map (ls.getD · 0)) = ls.getD e.dstWire 0 ∧
  operationRule ls e ∧ e.primitive = true ∧ signatureOk types e = true

instance (types : List TensorType) (ls : List Nat) (e : ArrayEdge) :
    Decidable (EdgeTyping types ls e) := by unfold EdgeTyping; infer_instance

theorem EdgeTyping.edgeOk {types : List TensorType} {ls : List Nat} {e : ArrayEdge}
    (h : EdgeTyping types ls e) : edgeOk ls e = true := by
  rcases h with ⟨hd, hs, hl, hop, _, _⟩
  simp only [Obend.Hardware.ArrayHypergraph.edgeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨hd, hs⟩, hl⟩, ?_⟩
  cases hOp : e.op <;> simp_all [operationRule, Bool.and_eq_true, List.all_eq_true,
    Bool.not_eq_true', List.contains_iff_mem, beq_iff_eq]

/-- SSA scope is stronger than the legacy graph invariant: every read must have a producer
or name an input, and inputs cannot be overwritten. -/
def definedBeforeUse : List Nat → List ArrayEdge → Bool
  | _, [] => true
  | available, e :: es =>
      e.srcWires.all available.contains && !available.contains e.dstWire &&
      definedBeforeUse (e.dstWire :: available) es

/-- Global typing: each wire has one shape and element type, destinations are unique, and a read
cannot precede its producer. These are reusable derivation premises, not an assumption of `wf`. -/
def GraphTyping (types : List TensorType) (g : ArrayGraph) : Prop :=
  types.map TensorType.size = g.lengths ∧
  (∀ w ∈ g.inputs, w < g.lengths.length) ∧
  (∀ w ∈ g.outputs, w < g.lengths.length) ∧
  (∀ e ∈ g.edges, EdgeTyping types g.lengths e) ∧
  (g.edges.map (·.dstWire)).Nodup ∧
  noWriteAfterRead g.edges = true ∧
  definedBeforeUse g.inputs g.edges = true ∧
  g.outputs.all (fun w => g.inputs.contains w || (g.edges.map (·.dstWire)).contains w) = true

instance (types : List TensorType) (g : ArrayGraph) : Decidable (GraphTyping types g) := by
  unfold GraphTyping
  infer_instance

theorem GraphTyping.wf {types : List TensorType} {g : ArrayGraph}
    (h : GraphTyping types g) : g.wf = true := by
  rcases h with ⟨_, hi, ho, he, hn, hr, _, _⟩
  simp only [ArrayGraph.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hi, ho⟩, fun e h => (he e h).edgeOk⟩, hn⟩, hr⟩,
    fun e h => (he e h).2.2.2.2.1⟩

structure TypedGraph where
  graph : ArrayGraph
  types : List TensorType
  typing : GraphTyping types graph

/-- The boundary checker constructs a proof once. The returned object is consumed by all later
passes, and failure names whether shape representation, edge typing, or graph scope failed. -/
def checkTypedGraph (types : List TensorType) (g : ArrayGraph) : Except String TypedGraph :=
  if h : GraphTyping types g then .ok ⟨g, types, h⟩
  else if types.map TensorType.size != g.lengths then .error "tensor shapes do not match wire storage lengths"
  else match g.edges.find? (fun e => !decide (EdgeTyping types g.lengths e)) with
    | some e => .error s!"array operation {e.opIdx} at wire {e.dstWire}: invalid shape, element signature, or wire scope"
    | none => .error "graph boundary or single-assignment ordering is invalid"

/-- A successful boundary check retains precisely its input graph and annotations. -/
theorem checkTypedGraph_result (types : List TensorType) (g : ArrayGraph) (t : TypedGraph)
    (h : checkTypedGraph types g = .ok t) : t.graph = g ∧ t.types = types := by
  unfold checkTypedGraph at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h
    · split at h <;> cases h

theorem checkTypedGraph_graph (types : List TensorType) (g : ArrayGraph) (t : TypedGraph)
    (h : checkTypedGraph types g = .ok t) : t.graph = g :=
  (checkTypedGraph_result types g t h).1

theorem checkTypedGraph_typing (types : List TensorType) (g : ArrayGraph) (t : TypedGraph)
    (h : checkTypedGraph types g = .ok t) : GraphTyping types g := by
  obtain ⟨hg, ht⟩ := checkTypedGraph_result types g t h
  simpa [hg, ht] using t.typing

/-- Explicit word-vector annotation for frontends whose source type is a flat word array. -/
def wordTypes (g : ArrayGraph) : List TensorType := g.lengths.map (fun n => ⟨[n], .word⟩)

def TypedGraph.lower (g : TypedGraph) : Gpu.GpuProgram := Gpu.lowerArrayToGpu g.graph

theorem TypedGraph.lower_sound (g : TypedGraph) (env : Nat → Vec) (flat : Nat → Word)
    (hGood : Gpu.Good g.graph.lengths env) (hFlat : Gpu.Flat g.graph.lengths env flat) :
    Gpu.runProgram g.lower flat = evalGraph g.graph env :=
  Gpu.lowerArrayToGpu_sound g.graph g.typing.wf env flat hGood hFlat

end Obend.Hardware.ArrayTyping
