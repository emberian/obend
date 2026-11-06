import Obend.Hardware.ArrayTyping
import Lean.Data.Json

/-!
Reads catgrad's serde `core::Term`, whose graph is open-hypergraphs' lax OpenHypergraph.
The envelope supplies concrete input tensor types and independently evaluated test vectors.
Only quotiented, topologically ordered U32 tensor graphs are admitted. Unsupported operations
are errors containing the serialized operation, never guessed or replaced with an identity.
This importer is executable, not a proved catgrad compiler. The GPU lowering theorem starts at
its checked ArrayGraph; the external catgrad interpreter comparison is a separate finite gate.
-/
namespace Obend.Hardware.Gpu.CatgradImport
open Lean Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph

structure TestVector where
  inputs : List (List Nat)
  outputs : List (List Nat)
  deriving FromJson

structure Imported where
  name : String
  typed : Obend.Hardware.ArrayTyping.TypedGraph
  vectors : List TestVector

def Imported.graph (i : Imported) : ArrayGraph := i.typed.graph

private structure Tensor where
  wire : Nat
  shape : List Nat

private structure Build where
  lengths : Array Nat := #[]
  edges : Array ArrayEdge := #[]
  types : Array Obend.Hardware.ArrayTyping.TensorType := #[]

private abbrev M := StateT Build (Except String)

private def node (n : Nat) (op : ArrayOp) (srcs : List Nat) : M Nat := do
  let s ← get
  let w := s.lengths.size
  let next : Build := {
    lengths := s.lengths.push n
    edges := s.edges.push ⟨s.edges.size, op, srcs, w⟩
    types := s.types.push ⟨[n], .word⟩ }
  set next
  return w

private def fresh (n : Nat) : M Nat := do
  let s ← get
  set { s with lengths := s.lengths.push n, types := s.types.push ⟨[n], .word⟩ }
  return s.lengths.size

private def mapOp (n : Nat) (op : ElemOp) (srcs : List Nat) : M Nat := do
  let s ← get
  node n (.map n (ElemProg.single op srcs s.lengths.size)) srcs

private def constant (n : Nat) (v : Nat) : M Nat :=
  node n (.const (List.replicate n (BitVec.ofNat 64 v))) []

/-- U32 arithmetic is explicitly reduced modulo 2^32, at every U32 output boundary. -/
private def mask32 (n w : Nat) : M Nat := do
  let mask ← constant n 4294967295
  mapOp n .band [w, mask]

private def gather (sourceLen : Nat) (indices : List Nat) (w : Nat) : M Nat :=
  node indices.length (.gather ⟨indices.length, sourceLen, indices⟩) [w]

private def fail {α : Type} (message : String) : M α := throw message

private def shapeSize (shape : List Nat) : Nat := shape.foldl (· * ·) 1

private def mapScalar (op : String) (args : List Tensor) : M Tensor := do
  let (arity, elem, wrap) ← match op with
    | "Add" => pure (2, ElemOp.scalar .add, true)
    | "Sub" => pure (2, ElemOp.scalar .sub, true)
    | "Mul" => pure (2, ElemOp.scalar .mul, true)
    | "LT" => pure (2, ElemOp.ult, false)
    | "Where" => pure (3, ElemOp.scalar .mux, false)
    | _ => fail s!"unsupported catgrad operation Tensor.Map.{op}"
  let some first := args.head? | fail s!"Map {op}: missing operand"
  unless args.all (·.shape == first.shape) do fail s!"Map {op}: shape mismatch (implicit broadcasting unsupported)"
  let n := shapeSize first.shape
  let ws := args.map (·.wire)
  unless args.length == arity do fail s!"Map {op}: expected {arity} operands"
  let w ← mapOp n elem ws
  let w ← if wrap then mask32 n w else pure w
  return ⟨w, first.shape⟩

private def matmul (args : List Tensor) : M Tensor := do
  let [a,b] := args | fail "MatMul: expected two tensors"
  let [rows,inner] := a.shape | fail "MatMul: only rank-2 tensors currently supported"
  let [inner',cols] := b.shape | fail "MatMul: only rank-2 tensors currently supported"
  unless inner == inner' do fail "MatMul: contraction dimensions disagree"
  let n := rows * cols
  let terms := n * inner
  let x ← gather (rows * inner)
    ((List.range terms).map fun e => (e / inner / cols) * inner + e % inner) a.wire
  let y ← gather (inner * cols)
    ((List.range terms).map fun e => (e % inner) * cols + (e / inner) % cols) b.wire
  let products ← mapOp terms (.scalar .mul) [x,y]
  -- Each U32 product fits U64; reducing modulo 2^64 then masking gives the same
  -- U32 ring sum as wrapping at every addition. This is not a float reassociation.
  let sum ← node n (.segReduce .add (List.replicate n inner)) [products]
  let sum ← mask32 n sum
  return ⟨sum, [rows,cols]⟩

private def lowerOp (j : Json) (args : List Tensor) : M Tensor := do
  let arr ← match j.getObjVal? "Arr" with
    | .ok v => pure v
    | .error _ => fail s!"unsupported catgrad operation {j.compress} (definitions must be expanded)"
  if arr == Json.str "Copy" then
    let [a] := args | fail "Copy: expected one input"
    return a
  let tensor ← match arr.getObjVal? "Tensor" with
    | .ok v => pure v
    | .error _ => fail s!"unsupported catgrad operation {arr.compress}"
  if tensor == Json.str "MatMul" then return ← matmul args
  match tensor.getObjValAs? String "Map" with
  | .ok op => mapScalar op args
  | .error _ => fail s!"unsupported catgrad operation Tensor.{tensor.compress}"

private def getTensor (nodes : Array (Option Tensor)) (i : Nat) : M Tensor :=
  match (nodes[i]?).join with
  | some t => pure t
  | none => fail s!"catgrad wire {i}: out of range or read before definition"

private def lower (j : Json) : M (String × Obend.Hardware.ArrayTyping.TypedGraph × List TestVector) := do
  let format ← j.getObjValAs? String "format"
  unless format == "catgrad-core-u32-v1" do fail s!"unsupported catgrad envelope {format}"
  let name ← j.getObjValAs? String "name"
  let term ← j.getObjVal? "term"
  let h ← term.getObjVal? "hypergraph"
  let labels ← h.getObjValAs? (List String) "nodes"
  unless labels.all (· == "Tensor") do fail "unsupported catgrad node type (only Tensor supported)"
  let quotient ← h.getObjValAs? (List (List Nat)) "quotient"
  unless quotient == [[],[]] do fail "catgrad quotient must be resolved before import"
  let sources ← term.getObjValAs? (List Nat) "sources"
  let targets ← term.getObjValAs? (List Nat) "targets"
  let types ← j.getObjValAs? (List Json) "inputTypes"
  unless sources.length == types.length do fail "catgrad inputTypes count mismatch"
  let mut nodes : Array (Option Tensor) := Array.replicate labels.length none
  let mut inputs := []
  for (i,ty) in sources.zip types do
    unless i < nodes.size do fail s!"catgrad source {i} out of range"
    unless ((nodes[i]?).join).isNone do fail s!"catgrad duplicate input {i}"
    let dtype ← ty.getObjValAs? String "dtype"
    unless dtype == "U32" do fail s!"unsupported catgrad dtype {dtype}; IEEE floating point is not integer arithmetic"
    let shape ← ty.getObjValAs? (List Nat) "shape"
    let w ← fresh (shapeSize shape)
    modify fun s => { s with types := s.types.set! w ⟨shape, .word⟩ }
    -- A shape-changing identity gather makes flattening explicit in the typed graph.
    let flat ← gather (shapeSize shape) (List.range (shapeSize shape)) w
    nodes := nodes.set! i (some ⟨flat,shape⟩)
    inputs := inputs ++ [w]
  let mut consumed : List Nat := []
  let edges ← h.getObjValAs? (List Json) "edges"
  let adjacency ← h.getObjValAs? (List Json) "adjacency"
  unless edges.length == adjacency.length do fail "catgrad edges/adjacency count mismatch"
  for (op,adj) in edges.zip adjacency do
    let ss ← adj.getObjValAs? (List Nat) "sources"
    let ts ← adj.getObjValAs? (List Nat) "targets"
    for source in ss do
      if source ∈ consumed then fail s!"catgrad wire {source}: multiple reads require explicit Copy"
      consumed := source :: consumed
    let args ← ss.mapM (getTensor nodes)
    let result ← lowerOp op args
    let isCopy := (op.getObjVal? "Arr").toOption == some (Json.str "Copy")
    unless isCopy || ts.length == 1 do fail s!"catgrad operation {op.compress}: expected one target"
    unless !ts.isEmpty do fail "catgrad Copy: empty target list unsupported"
    for dst in ts do
      unless dst < nodes.size do fail s!"catgrad destination {dst} out of range"
      unless ((nodes[dst]?).join).isNone do fail s!"catgrad destination {dst} written twice"
      nodes := nodes.set! dst (some result)
  for target in targets do
    if target ∈ consumed then fail s!"catgrad output {target}: already consumed (requires Copy)"
    consumed := target :: consumed
  let outputs ← targets.mapM fun i => do
    let t ← getTensor nodes i
    let n := shapeSize t.shape
    let w ← gather n (List.range n) t.wire
    modify fun s => { s with types := s.types.set! w ⟨t.shape, .word⟩ }
    return w
  let state ← get
  let graph : ArrayGraph := ⟨state.lengths.toList, inputs, outputs, state.edges.toList⟩
  let typed ← Obend.Hardware.ArrayTyping.checkTypedGraph state.types.toList graph
  let vectors ← j.getObjValAs? (List TestVector) "vectors"
  unless !vectors.isEmpty do fail "catgrad requires at least one independent interpreter vector"
  for v in vectors do
    for (ws, boundary) in [(v.inputs, inputs), (v.outputs, outputs)] do
      unless ws.length == boundary.length do fail "catgrad vector boundary count mismatch"
      for (vals,w) in ws.zip boundary do
        unless vals.length == graph.lengths.getD w 0 do fail "catgrad vector shape mismatch"
        unless vals.all (· < 4294967296) do fail "catgrad U32 vector value out of range"
  return (name,typed,vectors)

def importJson (j : Json) : Except String Imported := do
  let ((name,typed,vectors),_) ← (lower j).run {}
  return ⟨name,typed,vectors⟩

private def wiresText (ws : List (List Nat)) : String :=
  String.intercalate ";" (ws.map fun xs => if xs.isEmpty then "-" else String.intercalate "," (xs.map toString))

/-- Check every oracle vector against the Lean array evaluator before writing any GPU artifact. -/
def writeFile (source dir : System.FilePath) (plant : Plant := .none) : IO Unit := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile source))
  let imported ← IO.ofExcept (importJson j)
  let g := imported.graph
  let mut lines := []
  for (v,i) in imported.vectors.zipIdx do
    let env := mkEnv g.lengths g.inputs (v.inputs.map fun xs => xs.map (BitVec.ofNat 64))
    let got := evalGraphArr g ((List.range g.lengths.length).map fun w => (env w).toArray).toArray
    unless got.map (List.map BitVec.toNat) == v.outputs do
      throw <| IO.userError s!"catgrad interpreter/model disagreement at vector {i}"
    lines := lines ++ [s!"{i}\t{wiresText v.inputs}\t{wiresText v.outputs}"]
  let p := imported.typed.lower
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (emitPlanJson imported.name p)
  for (s,k) in p.stages.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (emitStageWgsl plant imported.name k p.stages.length s)
  IO.FS.writeFile (dir / "expected.tsv") (String.intercalate "\n" lines ++ "\n")
  IO.println s!"{imported.name}: {g.edges.length} edges, {p.stages.length} dispatches, {imported.vectors.length} catgrad interpreter vectors agree with Lean model"

end Obend.Hardware.Gpu.CatgradImport
