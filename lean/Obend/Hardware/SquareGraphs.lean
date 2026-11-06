module
/-
# Obend.Hardware.SquareGraphs — the graphs both gates run

One list of graphs with their test vectors, shared by `obend-emit-gpu` (`lean/tools/emitgpu`: the
shaders, plan and `expected.tsv` of `hardware/gpu/graphs/<graph>/`) and `obend-emit-sv`'s `square-<graph>`
targets (`lean/tools/emitsv`: the SystemVerilog, the LEC half, the Verilator harness and the HDL model's
expected values of `hardware/gpu/square/`). `squarePlan` names the ones the square runs through both
devices and what each is for; `squareGraph` checks a selected entry and pairs it with its `RtlModule`.

The scalar fixtures (`treeGraph`, `muxChainGraph`, `allOpsGraph`), aliases compiling the field and
Stockham NTT source programs, the independent NTT references (`nttFast` and `nttReference`), and the
vectors (`vectorFor`) are here; `expectedTsv` prints `expected.tsv` from any model of the outputs, so the
array model's file and the HDL model's can be compared byte for byte.
-/
public import Obend.Hardware.Square
public import Obend.Hardware.Gpu.ArrayPrograms
public import Obend.Hardware.Gpu.SoacPrograms
public import Obend.Hardware.Gpu.SourcePrograms
@[expose] public section

namespace Obend.Hardware.SquareGraphs
open Obend.Hardware.HDL
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.Square

/-! ## Shared source programs

The source builder lives in ArrayPrograms. Both devices consume its general compiler;
there is no parallel graph-wire builder here. GPU admission also checks the actual
Core4 composition member and retains the shape/element derivation.
-/
export Obend.Hardware.Gpu.ArrayPrograms (goldilocksP powMod rootOfUnity2to32 rootOfUnity)

def nttGraph (n : Nat) : ArrayGraph :=
  ArraySource.compile [n] (ArrayPrograms.nttSource n)

/-- The naive DFT over the Goldilocks field, `y_k = Σ_j x_j ω^{jk}`, with a table of the powers of `ω`. -/
def nttReference (xs : List Nat) : List Nat :=
  let n := xs.length
  if n == 0 then [] else
  let ω := rootOfUnity n
  let pw : Array Nat := (Array.range n).map fun i => powMod ω i goldilocksP
  let xa := xs.toArray
  (List.range n).map fun k =>
    (List.range n).foldl (fun acc j => (acc + xa[j]! * pw[(j * k) % n]!) % goldilocksP) 0

/-- The recursive radix-2 NTT in `Nat` arithmetic: `y_k = E_k + ω^k O_k`, `y_{k+n/2} = E_k - ω^k O_k`. -/
partial def nttFast (xs : Array Nat) (ω : Nat) : Array Nat :=
  let n := xs.size
  if n ≤ 1 then xs else
  let half := n / 2
  let ω2 := ω * ω % goldilocksP
  let ev := nttFast ((Array.range half).map fun i => xs[2 * i]!) ω2
  let od := nttFast ((Array.range half).map fun i => xs[2 * i + 1]!) ω2
  let pw := (Array.range half).map fun j => powMod ω j goldilocksP
  (Array.range n).map fun j =>
    if j < half then (ev[j]! + pw[j]! * od[j]! % goldilocksP) % goldilocksP
    else
      let j' := j - half
      (ev[j']! + goldilocksP - pw[j']! * od[j']! % goldilocksP) % goldilocksP

/-! ## Array graphs besides the NTT -/

def macReverseGraph (n : Nat) : ArrayGraph :=
  ArraySource.compile [n, n] (ArrayPrograms.macReverseSource n)

def glMulGraph (n : Nat) : ArrayGraph :=
  ArraySource.compile [n, n] (ArrayPrograms.glMulSource n)

/-! ## Scalar graphs, as their one-element instance -/

def treeGraph (n : Nat) : StrictOpenHypergraph :=
  let rec levels (fuel : Nat) (lo cnt nextWire opIdx : Nat) (acc : List HyperEdge) : List HyperEdge × Nat :=
    match fuel with
    | 0 => (acc, lo)
    | fuel + 1 =>
      if cnt ≤ 1 then (acc, lo)
      else
        let half := cnt / 2
        let edges := (List.range half).map fun i =>
          { opIdx := opIdx + i, op := HypergraphOp.add, srcWires := [lo + 2 * i, lo + 2 * i + 1]
          , dstWire := nextWire + i : HyperEdge }
        levels fuel nextWire half (nextWire + half) (opIdx + half) (acc ++ edges)
  let (edges, root) := levels (n + 1) 0 n n 0 []
  let numWires := if n ≤ 1 then n else 2 * n - 1
  mkStrictOpenHypergraph numWires (List.range n) [root] edges

def muxChainGraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 8 [0, 1, 2, 3] [4, 7]
    [ { opIdx := 0, op := .mux,     srcWires := [0, 1, 2], dstWire := 4 }
    , { opIdx := 1, op := .mul,     srcWires := [4, 3],    dstWire := 5 }
    , { opIdx := 2, op := .const 5, srcWires := [],        dstWire := 6 }
    , { opIdx := 3, op := .mux,     srcWires := [5, 6, 0], dstWire := 7 } ]

def allOpsGraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 11 [0, 1, 2] [8, 9, 10]
    [ { opIdx := 0, op := .scale 3,           srcWires := [0],       dstWire := 3 }
    , { opIdx := 1, op := .mac,               srcWires := [1, 2, 0], dstWire := 4 }
    , { opIdx := 2, op := .const (-7),        srcWires := [],        dstWire := 5 }
    , { opIdx := 3, op := .sub,               srcWires := [3, 4],    dstWire := 6 }
    , { opIdx := 4, op := .mul,               srcWires := [6, 5],    dstWire := 7 }
    , { opIdx := 5, op := .add,               srcWires := [7, 3],    dstWire := 8 }
    , { opIdx := 6, op := .scale (-(2 ^ 40)), srcWires := [4],       dstWire := 9 }
    , { opIdx := 7, op := .mux,               srcWires := [0, 8, 9], dstWire := 10 } ]

/-! ## The graphs and their vectors -/

inductive Kind where
  | plain
  | ntt
  deriving DecidableEq

/-- The scalar graphs: name, the Lean definition's name, the graph. -/
def scalarGraphs : List (String × String × StrictOpenHypergraph) :=
  [ ("diamond", "Obend.Hardware.OpenHypergraph.goldenDiamondHypergraph", goldenDiamondHypergraph)
  , ("optic-mul", "Obend.Hardware.OpenHypergraph.compileOpticToHypergraph .mul", compileOpticToHypergraph .mul)
  , ("optic-linearmac", "Obend.Hardware.OpenHypergraph.compileOpticToHypergraph (.linearMac 7)",
      compileOpticToHypergraph (.linearMac 7))
  , ("optic-bilinear", "Obend.Hardware.OpenHypergraph.compileOpticToHypergraph (.bilinear (-3))",
      compileOpticToHypergraph (.bilinear (-3)))
  , ("adjoint-mul-add",
      "Obend.Hardware.OpenHypergraph.compileGraphAdjoint (compileOpticChain2FwdHypergraph .mul .add)",
      compileGraphAdjoint (compileOpticChain2FwdHypergraph .mul .add))
  , ("adjoint-square-bilinear",
      "Obend.Hardware.OpenHypergraph.compileGraphAdjoint (compileOpticChain2FwdHypergraph .square (.bilinear 5))",
      compileGraphAdjoint (compileOpticChain2FwdHypergraph .square (.bilinear 5)))
  , ("allops", "Obend.Hardware.SquareGraphs.allOpsGraph", allOpsGraph)
  , ("muxchain", "Obend.Hardware.SquareGraphs.muxChainGraph", muxChainGraph)
  , ("tree512", "Obend.Hardware.SquareGraphs.treeGraph 512", treeGraph 512) ]

/-- Selection builds only the requested graph, keeping its checked typing receipt. -/
structure GraphCase where
  name : String
  definition : String
  build : Unit → Except String Obend.Hardware.ArrayTyping.TypedGraph
  kind : Kind

def scalarCase (name definition : String) (graph : StrictOpenHypergraph) : GraphCase :=
  ⟨name, definition, fun _ => Obend.Hardware.ArrayTyping.checkTypedGraph
    (Obend.Hardware.ArrayTyping.wordTypes (ofScalar graph)) (ofScalar graph), .plain⟩

def sourceCase (name definition : String) (lengths : List Nat)
    (source : Unit → ArraySource.Program) (kind : Kind := .plain) : GraphCase :=
  ⟨name, definition, fun _ => (ArrayPrograms.compileSource name lengths (source ())).map (·.typed), kind⟩

def graphTypes (name : String) (g : ArrayGraph) : List Obend.Hardware.ArrayTyping.TensorType :=
  if name == "source-leaf-fixed-square" then
    g.lengths.zipIdx.map fun (n, w) => ⟨[n], .fixed (if w == 0 then 8 else 16)⟩
  else Obend.Hardware.ArrayTyping.wordTypes g

/-- One shared workload registry for GPU and RTL emission; field/NTT/SOAC entries
are source members, and scalar book entries use the checked Core4 recognizer. -/
def graphs : List GraphCase :=
  scalarGraphs.map (fun (name, definition, g) => scalarCase name definition g) ++
  [sourceCase "mac-reverse-1000" "Obend.Hardware.SquareGraphs.macReverseGraph 1000" [1000, 1000]
      (fun _ => ArrayPrograms.macReverseSource 1000)] ++
  [4, 256].map (fun n => sourceCase s!"glmul-{n}" s!"Obend.Hardware.SquareGraphs.glMulGraph {n}"
      [n, n] (fun _ => ArrayPrograms.glMulSource n) .ntt) ++
  [4, 16, 64, 1024, 65536].map (fun n => sourceCase s!"ntt-{n}" s!"Obend.Hardware.SquareGraphs.nttGraph {n}"
      [n] (fun _ => ArrayPrograms.nttSource n) .ntt) ++
  SoacPrograms.cases.map (fun (name, ns) =>
    sourceCase name s!"Obend.Hardware.Gpu.SoacPrograms.graph {repr ns}" [ns.sum]
      (fun _ => SoacPrograms.source ns)) ++
  SourcePrograms.cases.map (fun c =>
    ⟨c.name, s!"Core4 source member {c.name}", fun _ => do
      let p ← c.compile
      Obend.Hardware.ArrayTyping.checkTypedGraph (graphTypes c.name p.plan.graph) p.plan.graph,
      .plain⟩)

def pool : List Int :=
  [0, 1, -1, 2, 3, -3, 10, 255, -256, 65535, 2 ^ 31, -(2 ^ 31), 2 ^ 32 + 1, 2 ^ 62, -(2 ^ 62),
   2 ^ 63 - 1, -(2 ^ 63), 123456789, -987654321]

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A deterministic pseudo-random 64-bit word for element `i` of input `w` of vector `v`. -/
def draw (v w i : Nat) : Nat :=
  (List.range (i % 7 + 1)).foldl (fun acc _ => lcg acc) (lcg (v * 7919 + w * 104729 + i * 31 + 17))

def signed (s : Nat) : Int := (s : Int) - (if s ≥ 2 ^ 63 then 2 ^ 64 else 0)

/-- Vector `v` for a graph: field elements (`< p`) for the field graphs; otherwise the first six vectors
walk the pool, the next four are one-hot (one input wire holds `7`, every other `0`: an operator whose
result reaches an output only through a test against zero, as `muxchain`'s multiply does, is seen only
by a vector with a zero operand), and later ones are pseudo-random words. -/
def vectorFor (kind : Kind) (lens : List Nat) (v : Nat) : List (List Int) :=
  lens.zipIdx.map fun (n, w) =>
    (List.range n).map fun i =>
      match kind with
      | .ntt => (draw v w i % goldilocksP : Int)
      | .plain =>
        if v < 6 then pool.getD ((i + w + 3 * v) % pool.length) 0
        else if v < 10 then (if w == v - 6 then 7 else 0)
        else signed (draw v w i)

def vectorCount (g : ArrayGraph) : Nat :=
  let total := sumNatList (g.inputs.map (g.lengths.getD · 0))
  if total ≥ 2 ^ 14 then 2 else if total ≥ 64 then 6 else 12

/-! ## Expected values and the checks -/

def wireText (xs : List Int) : String :=
  if xs.isEmpty then "-" else String.intercalate "," (xs.map toString)

def wiresText (ws : List (List Int)) : String := String.intercalate ";" (ws.map wireText)

def toVec (xs : List Int) : Vec := xs.map (BitVec.ofInt 64)

/-- The vectors of a graph, as drawn: per vector, per input wire, the elements as integers. -/
def graphVectors (g : ArrayGraph) (kind : Kind) (name : String := "") : List (List (List Int)) :=
  match SourcePrograms.sourceVectors? name with
  | some vs => vs.map fun inputs => inputs.map fun xs => xs.map (·.toInt)
  | none =>
    let inLens := g.inputs.map (g.lengths.getD · 0)
    (List.range (vectorCount g)).map (vectorFor kind inLens)

/-- `expected.tsv`: one line per vector, index, the input wires, and the output wires `model` gives
(wires separated by `;`, elements by `,`, signed 64-bit). -/
def expectedTsvValues (vectors : List (List (List Int))) (outputs : List (List Vec)) : String :=
  let signed64 (ws : List Int) : List Int := ws.map fun x => (BitVec.ofInt 64 x).toInt
  let lines := (vectors.zip outputs).zipIdx.map fun ((vals, result), v) =>
    s!"{v}\t{wiresText (vals.map signed64)}\t{wiresText (result.map fun ws => ws.map (·.toInt))}"
  String.intercalate "\n" lines ++ "\n"

def expectedTsv (g : ArrayGraph) (kind : Kind) (model : List (List Int) → List Vec)
    (name : String := "") : String :=
  let vectors := graphVectors g kind name
  expectedTsvValues vectors (vectors.map model)

/-- The array model's outputs for one vector (`evalGraphArr`, which is `evalGraph`: `evalGraphArr_eq`). -/
def arrayModel (g : ArrayGraph) (vals : List (List Int)) : List Vec :=
  let env := mkEnv g.lengths g.inputs (vals.map toVec)
  evalGraphArr g ((List.range g.lengths.length).map fun w => (env w).toArray).toArray

/-! ## The square -/

/-- A graph the square runs through both devices: its RTL module, the name of the Lean value the module
is (for the SystemVerilog header) and what the graph is there to exercise. -/
structure SquareGraph where
  name    : String
  typed   : Obend.Hardware.ArrayTyping.TypedGraph
  kind    : Kind
  rtl     : RtlModule
  lean    : String
  purpose : String

def SquareGraph.graph (sq : SquareGraph) : ArrayGraph := sq.typed.graph

/-- The SystemVerilog module name of a graph. -/
def svName (n : String) : String := "sq_" ++ String.map (fun c => if c == '-' then '_' else c) n

/-- The graphs the square runs and what each is for; each exercises something no other one does. -/
def squarePlan : List (String × String) :=
  [ ("allops", "every scalar operation: const (negative), add, sub, mul, scale (by -2^40), mac, mux, with wrap-around")
  , ("muxchain", "a multiply that reaches an output only through a mux's test against zero; its operator swap is seen only by a vector with a zero operand")
  , ("adjoint-square-bilinear", "a compileGraphAdjoint graph, whose wires are numbered out of definition order: the single-assignment lowering's reason")
  , ("tree512", "size: 511 chained adders, where the LEC's time goes")
  , ("glmul-4", "the bit operations of the Goldilocks multiply (ult, and, or, both shifts) as elementwise maps over arrays")
  , ("ntt-16", "gathers, concatenation and constant arrays: the Stockham NTT")
  , ("soac-boundaries", "segmented reductions/scans, empty segments, modular monoids, producer/consumer composition") ]

/-- Select and check the same source/typing receipt used by GPU emission before
lowering to RTL. Listing names never builds the circuits or the large NTT. -/
def squareGraph (name : String) : Except String SquareGraph := do
  let some (_, purpose) := squarePlan.find? (·.1 == name)
    | throw s!"unknown square graph {name}"
  let some c := graphs.find? (·.name == name)
    | throw s!"square graph {name} missing from shared registry"
  let typed ← c.build ()
  match scalarGraphs.find? (·.1 == name) with
  | some (_, ln, g) =>
    return { name := name, typed := typed, kind := c.kind, purpose := purpose
           , rtl := compileHypergraphToRtl (svName name) g
           , lean := s!"Obend.Hardware.Square.compileHypergraphToRtl \"{svName name}\" ({ln})" }
  | none =>
    return { name := name, typed := typed, kind := c.kind, purpose := purpose
           , rtl := compileArrayGraphToRtl (svName name) typed.graph
           , lean := s!"Obend.Hardware.Square.compileArrayGraphToRtl \"{svName name}\" ({c.definition})" }

/-- The flat output ports of the RTL module, regrouped by the output wires' lengths. -/
def regroup : List Nat → List Word → List Vec
  | [], _ => []
  | n :: rest, xs => xs.take n :: regroup rest (xs.drop n)

/-- The input ports for one vector: the input wires' elements in order (`boundaryElems`), as
`inputEnvOf` reads them. -/
def squareInputs (vals : List (List Int)) : Nat → Word :=
  let flat := (vals.map toVec).flatten
  fun p => flat.getD p 0#64

/-- The HDL model's outputs for one vector: `evalModuleOutputs` of the module, regrouped by output wire. -/
def squareModel (sq : SquareGraph) (vals : List (List Int)) : List Vec :=
  regroup (sq.graph.outputs.map (sq.graph.lengths.getD · 0))
    ((evalModuleOutputs sq.rtl (squareInputs vals) (fun _ => 0#64)).map Prod.snd)

/-- `expected.tsv` from the HDL model; the gate compares it byte for byte with the array model's. -/
def squareExpectedTsv (sq : SquareGraph) : String :=
  expectedTsv sq.graph sq.kind (squareModel sq) sq.name

end Obend.Hardware.SquareGraphs
