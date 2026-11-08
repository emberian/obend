module
/-
# Obend.Hardware.SquareGraphs — the graphs both gates run

One list of graphs with their test vectors, shared by `obend-emit-gpu` (`lean/tools/emitgpu`: the
shaders, plan and `expected.tsv` of `hardware/gpu/graphs/<graph>/`) and `obend-emit-sv`'s `square-<graph>`
targets (`lean/tools/emitsv`: the SystemVerilog, the LEC half, the Verilator harness and the HDL model's
expected values of `hardware/gpu/square/`). `squarePlan` names the ones the square runs through both
devices and what each is for; `squareGraphs` pairs each with its `RtlModule`.

The scalar fixtures (`treeGraph`, `muxChainGraph`, `allOpsGraph`), the Goldilocks field network
(`glMul`, the limb network of `Obend.Apps.ZkNtt.glMul`, elementwise), the array-routing fixture and the
vectors (`vectorFor`) are here; `expectedTsv` prints `expected.tsv` from any model of the outputs, so the
array model's file and the HDL model's can be compared byte for byte.
-/
public import Obend.Hardware.Square
public import Obend.Hardware.Gpu.GoldilocksSource
@[expose] public section

namespace Obend.Hardware.SquareGraphs
open Obend.Hardware.HDL
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.Square

open Obend.Hardware.ArrayBuild Obend.Hardware.Gpu.GoldilocksSource

/-! ## Shared array graphs -/

/-- Array routing shared by the RTL and GPU gates: constants, elementwise arithmetic,
reverse gather and concatenation. Workgroup NTTs have a different source language. -/
def arrayRouteGraph : ArrayGraph :=
  runBuild (fun ins => do
    let x := ins.getD 0 0
    let c ← constWire [11#64, BitVec.ofInt 64 (-3), 4294967297#64, 7#64]
    let sum ← map2 4 (.scalar .add) x c
    let rev ← node 4 (.gather ⟨4, 4, [3, 2, 1, 0]⟩) [sum]
    let out ← node 8 .concat [rev, sum]
    pure [out]) [4]

/-! ## Array graphs besides the NTT -/

/-- Elementwise `a * b + c` over length-`n` wires, then a gather that reverses it: the lowering's map,
constant and gather kernels on one wire of several workgroups. -/
def macReverseGraph (n : Nat) : ArrayGraph :=
  runBuild (fun ins => do
    let a := ins.getD 0 0
    let b := ins.getD 1 0
    let c ← broadcast n 7#64
    let m ← map3 n (.scalar .mac) a b c
    let r ← node n (.gather { source := n, target := n, table := (List.range n).reverse }) [m]
    pure [m, r]) [n, n]

/-- A field multiply alone, elementwise, for the arithmetic tooth on big words. -/
def glMulGraph (n : Nat) : ArrayGraph :=
  runBuild (fun ins => do
    let k ← glConsts n
    let y ← glMul n k (ins.getD 0 0) (ins.getD 1 0)
    pure [y]) [n, n]

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

/-- The array graphs: name, the Lean definition's name, the graph, how its vectors are drawn. -/
def arrayGraphs : List (String × String × ArrayGraph × Kind) :=
  [ ("mac-reverse-1000", "Obend.Hardware.SquareGraphs.macReverseGraph 1000", macReverseGraph 1000, .plain)
  , ("glmul-4",          "Obend.Hardware.SquareGraphs.glMulGraph 4", glMulGraph 4, .ntt)
  , ("glmul-256",        "Obend.Hardware.SquareGraphs.glMulGraph 256", glMulGraph 256, .ntt)
  , ("array-route", "Obend.Hardware.SquareGraphs.arrayRouteGraph", arrayRouteGraph, .plain) ]

/-- Ordinary array graphs shared by both emitters. Workgroup NTT programs are in `Gpu.Ntt`. -/
def graphs : List (String × ArrayGraph × Kind) :=
  scalarGraphs.map (fun (n, _, g) => (n, ofScalar g, .plain)) ++
  arrayGraphs.map (fun (n, _, g, k) => (n, g, k))

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
def graphVectors (name : String) (g : ArrayGraph) (kind : Kind) : List (List (List Int)) :=
  let inLens := g.inputs.map (g.lengths.getD · 0)
  (List.range (vectorCount g)).map fun v =>
    if name == "glmul-256" && v == 0 then
      let corners : List Nat := [0, 1, 4294967295, 4294967296, goldilocksP-1, goldilocksP,
        goldilocksP+1, 18446744073709551615]
      inLens.zipIdx.map fun (n, w) => (List.range n).map fun i =>
        (corners.getD ((i / (if w == 0 then 1 else corners.length)) % corners.length) 0 : Int)
    else vectorFor kind inLens v

/-- `expected.tsv`: one line per vector, index, the input wires, and the output wires `model` gives
(wires separated by `;`, elements by `,`, signed 64-bit). -/
def expectedTsv (name : String) (g : ArrayGraph) (kind : Kind) (model : List (List Int) → List Vec) : String :=
  let signed64 (ws : List Int) : List Int := ws.map fun x => (BitVec.ofInt 64 x).toInt
  let lines := (graphVectors name g kind).zipIdx.map fun (vals, v) =>
    s!"{v}\t{wiresText (vals.map signed64)}\t{wiresText ((model vals).map fun ws => ws.map (·.toInt))}"
  String.intercalate "\n" lines ++ "\n"

/-- The array model's outputs for one vector (`evalGraphArr`, which is `evalGraph`: `evalGraphArr_eq`). -/
def arrayModel (g : ArrayGraph) (vals : List (List Int)) : List Vec :=
  let env := mkEnv g.lengths g.inputs (vals.map toVec)
  evalGraphArr g ((List.range g.lengths.length).map fun w => (env w).toArray).toArray

/-! ## The square -/

/-- A graph the square runs through both devices: its RTL module, the name of the Lean value the module
is (for the SystemVerilog header) and what the graph is there to exercise. -/
structure SquareGraph where
  name    : String
  graph   : ArrayGraph
  kind    : Kind
  rtl     : RtlModule
  lean    : String
  purpose : String

/-- The SystemVerilog module name of a graph. -/
def svName (n : String) : String := "sq_" ++ String.map (fun c => if c == '-' then '_' else c) n

/-- The graphs the square runs and what each is for; each exercises something no other one does. -/
def squarePlan : List (String × String) :=
  [ ("allops", "every scalar operation: const (negative), add, sub, mul, scale (by -2^40), mac, mux, with wrap-around")
  , ("muxchain", "a multiply that reaches an output only through a mux's test against zero; its operator swap is seen only by a vector with a zero operand")
  , ("adjoint-square-bilinear", "a compileGraphAdjoint graph, whose wires are numbered out of definition order: the single-assignment lowering's reason")
  , ("tree512", "size: 511 chained adders, where the LEC's time goes")
  , ("glmul-4", "the bit operations of the Goldilocks multiply (ult, and, or, both shifts) as elementwise maps over arrays")
  , ("array-route", "gathers, concatenation and constant arrays with a shared producer") ]

/-- The graphs of `squarePlan`, a scalar one as its one-element instance through `compileHypergraphToRtl`
(`rtl_eq_gpu`), an array one through `compileArrayGraphToRtl` (`rtl_eq_gpu_array`). -/
def squareGraphs : List SquareGraph :=
  squarePlan.filterMap fun (n, purpose) =>
    match scalarGraphs.find? (·.1 == n), arrayGraphs.find? (·.1 == n) with
    | some (_, ln, g), _ =>
      some { name := n, graph := ofScalar g, kind := .plain, purpose := purpose
           , rtl := compileHypergraphToRtl (svName n) g
           , lean := s!"Obend.Hardware.Square.compileHypergraphToRtl \"{svName n}\" ({ln})" }
    | none, some (_, ln, g, k) =>
      some { name := n, graph := g, kind := k, purpose := purpose
           , rtl := compileArrayGraphToRtl (svName n) g
           , lean := s!"Obend.Hardware.Square.compileArrayGraphToRtl \"{svName n}\" ({ln})" }
    | none, none => none

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
  expectedTsv sq.name sq.graph sq.kind (squareModel sq)

end Obend.Hardware.SquareGraphs
