module
/-
# Obend.Hardware.SquareGraphs — the graphs both gates run

One list of graphs with their test vectors, shared by `obend-emit-gpu` (`lean/tools/emitgpu`: the
shaders, plan and `expected.tsv` of `hardware/gpu/graphs/<graph>/`) and `obend-emit-sv`'s `square-<graph>`
targets (`lean/tools/emitsv`: the SystemVerilog, the LEC half, the Verilator harness and the HDL model's
expected values of `hardware/gpu/square/`). `squareGraphs` names the ones the square runs through both
devices with the `RtlModule` of each: a scalar graph through `compileHypergraphToRtl`
(`rtl_eq_gpu`), an array graph through `compileArrayGraphToRtl` (`rtl_eq_gpu_array`).

The scalar fixtures (`treeGraph`, `muxChainGraph`, `allOpsGraph`), the Goldilocks field network
(`glMul`, the limb network of `Obend.Apps.ZkNtt.glMul`, elementwise), the radix-2 NTT (`nttGraph`) and the
vectors (`vectorFor`) are here; `expectedTsv` prints `expected.tsv` from any model of the outputs, so the
array model's file and the HDL model's can be compared byte for byte.
-/
public import Obend.Hardware.Square
@[expose] public section

namespace Obend.Hardware.SquareGraphs
open Obend.Hardware.HDL
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.Square

/-! ## A builder for array graphs -/

structure Build where
  lengths : Array Nat := #[]
  edges   : Array ArrayEdge := #[]

abbrev BuildM := StateM Build

def newWire (n : Nat) : BuildM Nat := do
  let st ← get
  set { st with lengths := st.lengths.push n }
  pure st.lengths.size

def emit (op : ArrayOp) (srcs : List Nat) (dst : Nat) : BuildM Unit :=
  modify fun st => { st with edges := st.edges.push { opIdx := st.edges.size, op := op, srcWires := srcs, dstWire := dst } }

/-- A fresh wire of length `n` written by `op`. -/
def node (n : Nat) (op : ArrayOp) (srcs : List Nat) : BuildM Nat := do
  let w ← newWire n
  emit op srcs w
  pure w

def constWire (vals : List Word) : BuildM Nat := node vals.length (.const vals) []

/-- `n` copies of one word. -/
def broadcast (n : Nat) (v : Word) : BuildM Nat := constWire (List.replicate n v)

def map2 (n : Nat) (op : ElemOp) (a b : Nat) : BuildM Nat := node n (.map n op) [a, b]
def map3 (n : Nat) (op : ElemOp) (a b c : Nat) : BuildM Nat := node n (.map n op) [a, b, c]

def runBuild (inputs : List Nat → BuildM (List Nat)) (inputLens : List Nat) : ArrayGraph :=
  let ((ins, outs), st) := (do
    let ins ← inputLens.mapM newWire
    let outs ← inputs ins
    pure (ins, outs)).run {}
  { lengths := st.lengths.toList, inputs := ins, outputs := outs, edges := st.edges.toList }

/-! ## The Goldilocks field, elementwise (the network of `Obend.Apps.ZkNtt.glMul`) -/

def goldilocksP : Nat := 18446744069414584321

/-- The field constants a vector of length `n` needs: `p`, the low mask and the shift. -/
structure GlConsts where
  p    : Nat
  mask : Nat
  s32  : Nat

def glConsts (n : Nat) : BuildM GlConsts := do
  let p ← broadcast n (BitVec.ofNat 64 goldilocksP)
  let mask ← broadcast n 0xFFFFFFFF#64
  let s32 ← broadcast n 32#64
  pure ⟨p, mask, s32⟩

/-- `x < p ? x : x - p`. -/
def glCanon (n : Nat) (k : GlConsts) (x : Nat) : BuildM Nat := do
  let lt ← map2 n .ult x k.p
  let sub ← map2 n (.scalar .sub) x k.p
  map3 n (.scalar .mux) lt x sub

/-- `(a + b) mod p` for canonical `a b`, without a 65th bit. -/
def glAdd (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let remP ← map2 n (.scalar .sub) k.p b
  let lt ← map2 n .ult a remP
  let sum ← map2 n (.scalar .add) a b
  let wrap ← map2 n (.scalar .sub) a remP
  map3 n (.scalar .mux) lt sum wrap

/-- `(a - b) mod p` for canonical `a b`. -/
def glSub (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let lt ← map2 n .ult a b
  let pb ← map2 n (.scalar .sub) k.p b
  let wrap ← map2 n (.scalar .add) pb a
  let diff ← map2 n (.scalar .sub) a b
  map3 n (.scalar .mux) lt wrap diff

/-- `(a * b) mod p` for any 64-bit `a b`: four 32×32 limb products, the 128-bit product `(lo, hi)`, then
the shift/mask reduction (`goldilocksReduce128Spec`). -/
def glMul (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let aLo ← map2 n .band a k.mask
  let aHi ← map2 n .shr a k.s32
  let bLo ← map2 n .band b k.mask
  let bHi ← map2 n .shr b k.s32
  let p00 ← map2 n (.scalar .mul) aLo bLo
  let p01 ← map2 n (.scalar .mul) aLo bHi
  let p10 ← map2 n (.scalar .mul) aHi bLo
  let p11 ← map2 n (.scalar .mul) aHi bHi
  let p00Hi ← map2 n .shr p00 k.s32
  let p01Lo ← map2 n .band p01 k.mask
  let p10Lo ← map2 n .band p10 k.mask
  let mid32a ← map2 n (.scalar .add) p00Hi p01Lo
  let mid32 ← map2 n (.scalar .add) mid32a p10Lo
  let p00Lo ← map2 n .band p00 k.mask
  let mid32Lo ← map2 n .band mid32 k.mask
  let mid32LoSh ← map2 n .shl mid32Lo k.s32
  let lo ← map2 n .bor p00Lo mid32LoSh
  let p01Hi ← map2 n .shr p01 k.s32
  let p10Hi ← map2 n .shr p10 k.s32
  let mid32Hi ← map2 n .shr mid32 k.s32
  let hi1 ← map2 n (.scalar .add) p11 p01Hi
  let hi2 ← map2 n (.scalar .add) hi1 p10Hi
  let hi ← map2 n (.scalar .add) hi2 mid32Hi
  let hiLo ← map2 n .band hi k.mask
  let hiHi ← map2 n .shr hi k.s32
  let hiLoSh ← map2 n .shl hiLo k.s32
  let mid ← map2 n (.scalar .sub) hiLoSh hiLo
  let loC ← glCanon n k lo
  let t1 ← glAdd n k loC mid
  glSub n k t1 hiHi

/-! ## The NTT -/

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1
  let mut bb := b % m
  let mut ee := e
  while ee > 0 do
    if ee % 2 == 1 then r := r * bb % m
    bb := bb * bb % m
    ee := ee / 2
  return r

/-- A primitive `2^32`-th root of unity in the Goldilocks field (`7^((p-1)/2^32)`). -/
def rootOfUnity2to32 : Nat := powMod 7 ((goldilocksP - 1) / 2 ^ 32) goldilocksP

/-- A primitive `n`-th root, `n` a power of two dividing `2^32`. -/
def rootOfUnity (n : Nat) : Nat := powMod rootOfUnity2to32 (2 ^ 32 / n) goldilocksP

/-- The even and odd positions of a length-`n` wire, as gather tables. -/
def evens (n : Nat) : FiniteFunction := { source := n / 2, target := n, table := (List.range (n / 2)).map (2 * ·) }
def odds (n : Nat) : FiniteFunction := { source := n / 2, target := n, table := (List.range (n / 2)).map (2 * · + 1) }

/-- Radix-2 Cooley–Tukey over a wire of length `n = 2^levels`: `y_k = E_k + ω^k O_k`,
`y_{k + n/2} = E_k - ω^k O_k`, the halves concatenated. Inputs are assumed canonical (`< p`). -/
partial def nttOf (x : Nat) (n : Nat) : BuildM Nat := do
  if n ≤ 1 then pure x
  else
    let half := n / 2
    let ev ← node half (.gather (evens n)) [x]
    let od ← node half (.gather (odds n)) [x]
    let e ← nttOf ev half
    let o ← nttOf od half
    let ω := rootOfUnity n
    let twiddles ← constWire ((List.range half).map fun k => BitVec.ofNat 64 (powMod ω k goldilocksP))
    let k ← glConsts half
    let t ← glMul half k o twiddles
    let lo ← glAdd half k e t
    let hi ← glSub half k e t
    node n .concat [lo, hi]

def nttGraph (n : Nat) : ArrayGraph :=
  runBuild (fun ins => do
    let y ← nttOf (ins.getD 0 0) n
    pure [y]) [n]

/-- The naive DFT, the reference the emitter checks the graph against. -/
def nttReference (xs : List Nat) : List Nat :=
  let n := xs.length
  let ω := rootOfUnity n
  (List.range n).map fun k =>
    (xs.zipIdx.foldl (fun acc (xj, j) => (acc + xj * powMod ω (j * k) goldilocksP) % goldilocksP) 0)

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
  , ("ntt-4",            "Obend.Hardware.SquareGraphs.nttGraph 4", nttGraph 4, .ntt)
  , ("ntt-16",           "Obend.Hardware.SquareGraphs.nttGraph 16", nttGraph 16, .ntt)
  , ("ntt-64",           "Obend.Hardware.SquareGraphs.nttGraph 64", nttGraph 64, .ntt) ]

/-- Every graph the GPU gate runs: the scalar ones as their one-element instance, then the array ones. -/
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
  if sumNatList (g.inputs.map (g.lengths.getD · 0)) ≥ 64 then 6 else 12

/-! ## Expected values and the checks -/

def wireText (xs : List Int) : String :=
  if xs.isEmpty then "-" else String.intercalate "," (xs.map toString)

def wiresText (ws : List (List Int)) : String := String.intercalate ";" (ws.map wireText)

def toVec (xs : List Int) : Vec := xs.map (BitVec.ofInt 64)

/-- The vectors of a graph, as drawn: per vector, per input wire, the elements as integers. -/
def graphVectors (g : ArrayGraph) (kind : Kind) : List (List (List Int)) :=
  let inLens := g.inputs.map (g.lengths.getD · 0)
  (List.range (vectorCount g)).map (vectorFor kind inLens)

/-- `expected.tsv`: one line per vector, index, the input wires, and the output wires `model` gives
(wires separated by `;`, elements by `,`, signed 64-bit). -/
def expectedTsv (g : ArrayGraph) (kind : Kind) (model : List (List Int) → List Vec) : String :=
  let signed64 (ws : List Int) : List Int := ws.map fun x => (BitVec.ofInt 64 x).toInt
  let lines := (graphVectors g kind).zipIdx.map fun (vals, v) =>
    s!"{v}\t{wiresText (vals.map signed64)}\t{wiresText ((model vals).map fun ws => ws.map (·.toInt))}"
  String.intercalate "\n" lines ++ "\n"

/-- The array model's outputs for one vector (`evalGraphArr`, which is `evalGraph`: `evalGraphArr_eq`). -/
def arrayModel (g : ArrayGraph) (vals : List (List Int)) : List Vec :=
  let env := mkEnv g.lengths g.inputs (vals.map toVec)
  evalGraphArr g ((List.range g.lengths.length).map env).toArray

/-! ## The square -/

/-- A graph the square runs through both devices, with its RTL module and the name of the Lean value
the module is, for the SystemVerilog header. -/
structure SquareGraph where
  name  : String
  graph : ArrayGraph
  kind  : Kind
  rtl   : RtlModule
  lean  : String
  /-- The square theorem's hypothesis beyond `ArrayGraph.wf`, decided: `(wireDefs g).Nodup` for a
  scalar graph (`rtl_eq_gpu`), `edgesAcyclic g` for an array graph (`rtl_eq_gpu_array`). -/
  hyp   : Bool

/-- The SystemVerilog module name of a graph. -/
def svName (n : String) : String := "sq_" ++ String.map (fun c => if c == '-' then '_' else c) n

/-- The scalar graphs through `compileHypergraphToRtl`, and the array graphs small enough for Verilator
and the LEC through `compileArrayGraphToRtl`. -/
def squareGraphs : List SquareGraph :=
  scalarGraphs.map (fun (n, ln, g) =>
    { name := n, graph := ofScalar g, kind := .plain
    , rtl := compileHypergraphToRtl (svName n) g
    , lean := s!"Obend.Hardware.OpenHypergraph.compileHypergraphToRtl \"{svName n}\" ({ln})"
    , hyp := decide (wireDefs g).Nodup }) ++
  (arrayGraphs.filter (fun (n, _, _, _) => n == "glmul-4" || n == "ntt-16")).map (fun (n, ln, g, k) =>
    { name := n, graph := g, kind := k
    , rtl := compileArrayGraphToRtl (svName n) g
    , lean := s!"Obend.Hardware.Square.compileArrayGraphToRtl \"{svName n}\" ({ln})"
    , hyp := edgesAcyclic g })

/-- The flat output ports of the RTL module, regrouped by the output wires' lengths. -/
def regroup : List Nat → List Word → List Vec
  | [], _ => []
  | n :: rest, xs => xs.take n :: regroup rest (xs.drop n)

/-- The input ports for one vector: the input wires' elements in order (`boundaryElems`; a scalar graph's
wires are singletons, so the same flattening serves `compileHypergraphToRtl`'s ports). -/
def squareInputs (vals : List (List Int)) : Nat → Word :=
  let flat := (vals.map toVec).flatten
  fun p => flat.getD p 0#64

/-- The HDL model's outputs for one vector: `evalModuleOutputs` of the module, regrouped by output wire. -/
def squareModel (sq : SquareGraph) (vals : List (List Int)) : List Vec :=
  regroup (sq.graph.outputs.map (sq.graph.lengths.getD · 0))
    ((evalModuleOutputs sq.rtl (squareInputs vals) (fun _ => 0#64)).map Prod.snd)

/-- `expected.tsv` from the HDL model; the gate compares it byte for byte with the array model's. -/
def squareExpectedTsv (sq : SquareGraph) : String :=
  expectedTsv sq.graph sq.kind (squareModel sq)

end Obend.Hardware.SquareGraphs
