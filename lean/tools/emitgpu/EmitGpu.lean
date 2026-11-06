/-
# `obend-emit-gpu` — array hypergraphs lowered to compute shaders (`Obend.Hardware.Gpu`)

    obend-emit-gpu list
    obend-emit-gpu <graph> --out DIR [--plant P]
        DIR/plan.json (the flat wire buffer's size, every wire's base and length, the constant and index
        buffers, the boundary wires, one shader per wavefront stage), DIR/stage_<k>.wgsl, and
        DIR/expected.tsv, one line per vector: index, the input wires, and the output wires
        `Obend.Hardware.Gpu.runProgram` shows (wires separated by `;`, elements by `,`, signed 64-bit)
    obend-emit-gpu all --out DIR [--plant P]
        every graph, each under DIR/<graph>/

`--plant addAsSub` emits every `+` as `-`; `--plant swapMux` exchanges the arms of every `select`:
rules planted in the shader text only, for `hardware/gpu/verify_gpu.sh`'s tooth. The expected values
are always the unplanted model's.

Expected values are `evalGraphArr`'s, which is `evalGraph` with the wires stored (`evalGraphArr_eq`).
Before writing, the emitter requires a checked typed graph and retains its derivation through
lowering. Array workloads are selected Core4 members compiled through `ArrayMember.checkMember`.
It also refuses an
NTT graph whose evaluation disagrees with a recursive radix-2 NTT over the Goldilocks field in `Nat`
arithmetic (`nttFast`), which for the smaller sizes is itself checked against the naive DFT
(`nttReference`). These are tests of the fixtures, run on every emission.

The NTT graphs are Stockham radix-2 (Govindaraju et al. 2008; ec-gpu's `radix_fft` kernel with
`deg = 1`, whose output index is `((j - k) << 1) + k`): every stage reads the two halves of the
previous stage's output, multiplies the upper half by `ω_{2Ns}^{j mod Ns}`, and writes the sum and
difference expanded by the sub-transform size, so an NTT of `n` points is `log₂ n` stages of a few
dozen edges over whole wires, and no bit reversal. The field operations are the limb network of
`Obend.Apps.ZkNtt.glMul`; after fusion each stage's sum and difference are one kernel each.
-/
import Obend.Hardware.Gpu
import Obend.Hardware.ArrayTyping
import Obend.Hardware.Gpu.ArrayPrograms
import Obend.Hardware.Gpu.SourcePrograms
import Obend.Hardware.Gpu.SoacPrograms
import Obend.Hardware.Gpu.BookImport
import Obend.Hardware.Gpu.CatgradImport

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.Gpu.ArrayPrograms

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

/-- Compilation is delayed until selection, so listing a workload or importing a
book never constructs every NTT's Core4 syntax. The typed receipt is retained. -/
structure GraphCase where
  name : String
  build : Unit → Except String Obend.Hardware.ArrayTyping.TypedGraph
  kind : Kind

def scalarCase (name : String) (graph : StrictOpenHypergraph) : GraphCase :=
  ⟨name, fun _ => Obend.Hardware.ArrayTyping.checkTypedGraph
    (Obend.Hardware.ArrayTyping.wordTypes (ofScalar graph)) (ofScalar graph), .plain⟩

def sourceCase (name : String) (lengths : List Nat) (source : Unit → ArraySource.Program)
    (kind : Kind := .plain) : GraphCase :=
  ⟨name, fun _ => (compileSource name lengths (source ())).map (·.typed), kind⟩

def graphs : List GraphCase :=
  [ scalarCase "diamond" goldenDiamondHypergraph
  , scalarCase "optic-mul" (compileOpticToHypergraph .mul)
  , scalarCase "optic-linearmac" (compileOpticToHypergraph (.linearMac 7))
  , scalarCase "optic-bilinear" (compileOpticToHypergraph (.bilinear (-3)))
  , scalarCase "adjoint-mul-add" (compileGraphAdjoint (compileOpticChain2FwdHypergraph .mul .add))
  , scalarCase "adjoint-square-bilinear"
      (compileGraphAdjoint (compileOpticChain2FwdHypergraph .square (.bilinear 5)))
  , scalarCase "allops" allOpsGraph
  , scalarCase "muxchain" muxChainGraph
  , scalarCase "tree512" (treeGraph 512)
  , sourceCase "mac-reverse-1000" [1000, 1000] (fun _ => macReverseSource 1000)
  , sourceCase "glmul-256" [256, 256] (fun _ => glMulSource 256) .ntt ] ++
    [4, 16, 64, 1024, 65536].map (fun n =>
      sourceCase s!"ntt-{n}" [n] (fun _ => nttSource n) .ntt) ++
    Obend.Hardware.Gpu.SoacPrograms.cases.map (fun (name, ns) =>
      sourceCase name [ns.sum] (fun _ => Obend.Hardware.Gpu.SoacPrograms.source ns))

def pool : List Int :=
  [0, 1, -1, 2, 3, -3, 10, 255, -256, 65535, 2 ^ 31, -(2 ^ 31), 2 ^ 32 + 1, 2 ^ 62, -(2 ^ 62),
   2 ^ 63 - 1, -(2 ^ 63), 123456789, -987654321]

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A deterministic pseudo-random 64-bit word for element `i` of input `w` of vector `v`. -/
def draw (v w i : Nat) : Nat :=
  (List.range (i % 7 + 1)).foldl (fun acc _ => lcg acc) (lcg (v * 7919 + w * 104729 + i * 31 + 17))

def signed (s : Nat) : Int := (s : Int) - (if s ≥ 2 ^ 63 then 2 ^ 64 else 0)

/-- Vector `v` for a graph: field elements (`< p`) for the field graphs; otherwise the first vectors walk
the pool and later ones are pseudo-random words. -/
def vectorFor (kind : Kind) (lens : List Nat) (v : Nat) : List (List Int) :=
  lens.zipIdx.map fun (n, w) =>
    (List.range n).map fun i =>
      match kind with
      | .ntt => (draw v w i % goldilocksP : Int)
      | .plain =>
        if v < 6 then pool.getD ((i + w + 3 * v) % pool.length) 0
        else signed (draw v w i)

def vectorCount (g : ArrayGraph) : Nat :=
  let total := sumNatList (g.inputs.map (g.lengths.getD · 0))
  if total ≥ 2 ^ 14 then 2 else if total ≥ 64 then 6 else 12

/-! ## Expected values and the checks -/

def wireText (xs : List Int) : String :=
  if xs.isEmpty then "-" else String.intercalate "," (xs.map toString)

def wiresText (ws : List (List Int)) : String := String.intercalate ";" (ws.map wireText)

def toVec (xs : List Int) : Vec := xs.map (BitVec.ofInt 64)

def graphTypes (name : String) (g : ArrayGraph) : List Obend.Hardware.ArrayTyping.TensorType :=
  if name == "source-leaf-fixed-square" then
    g.lengths.zipIdx.map fun (n, w) => ⟨[n], .fixed (if w == 0 then 8 else 16)⟩
  else Obend.Hardware.ArrayTyping.wordTypes g

def writeGraph (name : String) (typed : Obend.Hardware.ArrayTyping.TypedGraph) (kind : Kind) (dir : System.FilePath) (plant : Plant) : IO Unit := do
  let g := typed.graph
  let p := typed.lower
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (emitPlanJson name p)
  for (s, k) in p.stages.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (emitStageWgsl plant name k p.stages.length s)
  let inLens := g.inputs.map (g.lengths.getD · 0)
  let mut lines : Array String := #[]
  let vectors : List (List (List Int)) := match Obend.Hardware.Gpu.SourcePrograms.sourceVectors? name with
    | some vs => vs.map fun (inputs : List Vec) => inputs.map fun (xs : Vec) => xs.map (fun (w : Word) => w.toInt)
    | none => (List.range (vectorCount g)).map (vectorFor kind inLens)
  for (vals, v) in vectors.zipIdx do
    let env := mkEnv g.lengths g.inputs (vals.map toVec)
    let model := evalGraphArr g ((List.range g.lengths.length).map fun w => (env w).toArray).toArray
    unless Obend.Hardware.Gpu.SourcePrograms.checkSourceExpected name (vals.map toVec) model do
      throw <| IO.userError s!"{name} vector {v}: graph disagrees with the independent source reference"
    unless Obend.Hardware.Gpu.SoacPrograms.checkSoacExpected name (vals.map toVec) model do
      throw <| IO.userError s!"{name} vector {v}: graph disagrees with the independent SOAC reference"
    if name == "glmul-256" then
      let left := (toVec (vals.getD 0 [])).map (·.toNat)
      let right := (toVec (vals.getD 1 [])).map (·.toNat)
      let fieldReference := List.zipWith (fun a b => a * b % goldilocksP) left right
      unless (model.getD 0 []).map (·.toNat) == fieldReference do
        throw <| IO.userError s!"{name} vector {v}: source field multiply disagrees with exact Nat arithmetic modulo p"
    if kind == .ntt && name.startsWith "ntt" then
      let input := (vals.getD 0 []).map Int.toNat
      let fast := (nttFast input.toArray (rootOfUnity input.length)).toList
      unless (model.getD 0 []).map (·.toNat) == fast do
        throw <| IO.userError s!"{name} vector {v}: the NTT graph disagrees with the recursive NTT"
      if input.length ≤ 4096 then
        unless nttReference input == fast do
          throw <| IO.userError s!"{name} vector {v}: the recursive NTT disagrees with the naive DFT"
    let signed64 (ws : List Int) : List Int := ws.map fun x => (BitVec.ofInt 64 x).toInt
    lines := lines.push s!"{v}\t{wiresText (vals.map signed64)}\t{wiresText (model.map fun ws => ws.map (·.toInt))}"
  IO.FS.writeFile (dir / "expected.tsv") (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"  {name}: {g.lengths.length} wires ({p.words} words), {g.edges.length} edges, \
    {(fuseGraph g).edges.length} after fusion, {p.consts.length} constants, \
    {p.tables.length} indices, {p.stages.length} dispatches \
    ({String.intercalate "," (p.stages.map fun s => toString s.kernels.length)} kernels), \
    {vectors.length} vectors -> {dir}"

/-! ## Main -/

def usage : String :=
  "usage: obend-emit-gpu list | <graph> --out DIR [--plant addAsSub|swapMux] | all --out DIR [--plant P] | catgrad FILE --out DIR [--plant P] | leaf BOOK MEMBER INPUTS --out DIR [--plant P] | leaf-example --out DIR"

def main (args : List String) : IO UInt32 := do
  match Obend.Hardware.Gpu.SourcePrograms.checkRefusals with
  | .error reason => IO.eprintln reason; return 1
  | .ok _ => pure ()
  let graphs := graphs ++ Obend.Hardware.Gpu.SourcePrograms.cases.map (fun c =>
    ⟨c.name, fun _ => do
      let p ← c.compile
      Obend.Hardware.ArrayTyping.checkTypedGraph (graphTypes c.name p.plan.graph) p.plan.graph,
      .plain⟩)
  match args with
  | ["list"] =>
    for item in graphs do IO.println item.name
    return 0
  | name :: rawRest =>
    let payload := if name == "catgrad" then 1 else if name == "leaf" then 3 else 0
    let file := rawRest.head?
    let rest := rawRest.drop payload
    let mut out : Option String := none
    let mut plant : Plant := .none
    let mut r := rest
    while !r.isEmpty do
      match r with
      | "--out" :: d :: r' => out := some d; r := r'
      | "--plant" :: p :: r' =>
        match Plant.ofString? p with
        | some pl => plant := pl; r := r'
        | none => IO.eprintln s!"unknown plant {p}"; return 2
      | other :: _ => IO.eprintln s!"unexpected argument {other}\n{usage}"; return 2
      | [] => pure ()
    let some dir := out | IO.eprintln usage; return 2
    if name == "catgrad" then
      let some path := file | IO.eprintln "catgrad requires an input file"; return 2
      Obend.Hardware.Gpu.CatgradImport.writeFile path dir plant
      return 0
    if name == "leaf-example" then
      Obend.Hardware.Gpu.BookImport.writeExample dir
      return 0
    if name == "leaf" then
      let some path := file | IO.eprintln "leaf requires BOOK MEMBER INPUTS"; return 2
      let some member := rawRest[1]? | IO.eprintln "leaf requires a member name"; return 2
      let some inputs := (rawRest[2]? : Option String) | IO.eprintln "leaf requires an input vector file"; return 2
      Obend.Hardware.Gpu.BookImport.writeFile path member inputs dir plant
      return 0
    if name == "all" then
      for item in graphs do
        let typed ← match item.build () with
          | .ok typed => pure typed
          | .error reason => throw <| IO.userError s!"{item.name}: {reason}"
        writeGraph item.name typed item.kind (dir / item.name) plant
      return 0
    match graphs.find? (·.name == name) with
    | some item =>
      let typed ← match item.build () with
        | .ok typed => pure typed
        | .error reason => throw <| IO.userError s!"{name}: {reason}"
      writeGraph name typed item.kind dir plant
      return 0
    | none => IO.eprintln s!"unknown graph {name}; `obend-emit-gpu list`"; return 2
  | [] => IO.eprintln usage; return 2
