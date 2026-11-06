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

The shared source registry and vectors are `Obend.Hardware.SquareGraphs`, consumed by both
GPU and RTL emitters. Expected values are `evalGraphArr`'s, which is `evalGraph` with the wires stored (`evalGraphArr_eq`).
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
import Obend.Hardware.SquareGraphs
import Obend.Hardware.Gpu.BookImport
import Obend.Hardware.Gpu.CatgradImport

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.SquareGraphs

/-! ## Expected values and external reference checks -/

def writeGraph (name : String) (typed : Obend.Hardware.ArrayTyping.TypedGraph) (kind : Kind) (dir : System.FilePath) (plant : Plant) : IO Unit := do
  let g := typed.graph
  let p := typed.lower
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (emitPlanJson name p)
  for (s, k) in p.stages.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (emitStageWgsl plant name k p.stages.length s)
  let vectors := graphVectors g kind name
  let mut outputs : Array (List Vec) := #[]
  for (vals, v) in vectors.zipIdx do
    let model := arrayModel g vals
    unless Obend.Hardware.Gpu.SourcePrograms.checkSourceExpected name (vals.map toVec) model do
      throw <| IO.userError s!"{name} vector {v}: graph disagrees with the independent source reference"
    unless Obend.Hardware.Gpu.SoacPrograms.checkSoacExpected name (vals.map toVec) model do
      throw <| IO.userError s!"{name} vector {v}: graph disagrees with the independent SOAC reference"
    if name.startsWith "glmul-" then
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
    outputs := outputs.push model
  IO.FS.writeFile (dir / "expected.tsv") (expectedTsvValues vectors outputs.toList)
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
