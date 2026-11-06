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

The graphs, their vectors and the `expected.tsv` printer are `Obend.Hardware.SquareGraphs`, shared with
`obend-emit-sv`'s `square-<graph>` targets (the same graphs through the RTL lowering). Expected values
are `evalGraphArr`'s, which is `evalGraph` with the wires stored (`evalGraphArr_eq`). Before writing, the
emitter refuses a graph that fails `ArrayGraph.wf` (which is the hypothesis of `lowerArrayToGpu_sound`,
so the expected values are `evalGraph`'s and the device must show them) and an NTT graph whose
evaluation disagrees with the naive DFT over the Goldilocks field (`nttReference`). These are tests of
the fixtures, run on every emission.
-/
import Obend.Hardware.SquareGraphs

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.SquareGraphs

/-! ## Expected values and the checks -/

def writeGraph (name : String) (g : ArrayGraph) (kind : Kind) (dir : System.FilePath) (plant : Plant) : IO Unit := do
  unless g.wf do
    throw <| IO.userError s!"{name}: the graph is not well-formed (ArrayGraph.wf)"
  let p := lowerArrayToGpu g
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (emitPlanJson name p)
  for (s, k) in p.stages.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (emitStageWgsl plant name k p.stages.length s)
  if kind == .ntt && name.startsWith "ntt" then
    for (vals, v) in (graphVectors g kind).zipIdx do
      let ref := nttReference ((vals.getD 0 []).map Int.toNat)
      unless ((arrayModel g vals).getD 0 []).map (·.toNat) == ref do
        throw <| IO.userError s!"{name} vector {v}: the NTT graph disagrees with the naive DFT"
  IO.FS.writeFile (dir / "expected.tsv") (expectedTsv g kind (arrayModel g))
  IO.println s!"  {name}: {g.lengths.length} wires ({p.words} words), {p.consts.length} constants, \
    {p.tables.length} indices, {p.stages.length} stages \
    ({String.intercalate "," (p.stages.map fun s => toString s.threads)} threads), \
    {vectorCount g} vectors -> {dir}"

/-! ## Main -/

def usage : String :=
  "usage: obend-emit-gpu list | <graph> --out DIR [--plant addAsSub|swapMux] | all --out DIR [--plant P]"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for (n, _, _) in graphs do IO.println n
    return 0
  | name :: rest =>
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
    if name == "all" then
      for (n, g, kind) in graphs do writeGraph n g kind (dir / n) plant
      return 0
    match graphs.find? (·.1 == name) with
    | some (_, g, kind) => writeGraph name g kind dir plant; return 0
    | none => IO.eprintln s!"unknown graph {name}; `obend-emit-gpu list`"; return 2
  | [] => IO.eprintln usage; return 2
