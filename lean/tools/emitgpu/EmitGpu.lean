/-
# `obend-emit-gpu` — checked array sources and block programs to compute shaders

`list` names workloads; `<name> --out DIR` emits a plan, shaders and expected.tsv;
`all --out DIR` emits every registered workload. `leaf`, `leaf-example` and `catgrad`
retain the checked source-import routes. `--plant` changes shader rules only.
`--artifacts-only` skips expected-value evaluation for registered workloads; the
external gate may reuse its unplanted oracle only after checking plan equality.

Ordinary workloads share the typed source registry and vectors in SquareGraphs.
Their checked typing/live-layout receipt reaches the ordinary Plan lowering;
expected outputs use evalGraphArr and independent source/SOAC/field references.

Gpu.Ntt.nttBlockProgram is the sole NTT construction. It uses ArrayKernel.Program
for indexed multi-output maps, register networks and shared-memory phases, derived
from ec-gpu radix_fft and Govindaraju et al. SC2008. Program.check admits bounds,
SSA closure, initialization and ownership; SourceProtocol.checkProgram checks the
physical-lane phase protocol against G4. NttSource.compile admits this program through the block-level Core4 source
fragment. NttSource.source_to_gpu_encoded covers its retained group/lane loops,
lexical register networks and shared phases via the general lowering.
NttCorrect proves the actual source is the DFT for every supported size and input;
NttSource.source_to_gpu_dft_encoded composes that value theorem with Core4 and the
admitted GPU lowering. Executable block outputs retain the independent recursive
NTT regression oracle; the former finite direct-DFT checks have been replaced
by the universal theorem imported below.
-/
import Obend.Hardware.SquareGraphs
import Obend.Hardware.Gpu.BookImport
import Obend.Hardware.Gpu.CollectiveImport
import Obend.Hardware.Gpu.ArrayEmit
import Obend.Hardware.Gpu.CatgradImport
import Obend.Hardware.Gpu.Ntt
import Obend.Hardware.Gpu.NttCorrect
import Obend.Hardware.ArrayKernel
import Obend.Hardware.Gpu.BlockEmit
import Obend.Hardware.Gpu.LayoutChecks
import Obend.Hardware.Gpu.DispatchProtocol

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.SquareGraphs
open Obend.Hardware.Gpu.Ntt
open Obend.Hardware.Gpu.GoldilocksSource

/-! ## Expected values and external reference checks -/

def writeGraph (name : String) (typed : Obend.Hardware.ArrayTyping.TypedGraph) (kind : Kind) (dir : System.FilePath) (plant : Plant) (artifactsOnly : Bool := false) : IO Unit := do
  let g := typed.graph
  let p := typed.lower
  let artifact ← ArrayEmit.write name p dir plant
  if artifactsOnly then return
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
    outputs := outputs.push model
  IO.FS.writeFile (dir / "expected.tsv") (expectedTsvValues vectors outputs.toList)
  IO.println s!"  {name}: {g.lengths.length} wires ({p.words} words), {g.edges.length} edges, \
    {(fuseGraph g).edges.length} after fusion, {p.consts.length} constants, \
    {artifact.tables.length} indices, {artifact.shaders.size} dispatches \
    ({String.intercalate "," (p.stages.map fun s => toString s.kernels.length)} kernels), \
    {vectors.length} vectors -> {dir}"

def writeBlockGraph (name : String) (n : Nat) (dir : System.FilePath) (plant : Plant) (artifactsOnly : Bool := false) : IO Unit := do
  let sourcePlan ← IO.ofExcept (NttSource.compile n)
  let p := sourcePlan.source
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (BlockEmit.emitPlan name p)
  for (d, k) in p.dispatches.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (BlockEmit.emitDispatch plant name p d)
  if artifactsOnly then return
  let mut lines := #[]
  let count := vectorCountFor [n]
  for v in [:count] do
    let vals := vectorFor .field [n] v
    let input := (vals.getD 0 []).map Int.toNat
    let mem := Obend.Hardware.ArrayKernel.initialMemory p (vals.map fun xs => (toVec xs).toArray)
    let result := Obend.Hardware.ArrayKernel.evalProgram p mem
    let model := p.outputs.map fun i => (result.getD i #[]).toList
    let fast := (nttFast input.toArray (rootOfUnity n)).toList
    unless (model.getD 0 []).map (·.toNat) == fast do
      throw <| IO.userError s!"{name} vector {v}: block array source disagrees with recursive NTT"
    lines := lines.push (expectedTsvLine v vals model)
  IO.FS.writeFile (dir / "expected.tsv") (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"  {name}: {BlockEmit.spaceSize p .device} device words, {BlockEmit.spaceSize p .shared} shared words, {p.dispatches.length} dispatches -> {dir}"

/-! ## Main -/

def usage : String :=
  "usage: obend-emit-gpu list | <graph> --out DIR [--plant addAsSub|swapMux|mulHighZero] | all --out DIR [--plant P] | catgrad FILE --out DIR [--plant P] | leaf BOOK MEMBER INPUTS --out DIR [--plant P] | leaf-example --out DIR"

def main (args : List String) : IO UInt32 := do
  match Obend.Hardware.Gpu.SourcePrograms.checkRefusals with
  | .error reason => IO.eprintln reason; return 1
  | .ok _ => pure ()
  match args with
  | ["check-layout"] =>
    for (name, ok) in layoutCheckResults do
      IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
    return if layoutCheckFixtures then 0 else 1
  | ["list"] =>
    for item in graphs do IO.println item.name
    for (name, _) in blockGraphs do IO.println name
    return 0
  | name :: rawRest =>
    let payload := if name == "catgrad" || name == "collective" then 1 else if name == "leaf" then 3 else 0
    let file := rawRest.head?
    let rest := rawRest.drop payload
    let mut out : Option String := none
    let mut plant : Plant := .none
    let mut artifactsOnly := false
    let mut r := rest
    while !r.isEmpty do
      match r with
      | "--out" :: d :: r' => out := some d; r := r'
      | "--artifacts-only" :: r' => artifactsOnly := true; r := r'
      | "--plant" :: p :: r' =>
        match Plant.ofString? p with
        | some pl => plant := pl; r := r'
        | none => IO.eprintln s!"unknown plant {p}"; return 2
      | other :: _ => IO.eprintln s!"unexpected argument {other}\n{usage}"; return 2
      | [] => pure ()
    let some dir := out | IO.eprintln usage; return 2
    if name == "collective" then
      let some path := file | IO.eprintln "collective requires a source specification"; return 2
      unless artifactsOnly do
        IO.eprintln "collective requires --artifacts-only; supply independent TSV or binary fixture vectors to the runner"
        return 2
      CollectiveImport.writeFile path dir plant
      return 0
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
        writeGraph item.name typed item.kind (dir / item.name) plant artifactsOnly
      for (blockName, n) in blockGraphs do
        writeBlockGraph blockName n (dir / blockName) plant artifactsOnly
      return 0
    if let some (_, n) := blockGraphs.find? (·.1 == name) then
      writeBlockGraph name n dir plant artifactsOnly
      return 0
    match graphs.find? (·.name == name) with
    | some item =>
      let typed ← match item.build () with
        | .ok typed => pure typed
        | .error reason => throw <| IO.userError s!"{name}: {reason}"
      writeGraph name typed item.kind dir plant artifactsOnly
      return 0
    | none => IO.eprintln s!"unknown graph {name}; `obend-emit-gpu list`"; return 2
  | [] => IO.eprintln usage; return 2
