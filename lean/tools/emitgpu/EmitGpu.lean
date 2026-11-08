/-
# `obend-emit-gpu` — array hypergraphs lowered to compute shaders (`Obend.Hardware.Gpu`)

    obend-emit-gpu list
    obend-emit-gpu <graph> --out DIR [--plant P]
        DIR/plan.json (the allocated device buffer's size, every wire's base and length, the constant and index
        buffers, the boundary wires, one shader per dispatch), DIR/stage_<k>.wgsl, and
        DIR/expected.tsv, one line per vector: index, the input wires, and the output wires
        `Obend.Hardware.Gpu.runProgram` shows (wires separated by `;`, elements by `,`, signed 64-bit)
    obend-emit-gpu all --out DIR [--plant P]
        every graph, each under DIR/<graph>/

`--plant addAsSub` emits every `+` as `-`; `--plant swapMux` exchanges the arms of every `select`:
rules planted in the shader text only, for `hardware/gpu/verify_gpu.sh`'s tooth. The expected values
are always the unplanted model's.

Expected values are `evalGraphArr`'s, which is `evalGraph` with the wires stored (`evalGraphArr_eq`).
Before writing, the emitter refuses a graph that fails `ArrayGraph.wf` (the hypothesis of
`lowerArrayToGpu_sound`, so the expected values are `evalGraph`'s and the device must show them) and an
NTT graph whose evaluation disagrees with a recursive radix-2 NTT over the Goldilocks field in `Nat`
arithmetic (`nttFast`), which for the smaller sizes is itself checked against the naive DFT
(`nttReference`). These are tests of the fixtures, run on every emission.

NTTs use `ArrayKernel.Program`: indexed multi-output maps, radix-4 register networks, shared-memory
phases, and balanced Stockham uploads derived from ec-gpu's `radix_fft` and Govindaraju et al. SC2008.
The source contains every index and arithmetic operation; the generic emitter contains no NTT shader.
`Program.check` admits bounds, SSA closure, initialization and ownership; `SourceProtocol.checkProgram`
checks the actual physical-lane phase protocol against G4. Expected outputs are the executable source
semantics, independently compared with `nttFast` and (at small sizes) the direct DFT. These comparisons
are gates, not a universal theorem that the chosen NTT construction is the mathematical DFT.
`--artifacts-only` omits expected-value evaluation so planted shader rules reuse the unplanted output
oracle once per external gate run; plan equality is required before that reuse.
-/
import Obend.Hardware.SquareGraphs
import Obend.Hardware.Gpu.Ntt
import Obend.Hardware.ArrayKernel
import Obend.Hardware.Gpu.BlockEmit
import Obend.Hardware.Gpu.LayoutChecks
import Obend.Hardware.Gpu.DispatchProtocol
import Obend.Hardware.Gpu.GoldilocksSource

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.SquareGraphs
open Obend.Hardware.Gpu.Ntt

open Obend.Hardware.ArrayBuild
open Obend.Hardware.Gpu.GoldilocksSource

def writeGraph (name : String) (g : ArrayGraph) (kind : Kind) (dir : System.FilePath) (plant : Plant) (artifactsOnly : Bool := false) : IO Unit := do
  unless g.wf do
    throw <| IO.userError s!"{name}: the graph is not well-formed (ArrayGraph.wf)"
  unless layoutOk g do
    throw <| IO.userError s!"{name}: allocated layout fails live-range separation or dispatch race check"
  let p := lowerArrayToGpu g
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (emitPlanJson name p)
  for (s, k) in p.stages.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (emitStageWgsl plant name k p.stages.length s)
  if artifactsOnly then return
  IO.FS.writeFile (dir / "expected.tsv") (expectedTsv name g kind (arrayModel g))
  IO.println s!"  {name}: {g.lengths.length} wires ({p.words} words), {g.edges.length} edges, \
    {(fuseGraph g).edges.length} after fusion, {p.consts.length} constants, \
    {p.tables.length} indices, {p.stages.length} dispatches \
    ({String.intercalate "," (p.stages.map fun s => toString s.kernels.length)} kernels), \
    {vectorCount g} vectors -> {dir}"

/-- Block programs replace the earlier per-stage NTT graphs. -/
def blockGraphs : List (String × Nat) :=
  [4, 16, 64, 1024, 65536, 1048576].map fun n => (s!"ntt-{n}", n)

def writeBlockGraph (name : String) (n : Nat) (dir : System.FilePath) (plant : Plant) (artifactsOnly : Bool := false) : IO Unit := do
  unless n >= 2 && n == 2^(Nat.log2 n) && n < 2^26 do
    throw <| IO.userError s!"{name}: expected a supported power-of-two size below 2^26"
  let p := nttBlockProgram n
  if let .error reason := p.check then
    throw <| IO.userError s!"{name}: block source rejected: {reason}"
  unless SourceProtocol.checkProgram p workgroupSize do
    throw <| IO.userError s!"{name}: source protocol fails G4 phase geometry or race certificate"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (BlockEmit.emitPlan name p)
  for (d, k) in p.dispatches.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (BlockEmit.emitDispatch plant name p d)
  if artifactsOnly then return
  let mut lines := #[]
  let count := if n > 4096 then 2 else if n >= 64 then 6 else 12
  for v in [:count] do
    let vals := vectorFor .ntt [n] v
    let input := (vals.getD 0 []).map Int.toNat
    let mem := Obend.Hardware.ArrayKernel.initialMemory p (vals.map fun xs => (toVec xs).toArray)
    let result := Obend.Hardware.ArrayKernel.evalProgram p mem
    let model := p.outputs.map fun i => (result.getD i #[]).toList
    let fast := (nttFast input.toArray (rootOfUnity n)).toList
    unless (model.getD 0 []).map (·.toNat) == fast do
      throw <| IO.userError s!"{name} vector {v}: block array source disagrees with recursive NTT"
    if n <= 1024 then
      unless nttReference input == fast do
        throw <| IO.userError s!"{name} vector {v}: recursive NTT disagrees with direct DFT"
    let signed64 (xs : List Int) := xs.map fun x => (BitVec.ofInt 64 x).toInt
    lines := lines.push s!"{v}\t{wiresText (vals.map signed64)}\t{wiresText (model.map fun xs => xs.map (·.toInt))}"
  IO.FS.writeFile (dir / "expected.tsv") (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"  {name}: {BlockEmit.spaceSize p .device} device words, {BlockEmit.spaceSize p .shared} shared words, {p.dispatches.length} dispatches -> {dir}"

/-! ## Main -/

def usage : String :=
  "usage: obend-emit-gpu list | <graph> --out DIR [--plant addAsSub|swapMux|mulHighZero] | all --out DIR [--plant P]"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check-layout"] =>
    for (name, ok) in layoutCheckResults do
      IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
    return if layoutCheckFixtures then 0 else 1
  | ["list"] =>
    for (n, _, _) in graphs do IO.println n
    for (n, _) in blockGraphs do IO.println n
    return 0
  | name :: rest =>
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
    if name == "all" then
      for (n, g, kind) in graphs do writeGraph n g kind (dir / n) plant artifactsOnly
      for (name, n) in blockGraphs do writeBlockGraph name n (dir / name) plant artifactsOnly
      return 0
    if let some (_, n) := blockGraphs.find? (·.1 == name) then
      writeBlockGraph name n dir plant artifactsOnly
      return 0
    match graphs.find? (·.1 == name) with
    | some (_, g, kind) => writeGraph name g kind dir plant artifactsOnly; return 0
    | none => IO.eprintln s!"unknown graph {name}; `obend-emit-gpu list`"; return 2
  | [] => IO.eprintln usage; return 2
