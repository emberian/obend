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
import Obend.Hardware.Gpu.NttKernel
import Obend.Hardware.ArrayKernel
import Obend.Hardware.Gpu.BlockEmit
import Obend.Hardware.Gpu.LayoutChecks
import Obend.Hardware.Gpu.DispatchProtocol

import Obend.Hardware.MultiDStencilTile
import Obend.Analysis.NonlinearMultiDPde
import Obend.Hardware.HDL
import Obend.Hardware.PdeSolvers
import Obend.Hardware.YosysLec

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
open Obend.Hardware.SquareGraphs
open Obend.Hardware.Gpu.Ntt
open Obend.Hardware.Gpu.GoldilocksSource
open Obend.Apps.ZkNtt (goldilocksPrime)

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
      let fieldReference := List.zipWith (fun a b => a * b % goldilocksPrime) left right
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

/-! ## Nonlinear PDE RTL fixtures, evaluated independently before SystemVerilog emission -/

open Obend.Analysis.NonlinearMultiDPde Obend.Hardware.MultiDStencilTile Obend.Hardware.HDL
open Obend.Hardware.PdeSolvers Obend.Hardware.YosysLec

private def writePdeVerilate (root : System.FilePath) : IO Unit := do
  let mut manifest : List String := []
  for (modelName, spec, axes, state) in
      [("EulerGas3D", EulerGas3D.spec, 3,
        fun (rho sign : Rat) => [rho, sign*3/4, -sign/2, sign/4, 8]),
       ("IdealMhd8Wave", IdealMhd8Wave.spec, 2,
        fun rho sign => [rho, sign*3/4, -sign/2, sign/4, 1/2, -1/4, 3/8, 8, sign/8]),
       ("BonaMasso1D", BonaMasso1DPrincipal.spec, 1,
        fun rho sign => [rho, 5/4 - sign/2, sign*3/4, -sign/2, sign*3/2]),
       ("BonaMassoZ4c1D", BonaMassoZ4c1D.spec, 1,
        fun rho sign => [rho, 5/4 - sign/2, sign*3/8, -sign/4, sign*3/8, sign/8])] do
    for axis in List.range axes do
      let name := s!"{modelName}_axis{axis}"
      let fluxRow := spec.fluxes.getD axis []
      let dag := compileFluxSsaDag (some spec.paramEnv) fluxRow
      let m := emitSystolicFluxCellRtlModule name spec.vars dag spec.paramEnv
      unless checkRtlModule m do throw <| IO.userError s!"{name}: malformed RTL"
      let dir := root / name
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir / s!"{name}.sv") (emitModuleSV m)
      IO.FS.writeFile (dir / s!"{name}_lec.smt2") (emitYosysLecSmt2 m)
      let mut cpp := s!"#include <cstdint>\n#include <cstdio>\n#include <verilated.h>\n#include \"V{name}.h\"\nint main() " ++ "{ " ++ s!"V{name} top; top.clk=0; top.rst=1; top.eval(); top.clk=1; top.eval(); top.rst=0;\n"
      for (rho, index) in ([1/2, 3/2, 2, 5/4, 1, 4] : List Rat).zipIdx do
        let sign : Rat := if index % 2 == 0 then 1 else -1
        let values := state rho sign
        let words := values.map ratToQ32Word
        let inputs := fun i => words.getD i 0#64
        let expected := evalFluxSsaDagQ32 inputs spec.paramEnv dag
        let wires := evalWireTable inputs (fun _ => 0#64) m.wires
        let actual := m.regs.map fun r => evalRtlExpr inputs wires (fun _ => 0#64) r.nextExpr
        unless actual == expected do throw <| IO.userError s!"{name}/{index}: RTL/reference disagreement"
        for (e, component) in fluxRow.zipIdx do
          let exactValue := evalFlux e ⟨(fun i => values.getD i 0), spec.paramEnv⟩
          let fixedValue : Rat := (expected.getD component 0#64).toInt / (4294967296 : Rat)
          let err := fixedValue - exactValue
          unless -(1/1048576 : Rat) ≤ err && err ≤ (1/1048576 : Rat) do
            throw <| IO.userError s!"{name}/{index}/{component}: rational flux enclosure failed"
        for (port, i) in spec.vars.zipIdx do cpp := cpp ++ s!"top.{port}={((words.getD i 0#64).toNat)}ULL; "
        cpp := cpp ++ "top.clk=0; top.eval(); top.clk=1; top.eval();\n"
        for (value, i) in expected.zipIdx do
          cpp := cpp ++ s!"if (uint64_t(top.flux_out_{i}) != {value.toNat}ULL) " ++ "{ std::fprintf(stderr, " ++ s!"\"{name} vector {index} component {i}: mismatch\\n\"); return 1; " ++ "}\n"
      cpp := cpp ++ s!"std::puts(\"{name}: 6 vectors, 0 ULP mismatch\"); return 0; " ++ "}\n"
      IO.FS.writeFile (dir / "test.cpp") cpp
      manifest := name :: manifest
      IO.println s!"  {name}: {m.wires.length} wires, six signed vectors with varying density or lapse -> {dir}"
  IO.FS.writeFile (root / "modules.txt") (String.intercalate "\n" manifest.reverse ++ "\n")

open Obend.Analysis.HyperbolicPde Obend.Hardware.Gpu.StencilTile

private def pdeInput (kind numVars variant : Nat) (dims : List Nat) : List (List Word) :=
  (List.range numVars).map fun c => (List.range (gridCellCount dims)).map fun j =>
    let x := (j + variant) % 8
    let wave : Rat := (([0,1,2,1,0,-1,-2,-1] : List Int).getD x 0 : Rat) / 16
    let rho : Rat := if x < 4 then 3/2 else 1
    ratToQ32Word (if kind == 0 then 1/2 + wave else if kind == 1 then
      ([rho, rho*wave, rho*(1/8), -rho*(1/16), if x < 4 then 3 else 2] : List Rat).getD c 0
      else if kind == 2 then
      ([rho, rho*(1/8), -rho*wave, rho*wave, 1/4, wave, -wave, 3, 0] : List Rat).getD c 0
      else ([rho, 1 + wave, wave, 1/8, -rho*wave] : List Rat).getD c 0)

private def pdeNeighbor (b : StencilBoundary) (dims : List Nat) (axis idx : Nat) (offset : Int) : Nat :=
  let coords := decodeMultiIdx dims idx
  encodeMultiIdx dims ((List.range dims.length).map fun d =>
    if d == axis then resolveStencilIdx b (dims.getD d 0) ((coords.getD d 0 : Int) + offset)
    else coords.getD d 0)

/-- Independent word oracle: reconstruct states, evaluate the SSA reference, then update conservatively. -/
private def pdeWordReference (spec : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (axis : Nat) (grids : List (List Word)) : List (List Word) :=
  let dag := compileFluxSsaDag (some spec.paramEnv) (spec.fluxes.getD axis [])
  let cells := (List.range (gridCellCount dims)).map fun idx => evalNonlinearFluxCellQ32 spec dag
    (fun offset j => (grids.getD j []).getD (pdeNeighbor b dims axis idx offset) 0#64)
  (List.range spec.numVars).map fun c => cells.map (fun cell => cell.getD c 0#64)

/-- Rational MUSCL oracle uses the original nonlinear flux expressions and rational coefficients. -/
private def pdeRatReference (spec : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (axis : Nat) (grids : List (List Word)) : List (List Rat) :=
  (List.range spec.numVars).map fun c => (List.range (gridCellCount dims)).map fun idx =>
    let u := fun offset j => ((grids.getD j []).getD (pdeNeighbor b dims axis idx offset) 0#64).toInt / (4294967296 : Rat)
    let slope := fun offset j => if spec.limiter == .firstOrder then 0 else
      minmod (u offset j-u (offset-1) j) (u (offset+1) j-u offset j)
    let face := fun offset => rusanovNonlinearFlux (spec.fluxes.getD axis []) spec.paramEnv spec.aMax
      (fun j => u offset j + slope offset j/2) (fun j => u (offset+1) j-slope (offset+1) j/2) c
    u 0 c-spec.cfl*(face 0-face (-1))

private def writePdeNonlinear (root : System.FilePath) (plant : Plant) : IO Unit := do
  for (workloadName, spec, dims, kind) in
      [("burgers-1d-q32", Burgers1D.spec, [8], 0),
       ("euler-3d-q32", EulerGas3D.spec, [4, 2, 2], 1),
       ("mhd-8wave-q32", IdealMhd8Wave.spec, [4, 4], 2),
       ("bona-masso-1d-q32", BonaMasso1DPrincipal.spec, [8], 3)] do
    let dir := root / workloadName
    IO.println s!"  {workloadName}: compiling shared nonlinear array source"
    (← IO.getStdout).flush
    let source := compileMultiDNonlinearFluxSweepSource spec .periodic dims 0
    IO.println s!"  {workloadName}: built {SoacOptimize.letCount source} shared bindings; checking Core4 member"
    (← IO.getStdout).flush
    let plan ← IO.ofExcept (ArrayPrograms.compileSource workloadName (List.replicate spec.numVars (gridCellCount dims)) source)
    IO.println s!"  {workloadName}: checked {plan.graph.edges.length} shared bindings; lowering WGSL"
    (← IO.getStdout).flush
    let artifact ← ArrayEmit.write workloadName plan.lower dir plant
    let mut vectors : List (List (List Int)) := []
    let mut outputs : List (List Obend.Hardware.ArrayHypergraph.Vec) := []
    for variant in [:3] do
      let base := pdeInput kind spec.numVars variant dims
      let grids := if variant == 2 then base.map (fun xs => List.replicate (gridCellCount dims) (xs.getD 0 0#64)) else base
      let vals := grids.map (List.map (·.toInt))
      let model := arrayModel plan.graph vals
      let reference := pdeWordReference spec .periodic dims 0 grids
      unless model == reference do throw <| IO.userError s!"{workloadName}: source/independent Q32 mismatch"
      if variant == 2 then
        unless model == grids do throw <| IO.userError s!"{workloadName}: constant state changed"
      let rational := pdeRatReference spec .periodic dims 0 grids
      for (component, exactComponent) in model.zip rational do
        for (word, exactValue) in component.zip exactComponent do
          let error := (word.toInt : Rat)/4294967296-exactValue
          unless -(1/1048576 : Rat) ≤ error && error ≤ (1/1048576 : Rat) do
            throw <| IO.userError s!"{workloadName}: rational enclosure failed"
      vectors := vals :: vectors
      outputs := model :: outputs
    IO.FS.writeFile (dir / "expected.tsv") (expectedTsvValues vectors.reverse outputs.reverse)
    IO.println s!"  {workloadName}: {spec.numVars} components, {artifact.shaders.size} dispatches, independent Q32 and rational checks passed -> {dir}"

/-! ## Main -/

def usage : String :=
  "usage: obend-emit-gpu list | <graph> --out DIR [--plant addAsSub|swapMux|mulHighZero] | all --out DIR [--plant P] | catgrad FILE --out DIR [--plant P] | leaf BOOK MEMBER INPUTS --out DIR [--plant P] | leaf-example --out DIR | pde-verilate --out DIR | pde-nonlinear --out DIR [--plant P]"

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
    if name == "pde-nonlinear" then
      writePdeNonlinear dir plant
      return 0
    if name == "pde-verilate" then
      writePdeVerilate dir
      return 0
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
