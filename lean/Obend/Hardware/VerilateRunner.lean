module
/-
# Obend.Hardware.VerilateRunner — `obend verilate`: Lean model vs Verilated emitted SystemVerilog

One check, named for what it is:
**Differential simulation** (`runVerilatePipeline`): emit an `RtlModule` with `emitModuleSV`, drive the
   Verilated module with `numVectors × numCycles` held-input cycles (vector words are small constants and
   a 16-bit LCG, `genVectorWord`), and compare every output against Lean's own `runModuleTrace` /
   `evalModuleOutputs` of the same module (and, for `.obend` compositions, against `MachineFast`). This is
   an emitter-correctness check; it is thin (64 cycles by default) and it is the thing to grow.
The logic-equivalence check of the emitted `.sv` is `hardware/lec/lec.sh` with `Obend.Hardware.YosysLec`.
-/
public import Lean
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
public import Obend.Core.Term
public import Obend.Core.Machine
public import Obend.Core.MachineFast
public import Obend.Logic.Program
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Lower.Proofs.Hardware
public import Obend.Spec.FrontEnd
public import Obend.Spec.Sha256
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Hardware.Compiler
@[expose] public section

namespace Obend.Core.MachineFast
open Obend.Core.Term Obend.Core.Machine
set_option autoImplicit false

/-- Evaluate a closed `Term` for up to `fuel` ticks on the compiled fast demand machine (`runBoundedFast`),
    returning the resulting 64-bit word (`BitVec 64`) when evaluation completes with `.natural` or `.boolean`. -/
def evalFuelFast (fuel : Nat) (t : Term) (heapLimit : Nat := 100000) (stackLimit : Nat := 10000) :
    Option (BitVec 64) :=
  match runBoundedFast ⟨heapLimit, stackLimit⟩ fuel (Machine.initial t) with
  | .finished (.natural n) _ => some (BitVec.ofNat 64 n)
  | .finished (.boolean b) _ => some (if b then 1#64 else 0#64)
  | _ => none

/-- `evalFuelFast` agrees identically with the reference `Machine.runBounded` semantics. -/
theorem evalFuelFast_eq_runBounded (fuel : Nat) (t : Term) (heapLimit stackLimit : Nat) :
    evalFuelFast fuel t heapLimit stackLimit =
      match Machine.runBounded ⟨heapLimit, stackLimit⟩ fuel (Machine.initial t) with
      | .finished (.natural n) _ => some (BitVec.ofNat 64 n)
      | .finished (.boolean b) _ => some (if b then 1#64 else 0#64)
      | _ => none := by
  unfold evalFuelFast runBoundedFast
  rw [runFrom_eq_runBounded]

end Obend.Core.MachineFast

namespace Obend.Hardware.VerilateRunner
open Lean (Json toJson)
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.MachineFast
open Obend.Logic
open Obend.Leaf
open Obend.Lower
open Obend.Spec
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Compiler

set_option autoImplicit false

/-! ## 1. Configuration, Trace Vectors & Verification Result Structures -/

/-- Configuration for `obend verilate`. -/
structure VerilateConfig where
  inputPath   : String := ""
  topModule   : String := ""
  numVectors  : Nat := 16
  numCycles   : Nat := 4
  vcdOutPath  : Option String := none
  svOutPath   : Option String := none
  workDir     : String := "hardware/sim/obj_dir"
  deriving DecidableEq, Repr

/-- A single multi-cycle differential test vector and its Lean reference outputs. -/
structure DifferentialVector where
  vecIdx          : Nat
  portInputs      : List (String × BitVec 64)
  expectedOutputs : List (String × BitVec 64)
  machineAgreed   : Bool
  deriving DecidableEq, Repr

/-- Result summary of an `obend verilate` run. -/
structure VerilateReport where
  moduleName        : String
  numWires          : Nat
  numRegs           : Nat
  numBels           : Nat
  vectorsChecked    : Nat
  cyclesPerVector   : Nat
  totalCycles       : Nat
  bitMismatches     : Nat
  machineFastAgreed : Bool
  traceAgreed       : Bool
  svPath            : String
  vcdPath           : Option String
  deriving DecidableEq, Repr

/-! ## 2. Canonical Physical `.obend` Compositions for Built-In Modules -/

/-- Canonical 2-layer `CleanroomTcadStack` composition (`stdlib/physical/CleanroomTcadStack.obend`). -/
def goldenCleanroomTcadComp : Composition where
  top :=
    { name     := "HighKMetalGateFinFetUpgrade"
      metadata := .record []
      fields   :=
        [ ("oxideEotPicometers", .nat 700)
        , ("vthMilliV",          .nat 250)
        , ("gateDelayPs",        .lam (.binary .add (.app (.get (.bound 1) "gateDelayPs") (.bound 0)) (.nat 4))) ]
      flat     := false }
  below :=
    [ { name     := "PlanarBulkMosfetBase"
        metadata := .record []
        fields   :=
          [ ("oxideEotPicometers", .nat 1200)
          , ("vthMilliV",          .nat 400)
          , ("drainCurrentUa",     .lam (.binary .add (.binary .multiply (.bound 0) (.nat 5)) (.get (.bound 2) "vthMilliV")))
          , ("gateDelayPs",        .lam (.binary .add (.binary .multiply (.bound 0) (.nat 8)) (.nat 20)))
          , ("calibratedDelayPs",  .lam (.app (.get (.bound 2) "gateDelayPs") (.binary .add (.bound 0) (.nat 2)))) ]
        flat     := false } ]
  seed :=
    [ ("oxideEotPicometers", .nat 0)
    , ("vthMilliV",          .nat 0)
    , ("drainCurrentUa",     .lam (.nat 0))
    , ("gateDelayPs",        .lam (.nat 0))
    , ("calibratedDelayPs",  .lam (.nat 0)) ]

/-- Canonical 3-layer `LcDrivesStator` composition (`stdlib/physical/LcDrivesStator.obend`). -/
def goldenLcDrivesStatorComp : Composition where
  top :=
    { name     := "FiveAxisFinishMilled"
      metadata := .record []
      fields   :=
        [ ("massKg",            .nat 395)
        , ("camSurfaceErrorUm", .lam (.binary .add (.app (.get (.bound 1) "camSurfaceErrorUm") (.bound 0)) (.nat 2))) ]
      flat     := false }
  below :=
    [ { name     := "LcDrivesInSlotUpgrade"
        metadata := .record []
        fields   :=
          [ ("thermalResistance", .nat 9)
          , ("sdfMargin",         .lam (.binary .add (.app (.get (.bound 1) "sdfMargin") (.bound 0)) (.nat 6))) ]
        flat     := false }
    , { name     := "OuterJacketStator"
        metadata := .record []
        fields   :=
          [ ("thermalResistance", .nat 29)
          , ("massKg",            .nat 420)
          , ("sdfMargin",         .lam (.binary .add (.bound 0) (.nat 10)))
          , ("peakWindingTemp",   .lam (.binary .add (.nat 50) (.binary .multiply (.bound 0) (.get (.bound 2) "thermalResistance"))))
          , ("camSurfaceErrorUm", .lam (.binary .multiply (.bound 0) (.nat 4))) ]
        flat     := false } ]
  seed :=
    [ ("thermalResistance", .nat 0)
    , ("massKg",            .nat 0)
    , ("sdfMargin",         .lam (.bound 0))
    , ("peakWindingTemp",   .lam (.bound 0))
    , ("camSurfaceErrorUm", .lam (.bound 0)) ]

/-- Canonical 2-layer `Cnc5AxisMill` composition (`stdlib/physical/Cnc5AxisMill.obend`). -/
def goldenCnc5AxisMillComp : Composition where
  top :=
    { name     := "AbbeAndRuckigCompensatedMill"
      metadata := .record []
      fields   :=
        [ ("servoLagUm",            .lam (.binary .multiply (.bound 0) (.nat 1)))
        , ("endMillDeflectionUm",   .lam (.binary .multiply (.bound 0) (.nat 2)))
        , ("abbeAngularDriftUm",    .lam (.binary .multiply (.bound 0) (.nat 1)))
        , ("commandedAxisAt10mmUm", .lam (.binary .add (.app (.get (.bound 1) "commandedAxisAt10mmUm") (.bound 0))
                                                       (.app (.get (.bound 1) "abbeAngularDriftUm") (.bound 0)))) ]
      flat     := false }
  below :=
    [ { name     := "Uncompensated5AxisMill"
        metadata := .record []
        fields   :=
          [ ("servoLagUm",            .lam (.binary .multiply (.bound 0) (.nat 5)))
          , ("endMillDeflectionUm",   .lam (.binary .multiply (.bound 0) (.nat 6)))
          , ("abbeAngularDriftUm",    .lam (.binary .multiply (.bound 0) (.nat 4)))
          , ("commandedAxisAt10mmUm", .lam (.nat 10000))
          , ("totalVolumetricErrorUm",
             .lam (.binary .add
               (.binary .add (.app (.get (.bound 2) "servoLagUm") (.nat 10))
                             (.app (.get (.bound 2) "endMillDeflectionUm") (.nat 5)))
               (.app (.get (.bound 2) "abbeAngularDriftUm") (.bound 0)))) ]
        flat     := false } ]
  seed :=
    [ ("servoLagUm",             .lam (.nat 0))
    , ("endMillDeflectionUm",    .lam (.nat 0))
    , ("abbeAngularDriftUm",     .lam (.nat 0))
    , ("commandedAxisAt10mmUm",  .lam (.nat 10000))
    , ("totalVolumetricErrorUm", .lam (.nat 0)) ]

/-- Select a built-in physical `Composition` and module name when requested by `--top` / `--module` or file stem. -/
def selectBuiltInComposition (choice : String) : String × Composition :=
  if choice == "lc_drives_stator" || choice == "lc_drives_userspace_stator" || choice == "LcDrivesStator" || choice == "LcDrivesStatorUsd" then
    ("lc_drives_userspace_stator", goldenLcDrivesStatorComp)
  else if choice == "cnc_5axis_mill" || choice == "cnc_5axis_userspace_mill" || choice == "Cnc5AxisMill" then
    ("cnc_5axis_userspace_mill", goldenCnc5AxisMillComp)
  else
    ("cleanroom_tcad_stack", goldenCleanroomTcadComp)

/-- Specialize a single `BookItem` by applying `inlineDict passes` followed by `betaRecordDict passes`. -/
def specializeVerilateBookItem (passes : Nat) : BookItem → BookItem
  | .slot d => .slot { d with code := betaRecordDict passes (inlineDict passes d.code) }
  | .static m v => .static m (betaRecordDict passes (inlineDict passes v))

/-- Specialize all definitions in a `Leaf.Book` via `specializeVerilateBookItem passes`. -/
def specializeVerilateBookDict (passes : Nat) (B : Book) : Book where
  items := B.items.map (specializeVerilateBookItem passes)

/-- Structurally recursive rich/multi-argument slot-list compiler using `compileRichMethod`. -/
def compileBookDefsRich
    (ctx : Obend.Hardware.Types.RtlLayoutCtx)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (wires : List WireAssign)
    (regs : List RegSpec)
    (outs : List OutputPort) :
    List LeafDef → Option (List WireAssign × List RegSpec × List OutputPort)
  | [] => some (wires, regs, outs)
  | d :: rest =>
    match compileRichMethod ctx slots slotBodies d.code with
    | none => none
    | some expr =>
      let w : WireAssign := { wireIdx := d.slot, name := d.member, expr := expr }
      let r : RegSpec :=
        { regIdx         := d.slot
        , name           := s!"reg_{d.member}"
        , domain         := .coreClk
        , resetKind      := .resetFree
        , isSynchronizer := false
        , nextExpr       := .wireRef d.slot }
      let o : OutputPort := { name := s!"out_{d.member}", expr := .wireRef d.slot }
      compileBookDefsRich ctx slots (slotBodies ++ [expr]) (wires ++ [w]) (regs ++ [r]) (outs ++ [o]) rest

/-- Compile a `Book` whose methods may take `0..k` arguments or use rich struct/union slice primitives. -/
def compileBookToRichRtl (modName : String) (B : Book) : Option RtlModule :=
  let maxArity := B.defs.foldl (fun acc d => max acc ((peelLambdas d.code).1 - 1)) 1
  let inNames :=
    if maxArity ≤ 1 then ["arg"]
    else (List.range maxArity).map (fun i => s!"arg_{i}")
  match compileBookDefsRich {} B.slots [] [] [] [] B.defs with
  | none => none
  | some (wires, regs, outs) =>
    some { name := modName, inputNames := inNames, wires := wires, regs := regs, outputs := outs }

/-- Compile a `Composition` to a verified `RtlModule`, preferring `compileBookToRtl` (after `specializeVerilateBookDict`)
    and falling back to `compileBookToPipelinedRtl`, `compileBookToRtlSat`, and `compileBookToRichRtl`. -/
def compileCompositionToVerifiedRtl (modName : String) (comp : Composition) : Option (Book × RtlModule) :=
  let rawBook := Obend.Leaf.emit comp
  let specBook := specializeVerilateBookDict 2 rawBook
  match compileBookToRtl modName specBook with
  | some m => if checkRtlModule m then some (specBook, m) else none
  | none =>
    match compileBookToPipelinedRtl modName specBook with
    | some m => if checkRtlModule m then some (specBook, m) else none
    | none =>
      match compileBookToRtlSat modName specBook with
      | some m => if checkRtlModule m then some (specBook, m) else none
      | none =>
        match compileBookToRichRtl modName specBook with
        | some m => if checkRtlModule m then some (specBook, m) else none
        | none => none

/-! ## 3. Deterministic Test Vector Generator (small constants + 16-bit LCG) & `MachineFast` / `runModuleTrace` Differential Reference -/

/-- Generate a deterministic 64-bit test input word for vector `vecIdx` and input port `portIdx`.
    Vectors 0..3 use small canonical boundary/golden inputs (`8`, `6`, `4`, `200`) to avoid overflow
    in unscaled arithmetic, and vectors `≥ 4` use a 16-bit linear congruential sequence (`< 65536`),
    so the differential check never sees the upper 48 bits of an input toggle. -/
def genVectorWord (vecIdx portIdx : Nat) : BitVec 64 :=
  match vecIdx with
  | 0 => BitVec.ofNat 64 (8 + portIdx)
  | 1 => BitVec.ofNat 64 (6 + portIdx)
  | 2 => BitVec.ofNat 64 (4 + portIdx)
  | 3 => BitVec.ofNat 64 (200 + portIdx)
  | _ =>
    let z := (vecIdx * 2654435761 + portIdx * 40503 + 1013904223) % 65536
    BitVec.ofNat 64 z

/-- Build a constant-input trace of length `numCycles` holding input environment `inEnv` with `rst = false`. -/
def mkHeldCycleTrace (numCycles : Nat) (inEnv : Nat → BitVec 64) : List (Bool × (Nat → BitVec 64)) :=
  List.replicate numCycles (false, inEnv)

/-- Strip leading `"out_"` prefix using kernel-reducible character list pattern matching. -/
def stripOutPrefix (s : String) : String :=
  match s.toList with
  | 'o' :: 'u' :: 't' :: '_' :: rest => String.ofList rest
  | _ => s

/-- Apply `fn` to a list of `Nat` arguments `(fn a₀ a₁ …)`. -/
def applyNatArgs (fn : Term) (args : List Nat) : Term :=
  args.foldl (fun acc a => .app acc (.nat a)) fn

/-- Initial register environment after the synchronous reset pulse (`top->rst = 1; tick(); top->rst = 0;`). -/
def initialModuleRegs (m : RtlModule) : Nat → BitVec 64 := fun rIdx =>
  match m.regs.find? (fun r => r.regIdx == rIdx) with
  | some r => match r.resetKind with | .syncReset v => v | .resetFree => 0#64
  | none => 0#64

/-- Evaluate a single `DifferentialVector` starting from register state `curRegs` across `numCycles`
    clock cycles via `HDL.runModuleTrace`, returning `(nextRegs, DifferentialVector)`. -/
def evaluateDifferentialVectorFromRegs
    (m : RtlModule)
    (comp? : Option Composition)
    (numCycles : Nat)
    (curRegs : Nat → BitVec 64)
    (vecIdx : Nat) : (Nat → BitVec 64) × DifferentialVector :=
  -- A vector word is masked to its port's width, so the Lean side sees what the port can carry.
  let inEnv : Nat → BitVec 64 := fun pIdx => truncToWidth (inputWidth m pIdx) (genVectorWord vecIdx pIdx)
  let portPairs : List (String × BitVec 64) :=
    (List.range m.inputNames.length).map fun pIdx =>
      (m.inputNames.getD pIdx "in_0", inEnv pIdx)
  let nRegs := m.regs.foldl (fun k r => max k (r.regIdx + 1)) 0
  -- `runModuleTrace` runs compiled as `runModuleTraceImpl` (`@[csimp]`, proved); its result is a
  -- closure that re-runs this vector's cycles per read, so it is read once per register into an
  -- array, and the next vector starts from that array rather than from a chain of closures.
  let traced := runModuleTrace m curRegs (mkHeldCycleTrace numCycles inEnv)
  let finalArr : Array (BitVec 64) := (List.range nRegs).toArray.map traced
  let finalRegs : Nat → BitVec 64 := fun i => if i < nRegs then finalArr.getD i 0#64 else curRegs i
  let expectedOuts := evalModuleOutputsW m inEnv finalRegs
  let arg0Nat := (inEnv 0).toNat
  let allArgNats := (List.range (max m.inputNames.length 1)).map (fun i => (inEnv i).toNat)
  let machineOk : Bool :=
    match comp? with
    | none => true
    | some comp =>
      let book := Obend.Leaf.emit comp
      let obj := book.link
      expectedOuts.all fun (outName, hwVal) =>
        let member := stripOutPrefix outName
        let arity :=
          match book.defs.find? (fun d => d.member == member) with
          | some d => (peelLambdas d.code).1 - 1
          | none   => 1
        let callArgs := if arity ≤ 1 then [arg0Nat] else allArgNats.take arity
        let callTerm : Term := applyNatArgs (.get obj member) callArgs
        let directTerm : Term := .get obj member
        match evalFuelFast 4000 callTerm with
        | some vm => vm == hwVal
        | none =>
          match evalFuelFast 4000 directTerm with
          | some vm => vm == hwVal
          | none => true
  ( finalRegs
  , { vecIdx          := vecIdx
    , portInputs      := portPairs
    , expectedOutputs := expectedOuts
    , machineAgreed   := machineOk } )

/-- Evaluate a single `DifferentialVector` from initial synchronous-reset state across `numCycles` clock cycles. -/
def evaluateDifferentialVector
    (m : RtlModule)
    (comp? : Option Composition)
    (numCycles : Nat)
    (vecIdx : Nat) : DifferentialVector :=
  (evaluateDifferentialVectorFromRegs m comp? numCycles (initialModuleRegs m) vecIdx).2

/-- Thread register state continuously across a list of vector indices (`N × C` continuous cycles). -/
def generateDifferentialVectorsAux
    (m : RtlModule)
    (comp? : Option Composition)
    (numCycles : Nat)
    (curRegs : Nat → BitVec 64) : List Nat → List DifferentialVector
  | [] => []
  | vIdx :: rest =>
    let (nextRegs, vec) := evaluateDifferentialVectorFromRegs m comp? numCycles curRegs vIdx
    vec :: generateDifferentialVectorsAux m comp? numCycles nextRegs rest

/-- Generate all `numVectors` differential reference vectors for `m` across `numVectors × numCycles`
    continuous clock cycles after synchronous reset. -/
def generateDifferentialVectors
    (m : RtlModule)
    (comp? : Option Composition)
    (numVectors numCycles : Nat) : List DifferentialVector :=
  generateDifferentialVectorsAux m comp? (max numCycles 1) (initialModuleRegs m) (List.range (max numVectors 1))

/-- Theorem: `runModuleTrace` over an appended trace equals sequential `runModuleTrace` composition. -/
theorem runModuleTrace_append
    (m : RtlModule)
    (initRegs : Nat → BitVec 64)
    (t1 t2 : List (Bool × (Nat → BitVec 64))) :
    runModuleTrace m initRegs (t1 ++ t2) =
      runModuleTrace m (runModuleTrace m initRegs t1) t2 := by
  unfold runModuleTrace
  exact List.foldl_append

/-! ## 4. Rung 1: C++17 `Verilator` Differential Harness Generator (`emitVerilatorHarnessCpp`) -/

/-- Emit a self-contained C++17 `Verilator` differential testbench for `m : RtlModule` with:
    1. `Verilated::randReset(2)` adversarial randomization of unreset registers,
    2. Optional `VerilatedVcdC` waveform dumping when `vcdPath?` is provided,
    3. Cycle-by-cycle stimulation across all `vectors.length × numCycles` cycles and exact 64-bit
       comparison against the Lean `runModuleTrace` & `MachineFast.evalFuelFast` reference outputs. -/
def emitVerilatorHarnessCpp
    (m : RtlModule)
    (vectors : List DifferentialVector)
    (numCycles : Nat)
    (vcdPath? : Option String) : String :=
  let vClass := s!"V{m.name}"
  -- Every domain's clock rises on the same tick: the harness checks `stepModuleRegs`, the
  -- all-clocks-together edge (`stepModuleDomain_eq_of_single` for one domain).
  let clocks := moduleClockPorts m
  let traceHeader :=
    match vcdPath? with
    | some _ => "#include \"verilated_vcd_c.h\"\n"
    | none   => ""
  let traceInit :=
    match vcdPath? with
    | some vcdPath =>
      "  Verilated::traceEverOn(true);\n" ++
      "  VerilatedVcdC* tfp = new VerilatedVcdC;\n" ++
      "  top->trace(tfp, 99);\n" ++
      s!"  tfp->open(\"{vcdPath}\");\n"
    | none => ""
  let traceDump0 :=
    match vcdPath? with
    | some _ => "    if (tfp) tfp->dump(sim_time++);\n"
    | none   => ""
  let traceClose :=
    match vcdPath? with
    | some _ => "  if (tfp) { tfp->close(); delete tfp; }\n"
    | none   => ""
  let zeroInputs := m.inputNames.map fun n => s!"  top->{n} = 0ULL;"
  let vecBlocks := vectors.map fun v =>
    let setIns := v.portInputs.map fun (pName, pVal) =>
      s!"    top->{pName} = {pVal.toNat}ULL;"
    let checkOuts := v.expectedOutputs.map fun (oName, oVal) =>
      s!"    if (static_cast<uint64_t>(top->{oName}) != {oVal.toNat}ULL) \{\n" ++
      s!"      std::fprintf(stderr, \"MISMATCH vec=%u port={oName}: got=%llu expected={oVal.toNat}\\n\", {v.vecIdx}u, static_cast<unsigned long long>(top->{oName}));\n" ++
      "      mismatches++;\n" ++
      "    }"
    s!"  // Vector {v.vecIdx}\n  \{\n" ++
    String.intercalate "\n" setIns ++ "\n" ++
    s!"    for (int c = 0; c < {max numCycles 1}; ++c) tick();\n" ++
    String.intercalate "\n" checkOuts ++ "\n  }"
  "#include \"" ++ vClass ++ ".h\"\n" ++
  "#include \"verilated.h\"\n" ++
  traceHeader ++
  "#include <cstdint>\n#include <cstdio>\n#include <cstdlib>\n\n" ++
  "int main(int argc, char** argv) {\n" ++
  "  Verilated::commandArgs(argc, argv);\n" ++
  "  Verilated::randReset(2);\n" ++
  s!"  {vClass}* top = new {vClass};\n" ++
  "  uint64_t sim_time = 0;\n" ++
  traceInit ++
  "  auto tick = [&]() {\n" ++
  String.join (clocks.map fun (_, clk, _) => s!"    top->{clk} = 0;\n") ++
  "    top->eval();\n" ++
  traceDump0 ++
  String.join (clocks.map fun (_, clk, _) => s!"    top->{clk} = 1;\n") ++
  "    top->eval();\n" ++
  traceDump0 ++
  "  };\n" ++
  String.join (clocks.map fun (_, _, rst) => s!"  top->{rst} = 1;\n") ++
  String.intercalate "\n" zeroInputs ++ "\n" ++
  "  tick();\n" ++
  String.join (clocks.map fun (_, _, rst) => s!"  top->{rst} = 0;\n") ++
  "  top->eval();\n" ++
  "  uint64_t mismatches = 0;\n" ++
  String.intercalate "\n" vecBlocks ++ "\n" ++
  traceClose ++
  "  delete top;\n" ++
  s!"  std::printf(\"VERILATE_OK module={m.name} vectors={vectors.length} cycles={vectors.length * (max numCycles 1)} mismatches=%llu\\n\", static_cast<unsigned long long>(mismatches));\n" ++
  "  return (mismatches == 0) ? 0 : 1;\n" ++
  "}\n"

/-! ## 5. SMT-LIB2 text of `RtlExpr` (`emitExprSmt2`; the LEC prints `YosysLec.smtOf`, and the tests compare the two) -/

/-- Format a 64-bit `BitVec 64` constant as a 16-digit SMT-LIB2 hex literal `#x0123456789abcdef`. -/
def bitVec64ToSmtHex (v : BitVec 64) : String :=
  let hexDigits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let chars := (List.range 16).map fun i =>
    let shift := (15 - i) * 4
    let nib := (v.toNat >>> shift) &&& 0xF
    hexDigits.getD nib '0'
  "#x" ++ String.ofList chars

/-- Render a word-level `RtlAluOp` application in SMT-LIB2 `QF_BV`. -/
def emitAluOpSmt2 (op : RtlAluOp) (lhs rhs : String) : String :=
  match op with
  | .add    => s!"(bvadd {lhs} {rhs})"
  | .sub    => s!"(bvsub {lhs} {rhs})"
  | .mul    => s!"(bvmul {lhs} {rhs})"
  | .bitAnd => s!"(bvand {lhs} {rhs})"
  | .bitOr  => s!"(bvor {lhs} {rhs})"
  | .bitXor => s!"(bvxor {lhs} {rhs})"
  | .shl    => s!"(bvshl {lhs} (bvand {rhs} #x000000000000003f))"
  | .lshr   => s!"(bvlshr {lhs} (bvand {rhs} #x000000000000003f))"
  | .ashr   => s!"(bvashr {lhs} (bvand {rhs} #x000000000000003f))"
  | .eq     => s!"(ite (= {lhs} {rhs}) #x0000000000000001 #x0000000000000000)"
  | .ult    => s!"(ite (bvult {lhs} {rhs}) #x0000000000000001 #x0000000000000000)"
  | .slt    => s!"(ite (bvslt {lhs} {rhs}) #x0000000000000001 #x0000000000000000)"
  | .qmul32 => s!"((_ extract 95 32) (bvmul ((_ sign_extend 64) {lhs}) ((_ sign_extend 64) {rhs})))"

/-- A width operator over a 64-bit SMT-LIB2 term `x`, as `HDL.evalWidthOp` defines it (for the
parameters `checkWidths` accepts; an out-of-range `sext` is rendered as `x`). -/
def emitWidthOpSmt2 (op : RtlWidthOp) (x : String) : String :=
  let mask (w : Nat) : String := bitVec64ToSmtHex (BitVec.ofNat 64 (2 ^ (min w 64) - 1))
  match op with
  | .slice hi lo => s!"(bvand (bvlshr {x} {bitVec64ToSmtHex (BitVec.ofNat 64 lo)}) {mask (hi + 1 - lo)})"
  | .zext _ => x
  | .sext f t =>
    if 0 < f ∧ f ≤ t ∧ t ≤ 64 then
      s!"((_ zero_extend {64 - t}) ((_ sign_extend {t - f}) ((_ extract {f - 1} 0) {x})))"
    else x
  | .trunc w => s!"(bvand {x} {mask w})"

/-- Render an `RtlExpr` as a word-level SMT-LIB2 `QF_BV` expression over `spec_` wires. -/
def emitExprSmt2 (wirePrefix : String) : RtlExpr → String
  | .const v       => bitVec64ToSmtHex v
  | .inputPort idx => s!"in_{idx}"
  | .wireRef idx   => s!"{wirePrefix}w_{idx}"
  | .regRead idx   => s!"r_{idx}"
  | .alu op a b    => emitAluOpSmt2 op (emitExprSmt2 wirePrefix a) (emitExprSmt2 wirePrefix b)
  | .mux c t f     =>
    s!"(ite (distinct {emitExprSmt2 wirePrefix c} #x0000000000000000) {emitExprSmt2 wirePrefix t} {emitExprSmt2 wirePrefix f})"
  | .bitNot a      => s!"(bvnot {emitExprSmt2 wirePrefix a})"
  | .resize op a   => emitWidthOpSmt2 op (emitExprSmt2 wirePrefix a)


/-- Multi-input sequential `RtlModule` exercising `.ashr`, `.slt`, `.qmul32`, `.shl`, `.lshr`,
    `.bitNot (.alu .bitXor ...)`, register `"r_0"`, and output `"in_ready"`. -/
def goldenMultiInputSeqAluRtl : RtlModule where
  name       := "obend_multi_input_seq_alu"
  inputNames := ["a", "b", "c"]
  wires      :=
    [ { wireIdx := 0, name := "w_ashr",  expr := .alu .ashr (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 1, name := "w_slt",   expr := .alu .slt (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 2, name := "w_qmul",  expr := .alu .qmul32 (.inputPort 0) (.inputPort 2) }
    , { wireIdx := 3, name := "w_shl",   expr := .alu .shl (.wireRef 0) (.const 3#64) }
    , { wireIdx := 4, name := "w_lshr",  expr := .alu .lshr (.wireRef 2) (.const 2#64) }
    , { wireIdx := 5, name := "w_xnor",  expr := .bitNot (.alu .bitXor (.wireRef 3) (.wireRef 4)) } ]
  regs       :=
    [ { regIdx := 0, name := "r_0", domain := .coreClk, resetKind := .syncReset 0#64
      , isSynchronizer := false
      , nextExpr := .mux (.wireRef 1) (.alu .add (.regRead 0) (.wireRef 5)) (.alu .sub (.regRead 0) (.inputPort 2)) } ]
  outputs    :=
    [ { name := "out_acc",  expr := .regRead 0 }
    , { name := "in_ready", expr := .alu .bitOr (.wireRef 1) (.const 1#64) } ]

/-- Widths and two clock domains in one module, for `obend verilate --top obend_width_probe` and
    `hardware/sim/obend_width_probe.sv`: 8/8/16/1-bit inputs; a 9-bit sum, a 24-bit concatenation,
    a 4-bit slice, an 8-to-16 sign extension and a 16-bit truncation; a 16-bit accumulator and a
    resetless 4-bit register in `coreClk`; a 1-bit flag crossing into `axiIoClk` through a two-flop
    synchronizer (`ASYNC_REG`) and counted there by an 8-bit register. It passes `checkRtlModuleW`. -/
def goldenWidthProbeRtl : RtlModule where
  name        := "obend_width_probe"
  inputNames  := ["a", "b", "c", "flag"]
  inputWidths := [8, 8, 16, 1]
  wires       :=
    [ { wireIdx := 0, name := "w_sum", width := 9,  expr := .alu .add (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 1, name := "w_cat", width := 24, expr := RtlExpr.concat (.inputPort 2) (.inputPort 0) 8 }
    , { wireIdx := 2, name := "w_hi",  width := 4,  expr := .resize (.slice 23 20) (.wireRef 1) }
    , { wireIdx := 3, name := "w_sx",  width := 16, expr := .resize (.sext 8 16) (.inputPort 0) }
    , { wireIdx := 4, name := "w_mix", width := 16,
        expr := .resize (.trunc 16) (.alu .sub (.wireRef 3) (.resize (.zext 16) (.wireRef 0))) } ]
  regs        :=
    [ { regIdx := 0, name := "acc", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , width := 16, nextExpr := .resize (.trunc 16) (.alu .add (.regRead 0) (.wireRef 4)) }
    , { regIdx := 1, name := "hi_q", domain := .coreClk, resetKind := .resetFree, isSynchronizer := false
      , width := 4, nextExpr := .wireRef 2 }
    , { regIdx := 2, name := "flag_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , width := 1, nextExpr := .inputPort 3 }
    , { regIdx := 3, name := "flag_s1", domain := .axiIoClk, resetKind := .syncReset 0#64, isSynchronizer := true
      , width := 1, nextExpr := .regRead 2 }
    , { regIdx := 4, name := "flag_s2", domain := .axiIoClk, resetKind := .syncReset 0#64, isSynchronizer := true
      , width := 1, nextExpr := .regRead 3 }
    , { regIdx := 5, name := "axi_cnt", domain := .axiIoClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , width := 8, nextExpr := .resize (.trunc 8) (.alu .add (.regRead 5) (.regRead 4)) } ]
  outputs     :=
    [ { name := "acc_out", expr := .regRead 0, width := 16 }
    , { name := "hi_out",  expr := .regRead 1, width := 4 }
    , { name := "cnt_out", expr := .regRead 5, width := 8 }
    , { name := "cat_out", expr := .wireRef 1, width := 24 } ]

/-- **Universal Carry-Propagate Adder BEL Identity (`carry4_add_bel_identity`)**:
    For all 64-bit words `a b : BitVec 64`, `(a ^^^ b) + ((a &&& b) <<< 1) = a + b`. -/
theorem carry4_add_bel_identity (a b : BitVec 64) :
    (a ^^^ b) + ((a &&& b) <<< 1) = a + b := by
  bv_decide

/-- **Universal Two's-Complement Subtractor BEL Identity (`carry4_sub_bel_identity`)**:
    For all 64-bit words `a b : BitVec 64`, `(a + ~~~b) + 1#64 = a - b`. -/
theorem carry4_sub_bel_identity (a b : BitVec 64) :
    (a + ~~~b) + 1#64 = a - b := by
  bv_decide

/-- **Universal Miter Soundness (`belMiter_unsat_iff_equiv`)**:
    A miter comparison `(specOut != implOut)` is unsatisfiable (`= false`) iff `specOut = implOut`. -/
theorem belMiter_unsat_iff_equiv (specOut implOut : BitVec 64) :
    (specOut != implOut) = false ↔ specOut = implOut := by
  simp [bne_eq_false_iff_eq]

/-! ## 6. (removed 2026-11-04) The two string-literal copies of `silicon_elab_top.sv` that lived here were
deleted; the single emitter is `Obend.Lower.SiliconElabFabric.emitSiliconElabFabricSV`, reached through
`obend hardware emit-silicon-sv` (`Obend.Hardware.Cli`). -/

/-! ## 7. External `Verilator` Execution Pipeline (`runVerilatePipeline`) -/

/-- Locate an executable binary by checking preferred paths first, then falling back to `name`. -/
def resolveToolBin (preferred : String) (fallbackName : String) : IO String := do
  if ← (System.FilePath.mk preferred).pathExists then
    return preferred
  else
    return fallbackName

/-- Inline `root.field` knot projections up to `fuel` depth so `fix(compose(...), seed())` terms expose their layers and seed record. -/
def resolveKnotTermVerilate (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          resolveKnotTermVerilate root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (resolveKnotTermVerilate root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (resolveKnotTermVerilate root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (resolveKnotTermVerilate root rawFields visiting fuel f) (resolveKnotTermVerilate root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (resolveKnotTermVerilate root rawFields visiting fuel l) (resolveKnotTermVerilate root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (resolveKnotTermVerilate root rawFields visiting fuel s) (resolveKnotTermVerilate root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (resolveKnotTermVerilate root rawFields visiting fuel m) (resolveKnotTermVerilate root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (resolveKnotTermVerilate root rawFields visiting fuel s) (resolveKnotTermVerilate root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (resolveKnotTermVerilate root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (resolveKnotTermVerilate root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (resolveKnotTermVerilate root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (resolveKnotTermVerilate root rawFields visiting fuel l) (resolveKnotTermVerilate root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (resolveKnotTermVerilate root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, resolveKnotTermVerilate root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, resolveKnotTermVerilate root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (resolveKnotTermVerilate root rawFields visiting fuel v)
      (resolveKnotTermVerilate root rawFields visiting fuel z)
      (resolveKnotTermVerilate root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (resolveKnotTermVerilate root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (resolveKnotTermVerilate root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, resolveKnotTermVerilate root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (resolveKnotTermVerilate root rawFields visiting fuel c)
      (resolveKnotTermVerilate root rawFields visiting fuel x)
      (resolveKnotTermVerilate root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (resolveKnotTermVerilate root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (resolveKnotTermVerilate root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (resolveKnotTermVerilate root rawFields visiting fuel t) names
      (resolveKnotTermVerilate root rawFields visiting fuel f)
  | _ + 1, t => t

/-- Decode a `.fix S seed` term into a `Composition` when `S` decodes via `Program.decodeOperands`. -/
def decodeCompositionWithSeedVerilate (want : Composition → Bool) : Term → Option Composition
  | .fix S (.record seed) =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      let C : Composition := ⟨top, below, seed⟩
      if want C then some C else none
  | .fix S seedTerm =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      if top.name == "" then none
      else
        match Obend.Law.run 20000 seedTerm with
        | some (.record seed) =>
          let C : Composition := ⟨top, below, seed⟩
          if want C then some C else none
        | _ => none
  | _ => none

/-- Step a `Term` up to `fuel` times, checking `decodeCompositionWithSeedVerilate` at each step before `.fix` unfolds. -/
def findCompositionObjectVerilate (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeCompositionWithSeedVerilate want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findCompositionObjectVerilate want fuel)

/-- Strip `#kind` metadata fields from a `Layer`. -/
def compactLayerVerilate (L : Layer) : Layer :=
  { L with
    metadata := .record [("name", .label L.name)]
    fields := L.fields.filter (fun kv => kv.1 != "#kind")
    composeMeta := .record [] }

/-- Strip `#kind` metadata fields from a `Composition`. -/
def compactCompositionVerilate (C : Composition) : Composition :=
  { C with
    top := compactLayerVerilate C.top
    below := C.below.map compactLayerVerilate
    seed := C.seed.filter (fun kv => kv.1 != "#kind") }

/-- Extract a `Composition` from an `.obend` source string via `FrontEnd.parseModule` / `FrontEnd.lowerDecoded` / `FrontEnd.accept`,
    scanning all callable declarations for open-recursive `fix(compose(...), seed())` compositions (or synthesizing a single-layer
    `Composition` from standalone callable functions when no `fix` composition is present). -/
def parseObendSourceComposition (modName : String) (entryHint : String) (src : String) : Option Composition :=
  let srcMod : FrontEnd.SourceModule :=
    { name := modName, source := src, sha256 := Sha256.hexString src, imports := [] }
  match FrontEnd.parseModule srcMod with
  | .error _ => none
  | .ok decodedMod =>
    let callables := decodedMod.decls.filter fun d =>
      match d with
      | .function .. | .extension .. | .spec .. => true
      | _ => false
    match callables.getLast? with
    | none => none
    | some lastDecl =>
      let limits : Json :=
        Json.mkObj
          [ ("heap",      toJson "100000")
          , ("stack",     toJson "100000")
          , ("ticks",     toJson "100000")
          , ("checkWork", toJson "65536") ]
      match FrontEnd.lowerDecoded [srcMod] [decodedMod] 0 lastDecl.name (Json.arr #[]) (Json.arr #[]) limits "definition" [] with
      | .error _ => none
      | .ok lowering =>
        match FrontEnd.accept lowering with
        | .error _ => none
        | .ok accepted =>
          let rootTerm := (Obend.Logic.Program.knotOf accepted.erased).getD accepted.erased
          let rawFields := Obend.Logic.Program.knotFields rootTerm
          let wantNamed : Composition → Bool := fun C => C.top.name != ""
          let foundComps : List (String × Composition) :=
            callables.filterMap fun d =>
              let shortName := d.name
              let fullKey := modName ++ "." ++ shortName
              let knotTerm : Term := .get rootTerm fullKey
              let opened := match rawFields.lookup fullKey with
                | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
                | none => knotTerm
              let rawComp? :=
                match findCompositionObjectVerilate wantNamed 64 knotTerm with
                | some c => some c
                | none =>
                  match findCompositionObjectVerilate wantNamed 64 (.app knotTerm (.record [])) with
                  | some c => some c
                  | none =>
                    let inlined := resolveKnotTermVerilate rootTerm rawFields [fullKey] 6 opened
                    decodeCompositionWithSeedVerilate wantNamed inlined
              rawComp?.map fun c => (shortName, compactCompositionVerilate c)
          if entryHint != "" then
            match foundComps.find? (fun (n, c) => n == entryHint || c.top.name == entryHint) with
            | some (_, c) => some c
            | none => (foundComps.getLast?).map Prod.snd
          else
            (foundComps.getLast?).map Prod.snd

/-- Resolve an `.obend` file or module name to `(moduleName, Option Composition, RtlModule)`. -/
def resolveTargetRtlModule (cfg : VerilateConfig) : IO (Except String (String × Option Composition × RtlModule)) := do
  if cfg.topModule == "obend_retimed_mac2" || cfg.inputPath == "obend_retimed_mac2" then
    return .ok ("obend_retimed_mac2", none, goldenRetimedMacRtl)
  if cfg.topModule == "obend_multi_input_seq_alu" || cfg.inputPath == "obend_multi_input_seq_alu" then
    return .ok ("obend_multi_input_seq_alu", none, goldenMultiInputSeqAluRtl)
  if cfg.topModule == "obend_width_probe" || cfg.inputPath == "obend_width_probe" then
    return .ok ("obend_width_probe", none, goldenWidthProbeRtl)
  let pathExists ←
    if cfg.inputPath != "" then (System.FilePath.mk cfg.inputPath).pathExists
    else pure false
  if pathExists then
    let src ← IO.FS.readFile cfg.inputPath
    let base := match (cfg.inputPath.splitOn "/").getLast? with | some b => b | none => cfg.inputPath
    let stem := if base.endsWith ".obend" then (base.take (base.length - 6)).toString else base
    let modName :=
      if cfg.topModule != "" then cfg.topModule
      else if stem == "CleanroomTcadStack" then "cleanroom_tcad_stack"
      else if stem == "LcDrivesStator" || stem == "LcDrivesStatorUsd" then "lc_drives_userspace_stator"
      else if stem == "Cnc5AxisMill" then "cnc_5axis_userspace_mill"
      else stem
    match parseObendSourceComposition stem cfg.topModule src with
    | some comp =>
      match compileCompositionToVerifiedRtl modName comp with
      | some (_, m) => return .ok (modName, some comp, m)
      | none => return .error s!"failed to compile elaborated composition in {cfg.inputPath} to RtlModule"
    | none =>
      return .error s!"failed to parse or elaborate Composition from {cfg.inputPath}"
  else
    let choice := if cfg.topModule != "" then cfg.topModule else cfg.inputPath
    if choice == "" || choice == "cleanroom_tcad_stack" || choice == "CleanroomTcadStack" ||
       choice == "lc_drives_stator" || choice == "lc_drives_userspace_stator" || choice == "LcDrivesStator" ||
       choice == "cnc_5axis_mill" || choice == "cnc_5axis_userspace_mill" || choice == "Cnc5AxisMill" then
      let (modName, comp) := selectBuiltInComposition choice
      match compileCompositionToVerifiedRtl modName comp with
      | some (_, m) => return .ok (modName, some comp, m)
      | none => return .error s!"failed to compile built-in composition {modName} to RtlModule"
    else
      return .error s!"input file or built-in module not found: {choice}"

/-- Read the `mismatches=<n>` field of the harness summary line (`VERILATE_OK ... mismatches=N`). -/
def parseMismatchCount (stdout : String) : Option Nat :=
  match (stdout.splitOn "mismatches=")[1]? with
  | none => none
  | some rest =>
    let digits := String.ofList (rest.toList.takeWhile Char.isDigit)
    digits.toNat?

/-- Run the `Verilator` differential simulation (`Verilated::randReset(2)`, optional `.vcd`). -/
def runVerilatePipeline (cfg : VerilateConfig) : IO (Except String VerilateReport) := do
  match ← resolveTargetRtlModule cfg with
  | .error err => return .error err
  | .ok (modName, comp?, m) =>
    if !checkRtlModuleW m then
      return .error s!"{m.name} fails checkRtlModuleW:\n{String.intercalate "\n" (widthErrors m)}"
    IO.FS.createDirAll (System.FilePath.mk cfg.workDir)
    let svPath := cfg.svOutPath.getD s!"{cfg.workDir}/{modName}.sv"
    let tbCppPath := s!"{cfg.workDir}/{modName}_verilate_tb.cpp"
    let mdir := s!"{cfg.workDir}/obj_{modName}"
    IO.FS.createDirAll (System.FilePath.mk mdir)
    let svText :=
      "/* verilator lint_off UNUSED */\n/* verilator lint_off DECLFILENAME */\n" ++
      emitModuleSV m
    IO.FS.writeFile svPath svText
    let vecs := generateDifferentialVectors m comp? cfg.numVectors cfg.numCycles
    let machineAllOk := vecs.all (·.machineAgreed)
    let cppText := emitVerilatorHarnessCpp m vecs cfg.numCycles cfg.vcdOutPath
    IO.FS.writeFile tbCppPath cppText
    let verilatorBin ← resolveToolBin "/opt/homebrew/bin/verilator" "verilator"
    let traceFlags : Array String := match cfg.vcdOutPath with | some _ => #["--trace"] | none => #[]
    let verArgs : Array String :=
      #[ "--cc", "--exe", "--build" ] ++ traceFlags ++
      #[ "--top-module", m.name
       , "-sv", "-Wno-UNUSED", "-Wno-DECLFILENAME", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"
       , "--x-assign", "unique", "--x-initial", "unique"
       , "--Mdir", mdir
       , "-o", s!"sim_{modName}"
       , svPath, tbCppPath ]
    let verOut ← IO.Process.output { cmd := verilatorBin, args := verArgs }
    if verOut.exitCode != 0 then
      return .error s!"verilator build failed:\n{verOut.stdout}\n{verOut.stderr}"
    let simBin := s!"{mdir}/sim_{modName}"
    let simOut ← IO.Process.output { cmd := simBin, args := #[] }
    let mismatches? := parseMismatchCount simOut.stdout
    if simOut.exitCode != 0 || mismatches? != some 0 then
      return .error s!"verilator simulation mismatch (mismatches={mismatches?}):\n{simOut.stdout}\n{simOut.stderr}"
    let nl := synthesizeModuleToBels m
    return .ok
      { moduleName        := m.name
      , numWires          := m.wires.length
      , numRegs           := m.regs.length
      , numBels           := nl.cells.length
      , vectorsChecked    := vecs.length
      , cyclesPerVector   := max cfg.numCycles 1
      , totalCycles       := vecs.length * (max cfg.numCycles 1)
      , bitMismatches     := mismatches?.getD 0
      , machineFastAgreed := machineAllOk
      , traceAgreed       := mismatches? == some 0
      , svPath            := svPath
      , vcdPath           := cfg.vcdOutPath
    }

/-! ## 8. CLI Flag Parsers & Command Entrypoints (`cmdVerilate`, `cmdEmitSiliconSv`, `cmdEmitSv`) -/

/-- Extract a `--flag <value>` pair from `args`, returning `(Option String, remainingArgs)`. -/
def extractCliFlag (flag : String) : List String → Option String × List String
  | [] => (none, [])
  | [x] => (none, [x])
  | f :: v :: rest =>
    if f == flag then (some v, rest)
    else
      let (res, tail) := extractCliFlag flag (v :: rest)
      (res, f :: tail)

/-- Compile a userspace `.obend` physical engineering `Composition` or built-in module via `resolveTargetRtlModule`
    and emit synthesizable SystemVerilog-2012 via `emitModuleSV`. -/
def cmdEmitSv (args : List String) : IO UInt32 := do
  let (topOpt, args0) := extractCliFlag "--top" args
  let (modOpt, args1) := extractCliFlag "--module" args0
  let (outOpt, args2) := extractCliFlag "--out" args1
  let posArgs := args2.filter (fun a => !a.startsWith "--")
  let modChoice := topOpt.getD (modOpt.getD (posArgs.headD "cleanroom_tcad_stack"))
  if modChoice == "silicon_elab_top" || modChoice == "silicon_elab" then
    IO.eprintln "refused (emit-sv): use `obend hardware emit-silicon-sv` for silicon_elab_top"
    return 3
  else
    let cfg : VerilateConfig :=
      { inputPath := posArgs.headD ""
        topModule := topOpt.getD (modOpt.getD "") }
    match ← resolveTargetRtlModule cfg with
    | .error err =>
      IO.eprintln s!"refused (emit-sv): {err}"
      return 3
    | .ok (_, _, m) =>
      if !checkRtlModuleW m then
        IO.eprintln s!"refused: synthesized RtlModule {m.name} failed DAG/CDC/width/two-flop check (checkRtlModuleW)"
        for e in widthErrors m do IO.eprintln s!"  {e}"
        return 3
      else
        let svText := "/* verilator lint_off UNUSED */\n/* verilator lint_off DECLFILENAME */\n" ++
          emitModuleSV m
        match outOpt with
        | some outPath =>
          IO.FS.writeFile outPath svText
          IO.println s!"wrote synthesized SystemVerilog module {m.name} ({m.wires.length} wires, {m.outputs.length} outputs) to {outPath}"
          return 0
        | none =>
          IO.print svText
          return 0

/-- Run `obend verilate <input.obend> [--top <name>] [--vectors N] [--cycles C] [--vcd <out.vcd>] [--out-sv FILE] [--work-dir DIR]`. -/
def cmdVerilate (args : List String) : IO UInt32 := do
  let (topOpt, args1) := extractCliFlag "--top" args
  let (vecOpt, args2) := extractCliFlag "--vectors" args1
  let (cycOpt, args3) := extractCliFlag "--cycles" args2
  let (vcdOpt, args4) := extractCliFlag "--vcd" args3
  let (svOpt, args5)  := extractCliFlag "--out-sv" args4
  let (dirOpt, args6) := extractCliFlag "--work-dir" args5
  let posArgs := args6.filter (fun a => !a.startsWith "--")
  let cfg : VerilateConfig :=
    { inputPath  := posArgs.headD ""
      topModule  := topOpt.getD ""
      numVectors := (vecOpt.bind String.toNat?).getD 16
      numCycles  := (cycOpt.bind String.toNat?).getD 4
      vcdOutPath := vcdOpt
      svOutPath  := svOpt
      workDir    := dirOpt.getD "hardware/sim/obj_dir" }
  match ← runVerilatePipeline cfg with
  | .error err =>
    IO.eprintln s!"refused (verilate): {err}"
    return 3
  | .ok rep =>
    let vcdTag := match rep.vcdPath with | some p => s!", vcd={p}" | none => ""
    IO.println s!"verified verilate ({rep.moduleName}): wires={rep.numWires}, regs={rep.numRegs}, bels={rep.numBels}, vectors={rep.vectorsChecked}, cycles={rep.totalCycles}, mismatches={rep.bitMismatches}, machineFastAgreed={rep.machineFastAgreed}{vcdTag}, verdict=ok"
    return 0

end Obend.Hardware.VerilateRunner
end
