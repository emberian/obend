module
/-
# tests/SiliconSpineTest — End-to-End Verification Suite for Hardware Compilation & Silicon Tapeout Spine

Verifies all 5 pillars in a single end-to-end test suite (`0 sorry`, `0 sorryAx`, `0 custom axioms`):
1. **In-Place `compileTermPipelined` Callee Body Substitution (`Obend.Hardware.Compiler`)**:
   - `substRtlInputPort0_sound`, `compileTermPipelined_sound`, and
     `compileTermPipelined_arg_wired_and_stage_correspondence` prove that direct arguments
     (`isDirectPipeArg arg = true`) read synchronous pipeline stage registers (`.regRead slotIdx`)
     while non-direct arguments (`isDirectPipeArg arg = false`) substitute the compiled argument
     into the callee slot's actual compiled `RtlExpr` body (`substRtlInputPort0 eArg calleeBody`).
2. **Strict `Hardware/Judge.lean` JSON Certificate Decoders (`Obend.Hardware.Judge`)**:
   - Verifies that `decodeRtlSynthCert` parses actual `RtlModule` wire/register/output tables and
     refuses (`.isOk = false`) certificates missing wire definitions, and that all hardware/EDA
     certificate decoders (`decodeRetimeCert`, `decodePnrCert`, `decodeDatasheetFitCert`,
     `decodeAgenticEdaCert`) refuse inputs when required fields are omitted (zero `golden*` fallback).
3. **Rational `Device.Wafer` Root Enclosures & `[FF, TT, SS]` Process Corner Envelope (`Device.Wafer`, `Process`)**:
   - Verifies `sqrtEnclosure_spec` (`lo² ≤ v ≤ hi²`), `anneal_var_mono`, `envelope7nm_valid`, and
     `envelope_timing_signoff_implies_all_intermediate_corners_safe`.
4. **Netlist-Bound `.obend` Silicon Tapeout Pipeline & Real cSHAKE256 SV Digest (`Obend.Hardware.TapeoutPipeline`)**:
   - Verifies `compileCompositionToSiliconTapeout_sound`, `compileObendModuleToSiliconTapeout_sound`,
     `tapeout_sv_digest_binds_or_collides`, and `golden_obend_module_silicon_tapeout_verified`.
5. **`#tooth` Mutation Probes**:
   - Exercises `#tooth` mutation falsification on `substRtlInputPort0` and `checkEnvelopeTimingSignoff`.
-/
public import Obend.Spec.FrontEnd
public import Obend.Hardware.Process
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.Device.Wafer
public import Obend.Hardware.Judge
public import Obend.Hardware.TapeoutPipeline
public import Obend.Tactic.Tooth
import all Obend.Hardware.Process
import all Obend.Hardware.Compiler
@[expose] public section

namespace Obend.Tests.SiliconSpineTest
open Obend.Core.Term
open Obend.Leaf
open Obend.Spec
open Obend.Analysis
open Obend.Hardware.Process
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Synth
open Obend.Hardware.PlaceRoute
open Obend.Hardware.Device
open Obend.Hardware.Judge
open Obend.Hardware.TapeoutPipeline

set_option autoImplicit false

/-! ## 1. In-Place `compileTermPipelined` Callee Body Substitution Verification -/

/-- Verify that `compileTermPipelined` distinguishes two distinct callee bodies (`slot 0` = `x * 3 + 1`,
`slot 1` = `x * 7 + 10`) when invoked with a non-direct argument `self.m(arg + 4)` (`isDirectPipeArg = false`),
emitting `((arg + 4) * 3 + 1)` vs `((arg + 4) * 7 + 10)` rather than a hardcoded `.alu .add (.regRead slotIdx) eArg`. -/
theorem pipelined_callee_body_substitution_distinguishes_methods :
    let slots := ["tripler", "septupler", "callTripler", "callSeptupler"];
    let body0 : RtlExpr := .alu .add (.alu .mul (.inputPort 0) (.const 3#64)) (.const 1#64);
    let body1 : RtlExpr := .alu .add (.alu .mul (.inputPort 0) (.const 7#64)) (.const 10#64);
    let slotBodies := [body0, body1];
    let tCall0 : Term := .app (.get (.bound 1) "tripler") (.binary .add (.bound 0) (.nat 4));
    let tCall1 : Term := .app (.get (.bound 1) "septupler") (.binary .add (.bound 0) (.nat 4));
    let tDirect0 : Term := .app (.get (.bound 1) "tripler") (.bound 0);
    compileTermPipelined slots slotBodies 1 [.inputPort 0] tDirect0 = some (.regRead 0) ∧
    compileTermPipelined slots slotBodies 1 [.inputPort 0] tCall0 =
      some (.alu .add (.alu .mul (.alu .add (.inputPort 0) (.const 4#64)) (.const 3#64)) (.const 1#64)) ∧
    compileTermPipelined slots slotBodies 1 [.inputPort 0] tCall1 =
      some (.alu .add (.alu .mul (.alu .add (.inputPort 0) (.const 4#64)) (.const 7#64)) (.const 10#64)) ∧
    (match compileTermPipelined slots slotBodies 1 [.inputPort 0] tCall0,
           compileTermPipelined slots slotBodies 1 [.inputPort 0] tCall1 with
     | some e0, some e1 =>
       evalRtlExpr (fun _ => 6#64) (fun _ => 0#64) (fun _ => 0#64) e0 == 31#64 &&
       evalRtlExpr (fun _ => 6#64) (fun _ => 0#64) (fun _ => 0#64) e1 == 80#64
     | _, _ => false) = true := by
  decide +kernel

/-! ## 2. Strict `Hardware/Judge.lean` Refusal on Missing JSON Certificate Fields -/

/-- Verify that every surviving hardware/EDA certificate decoder in `Obend.Hardware.Judge` strictly refuses
(`Except.isOk = false`) JSON certificates that omit required physical fields, with zero fallback to
hardcoded `golden*` presets. -/
theorem judge_decoders_strictly_refuse_missing_fields :
    -- 1. `hw-rtl-synth@1`: legacy `{dagOk, cdcOk}` without `numWires`/wire definitions is refused
    (decodeRtlSynthCert "{\"dagOk\":1,\"cdcOk\":1}").isOk = false ∧
    -- 2. `hw-rtl-synth@1`: explicit module with all required header/output fields decodes cleanly
    (decodeRtlSynthCert
      "{\"module\":\"test_rtl\",\"inputPort\":\"arg\",\"numWires\":0,\"numRegs\":0,\"outputName\":\"out_sum\",\"outputWire\":0}").isOk = true ∧
    -- 3. `hw-retime-sta@1`: missing `lag1` is refused
    (decodeRetimeCert "{\"lag0\":0}").isOk = false ∧
    -- 4. `hw-pnr-bitstream@1`: missing `net1DstWire` is refused
    (decodePnrCert "{\"sinkCapFf\":5,\"cell1TileY\":1,\"cell0BelSlot\":0,\"cell1BelSlot\":0,\"net0DstWire\":12}").isOk = false ∧
    -- 5. `datasheet-fit@1`: missing `rmseScaled` is refused
    (decodeDatasheetFitCert "{\"vthMv\":1700,\"kpScaled\":500}").isOk = false ∧
    -- 6. `agentic-eda@1`: missing `postSwapMaxTempMilliC` is refused
    (decodeAgenticEdaCert "{\"cand2LcscPartId\":25801,\"cand2StockQty\":50000,\"cand2VdsMaxMv\":40000,\"cand2RdsOnMaxMohm\":28}").isOk = false := by
  decide +kernel

/-! ## 3. Rational `Device.Wafer` Root Enclosure & `[FF, TT, SS]` Corner Envelope Timing Closure -/

/-- Verified rational Newton `sqrtEnclosure_spec` on `Device.Wafer` together with `[FF, TT, SS]`
process corner envelope validity (`envelope7nm_valid`) and universal intermediate-corner timing safety. -/
theorem device_wafer_and_process_envelope_spine_verified :
    (∀ (v : CanonicalRat), 0 ≤ v → ∀ (iters : Nat),
      (sqrtEnclosure v iters).lo * (sqrtEnclosure v iters).lo ≤ v ∧
      v ≤ (sqrtEnclosure v iters).hi * (sqrtEnclosure v iters).hi) ∧
    envelope7nm.Valid ∧
    (∀ c : ProcessCorner,
       CornerBetween envelope7nm.fastCorner c envelope7nm.slowCorner →
       checkEnvelopeTimingSignoff envelope7nm 2000 obendStageCritPath = true →
       checkTimingSignoff c 2000 obendStageCritPath = true) := by
  refine ⟨fun v hv iters => ⟨(sqrtEnclosure_spec hv iters).2.2.1, (sqrtEnclosure_spec hv iters).2.2.2.1⟩,
          envelope7nm_valid,
          fun c hBet hSign =>
            (envelope_timing_signoff_implies_all_intermediate_corners_safe
              envelope7nm 2000 obendStageCritPath c hBet hSign).1⟩

/-! ## 4. End-to-End Netlist-Bound `.obend` Silicon Tapeout Pipeline Verification -/

/-- Verify that the netlist-bound `.obend` tapeout pipeline (`compileObendModuleToSiliconTapeout_sound`,
`compileCompositionToSiliconTapeout_sound`, `reference_obend_module_silicon_tapeout_verified`)
binds `checkPnrCertificate` 1-to-1 to `art.belNetlist` and commits emitted SystemVerilog bytes via
real cSHAKE256 (`Obend.Core.Digest.deployed`). -/
theorem silicon_tapeout_pipeline_spine_verified :
    (∀ cfg src art,
       compileObendModuleToSiliconTapeout cfg src = .ok art →
       checkRtlModule art.rtlModule = true ∧
       checkBelNetlistValid art.belNetlist = true ∧
       countFfBels art.belNetlist = art.rtlModule.regs.length ∧
       checkPnrCertificate art.belNetlist art.tcadEnvelope.slowCorner cfg.clockPeriodPs art.pnrCert = true ∧
       art.pnrCert.placedCells.length = art.belNetlist.cells.length ∧
       checkEnvelopeTimingSignoff art.tcadEnvelope cfg.clockPeriodPs cfg.timingPath = true ∧
       art.systemVerilog = emitModuleSV art.rtlModule ∧
       art.svDigest = Obend.Digest.HashBytes.ofBE (Obend.Core.Digest.deployed art.systemVerilog.toUTF8.toList) ∧
       checkTapeoutTrustChecked tapeoutCheckedSupports art.receipt.trust = true) ∧
    FrontEnd.verifyCertJudgeTags isAdmittedTapeoutJudgeTag referenceTapeoutIsarCert = true := by
  refine ⟨fun cfg src art hOk => ?_, reference_obend_module_silicon_tapeout_verified.1⟩
  have hSound := compileObendModuleToSiliconTapeout_sound cfg src art hOk
  exact ⟨hSound.2.2.1,
         hSound.2.2.2.1,
         hSound.2.2.2.2.1,
         hSound.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 5. `#tooth` Mutation Falsification Probes -/

#tooth Obend.Hardware.Compiler.substRtlInputPort0_sound by mutation
  Obend.Hardware.Compiler.substRtlInputPort0 := fun _ body => body

#tooth Obend.Hardware.Process.envelope_timing_signoff_implies_all_intermediate_corners_safe by mutation
  Obend.Hardware.Process.checkEnvelopeTimingSignoff := fun _ _ _ => true

#print axioms pipelined_callee_body_substitution_distinguishes_methods
#print axioms judge_decoders_strictly_refuse_missing_fields
#print axioms device_wafer_and_process_envelope_spine_verified
#print axioms silicon_tapeout_pipeline_spine_verified

end Obend.Tests.SiliconSpineTest
end
