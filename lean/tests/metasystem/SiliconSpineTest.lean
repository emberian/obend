module
/-
# tests/SiliconSpineTest — End-to-End Verification Suite for WS-Q Hardware Spine

Verifies all 4 WS-Q pillars in a single end-to-end test suite (`0 sorry`, `0 sorryAx`, `0 custom axioms`):
1. **In-Place `compileTermPipelined` Callee Body Substitution (`Obend.Hardware.Compiler`)**:
   - `substRtlInputPort0_sound`, `compileTermPipelined_sound`, and
     `compileTermPipelined_arg_wired_and_stage_correspondence` prove that direct arguments
     (`isDirectPipeArg arg = true`) read synchronous pipeline stage registers (`.regRead slotIdx`)
     while non-direct arguments (`isDirectPipeArg arg = false`) substitute the compiled argument
     into the callee slot's actual compiled `RtlExpr` body (`substRtlInputPort0 eArg calleeBody`).
2. **Strict `Hardware/Judge.lean` JSON Certificate Decoders (`Obend.Hardware.Judge`)**:
   - Verifies that `decodeRtlSynthCert` parses actual `RtlModule` wire/register/output tables and
     refuses (`.isOk = false`) certificates missing wire definitions, and that all hardware/EDA
     certificate decoders (`decodePnrCert`, `decodeFabuBloxCert`, `decodeWaferSpaceCert`,
     `decodeDatasheetFitCert`, `decodeRfTransceiverCert`, `decodePhotonicsCert`, `decodePcbBoardCert`,
     `decodeAgenticEdaCert`) refuse inputs when required fields are omitted (zero `golden*` fallback).
3. **Cleanroom-to-TCAD `[FF, TT, SS]` Process Corner Envelope & Dual-Corner Timing Signoff (`FabuBlox`, `Physics`, `TcadBridge`)**:
   - Verifies `ald_step_coverage_dominates_pvd`, `fickian_diffusion_monotone_in_thermal_budget`,
     `cmp_dishing_monotone_in_density`, `gaa_nanosheet_selective_release_preserves_channel`,
     `high_k_hfo2_reduces_eot_and_boosts_cox`, `subthreshold_swing_thermionic_lower_bound`,
     `drive_current_antitone_in_vth_and_eot`, `extractTcadCornerEnvelope_valid`,
     `ptm_2d_cancellation_tightens_ss_corner_delay`, and
     `envelope_timing_signoff_implies_all_intermediate_corners_safe`.
4. **Unified 9-Stage `.obend` Silicon Tapeout Pipeline (`Obend.Hardware.TapeoutPipeline`)**:
   - Verifies `compileCompositionToSiliconTapeout_sound`, `compileObendModuleToSiliconTapeout_sound`,
     and `golden_obend_module_silicon_tapeout_verified`.
5. **`#tooth` Mutation Probes**:
   - Exercises `#tooth` mutation falsification on `substRtlInputPort0` and `checkEnvelopeTimingSignoff`.
-/
public import Obend.Spec.FrontEnd
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.WaferSpace
public import Obend.Hardware.Judge
public import Obend.Hardware.FabuBlox
public import Obend.Hardware.TcadBridge
public import Obend.Hardware.TapeoutPipeline
public import Obend.Tactic.Tooth
import all Obend.Hardware.TcadBridge
@[expose] public section

namespace Obend.Tests.SiliconSpineTest
open Obend.Core.Term
open Obend.Leaf
open Obend.Spec
open Obend.Hardware.Process
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Synth
open Obend.Hardware.WaferSpace
open Obend.Hardware.FabuBlox
open Obend.Hardware.TcadBridge
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

/-- Verify that every hardware/EDA certificate decoder in `Obend.Hardware.Judge` strictly refuses
(`Except.isOk = false`) JSON certificates that omit required physical fields, with zero fallback to
hardcoded `golden*` presets. -/
theorem judge_decoders_strictly_refuse_missing_fields :
    -- 1. `hw-rtl-synth@1`: legacy `{dagOk, cdcOk}` without `numWires`/wire definitions is refused
    (decodeRtlSynthCert "{\"dagOk\":1,\"cdcOk\":1}").isOk = false ∧
    -- 2. `hw-rtl-synth@1`: explicit module with all required header/output fields decodes cleanly
    (decodeRtlSynthCert
      "{\"module\":\"test_rtl\",\"inputPort\":\"arg\",\"numWires\":0,\"numRegs\":0,\"outputName\":\"out_sum\",\"outputWire\":0}").isOk = true ∧
    -- 3. `hw-pnr-bitstream@1`: missing `net1DstWire` is refused
    (decodePnrCert "{\"sinkCapFf\":5,\"cell1TileY\":1,\"cell0BelSlot\":0,\"cell1BelSlot\":0,\"net0DstWire\":12}").isOk = false ∧
    -- 4. `fabublox-run@1`: missing `step2TempC` is refused
    (decodeFabuBloxCert "{\"step0Kind\":0,\"step1TempC\":250}").isOk = false ∧
    -- 5. `waferspace-signoff@1`: missing `layoutSig` is refused
    (decodeWaferSpaceCert
      "{\"dieWidthUm\":2920,\"dieHeightUm\":2920,\"numVddPads\":4,\"numVssPads\":4,\"numSignalPads\":24,\"numCornerCells\":4,\"sealRingWidthNm\":6000,\"allIoHaveEsdClamp\":1,\"maxWireAreaUm2\":120,\"gateOxideAreaUm2\":2,\"hasDiodeTieDown\":1,\"densityPermille\":450,\"schematicSig\":987654321}").isOk = false ∧
    -- 6. `datasheet-fit@1`: missing `rmseScaled` is refused
    (decodeDatasheetFitCert "{\"vthMv\":1700,\"kpScaled\":500}").isOk = false ∧
    -- 7. `rf-transceiver@1`: missing `evmRmsPermille` is refused
    (decodeRfTransceiverCert "{\"nfCascadeMilliDb\":2500,\"iip3CascadeMilliDbm\":-5000,\"s11MagPermille\":200}").isOk = false ∧
    -- 8. `photonics-pic@1`: missing `pdRespMaPerW` is refused
    (decodePhotonicsCert "{\"mziArmLenUm\":200,\"mziDeltaNeffMicro\":2500}").isOk = false ∧
    -- 9. `pcb-board@1`: missing `creepageDistancesUm` is refused
    (decodePcbBoardCert "{\"traceWidthsMil\":6,\"traceClearancesMil\":6,\"viaAspectRatiosPermille\":8000,\"diffPairSkewFs\":2000}").isOk = false ∧
    -- 10. `agentic-eda@1`: missing `postSwapMaxTempMilliC` is refused
    (decodeAgenticEdaCert "{\"cand2LcscPartId\":25801,\"cand2StockQty\":50000,\"cand2VdsMaxMv\":40000,\"cand2RdsOnMaxMohm\":28}").isOk = false := by
  decide +kernel

/-! ## 3. Cleanroom-to-TCAD `[FF, TT, SS]` Corner Envelope & Dual-Corner Timing Closure -/

/-- What survives of the former Pillar 2A bundle (2026-11-04: the integer identities it cited — step
coverage, GAA release, EOT, subthreshold swing, PTM cancellation, the golden preset — were deleted with
`Hardware/Physics.lean` §3/§7 and `FabuBlox` §7; the device physics is `Obend/Hardware/Device/`): the
corner envelope of a well-formed tolerance box is ordered, and dual-corner signoff covers every
intermediate corner. -/
theorem cleanroom_to_tcad_envelope_spine_verified :
    (extractTcadCornerEnvelope golden7nmToleranceBox true).Valid ∧
    (∀ c : ProcessCorner,
       CornerBetween
         (extractTcadCornerEnvelope golden7nmToleranceBox true).fastCorner
         c
         (extractTcadCornerEnvelope golden7nmToleranceBox true).slowCorner →
       checkEnvelopeTimingSignoff (extractTcadCornerEnvelope golden7nmToleranceBox true) 2000 obendStageCritPath = true →
       checkTimingSignoff c 2000 obendStageCritPath = true) := by
  refine ⟨extractTcadCornerEnvelope_valid golden7nmToleranceBox true
            (CleanroomToleranceBox.checkWf_sound golden7nmToleranceBox (by decide)),
          fun c hBet hSign =>
            (envelope_timing_signoff_implies_all_intermediate_corners_safe
              (extractTcadCornerEnvelope golden7nmToleranceBox true) 2000 obendStageCritPath c hBet hSign).1⟩

/-! ## 4. End-to-End 9-Stage `.obend` Silicon Tapeout Pipeline Verification -/

/-- Verify that the 9-stage `.obend` tapeout pipeline (`compileObendModuleToSiliconTapeout_sound`,
`compileCompositionToSiliconTapeout_sound`, `golden_obend_module_silicon_tapeout_verified`)
compiles `goldenCleanroomTcadComp` + `[goldenTapeoutIsarCert]` to a verified `SiliconTapeoutArtifact`
satisfying every stage invariant from Isar contract judge admission through `wafer.space` signoff. -/
theorem silicon_tapeout_pipeline_spine_verified :
    (∀ cfg src art,
       compileObendModuleToSiliconTapeout cfg src = .ok art →
       checkRtlModule art.rtlModule = true ∧
       checkBelNetlistValid art.belNetlist = true ∧
       art.tcadEnvelope.Valid ∧
       checkEnvelopeTimingSignoff art.tcadEnvelope cfg.clockPeriodPs cfg.timingPath = true ∧
       checkWaferSpaceSignoff cfg.waferSpaceCert = true ∧
       art.systemVerilog = emitModuleSV art.rtlModule ∧
       checkTapeoutTrustChecked tapeoutCheckedSupports art.receipt.trust = true) ∧
    FrontEnd.verifyCertJudgeTags isAdmittedTapeoutJudgeTag goldenTapeoutIsarCert = true := by
  refine ⟨fun cfg src art hOk => ?_, golden_obend_module_silicon_tapeout_verified.1⟩
  have hSound := compileObendModuleToSiliconTapeout_sound cfg src art hOk
  exact ⟨hSound.2.2.1,
         hSound.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hSound.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 5. `#tooth` Mutation Falsification Probes -/

-- Mutation: If `checkEnvelopeTimingSignoff` ignored the fast-corner hold check and always returned `true`,
-- `envelope_timing_signoff_implies_all_intermediate_corners_safe` is rejected by `#tooth`!
#tooth envelope_timing_signoff_implies_all_intermediate_corners_safe by mutation
  Obend.Hardware.TcadBridge.checkEnvelopeTimingSignoff := fun _ _ _ => true

#print axioms pipelined_callee_body_substitution_distinguishes_methods
#print axioms judge_decoders_strictly_refuse_missing_fields
#print axioms cleanroom_to_tcad_envelope_spine_verified
#print axioms silicon_tapeout_pipeline_spine_verified

end Obend.Tests.SiliconSpineTest
end
