module
import all Obend.Hardware.Judge
/-
# tests/SiliconSpineTest — End-to-End Verification Suite for Hardware Compilation & Process Corner Spine

Verifies all 4 pillars in a single end-to-end test suite (`0 sorry`, `0 sorryAx`, `0 custom axioms`):
1. **In-Place `compileTermPipelined` Callee Body Substitution (`Obend.Hardware.Compiler`)**:
   - `substRtlInputPort0_sound`, `compileTermPipelined_sound`, and
     `compileTermPipelined_arg_wired_and_stage_correspondence` prove that direct arguments
     (`isDirectPipeArg arg = true`) read synchronous pipeline stage registers (`.regRead slotIdx`)
     while non-direct arguments (`isDirectPipeArg arg = false`) substitute the compiled argument
     into the callee slot's actual compiled `RtlExpr` body (`substRtlInputPort0 eArg calleeBody`).
2. **Strict `Hardware/Judge.lean` JSON Certificate Decoders (`Obend.Hardware.Judge`)**:
   - Verifies that `decodeRtlSynthCert` parses actual `RtlModule` wire/register/output tables and
     refuses (`.isOk = false`) certificates missing wire definitions, and that all hardware/EDA
     certificate decoders (`decodeRetimeCert`, `decodePnrCert`, `decodeAgenticEdaCert`) refuse inputs
     when required fields are omitted (zero `golden*` fallback).
3. **Rational `Device.Wafer` Root Enclosures & `[FF, TT, SS]` Process Corner Envelope (`Device.Wafer`, `Process`)**:
   - Verifies `sqrtEnclosure_spec` (`lo² ≤ v ≤ hi²`), `anneal_var_mono`, `envelope7nm_valid`, and
     `envelope_timing_signoff_implies_all_intermediate_corners_safe`.
4. **`#tooth` Mutation Probes**:
   - Exercises `#tooth` mutation falsification on `substRtlInputPort0` and `checkEnvelopeTimingSignoff`.
-/
public import Obend.Spec.FrontEnd
public import Obend.Hardware.Process
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.Device.Wafer
public import Obend.Hardware.Judge
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
    (decodeRtlSynthCert (encodeRtlSynthCert flatMulAddRtlModule)).isOk = true ∧
    -- 3. `hw-retime-sta@1`: missing `lag1` is refused
    (decodeRetimeCert "{\"lag0\":0}").isOk = false ∧
    -- 4. `hw-pnr-bitstream@1`: missing `net1DstWire` is refused
    (decodePnrCert "{\"sinkCapFf\":5,\"cell1TileY\":1,\"cell0BelSlot\":0,\"cell1BelSlot\":0,\"net0DstWire\":12}").isOk = false ∧
    -- 5. `agentic-eda@1`: missing `postSwapMaxTempMilliC` is refused
    (decodeAgenticEdaCert "{\"cand2LcscPartId\":25801,\"cand2StockQty\":50000,\"cand2VdsMaxMv\":40000,\"cand2RdsOnMaxMohm\":28}").isOk = false := by
  rw [decodeRtlSynthCert_encodeRtlSynthCert_roundtrip]
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

/-! ## 4. `#tooth` Mutation Falsification Probes -/

#tooth Obend.Hardware.Compiler.substRtlInputPort0_sound by mutation
  Obend.Hardware.Compiler.substRtlInputPort0 := fun _ body => body

#tooth Obend.Hardware.Process.envelope_timing_signoff_implies_all_intermediate_corners_safe by mutation
  Obend.Hardware.Process.checkEnvelopeTimingSignoff := fun _ _ _ => true

#print axioms pipelined_callee_body_substitution_distinguishes_methods
#print axioms judge_decoders_strictly_refuse_missing_fields
#print axioms device_wafer_and_process_envelope_spine_verified

end Obend.Tests.SiliconSpineTest
end
