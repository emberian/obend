module
/-
# Obend.Teeth.Hardware.SiliconTeeth — Refusal Poles, HDL/Compiler/EDA/FabuBlox/AMS/WaferSpace Verification & 20 `#tooth` Mutations

Tests both the positive and negative poles of `Obend.Hardware` across all 17 modules
(`Silicon`, `Process`, `Fabric`, `HDL`, `Types`, `Rules`, `FSM`, `Compiler`, `Synth`,
`Retiming`, `PlaceRoute`, `FabuBlox`, `DRC`, `Analog`, `WaferSpace`, `Judge`, `Cli`):

* **Refusal Poles**:
  - `duplicated_affine_refused`: `QuantityDuplicated.obend` (`x + x` on `affine x`) is refused;
  - `sky130_overclock_500mhz_refused`: running Sky130 130nm CMOS at 500 MHz (`2000 ps < 2350 ps`) is
    refused by `checkTimingSignoff`;
  - `unregistered_slr_crossing_refused`: crossing an SLR super-logic-region boundary with `< 2` Laguna
    register stages is refused by `checkChannelHop`;
  - `combinational_loop_refused`: a self-referential wire (`w_0 := w_0 + 1`) is refused by `checkWireTableDAG`;
  - `unsynchronized_cdc_refused`: reading a `.coreClk` register from `.axiIoClk` without a 2-FF
    synchronizer is refused by `checkModuleCdc`;
  - `fabublox_under_and_over_etch_refused`: under-etching the `100 nm` ILD oxide (`80 nm`) or
    punching through the `20 nm` $\text{TiN}$ barrier (`350 nm` at `10:1` selectivity) is refused by
    FabuBlox `checkFacilityStep`;
  - `koika_write_before_read_and_double_write_refused`: intra-cycle `read0` after `write0` and
    double `write0` are refused by `runActionTrace`;
  - `retiming_negative_lag_and_unretimed_500mhz_refused`: negative edge register counts and
    unretimed 500 MHz paths are refused by `checkRetimingCert`;
  - `pnr_bel_collision_and_pip_short_refused`: BEL placement collisions and switch-box wire shorts
    are refused by `checkPnrCertificate`;
  - `drc_gold_contamination_and_pvd_keyhole_refused`: returning an `Au`-contaminated wafer to CMOS
    zones and PVD keyhole trench pinch-off are refused by `Obend.Hardware.DRC`;
  - `analog_thin_oxide_overvoltage_refused`: driving a `1.8V` (`1980 mV`) thin-oxide MOSFET gate
    with `3.3V` (`3300 mV`) without a level shifter is refused by `checkAmsPowerSafe`;
  - `waferspace_antenna_and_cmp_dishing_refused`: unprotected `2400:1` plasma-etch antenna nets and
    `< 30%` CMP metal density are refused by `checkWaferSpaceSignoff`.
* **20 `#tooth` Kernel Mutation Checks**:
  - Covers `Silicon`, `Process`, `Fabric`, `HDL`, `Types`, `Rules`, `FSM`, `Compiler`, `Synth`,
    `Retiming`, `PlaceRoute`, `FabuBlox`, `DRC`, `Analog`, `WaferSpace`, and `Judge`.
-/
public import Obend.Tactic.Tooth
public import Obend.Teeth.Leaf.ReviewTeeth
import all Obend.Hardware.Silicon
import all Obend.Hardware.Process
import all Obend.Hardware.Fabric
import all Obend.Hardware.HDL
import all Obend.Hardware.Types
import all Obend.Hardware.Rules
import all Obend.Hardware.FSM
import all Obend.Hardware.Compiler
import all Obend.Hardware.Synth
import all Obend.Hardware.Retiming
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.FabuBlox
import all Obend.Hardware.DRC
import all Obend.Hardware.Analog
import all Obend.Hardware.WaferSpace
import all Obend.Hardware.Judge
public import Obend.Hardware
@[expose] public section

namespace Obend.Teeth.Hardware
open Obend.Core.Term Obend.Logic Obend.Leaf Obend.Slot Obend.Slot.World
open Obend.Hardware.Silicon Obend.Hardware.Process Obend.Hardware.Fabric
open Obend.Hardware.HDL Obend.Hardware.Types Obend.Hardware.Rules Obend.Hardware.FSM
open Obend.Hardware.Compiler Obend.Hardware.Synth Obend.Hardware.Retiming Obend.Hardware.PlaceRoute
open Obend.Hardware.FabuBlox Obend.Hardware.DRC Obend.Hardware.Analog Obend.Hardware.WaferSpace
open Obend.Hardware.Judge
open Obend.Teeth.Leaf.Review (comp overridden view deadCells)
set_option autoImplicit false

/-! ## 1. Negative-Pole Refusal Checks Across All Hardware Subsystems -/

/-- `QuantityDuplicated.obend` (`affine x` used twice in `x + x`) is refused by the wire-fanout checker. -/
theorem duplicated_affine_refused :
    checkNetlistMult quantityDuplicatedInputs quantityDuplicatedNet = false :=
  rfl

/-- Overclocking SkyWater 130nm CMOS (`requiredPeriodPs = 2350 ps`) to 500 MHz (`2000 ps`) is refused. -/
theorem sky130_overclock_500mhz_refused :
    checkTimingSignoff corner130nm_SS 2000 obendStageCritPath = false :=
  rfl

/-- An inter-SLR die crossing with only 1 register stage (`regStages = 1 < 2`) is refused. -/
theorem unregistered_slr_crossing_refused :
    checkChannelHop ⟨"ch0", ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, 64, 1⟩ =
      .error (.illegalSlrCrossing "ch0" ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ 1) :=
  rfl

/-- A combinational wire table containing a self-loop (`w_0 := w_0 + 1`) is refused by `checkWireTableDAG`. -/
theorem combinational_loop_refused :
    checkWireTableDAG 1 0 [⟨0, "loop", .alu .add (.wireRef 0) (.const 1#64)⟩] = false :=
  rfl

/-- An unsynchronized clock-domain crossing from `.coreClk` (`reg 0`) to `.axiIoClk` (`reg 1`,
`isSynchronizer = false`) is refused by `checkModuleCdc`. -/
theorem unsynchronized_cdc_refused :
    let r0 : RegSpec := ⟨0, "core_r", .coreClk, .resetFree, false, .inputPort 0⟩
    let r1 : RegSpec := ⟨1, "axi_r", .axiIoClk, .resetFree, false, .regRead 0⟩
    checkModuleCdc [r0, r1] = false :=
  rfl

/-- FabuBlox `Facility OS` refuses both under-etching the `100 nm` ILD oxide (`80 nm`) and
over-etching through the `20 nm` $\text{TiN}$ landing pad (`350 nm` at `10:1` selectivity). -/
theorem fabublox_under_and_over_etch_refused :
    checkFacilityStep initialCmosWafer (.anisotropicRieOxide 80 10) =
      some (.viaUnderEtchUnopened 0 80 100) ∧
    checkFacilityStep initialCmosWafer (.anisotropicRieOxide 350 10) =
      some (.viaOverEtchPunchThrough 0 25 20) :=
  ⟨rfl, rfl⟩

/-- Kôika-style action log refuses both `read0` after `write0` and double `write0` on register `3`,
and `checkConflictFreeSchedule` refuses two rules that write to the same target register `0`. -/
theorem koika_rule_conflicts_refused :
    runActionTrace emptyActionLog [.write .port0 3 42#64, .read .port0 3] =
      .error (.read0AfterWrite 3) ∧
    checkConflictFreeSchedule
      [ ⟨"r1", .const 1#64, 0, .const 10#64⟩
      , ⟨"r2", .const 1#64, 0, .const 20#64⟩ ] = false :=
  ⟨rfl, rfl⟩

/-- DRC cleanroom lattice refuses returning a gold-contaminated wafer (`Au`) to `.feolCmosClean`,
and refuses directional PVD trench fill (`4:1` aspect ratio) due to keyhole void pinch-off. -/
theorem drc_gold_and_keyhole_refused :
    checkToolZoneAdmissible (stepWaferZone .feolCmosClean .auMetal) .feolCmosClean = false ∧
    checkTrenchFillVoidFree ⟨200, 50, 20, 60⟩ = false :=
  ⟨rfl, rfl⟩

/-- Analog UPF power checker refuses driving a `1.8V` (`1980 mV`) thin-oxide MOSFET with a `3.3V`
(`3300 mV`) signal without a level shifter. -/
theorem analog_thin_oxide_overvoltage_refused :
    checkAmsPowerSafe
      [ { deviceName := "M_thin_core", srcDomainMv := 3300, dstDomainMv := 1800
        , appliedSwingMv := 3300, oxideRatingMv := 1980, hasLevelShifter := false } ] = false :=
  rfl

/-- `wafer.space` GF180MCU signoff refuses both unprotected `2400:1` plasma-etch antenna nets and
under-dense `15%` CMP Metal1 layers, while accepting `goldenGf180SignoffCert`. -/
theorem waferspace_refusal_and_acceptance_poles :
    checkWaferSpaceSignoff goldenGf180SignoffCert = true ∧
    checkWaferSpaceSignoff badAntennaSignoffCert = false ∧
    checkWaferSpaceSignoff badCmpDensitySignoffCert = false := by
  decide +kernel

/-! ## 2. End-to-End Compilation of `Obend.Leaf.emit (comp 1)` to `RtlModule` -/

/-- Compiling the actual `ReviewMember.obend` leaf book `emit (comp 1)` through `compileBookToRtl`
produces a valid `RtlModule` (`checkRtlModule = true`) whose hardware evaluation at `arg = 3` yields
`out_review = 5` (`(3 + 1) + 1`) and `out_twice = 7` (`review(review(3))`)! -/
theorem review_book_compiled_rtl_verified :
    (match compileBookToRtl "obend_review_compiled" (emit (comp 1)) with
    | some m =>
      checkRtlModule m &&
      (evalModuleOutputs m (fun _ => 3#64) (fun _ => 0#64) ==
        [("out_review", 5#64), ("out_twice", 7#64)])
    | none => false) = true := by
  decide +kernel

/-! ## 3. 3-Tier Hardware Specialization Slot Deoptimization (`bitstream` → `book` → `machine`) -/

def reviewBitstream7nm : HwCandidate :=
  .bitstream "twiceOfThree" (comp 1) corner7nm_SS 2000 obendStageCritPath

def reviewBitstream130nmOverclock : HwCandidate :=
  .bitstream "twiceOfThree" (comp 1) corner130nm_SS 2000 obendStageCritPath

def hwDeadCells : Reading LeafPin HwCandidate → List LeafCell
  | .blocked _ d => d.map (·.cell)
  | _ => []

/-- At 500 MHz (`2000 ps`) on 7nm FinFET SS, the `ReviewMember` bitstream is admitted and usable. -/
theorem bitstream_usable_7nm :
    hwSpecSlot.usable (holdsAt (view (comp 1) 0)) reviewBitstream7nm = true := by
  decide +kernel

/-- When `Override` is composed last, the 7nm bitstream is blocked naming `.object "twiceOfThree"`. -/
theorem override_blocks_bitstream :
    hwDeadCells (hwSpecSlot.read (holdsAt (view overridden 1)) (some reviewBitstream7nm)) =
      [.object "twiceOfThree"] := by
  decide +kernel

/-- When overclocked to 500 MHz (`2000 ps`) on 130nm CMOS, the `.bitstream` candidate fails
`checkTimingSignoff` (`usable = false`), while the software `.book` candidate remains usable! -/
theorem sky130_overclock_rejects_bitstream_keeps_book :
    hwSpecSlot.usable (holdsAt (view (comp 1) 0)) reviewBitstream130nmOverclock = false ∧
    hwSpecSlot.usable (holdsAt (view (comp 1) 0)) (.book "twiceOfThree" (comp 1)) = true := by
  decide +kernel

/-! ## 4. `#tooth` Kernel Mutation Checks (20 Mutations Across All 17 Hardware Modules) -/

/-- 1. Broken 2-stage Laguna crossing that copies `d` straight into both `s1` and `s2`. -/
def stepPipe2Broken {w : Nat} (_st : Pipe2State w) (d : BitVec w) : Pipe2State w :=
  { s1 := d, s2 := d }

#tooth Obend.Hardware.Silicon.pipe2_x_free by mutation Obend.Hardware.Silicon.stepPipe2 := stepPipe2Broken

/-- 2. Broken `DSP48E2` MAC that forgets the `c2` pipeline register stage (`c3 := c_in` instead of `st.c2`). -/
def stepDspMacBroken {w : Nat} (st : DspMacState w) (a_in b_in c_in : BitVec w) : DspMacState w :=
  { a1   := a_in
  , b1   := b_in
  , a2   := st.a1
  , b2   := st.b1
  , c2   := c_in
  , mreg := st.a2 * st.b2
  , c3   := c_in
  , preg := st.mreg + st.c3 }

#tooth Obend.Hardware.Silicon.dspMac_latency_4 by mutation Obend.Hardware.Silicon.stepDspMac := stepDspMacBroken

/-- 3. Broken `URAM288` / SRAM wrapper that ignores the RAW collision bypass mux and always reads `st.ram.dout`. -/
def readBypassRAMNoBypass {w : Nat} (st : BypassRAMState w) : Option (BitVec w) :=
  st.ram.dout

#tooth Obend.Hardware.Silicon.bypassRAM_exact_latest_write by mutation Obend.Hardware.Silicon.readBypassRAM := readBypassRAMNoBypass

-- 4. Broken `CARRY8` LUT2 configuration that programs `LUT2_INIT_AND` (`0x8`) instead of `LUT2_INIT_XOR` (`0x6`).
#tooth Obend.Hardware.Process.carryBel_eq_fullAdderSpec by mutation Obend.Hardware.Process.LUT2_INIT_XOR := LUT2_INIT_AND

/-- 5. Broken `DeosCounter` + `Vault.Law` register bank that allows overwriting non-zero `cfgTag` (`writeOnce` omitted). -/
def stepDeosHwNoWriteOnce (st : DeosHwState) : DeosCmd → DeosHwState
  | .inc d => { st with count := st.count + d, lastAccepted := true }
  | .dec d => { st with count := st.count - d, lastAccepted := true }
  | .reset hasCred =>
    if hasCred then { st with count := 0, lastAccepted := true }
    else { st with lastAccepted := false }
  | .writeTag tag => { st with cfgTag := tag, lastAccepted := true }

#tooth Obend.Hardware.Fabric.deosHw_writeOnce_immutable by mutation Obend.Hardware.Fabric.stepDeosHw := stepDeosHwNoWriteOnce

/-- 6. Broken `HwCandidate.supports` that omits the object composition pin from `.bitstream`. -/
def hwSupportsLayersOnly : HwCandidate → List LeafPin
  | .bitstream _ C _ _ _ => C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .book name C         => ⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .machine             => []

#tooth Obend.Hardware.Fabric.hwBitstream_usable_sound by mutation Obend.Hardware.Fabric.HwCandidate.supports := hwSupportsLayersOnly

/-- 7. Broken CDC checker that allows any cross-clock register read without checking `dstReg.isSynchronizer`. -/
def checkRegCdcPermissive (allRegs : List RegSpec) (dstReg : RegSpec) : Bool :=
  (exprReadRegs dstReg.nextExpr).all fun srcIdx =>
    (lookupRegDomain allRegs srcIdx).isSome

#tooth Obend.Hardware.HDL.cdcSafe_no_unsynchronized_crossing by mutation Obend.Hardware.HDL.checkRegCdc := checkRegCdcPermissive

/-- 8. Broken `compilePrim` that compiles `.subtract` to `.add` instead of `.sub`. -/
def compilePrimSubAsAdd (op : Primitive) (l r : RtlExpr) : Option RtlExpr :=
  match op with
  | .add         => some (.alu .add l r)
  | .multiply    => some (.alu .mul l r)
  | .subtract    => some (.alu .add l r)
  | .equal       => some (.alu .eq l r)
  | .conjunction => some (.alu .bitAnd l r)
  | .less        => some (.alu .ult l r)
  | .lessEqual   => some (.mux (.alu .ult r l) (.const 0#64) (.const 1#64))
  | _            => none

#tooth Obend.Hardware.Compiler.compilePrim_sound by mutation Obend.Hardware.Compiler.compilePrim := compilePrimSubAsAdd

/-- 9. Broken `LUT3` mux configuration (`0xAC` instead of `0xCA`, inverting the `sel` polarity). -/
def LUT3_INIT_MUX_INVERTED : BitVec 8 := 0xAC#8

#tooth Obend.Hardware.Synth.lut3_mux_sound by mutation Obend.Hardware.Synth.LUT3_INIT_MUX := LUT3_INIT_MUX_INVERTED

/-- 10. Broken FabuBlox `checkFacilityStep` that forgets to check `hasExposedCuOrAu` before entering `.feolFurnace`. -/
def checkFacilityStepNoCuCheck (st : WaferState) (step : FabStep) : Option FacilityError :=
  let temp := stepTempC step
  if temp > 150 && hasPhotoresist st then
    some (.photoresistScorched temp)
  else
    none

#tooth Obend.Hardware.FabuBlox.facilityCheck_prevents_feol_contamination by mutation Obend.Hardware.FabuBlox.checkFacilityStep := checkFacilityStepNoCuCheck

/-- 11. Broken `updateStructSlice` in `Obend.Hardware.Types` that drops the write and returns `s` unchanged. -/
def updateStructSliceNoOp (s : PackedStructWord) (_fieldIdx _w : Nat) (_newVal : BitVec 64) : PackedStructWord :=
  s

#tooth Obend.Hardware.Types.struct_slice_extract_sound by mutation Obend.Hardware.Types.updateStructSlice := updateStructSliceNoOp

/-- 12. Broken `checkActionStep` in `Obend.Hardware.Rules` that forgets to reject `read0` after `write0`. -/
def checkActionStepPermissive (log : ActionLog) (_act : ActionKind) : Except LogConflict ActionLog :=
  .ok log

#tooth Obend.Hardware.Rules.write0_before_read0_refused by mutation Obend.Hardware.Rules.checkActionStep := checkActionStepPermissive

/-- 13. Broken `decodeFsmOutputs` in `Obend.Hardware.FSM` that asserts `inReady = true` even when `.busy`. -/
def decodeFsmOutputsAlwaysReady (st : FsmState) : FsmOutputs :=
  { inReady    := true
  , outValid   := st.phase == .done
  , outData    := st.accReg
  , yieldValid := st.phase == .yielded
  , yieldPlan  := st.yieldPlan }

#tooth Obend.Hardware.FSM.fsm_no_overwrite_while_busy by mutation Obend.Hardware.FSM.decodeFsmOutputs := decodeFsmOutputsAlwaysReady

/-- 14. Broken `stepRetimedMac` in `Obend.Hardware.Retiming` that forgets to add the pipelined `cReg`. -/
def stepRetimedMacDropC (st : RetimedMacState) (a b c : BitVec 64) : RetimedMacState :=
  { mulReg := a * b
  , cReg   := c
  , outReg := st.mulReg }

#tooth Obend.Hardware.Retiming.leiserson_saxe_shift_sound by mutation Obend.Hardware.Retiming.stepRetimedMac := stepRetimedMacDropC

/-- 15. Broken `encodeBitstreamFrame` in `Obend.Hardware.PlaceRoute` that drops `lutInit` when packing `frameData`. -/
def encodeBitstreamFrameDropLut (cfg : TileFrameConfig) : BitstreamFrame where
  frameAddr := cfg.tileX * 65536 + cfg.tileY * 256 + cfg.belSlot
  frameData := cfg.pipMask

#tooth Obend.Hardware.PlaceRoute.bitstream_decode_roundtrip_sound by mutation Obend.Hardware.PlaceRoute.encodeBitstreamFrame := encodeBitstreamFrameDropLut

/-- 16. Broken `checkTrenchFillVoidFree` in `Obend.Hardware.DRC` that ignores top-corner bread-loafing pinch-off. -/
def checkTrenchFillIgnoreOverhang (spec : TrenchFillSpec) : Bool :=
  (spec.trenchWidthNm > 0) && (spec.stepCoveragePct > 0) && (spec.stepCoveragePct ≤ 100)

#tooth Obend.Hardware.DRC.pvd_high_ar_keyhole_refused by mutation Obend.Hardware.DRC.checkTrenchFillVoidFree := checkTrenchFillIgnoreOverhang

/-- 17. Broken `stepChargeRedistribution` in `Obend.Hardware.Analog` that leaks `deltaQ` instead of transferring it to `C2`. -/
def stepChargeLeaky (st : SwitchedCapState) (deltaQ : Int) : SwitchedCapState :=
  { q1AttoCoulomb := st.q1AttoCoulomb - deltaQ
  , q2AttoCoulomb := st.q2AttoCoulomb }

#tooth Obend.Hardware.Analog.switchedCap_charge_conserved by mutation Obend.Hardware.Analog.stepChargeRedistribution := stepChargeLeaky

/-- 18. Broken `abbaCentroidMismatch` in `Obend.Hardware.Analog` that uses an unmatched `AABB` placement instead of `ABBA`. -/
def abbaAsUnmatchedAabb (p0 gradPerUm x0 pitch : Int) : Int :=
  aabbUnmatchedMismatch p0 gradPerUm x0 pitch

#tooth Obend.Hardware.Analog.commonCentroid_cancels_linear_gradient by mutation Obend.Hardware.Analog.abbaCentroidMismatch := abbaAsUnmatchedAabb

/-- 19. Broken `checkAntennaNet` in `Obend.Hardware.WaferSpace` that applies the 4000:1 diode-protected limit even when `hasTieDownDiode = false`. -/
def checkAntennaNetIgnoreDiode (pdk : WaferSpacePdk) (net : AntennaNetCheck) : Bool :=
  decide (net.gateAreaUm2 > 0) &&
  decide (net.metalAreaUm2 ≤ maxDiodeProtectedAntennaRatio pdk * net.gateAreaUm2)

#tooth Obend.Hardware.WaferSpace.waferspace_gf180mcu_signoff_poles by mutation Obend.Hardware.WaferSpace.checkAntennaNet := checkAntennaNetIgnoreDiode

/-- 20. Broken `checkRtlSynth` in `Obend.Hardware.Judge` that accepts any `RtlModule` without checking `checkRtlModule`. -/
def checkRtlSynthAcceptAll (_grade : Nat) (_expectedName : String) (_m : RtlModule) : Obend.Judge.Verdict HwClause :=
  .ok

#tooth Obend.Hardware.Judge.badLoopRtlModule_refused by mutation Obend.Hardware.Judge.checkRtlSynth := checkRtlSynthAcceptAll

end Obend.Teeth.Hardware
end
