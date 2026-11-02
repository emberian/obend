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
import all Obend.Hardware.Thermal
import all Obend.Hardware.Datasheet
import all Obend.Hardware.Circuits
import all Obend.Hardware.RF
import all Obend.Hardware.Physics
import all Obend.Hardware.Photonics
import all Obend.Hardware.PCB
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.DSP
import all Obend.Hardware.AgenticEDA
import all Obend.Hardware.Magnetics
import all Obend.Hardware.FluidThermal
import all Obend.Hardware.PowerElectronics
import all Obend.Hardware.Mechanics
import all Obend.Hardware.Accelerators
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Kinematics
import all Obend.Hardware.OpenUSD
import all Obend.Hardware.UserspacePhysical
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.QuantumMatter
import all Obend.Analysis.Equitable
import all Obend.Analysis.QuantumWalk
import all Obend.Hardware.Codec
import all Obend.Hardware.Judge
public import Obend.Hardware
@[expose] public section

namespace Obend.Teeth.Hardware
open Obend.Core.Term Obend.Logic Obend.Leaf Obend.Slot Obend.Slot.World
open Obend.Hardware.Silicon Obend.Hardware.Process Obend.Hardware.Fabric
open Obend.Hardware.HDL Obend.Hardware.Types Obend.Hardware.Rules Obend.Hardware.FSM
open Obend.Hardware.Compiler Obend.Hardware.Synth Obend.Hardware.Retiming Obend.Hardware.PlaceRoute
open Obend.Hardware.FabuBlox Obend.Hardware.DRC Obend.Hardware.Analog Obend.Hardware.WaferSpace
open Obend.Hardware.Thermal Obend.Hardware.Datasheet Obend.Hardware.Circuits Obend.Hardware.RF
open Obend.Hardware.Physics Obend.Hardware.Photonics Obend.Hardware.PCB
open Obend.Hardware.ReductionMachine Obend.Hardware.DSP Obend.Hardware.AgenticEDA
open Obend.Hardware.Magnetics Obend.Hardware.FluidThermal
open Obend.Hardware.PowerElectronics Obend.Hardware.Mechanics Obend.Hardware.Accelerators Obend.Hardware.GeometryCAM
open Obend.Hardware.Kinematics Obend.Hardware.OpenUSD Obend.Hardware.UserspacePhysical
open Obend.Hardware.OpenHypergraph Obend.Hardware.QuantumMatter Obend.Analysis
open Obend.Hardware.Codec Obend.Hardware.Judge
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

/-- Unballasted power BJT electro-thermal feedback ($\gamma_{\text{th}} = 1440 \ge 1000$) is refused
by `checkThermalLoopStable`, and $155^\circ\text{C}$ junction temperature trips Schmitt TSD cutoff. -/
theorem thermal_runaway_and_tsd_overtemp_refused :
    checkThermalLoopStable unballastedPowerBjt = false ∧
    checkThermalLoopStable emitterBallastedPowerBjt = true ∧
    (stepTsdProtection standardTsdSpec ⟨true, 0⟩ 155000).stageEnabled = false :=
  ⟨rfl, rfl, rfl⟩

/-- Direct `SN74LS00` TTL $\to$ `CD74HC00` CMOS interfacing ($\text{NM}_H = -800\,\text{mV}$) and
uncalibrated model drift ($\varepsilon_\infty = 620\,\text{mV} > 25\,\text{mV}$) are refused. -/
theorem datasheet_ttl_to_hc_and_drift_refused :
    checkLogicInterface sn74ls00Datasheet.logic cd74hc00Datasheet.logic 0 400 = false ∧
    checkModelCalibration uncalibratedDrifted74ls00Preds sn74ls00Datasheet.transferCurve 25 = false ∧
    checkDatasheetFitSignoff goldenDatasheetFitCert = true ∧
    checkDatasheetFitSignoff badDirect74HcFitCert = false ∧
    checkDatasheetFitSignoff badUncalibratedDriftFitCert = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `SN74LS00` fanout overload (`25 > 10`) and synchronous Buck inductor saturation (`3691 mA > 3500 mA`)
are refused by `checkTtlFanout` and `checkBuckCcmSafe`. -/
theorem circuits_fanout_and_buck_saturation_refused :
    checkTtlFanout sn74ls00TotemParams 25 = false ∧
    checkBuckCcmSafe overloadedSaturatingBuckSpec = false :=
  ⟨rfl, rfl⟩

/-- Unmatched $300\,\Omega$ twin-lead on $50\,\Omega$ coax ($\text{VSWR} = 6:1$) and unfiltered Class-E
PA harmonics ($-18\,\text{dBc}$ vs $-43\,\text{dBc}$ FCC Part 97.307 limit) are refused. -/
theorem rf_vswr_and_unfiltered_pa_harmonics_refused :
    checkVswrUnder2To1 50 ⟨300, 0⟩ = false ∧
    checkFccPart97Harmonics unfilteredClassEPaSpec = false ∧
    checkRfTransceiverSignoff golden40mFt8TransceiverCert = true ∧
    checkRfTransceiverSignoff unfilteredPaTransceiverCert = false ∧
    checkRfTransceiverSignoff highVswrTransceiverCert = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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

/-- 21. Broken `evalBandgapRef` in `Obend.Hardware.Thermal` that subtracts the PTAT term instead of adding it (`-2 * alphaCtat * deltaT` drift instead of `0` drift!). -/
def evalBandgapRefInvertPtat (vbg0 alphaCtat alphaPtat weightK _temp deltaT : Int) : Int :=
  (vbg0 - alphaCtat * deltaT) - weightK * (alphaPtat * deltaT)

#tooth Obend.Hardware.Thermal.bandgap_zero_tempco_cancellation by mutation Obend.Hardware.Thermal.evalBandgapRef := evalBandgapRefInvertPtat

/-- 22. Broken `checkLogicInterface` in `Obend.Hardware.Datasheet` that forgets to verify `noiseMarginHigh` (allowing `74LS` $\to$ `74HC` direct negative margin). -/
def checkLogicInterfaceIgnoreHigh (drv rcv : LogicFamilySpec) (_pullupBoostMv minMarginMv : Int) : Bool :=
  decide (minMarginMv ≤ noiseMarginLow drv rcv) &&
  decide (drv.volMaxMv < rcv.vihMinMv)

#tooth Obend.Hardware.Datasheet.checkLogicInterface_guarantees_valid_thresholds by mutation Obend.Hardware.Datasheet.checkLogicInterface := checkLogicInterfaceIgnoreHigh

/-- 23. Broken `evalInaOutputUv` in `Obend.Hardware.Circuits` that forgets to apply `trimCmCancel` (leaking 60 Hz common-mode hum into the output). -/
def evalInaOutputUvNoTrim (p : InaParams) (vDiffUv vCmUv deltaTC : Int) : Int :=
  p.gainDiff * (vDiffUv + p.vos0Uv + p.dVosDtUvPerC * deltaTC) +
  p.gainCmRaw * vCmUv

#tooth Obend.Hardware.Circuits.ina_common_mode_cancelled_at_matched_bridge by mutation Obend.Hardware.Circuits.evalInaOutputUv := evalInaOutputUvNoTrim

/-- 24. Broken `gammaMagSqNum` in `Obend.Hardware.RF` that uses `zL.rOhm + z0` instead of `zL.rOhm - z0`. -/
def gammaMagSqNumAddInsteadOfSub (z0 : Int) (zL : Impedance) : Int :=
  (zL.rOhm + z0) * (zL.rOhm + z0) + zL.xOhm * zL.xOhm

#tooth Obend.Hardware.RF.conjugate_match_zero_reflection by mutation Obend.Hardware.RF.gammaMagSqNum := gammaMagSqNumAddInsteadOfSub

/-- 25. Broken `evalQuadratureImagePhaseCancel` in `Obend.Hardware.RF` that adds `gainI + gainQ` instead of subtracting `gainI - gainQ` (failing to reject the image sideband). -/
def evalQuadratureImageSumInsteadOfDiff (gainI gainQ phaseErr sigAmp : Int) : Int :=
  (gainI + gainQ) * sigAmp + phaseErr * sigAmp

#tooth Obend.Hardware.RF.tayloe_iq_cancels_image_sideband by mutation Obend.Hardware.RF.evalQuadratureImagePhaseCancel := evalQuadratureImageSumInsteadOfDiff

/-- 26. Broken `prouhetThueMorseMismatch1D` in `Obend.Hardware.Analog` that falls back to 4-cell `ABBA` (leaving a non-zero $4 c_{xx} d^2$ quadratic oxide bow residual instead of `0`). -/
def ptm8BrokenAsAbba4 (p0 gx cxx pitch : Int) : Int :=
  abbaQuadraticMismatch1D p0 gx cxx pitch

#tooth Obend.Hardware.Analog.prouhetThueMorse_cancels_linear_and_quadratic_bow by mutation Obend.Hardware.Analog.prouhetThueMorseMismatch1D := ptm8BrokenAsAbba4

/-- 27. Broken `evalCellContinuityRate` in `Obend.Hardware.Physics` that adds `cell.fluxOut` instead of subtracting it (violating finite-volume Scharfetter-Gummel flux conservation). -/
def evalCellContinuityAddFluxOut (cell : PddControlVolume) : Int :=
  cell.fluxIn + cell.fluxOut - cell.recombRate

#tooth Obend.Hardware.Physics.pdd_total_charge_conserved by mutation Obend.Hardware.Physics.evalCellContinuityRate := evalCellContinuityAddFluxOut

/-- 28. Broken `evalCouplerOut1Power` in `Obend.Hardware.Photonics` that drops the cross-coupled `dc.kappaSqPpm * pIn2Uw` term (violating CMT $2 \times 2$ coupler unitarity). -/
def evalCouplerOut1DropCross (dc : DirectionalCoupler) (pIn1Uw _pIn2Uw : Int) : Int :=
  dc.tSqPpm * pIn1Uw

#tooth Obend.Hardware.Photonics.directionalCoupler_conserves_optical_power by mutation Obend.Hardware.Photonics.evalCouplerOut1Power := evalCouplerOut1DropCross

/-- 29. Broken `evalOddModeZ0MilliOhm` in `Obend.Hardware.PCB` that adds `dp.couplingPermille` instead of subtracting it (confusing even-mode $Z_{0e}$ with odd-mode $Z_{0o}$). -/
def evalOddModeAsEvenMode (dp : DiffPairSpec) : Nat :=
  (dp.z0MilliOhm * (1000 + dp.couplingPermille)) / 1000

#tooth Obend.Hardware.PCB.diffImpedance_monotone_uncoupled by mutation Obend.Hardware.PCB.evalOddModeZ0MilliOhm := evalOddModeAsEvenMode

/-- 30. Broken `dprPhase2LoadFrame` in `Obend.Hardware.ReductionMachine` that loads `frame.newTile` without checking `frame.computedDigest == frame.expectedDigest` (allowing corrupt bitstreams onto the eFPGA). -/
def dprPhase2IgnoreCrc (frame : IcapBitstreamFrame) (t : ReconfigTileState) : ReconfigTileState :=
  if t.tileId == frame.targetTileId then
    { t with activeTile := frame.newTile, frameDigest := frame.computedDigest }
  else
    t

#tooth Obend.Hardware.ReductionMachine.dpr_corrupt_crc_keeps_tile_isolated by mutation Obend.Hardware.ReductionMachine.dprPhase2LoadFrame := dprPhase2IgnoreCrc

/-- 31. Broken `checkRollettUnconditionalStability` in `Obend.Hardware.DSP` that omits the $K > 1$ (`evalRollettDenominator sp < evalRollettNumerator sp`) check (admitting potentially oscillating LNAs). -/
def checkRollettIgnoreK (sp : TwoPortSParams) : Bool :=
  decide (0 ≤ sp.s11MagSqPermilleSq ∧ sp.s11MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.s22MagSqPermilleSq ∧ sp.s22MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.deltaMagSqPermilleSq ∧ sp.deltaMagSqPermilleSq < 1000000) &&
  decide (0 < evalRollettDenominator sp)

#tooth Obend.Hardware.DSP.rollettStability_sound by mutation Obend.Hardware.DSP.checkRollettUnconditionalStability := checkRollettIgnoreK

/-- 32. Broken `checkDatasheetCiteFresh` in `Obend.Hardware.AgenticEDA` that checks only `0 < cite.currentDatasheetHash` and ignores `cite.pinnedBlockHash = cite.currentDatasheetHash`. -/
def checkDatasheetCiteIgnoreHash (cite : DatasheetCitePin) : Bool :=
  decide (0 < cite.currentDatasheetHash)

#tooth Obend.Hardware.AgenticEDA.staleDatasheetCite_refused by mutation Obend.Hardware.AgenticEDA.checkDatasheetCiteFresh := checkDatasheetCiteIgnoreHash

/-- 33. Broken `encodeBinaryHwCert` in `Obend.Hardware.Codec` that emits wrong CBOR tag byte `0xEE` instead of `0xED`. -/
def encodeBinaryHwCertBadTag (c : BinaryHwCert) : List UInt8 :=
  (0xD9 : UInt8) :: (0x0B : UInt8) :: (0xEE : UInt8) :: (0x87 : UInt8) ::
    (cborEncodeU32 c.domain.toCode ++
      (cborEncodeI32 c.p0 ++
        (cborEncodeI32 c.p1 ++
          (cborEncodeI32 c.p2 ++
            (cborEncodeI32 c.p3 ++
              (cborEncodeI32 c.p4 ++ cborEncodeI32 c.p5))))))

#tooth Obend.Hardware.Codec.decode_encode_binaryHwCert by mutation Obend.Hardware.Codec.encodeBinaryHwCert := encodeBinaryHwCertBadTag

/-- 34. Broken `FemmTriangle2D.b0` in `Obend.Hardware.Magnetics` that adds `tri.y1 + tri.y2` instead of subtracting `tri.y1 - tri.y2` (violating 2D FEMM vector-potential gauge invariance). -/
def femmB0AddInsteadOfSub (tri : FemmTriangle2D) : Int :=
  tri.y1 + tri.y2

#tooth Obend.Hardware.Magnetics.femm_gauge_invariance by mutation Obend.Hardware.Magnetics.FemmTriangle2D.b0 := femmB0AddInsteadOfSub

/-- 35. Broken `evalIpmTorqueScaled` in `Obend.Hardware.Magnetics` that subtracts `(ld - lq) * id * iq` instead of adding it (reversing the IPM reluctance torque sign). -/
def evalIpmTorqueInvertReluctance (m : IpmMotorSpec) (idAmp iqAmp : Int) : Int :=
  m.polePairs * (m.psiPmMilliWb * iqAmp - (m.ldMicroH - m.lqMicroH) * idAmp * iqAmp)

#tooth Obend.Hardware.Magnetics.ipm_reluctance_torque_boost by mutation Obend.Hardware.Magnetics.evalIpmTorqueScaled := evalIpmTorqueInvertReluctance

/-- 36. Broken `evalPeakWindingTempMilliC` in `Obend.Hardware.FluidThermal` that subtracts `rCaloricMilliKPerW` instead of adding it (violating series thermal resistance monotonicity). -/
def evalPeakWindingTempSubCaloric (tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rCondMilliKPerW : Int) : Int :=
  tInletMilliC + powerLossW * (-rCaloricMilliKPerW + rConvMilliKPerW + rCondMilliKPerW)

#tooth Obend.Hardware.FluidThermal.higher_flow_and_convection_lowers_winding_temp by mutation Obend.Hardware.FluidThermal.evalPeakWindingTempMilliC := evalPeakWindingTempSubCaloric

/-- 37. Broken `evalSourceCurrent` in `Obend.Hardware.PowerElectronics` that adds `gs * v` instead of subtracting `gs * v` (destroying MPPT concavity and global maximum). -/
def evalSourceCurrentPositiveSlope (isc gs v : Int) : Int :=
  isc + gs * v

#tooth Obend.Hardware.PowerElectronics.mppt_incremental_conductance_global_max by mutation Obend.Hardware.PowerElectronics.evalSourceCurrent := evalSourceCurrentPositiveSlope

/-- 38. Broken `evalDroopFrequencyMilliHz` in `Obend.Hardware.PowerElectronics` that ignores the droop slope `droopGainMilliHzPerKw` (destroying autonomous proportional power sharing). -/
def evalDroopFrequencyNoDroop (omegaNomMilliHz _droopGainMilliHzPerKw activePowerKw : Int) : Int :=
  omegaNomMilliHz - activePowerKw

#tooth Obend.Hardware.PowerElectronics.distributed_droop_proportional_power_sharing by mutation Obend.Hardware.PowerElectronics.evalDroopFrequencyMilliHz := evalDroopFrequencyNoDroop

/-- 39. Broken `evalHotAirGapUm` in `Obend.Hardware.Mechanics` that adds `thermalGrowthUm` instead of subtracting it (claiming rotor heating widens the air gap instead of shrinking it). -/
def evalHotAirGapAddThermal (coldAirGapUm thermalGrowthUm centrifugalGrowthUm bearingRunoutUm : Int) : Int :=
  coldAirGapUm + thermalGrowthUm - (centrifugalGrowthUm + bearingRunoutUm)

#tooth Obend.Hardware.Mechanics.hot_air_gap_no_rub_sound by mutation Obend.Hardware.Mechanics.evalHotAirGapUm := evalHotAirGapAddThermal

/-- 40. Broken `checkReflexiveSelfClosure` in `Obend.Hardware.Mechanics` that skips checking `cells.all (checkCellSelfCovered cells)` (admitting non-self-reproducing open-loop factories). -/
def checkReflexiveSelfClosureIgnoreBom (cells : List FactoryCell) : Bool :=
  !cells.isEmpty && decide (0 ≤ evalNetFactoryPowerKw cells)

#tooth Obend.Hardware.Mechanics.von_neumann_reflexive_closure_sound by mutation Obend.Hardware.Mechanics.checkReflexiveSelfClosure := checkReflexiveSelfClosureIgnoreBom

/-- 41. Broken `evalOzakiBase13Product2` in `Obend.Hardware.Accelerators` that drops the cross-limb Tensor-Core products `a0 * b1 + a1 * b0`. -/
def evalOzakiBase13DropCross (a0 a1 b0 b1 : Int) : Int :=
  a0 * b0 + 169 * (a1 * b1)

#tooth Obend.Hardware.Accelerators.ozaki_base13_2limb_product_exact by mutation Obend.Hardware.Accelerators.evalOzakiBase13Product2 := evalOzakiBase13DropCross

/-- 42. Broken `stepSystolicPe` in `Obend.Hardware.Accelerators` that overwrites `partialSumIn` instead of accumulating `partialSumIn + act * weight`. -/
def stepSystolicPeNoAccum (_partialSumIn act weight : Int) : Int :=
  act * weight

#tooth Obend.Hardware.Accelerators.systolic_tpu_eq_dsp58_cascade_eq_kulisch_dot by mutation Obend.Hardware.Accelerators.stepSystolicPe := stepSystolicPeNoAccum

/-- 43. Broken `ivSub` in `Obend.Hardware.GeometryCAM` that subtracts `b.lo` from `a.lo` instead of `b.hi` (violating 3D F-Rep interval enclosure and causing octree pruning to miss thin walls). -/
def ivSubBrokenEndpoints (a b : FloatInterval) : FloatInterval where
  lo := a.lo - b.lo
  hi := a.hi - b.hi

#tooth Obend.Hardware.GeometryCAM.frep_interval_enclosure_sound by mutation Obend.Hardware.GeometryCAM.ivSub := ivSubBrokenEndpoints

/-- 44. Broken `evalActualCutterPosNm` in `Obend.Hardware.GeometryCAM` that ignores end-mill cantilever deflection `toolComplianceNmPerMn * radialForceMn` (pretending the cutter is infinitely rigid). -/
def evalActualCutterIgnoreDeflection (xCmdNm feedVelMmPerS servoLagNsPerMm _toolComplianceNmPerMn _radialForceMn : Int) : Int :=
  xCmdNm - feedVelMmPerS * servoLagNsPerMm

#tooth Obend.Hardware.GeometryCAM.machining_dimensional_error_identity by mutation Obend.Hardware.GeometryCAM.evalActualCutterPosNm := evalActualCutterIgnoreDeflection

/-- 45. Broken `insertPrimByStrength` in `Obend.Hardware.OpenUSD` that appends `p` after `q` instead of placing stronger/local `PrimSpec`s at the head (inverting OpenUSD `LIVERPS` composition strength). -/
def insertPrimByStrengthBroken (p : PrimSpec) : List PrimSpec → List PrimSpec
  | [] => [p]
  | q :: rest => q :: insertPrimByStrengthBroken p rest

#tooth Obend.Hardware.OpenUSD.insertPrimByStrength_localArc_head by mutation Obend.Hardware.OpenUSD.insertPrimByStrength := insertPrimByStrengthBroken

/-- 46. Broken `spatialPower` in `Obend.Hardware.Kinematics` that subtracts the linear power `dot3 f.force v.lin` instead of adding it (breaking Featherstone spatial adjoint-coadjoint duality and D'Alembert virtual work). -/
def spatialPowerBrokenLinear (f : SpatialWrench6D) (v : SpatialTwist6D) : Int :=
  dot3 f.torque v.ang - dot3 f.force v.lin

#tooth Obend.Hardware.Kinematics.featherstone_spatial_adjoint_duality by mutation Obend.Hardware.Kinematics.spatialPower := spatialPowerBrokenLinear

/-- 47. Broken `AffineForm1D.toInterval` in `Obend.Hardware.OpenUSD` that forgets to negate `radius` on the lower bound (collapsing the affine interval enclosure to a degenerate point and missing CSG surfaces). -/
def affineToIntervalCollapsed (af : AffineForm1D) : FloatInterval where
  lo := af.c0 + af.radius
  hi := af.c0 + af.radius

#tooth Obend.Hardware.OpenUSD.affine_to_interval_encloses_eval by mutation Obend.Hardware.OpenUSD.AffineForm1D.toInterval := affineToIntervalCollapsed

/-- 48. Broken `lcDrivesInSlotUpgradeLayer` in `Obend.Hardware.UserspacePhysical` that keeps outer-jacket `thermalResistance = 29` instead of `9` (breaking `.obend` userspace `LcDrivesStatorUsd.obend` -> `Leaf.Book` -> FPGA RTL lowering). -/
def lcDrivesInSlotUpgradeBrokenLayer : Layer where
  name := "LcDrivesStatorUsd.LcDrivesInSlotUpgrade"
  metadata := .label "LcDrivesStatorUsd.LcDrivesInSlotUpgrade"
  fields :=
    [ ("thermalResistance", .nat 29)
    , ("sdfMargin",
        .lam (.binary .add (.app (.get (.bound 1) "sdfMargin") (.bound 0)) (.nat 6)))
    ]

#tooth Obend.Hardware.UserspacePhysical.userspace_physical_stator_to_fpga_verified by mutation Obend.Hardware.UserspacePhysical.lcDrivesInSlotUpgradeLayer := lcDrivesInSlotUpgradeBrokenLayer

/-- 49. Broken `compileOpticAdjoint` in `Obend.Hardware.OpenHypergraph` that maps every `OpticOp` to `.add` (breaking `catgrad` reverse-mode AD cotangent soundness for `.sub` and `.mul`). -/
def compileOpticAdjointAlwaysAdd (_op : OpticOp) : OpticAdjoint :=
  { op := .add, numResidualWires := 0, usesInputResiduals := false }

#tooth Obend.Hardware.OpenHypergraph.optic_reverse_ad_sound by mutation Obend.Hardware.OpenHypergraph.compileOpticAdjoint := compileOpticAdjointAlwaysAdd

/-- 50. Broken `stepCalyxSeqFsm` in `Obend.Hardware.Compiler` that fails to increment `activeGroupIdx` when a Calyx group completes (`done`), deadlocking the sequential schedule. -/
def stepCalyxSeqFsmStuckGroup
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64)
    (st : CalyxSeqFsmState) : CalyxSeqFsmState :=
  match groups[st.activeGroupIdx]? with
  | none =>
    { st with goSignal := false, doneSignal := true }
  | some g =>
    if st.cycleInGroup + 1 < g.latencyCycles then
      { st with cycleInGroup := st.cycleInGroup + 1, goSignal := true, doneSignal := false }
    else
      let v := evalRtlExpr inputs wires st.regState g.datapathExpr
      { activeGroupIdx := st.activeGroupIdx
        cycleInGroup   := 0
        goSignal       := true
        doneSignal     := false
        regState       := fun r => if r == g.targetRegIdx then v else st.regState r }

#tooth Obend.Hardware.Compiler.calyx_group_go_done_handshake_sound by mutation Obend.Hardware.Compiler.stepCalyxSeqFsm := stepCalyxSeqFsmStuckGroup

/-- 51. Broken `resolveTwoWireSplices` in `Obend.Hardware.ReductionMachine` that drops newly formed active pairs instead of returning them to `activeQueue` (breaking multi-cycle cascading Interaction-Net reduction). -/
def resolveTwoWireSplicesDropPairs (arena : List INetNode) (_w1 _w2 : PortRef × PortRef) : List INetNode × List ActivePair :=
  (arena, [])

#tooth Obend.Hardware.ReductionMachine.inet_dynamic_splice_cascading_reduction by mutation Obend.Hardware.ReductionMachine.resolveTwoWireSplices := resolveTwoWireSplicesDropPairs

/-- 52. Broken `ivMinChoice` in `Obend.Hardware.GeometryCAM` that returns `.right` when `a.hi ≤ b.lo` instead of `.left` (inverting `fidget` CSG union branch pruning). -/
def ivMinChoiceInverted (a b : FloatInterval) : FidgetChoice :=
  if decide (a.hi ≤ b.lo) then .right
  else if decide (b.hi ≤ a.lo) then .left
  else .both

#tooth Obend.Hardware.GeometryCAM.pruneFRepTape_sound by mutation Obend.Hardware.GeometryCAM.ivMinChoice := ivMinChoiceInverted

/-- 53. Broken `AffineForm3D.toInterval` in `Obend.Hardware.OpenUSD` that adds `af.radius` on `lo` instead of subtracting it (collapsing 3D affine SDF enclosures). -/
def affine3dToIntervalCollapsed (af : AffineForm3D) : FloatInterval where
  lo := af.c0 + af.radius
  hi := af.c0 + af.radius

#tooth Obend.Hardware.OpenUSD.affine3d_to_interval_encloses_eval by mutation Obend.Hardware.OpenUSD.AffineForm3D.toInterval := affine3dToIntervalCollapsed

/-- 54. Broken `evalRuckigProfile7` in `Obend.Hardware.Kinematics` that applies `+jMax` instead of `-jMax` in Phase 3 (violating rest-to-rest zero final velocity and acceleration). -/
def evalRuckigProfile7BrokenPhase3
    (st0 : RuckigState1D) (jMax : Int) (t1 t2 t3 t4 t5 t6 t7 : Int)
    (_signs : RuckigControlSigns) : RuckigState1D :=
  let st1 := stepRuckigSegment st0 jMax t1
  let st2 := stepRuckigSegment st1 0 t2
  let st3 := stepRuckigSegment st2 jMax t3
  let st4 := stepRuckigSegment st3 0 t4
  let st5 := stepRuckigSegment st4 (-jMax) t5
  let st6 := stepRuckigSegment st5 0 t6
  stepRuckigSegment st6 jMax t7

#tooth Obend.Hardware.Kinematics.ruckig_7phase_symmetric_rest_to_rest_identity by mutation Obend.Hardware.Kinematics.evalRuckigProfile7 := evalRuckigProfile7BrokenPhase3

/-- 55. Broken `stepElectroThermalTemp` in `Obend.Hardware.FluidThermal` that subtracts `(pBase + slopeBeta * (tCur - tInlet)) * rTh` instead of adding it (breaking the electro-thermal contraction identity). -/
def stepElectroThermalTempSubLoss (tInlet pBase slopeBeta rTh tCur : Int) : Int :=
  tInlet - (pBase + slopeBeta * (tCur - tInlet)) * rTh

#tooth Obend.Hardware.FluidThermal.electro_thermal_contraction_identity by mutation Obend.Hardware.FluidThermal.stepElectroThermalTemp := stepElectroThermalTempSubLoss

/-- 56. Broken `cborDecodeU32List` in `Obend.Hardware.Codec` that drops the decoded head element `x` instead of prepending `x :: xs` (breaking variable-length RFC 8949 CBOR tape round-trip). -/
def cborDecodeU32ListDropHead : Nat → List UInt8 → Option (List UInt32 × List UInt8)
  | 0, bytes => some ([], bytes)
  | k + 1, bytes =>
    match cborDecodeU32Word bytes with
    | some (_x, rest1) =>
      match cborDecodeU32ListDropHead k rest1 with
      | some (xs, rest2) => some (xs, rest2)
      | none => none
    | none => none

#tooth Obend.Hardware.Codec.cborDecodeU32List_encode_exact by mutation Obend.Hardware.Codec.cborDecodeU32List := cborDecodeU32ListDropHead

/-- 57. Broken `cellRowSum` in `Obend.Analysis.Equitable` that returns `0` instead of summing `H u v` over `cellJ` (breaking the equitable partition handshake identity $|C_i| Q_{i,j} = |C_j| Q_{j,i}$). -/
def cellRowSumZero (_H : Nat → Nat → Int) (_cellJ : List Nat) (_u : Nat) : Int := 0

#tooth Obend.Analysis.equitable_handshake_identity by mutation Obend.Analysis.cellRowSum := cellRowSumZero

/-- 58. Broken `evalPhotonicArray4LayerEven` in `Obend.Hardware.QuantumMatter` that duplicates `c01.1` on waveguide 1 instead of routing `c01.2` (violating 4-waveguide CMT unitary power conservation). -/
def evalPhotonicArray4LayerEvenDuplicatePort
    (t01 k01 t23 k23 : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let c01 := evalDirectionalCoupler2x2 t01 k01 e0 e1
  let c23 := evalDirectionalCoupler2x2 t23 k23 e2 e3
  (c01.1, c01.1, c23.1, c23.2)

#tooth Obend.Hardware.QuantumMatter.photonic_ctqw_array_power_conserved by mutation Obend.Hardware.QuantumMatter.evalPhotonicArray4LayerEven := evalPhotonicArray4LayerEvenDuplicatePort

end Obend.Teeth.Hardware
end
