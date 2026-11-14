module
/-
# Obend.Teeth.Hardware.SiliconTeeth — Refusal Poles, HDL/Compiler/EDA/AMS Verification & `#tooth` Mutations

Tests both the positive and negative poles of `Obend.Hardware` across surviving hardware & physical
modules (`Silicon`, `Process`, `HDL`, `Types`, `Compiler`, `Synth`,
`Retiming`, `PlaceRoute`, `DRC`, `Analog`, `Datasheet`, `Circuits`, `Device.Wafer`, `Photonics`,
`PCB`, `ReductionMachine`, `DSP`, `AgenticEDA`, `Magnetics`, `CurrentLoop`, `ThermalPassivity`,
`Accelerators`, `GeometryCAM`, `Kinematics`, `OpenUSD`, `OpenHypergraph`,
`QuantumMatter`, `Codec`, `Judge`, and `Apps.SiliconKernelVerilator`).
-/
public import Obend.Tactic.Tooth
public import Obend.Teeth.Leaf.ReviewTeeth
public import Obend.Apps.SiliconKernelVerilator
import all Obend.Apps.SiliconKernelVerilator
import all Obend.Lower.Inductive
import all Obend.Lower.LeanKernel
import all Obend.Lower.ExprCAM
import all Obend.Lower.DiscrTreeLUT
import all Obend.Lower.SiliconElabFabric
import all Obend.Hardware.Silicon
import all Obend.Hardware.Process
import all Obend.Hardware.NotebookProjection
import all Obend.Hardware.HDL
import all Obend.Hardware.Types
import all Obend.Hardware.Compiler
import all Obend.Hardware.Synth
import all Obend.Hardware.Retiming
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.DRC
import all Obend.Hardware.Analog
import all Obend.Hardware.Datasheet
import all Obend.Hardware.Circuits
import all Obend.Hardware.Device.Sky130Diode
import all Obend.Hardware.Device.Wafer
import all Obend.Hardware.Photonics
import all Obend.Hardware.PCB
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.DSP
import all Obend.Hardware.AgenticEDA
import all Obend.Hardware.Magnetics
import all Obend.Hardware.CurrentLoop
import all Obend.Hardware.ThermalPassivity
import all Obend.Hardware.Accelerators
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Kinematics
import all Obend.Hardware.OpenUSD
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.QuantumMatter
import all Obend.Analysis.Equitable
import all Obend.Analysis.QuantumWalk
import all Obend.Hardware.Codec
import all Obend.Hardware.Judge

namespace Obend.Teeth.Hardware
open Obend.Core.Term Obend.Logic Obend.Leaf Obend.Slot Obend.Slot.World
open Obend.Hardware.Silicon Obend.Hardware.Process
open Obend.Hardware.HDL Obend.Hardware.Types
open Obend.Hardware.Compiler Obend.Hardware.Synth Obend.Hardware.Retiming Obend.Hardware.PlaceRoute
open Obend.Hardware.DRC Obend.Hardware.Analog
open Obend.Hardware.Datasheet Obend.Hardware.Circuits
open Obend.Hardware.Photonics Obend.Hardware.PCB
open Obend.Hardware.ReductionMachine Obend.Hardware.DSP Obend.Hardware.AgenticEDA
open Obend.Hardware.Magnetics Obend.Hardware.CurrentLoop Obend.Hardware.ThermalPassivity
open Obend.Hardware.Accelerators Obend.Hardware.GeometryCAM
open Obend.Hardware.Kinematics Obend.Hardware.OpenUSD
open Obend.Hardware.OpenHypergraph Obend.Hardware.QuantumMatter Obend.Analysis
open Obend.Hardware.Codec Obend.Hardware.Judge
open Obend.Teeth.Leaf.Review (comp overridden view deadCells)
set_option autoImplicit false

private def erasedRouteFrameBytes (_ : PnrCertificate) : List UInt8 := []

#tooth Obend.Vault.HardwareProjection.pnrRouteFrameDigest_binding by mutation
  Obend.Vault.HardwareProjection.pnrRouteFrameBytes := erasedRouteFrameBytes


#tooth Obend.Hardware.Device.sky130Diode_full_recipe_inhabited by mutation
  Obend.Hardware.Device.sky130DiodeRecipe := fun pWellDose _ => [.implant .boron 160 pWellDose]

/-! ## 1. Negative-Pole Refusal Checks Across All Hardware Subsystems -/

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
    checkWireTableDAG 1 0 [{ wireIdx := 0, name := "loop", expr := .alu .add (.wireRef 0) (.const 1#64) }] = false :=
  rfl

/-- An unsynchronized clock-domain crossing from `.coreClk` (`reg 0`) to `.axiIoClk` (`reg 1`,
`isSynchronizer = false`) is refused by `checkModuleCdc`. -/
theorem unsynchronized_cdc_refused :
    let r0 : RegSpec := { regIdx := 0, name := "core_r", domain := .coreClk, resetKind := .resetFree, isSynchronizer := false, nextExpr := .inputPort 0 }
    let r1 : RegSpec := { regIdx := 1, name := "axi_r", domain := .axiIoClk, resetKind := .resetFree, isSynchronizer := false, nextExpr := .regRead 0 }
    checkModuleCdc [r0, r1] = false :=
  rfl

/-- Retiming negative edge register counts and unretimed 500 MHz critical paths are refused. -/
theorem retiming_negative_lag_and_unretimed_500mhz_refused :
    checkRetimingCert macUnretimedGraph negativeWeightBadCert corner7nm_SS 2000 = false ∧
    checkRetimingCert macUnretimedGraph identityRetimingCert corner7nm_SS 2000 = false := by
  decide +kernel

/-- Netlist-bound PnR checker refuses BEL placement collisions, PIP routing shorts, and BEL cell-count mismatches. -/
theorem pnr_bel_collision_and_pip_short_refused :
    checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 collidingBelPnrCert = false ∧
    checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 shortedWirePnrCert = false ∧
    checkPnrCertificate { validAdderBelNetlist with cells := [] } corner7nm_SS 2000 validAdderPnrCert = false :=
  ⟨rfl, rfl, rfl⟩

/-- DRC cleanroom lattice refuses returning a gold-contaminated wafer (`Au`) to `.feolCmosClean`,
and refuses directional PVD trench fill (`4:1` aspect ratio) due to keyhole void pinch-off. -/
example :
    checkToolZoneAdmissible (stepWaferZone .feolCmosClean .auMetal) .feolCmosClean = false ∧
    checkTrenchFillVoidFree ⟨200, 50, 20, 60⟩ = false :=
  ⟨rfl, rfl⟩

/-- Direct `SN74LS00` TTL $\to$ `CD74HC00` CMOS interfacing ($\text{NM}_H = -800\,\text{mV}$) and
uncalibrated model drift ($\varepsilon_\infty = 620\,\text{mV} > 25\,\text{mV}$) are refused. -/
example :
    checkLogicInterface sn74ls00Datasheet.logic cd74hc00Datasheet.logic 0 400 = false ∧
    checkModelCalibration uncalibratedDrifted74ls00Preds sn74ls00Datasheet.transferCurve 25 = false ∧
    checkDatasheetFitSignoff goldenDatasheetFitCert = true ∧
    checkDatasheetFitSignoff badDirect74HcFitCert = false ∧
    checkDatasheetFitSignoff badUncalibratedDriftFitCert = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `SN74LS00` fanout overload (`25 > 10`), synchronous Buck inductor saturation (`3691 mA > 3500 mA`),
and unstable feedback LNA ($K < 1$) are refused. -/
example :
    checkTtlFanout sn74ls00TotemParams 25 = false ∧
    checkBuckCcmSafe overloadedSaturatingBuckSpec = false ∧
    checkRollettUnconditionalStability unstableFeedbackLnaSParams = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## 2. End-to-End Compilation of `Obend.Leaf.emit (comp 1)` to `RtlModule` -/

/-- Compiling the actual `ReviewMember.obend` leaf book `emit (comp 1)` through `compileBookToRtl`
produces a valid `RtlModule` (`checkRtlModule = true`) whose hardware evaluation at `arg = 3` yields
`out_review = 5` (`(3 + 1) + 1`) and `out_twice = 7` (`review(review(3))`)! -/
example :
    (match compileBookToRtl "obend_review_compiled" (emit (comp 1)) with
    | some m =>
      checkRtlModule m &&
      (evalModuleOutputs m (fun _ => 3#64) (fun _ => 0#64) ==
        [("out_review", 5#64), ("out_twice", 7#64)])
    | none => false) = true := by
  decide +kernel

/-! ## 4. `#tooth` Kernel Mutation Checks Across Surviving & Repaired Hardware Modules -/

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

/-- 10. Broken barrel-shift routing BEL evaluator (`evalShiftRoute`) that ignores shift distance and returns `a` unchanged. -/
def evalShiftRouteNoOp (_dir : ShiftDir) (_dist : Nat) (a : BitVec 64) : BitVec 64 := a

#tooth Obend.Hardware.Synth.synthesizeModuleToBels_trace_equiv by mutation Obend.Hardware.Synth.evalShiftRoute := evalShiftRouteNoOp

/-- 11. Broken `updateStructSlice` in `Obend.Hardware.Types` that drops the write and returns `s` unchanged. -/
def updateStructSliceNoOp (s : PackedStructWord) (_fieldIdx _w : Nat) (_newVal : BitVec 64) : PackedStructWord :=
  s

#tooth Obend.Hardware.Types.struct_slice_extract_sound by mutation Obend.Hardware.Types.updateStructSlice := updateStructSliceNoOp

/-- 14. Broken `stepRetimedMac` in `Obend.Hardware.Retiming` that forgets to add the pipelined `cReg`. -/
def stepRetimedMacDropC (st : RetimedMacState) (a b c : BitVec 64) : RetimedMacState :=
  { mulReg := a * b
  , cReg   := c
  , outReg := st.mulReg }

#tooth Obend.Hardware.Retiming.leiserson_saxe_shift_sound by mutation Obend.Hardware.Retiming.stepRetimedMac := stepRetimedMacDropC

/-- 15. Broken `checkAllCombPathsMeetDelay` in `Obend.Hardware.Retiming` that ignores multi-hop combinational arrival bounds. -/
def mutantCheckAllCombPathsAcceptAll (_cert : RetimingCert) (_maxDelay : Nat) (_edges : List SyncEdge) : Bool := true

#tooth Obend.Hardware.Retiming.checkAllCombPathsMeetDelay_sound by mutation Obend.Hardware.Retiming.checkAllCombPathsMeetDelay := mutantCheckAllCombPathsAcceptAll

/-- 16. Broken `encodeBitstreamFrame` in `Obend.Hardware.PlaceRoute` that drops `lutInit` when packing `frameData`. -/
def encodeBitstreamFrameDropLut (cfg : TileFrameConfig) : BitstreamFrame where
  frameAddr := cfg.tileX * 65536 + cfg.tileY * 256 + cfg.belSlot
  frameData := cfg.pipMask

#tooth Obend.Hardware.PlaceRoute.bitstream_decode_roundtrip_sound by mutation Obend.Hardware.PlaceRoute.encodeBitstreamFrame := encodeBitstreamFrameDropLut

/-- 17. Broken `checkPlacementInjective` in `Obend.Hardware.PlaceRoute` that accepts colliding BEL placements. -/
def mutantCheckPlacementInjectiveAcceptAll (_cells : List PlacedCell) : Bool := true

#tooth Obend.Hardware.PlaceRoute.checkPnrCertificate_sound by mutation Obend.Hardware.PlaceRoute.checkPlacementInjective := mutantCheckPlacementInjectiveAcceptAll

/-- 18. Broken `checkTrenchFillVoidFree` in `Obend.Hardware.DRC` that ignores top-corner bread-loafing pinch-off. -/
def checkTrenchFillIgnoreOverhang (spec : TrenchFillSpec) : Bool :=
  (spec.trenchWidthNm > 0) && (spec.stepCoveragePct > 0) && (spec.stepCoveragePct ≤ 100)

#tooth Obend.Hardware.DRC.pvd_high_ar_keyhole_refused by mutation Obend.Hardware.DRC.checkTrenchFillVoidFree := checkTrenchFillIgnoreOverhang

/-- 19. Broken `abbaCentroidMismatch` in `Obend.Hardware.Analog` that uses an unmatched `AABB` placement instead of `ABBA`. -/
def abbaAsUnmatchedAabb (p0 gradPerUm x0 pitch : Int) : Int :=
  aabbUnmatchedMismatch p0 gradPerUm x0 pitch

#tooth Obend.Hardware.Analog.commonCentroid_cancels_linear_gradient by mutation Obend.Hardware.Analog.abbaCentroidMismatch := abbaAsUnmatchedAabb

/-- 20. Broken `prouhetThueMorseMismatch1D` in `Obend.Hardware.Analog` that falls back to 4-cell `ABBA`. -/
def ptm8BrokenAsAbba4 (p0 gx cxx pitch : Int) : Int :=
  abbaQuadraticMismatch1D p0 gx cxx pitch

#tooth Obend.Hardware.Analog.prouhetThueMorse_cancels_linear_and_quadratic_bow by mutation Obend.Hardware.Analog.prouhetThueMorseMismatch1D := ptm8BrokenAsAbba4

-- 21. Broken `chiralityBalanced2DMismatch` in `Obend.Hardware.Analog` that falls back to 4-cell `crossCoupledQuad2DMismatch` (leaving a non-zero $8 c_{xy} p_x p_y$ saddle residual!).
#tooth Obend.Hardware.Analog.chiralityBalanced2D_cancels_full_hessian by mutation Obend.Hardware.Analog.chiralityBalanced2DMismatch := Obend.Hardware.Analog.crossCoupledQuad2DMismatch

/-- 22. Broken `checkRtlSynth` in `Obend.Hardware.Judge` that accepts any `RtlModule` without checking `checkRtlModule`. -/
def mutantCheckRtlSynthAcceptAll (_grade : Nat) (_expectedName : String) (_m : RtlModule) : Obend.Judge.Verdict HwClause :=
  .ok

#tooth Obend.Hardware.Judge.badLoopRtlModule_refused by mutation Obend.Hardware.Judge.checkRtlSynth := mutantCheckRtlSynthAcceptAll

/-- 23. Broken `checkLogicInterface` in `Obend.Hardware.Datasheet` that forgets to verify `noiseMarginHigh`. -/
def mutantCheckLogicInterfaceIgnoreHigh (drv rcv : LogicFamilySpec) (_pullupBoostMv minMarginMv : Int) : Bool :=
  decide (minMarginMv ≤ noiseMarginLow drv rcv) &&
  decide (drv.volMaxMv < rcv.vihMinMv)

#tooth Obend.Hardware.Datasheet.checkLogicInterface_guarantees_valid_thresholds by mutation Obend.Hardware.Datasheet.checkLogicInterface := mutantCheckLogicInterfaceIgnoreHigh

/-- 24. Broken `evalInaOutputUv` in `Obend.Hardware.Circuits` that forgets to apply `trimCmCancel`. -/
def evalInaOutputUvNoTrim (p : InaParams) (vDiffUv vCmUv deltaTC : Int) : Int :=
  p.gainDiff * (vDiffUv + p.vos0Uv + p.dVosDtUvPerC * deltaTC) +
  p.gainCmRaw * vCmUv

#tooth Obend.Hardware.Circuits.ina_common_mode_cancelled_at_matched_bridge by mutation Obend.Hardware.Circuits.evalInaOutputUv := evalInaOutputUvNoTrim

/-- 25. Broken `WaferState.anneal` in `Obend.Hardware.Device` that leaves every profile's variance unchanged. -/
def annealNoDiffusion (w : Obend.Hardware.Device.WaferState) (_d : Obend.Hardware.Device.Diffusivities)
    (_timeS : Obend.Analysis.CanonicalRat) : Obend.Hardware.Device.WaferState := w

#tooth Obend.Hardware.Device.anneal_var_mono by mutation Obend.Hardware.Device.WaferState.anneal := annealNoDiffusion

-- 26. Broken `sqrtEnclosure` in `Obend.Hardware.Device` that sets `lo = v + 1` (violating `lo^2 ≤ v`).
#tooth Obend.Hardware.Device.sqrtEnclosure_spec by mutation Obend.Hardware.Device.sqrtEnclosure := (fun (v : Obend.Analysis.CanonicalRat) (_iters : optParam Nat 48) => (⟨v + 1, v + 1⟩ : Obend.Analysis.Interval))

/-- 27. Broken `evalPhaseShifter2x2` in `Obend.Hardware.Photonics` that negates `e1` regardless of `phasePhasor` (breaking zero-phase pure-cross MZI interference). -/
def evalPhaseShifter2x2BrokenFlip (_phasePhasor : ComplexField) (e1 e2 : ComplexField) : ComplexField × ComplexField :=
  ({ re := -e1.re, im := -e1.im }, e2)

#tooth Obend.Hardware.Photonics.cascaded_mzi_zero_phase_pure_cross by mutation Obend.Hardware.Photonics.evalPhaseShifter2x2 := evalPhaseShifter2x2BrokenFlip

/-- 28. Broken `fxSqrt` in `Obend.Hardware.PCB` that returns `0` (violating `a * fxS < (fxSqrt a + 1)^2` and positivity). -/
def fxSqrtZero (_a : Nat) : Nat := 0

#tooth Obend.Hardware.PCB.fxSqrt_enclosure by mutation Obend.Hardware.PCB.fxSqrt := fxSqrtZero

/-- 29. Broken `dprPhase2LoadFrame` in `Obend.Hardware.ReductionMachine` that loads `frame.newTile` without checking `frame.computedCrc64 == frame.expectedCrc64`. -/
def dprPhase2IgnoreCrc (frame : IcapBitstreamFrame) (t : ReconfigTileState) : ReconfigTileState :=
  if t.tileId == frame.targetTileId then
    { t with activeTile := frame.newTile, frameCrc64 := frame.computedCrc64 }
  else
    t

#tooth Obend.Hardware.ReductionMachine.dpr_corrupt_crc_keeps_tile_isolated by mutation Obend.Hardware.ReductionMachine.dprPhase2LoadFrame := dprPhase2IgnoreCrc

/-- 30. Broken `checkRollettUnconditionalStability` in `Obend.Hardware.DSP` that omits the $K > 1$ check. -/
def checkRollettIgnoreK (sp : TwoPortSParams) : Bool :=
  decide (0 ≤ sp.s11MagSqPermilleSq ∧ sp.s11MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.s22MagSqPermilleSq ∧ sp.s22MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.deltaMagSqPermilleSq ∧ sp.deltaMagSqPermilleSq < 1000000) &&
  decide (0 < evalRollettDenominator sp)

#tooth Obend.Hardware.DSP.rollettStability_sound by mutation Obend.Hardware.DSP.checkRollettUnconditionalStability := checkRollettIgnoreK

/-- 31. Broken `checkDatasheetCiteFresh` in `Obend.Hardware.AgenticEDA` that ignores `cite.pinnedBlockHash = cite.currentDatasheetHash`. -/
def checkDatasheetCiteIgnoreHash (cite : DatasheetCitePin) : Bool :=
  decide (0 < cite.currentDatasheetHash)

#tooth Obend.Hardware.AgenticEDA.staleDatasheetCite_refused by mutation Obend.Hardware.AgenticEDA.checkDatasheetCiteFresh := checkDatasheetCiteIgnoreHash

/-- 32. Broken `encodeBinaryHwCert` in `Obend.Hardware.Codec` that emits wrong CBOR tag byte `0xEE` instead of `0xED`. -/
def encodeBinaryHwCertBadTag (c : BinaryHwCert) : List UInt8 :=
  (0xD9 : UInt8) :: (0x0B : UInt8) :: (0xEE : UInt8) :: (0x87 : UInt8) ::
    (cborEncodeU32 c.domain.toCode ++
      (cborEncodeI32 c.p0 ++
        (cborEncodeI32 c.p1 ++
          (cborEncodeI32 c.p2 ++
            (cborEncodeI32 c.p3 ++
              (cborEncodeI32 c.p4 ++ cborEncodeI32 c.p5))))))

#tooth Obend.Hardware.Codec.decode_encode_binaryHwCert by mutation Obend.Hardware.Codec.encodeBinaryHwCert := encodeBinaryHwCertBadTag

/-- 33. Broken `FemmTriangle2D.b0` in `Obend.Hardware.Magnetics` that adds `tri.y1 + tri.y2` instead of subtracting `tri.y1 - tri.y2`. -/
def femmB0AddInsteadOfSub (tri : FemmTriangle2D) : Int :=
  tri.y1 + tri.y2

#tooth Obend.Hardware.Magnetics.femm_gauge_invariance by mutation Obend.Hardware.Magnetics.FemmTriangle2D.b0 := femmB0AddInsteadOfSub

/-- 34. Broken `stepBhPicardReluctivity` in `Obend.Hardware.Magnetics` that accumulates `nuCur + nuSecant` without convex relaxation (violating fixed-point stationarity). -/
def stepBhPicardUnnormalized (nuLinear kSat _omegaPermille nuCur bSq : Int) : Int :=
  nuCur + evalNonlinearReluctivity nuLinear kSat bSq

#tooth Obend.Hardware.Magnetics.stepBhPicardReluctivity_fixed_point by mutation Obend.Hardware.Magnetics.stepBhPicardReluctivity := stepBhPicardUnnormalized

/-- 35. Broken `evalEdgeQuadratic` in `Obend.Hardware.ThermalPassivity` that negates conductance `-g * (ti - tj)^2` (violating passive Laplacian dissipation). -/
def evalEdgeQuadraticAntiPassive (tempsMk : List Int) (e : ThermalEdge) : Int :=
  let dT := tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0
  0 - e.conductanceMwPerK * (dT * dT)

#tooth Obend.Hardware.ThermalPassivity.laplacian_quadratic_passive_universal by mutation Obend.Hardware.ThermalPassivity.evalEdgeQuadratic := evalEdgeQuadraticAntiPassive

/-- 36. Broken `rtlPiStep` in `Obend.Hardware.CurrentLoop` that drops proportional and integral error terms (`v = intMv`). -/
def rtlPiStepDead (_kpMilli _kiMilli _errMa intMv : Int) : Int × Int :=
  (intMv, intMv)

#tooth Obend.Hardware.CurrentLoop.rtlPiStep_within_lsb by mutation Obend.Hardware.CurrentLoop.rtlPiStep := rtlPiStepDead

/-- 37. Broken `evalOzakiBase13Product2` in `Obend.Hardware.Accelerators` that drops the cross-limb Tensor-Core products `a0 * b1 + a1 * b0`. -/
def evalOzakiBase13DropCross (a0 a1 b0 b1 : Int) : Int :=
  a0 * b0 + 169 * (a1 * b1)

#tooth Obend.Hardware.Accelerators.ozaki_base13_2limb_product_exact by mutation Obend.Hardware.Accelerators.evalOzakiBase13Product2 := evalOzakiBase13DropCross

/-- 38. Broken `stepSystolicPe` in `Obend.Hardware.Accelerators` that overwrites `partialSumIn` instead of accumulating `partialSumIn + act * weight`. -/
def stepSystolicPeNoAccum (_partialSumIn act weight : Int) : Int :=
  act * weight

#tooth Obend.Hardware.Accelerators.systolic_tpu_eq_dsp58_cascade_eq_kulisch_dot by mutation Obend.Hardware.Accelerators.stepSystolicPe := stepSystolicPeNoAccum

/-- 39. Broken `ivSub` in `Obend.Hardware.GeometryCAM` that subtracts `b.lo` from `a.lo` instead of `b.hi`. -/
def ivSubBrokenEndpoints (a b : FloatInterval) : FloatInterval where
  lo := a.lo - b.lo
  hi := a.hi - b.hi

#tooth Obend.Hardware.GeometryCAM.frep_interval_enclosure_sound by mutation Obend.Hardware.GeometryCAM.ivSub := ivSubBrokenEndpoints

/-- 40. Broken `insertPrimByStrength` in `Obend.Hardware.OpenUSD` that appends `p` after `q` instead of placing stronger/local `PrimSpec`s at the head. -/
def insertPrimByStrengthBroken (p : PrimSpec) : List PrimSpec → List PrimSpec
  | [] => [p]
  | q :: rest => q :: insertPrimByStrengthBroken p rest

#tooth Obend.Hardware.OpenUSD.insertPrimByStrength_localArc_head by mutation Obend.Hardware.OpenUSD.insertPrimByStrength := insertPrimByStrengthBroken

/-- 41. Broken `spatialPower` in `Obend.Hardware.Kinematics` that subtracts the linear power `dot3 f.force v.lin` instead of adding it. -/
def spatialPowerBrokenLinear (f : SpatialWrench6D) (v : SpatialTwist6D) : Int :=
  dot3 f.torque v.ang - dot3 f.force v.lin

#tooth Obend.Hardware.Kinematics.featherstone_spatial_adjoint_duality by mutation Obend.Hardware.Kinematics.spatialPower := spatialPowerBrokenLinear

/-- 42. Broken `AffineForm1D.toInterval` in `Obend.Hardware.OpenUSD` that forgets to negate `radius` on the lower bound. -/
def affineToIntervalCollapsed (af : AffineForm1D) : FloatInterval where
  lo := af.c0 + af.radius
  hi := af.c0 + af.radius

#tooth Obend.Hardware.OpenUSD.affine_to_interval_encloses_eval by mutation Obend.Hardware.OpenUSD.AffineForm1D.toInterval := affineToIntervalCollapsed

/-- 44. Broken `compileOpticAdjoint` in `Obend.Hardware.OpenHypergraph` that maps every `OpticOp` to `.add`. -/
def compileOpticAdjointAlwaysAdd (_op : OpticOp) : OpticAdjoint :=
  { op := .add, numResidualWires := 0, usesInputResiduals := false }

#tooth Obend.Hardware.OpenHypergraph.optic_reverse_ad_sound by mutation Obend.Hardware.OpenHypergraph.compileOpticAdjoint := compileOpticAdjointAlwaysAdd

/-- 45. Broken `stepCalyxSeqFsm` in `Obend.Hardware.Compiler` that fails to increment `activeGroupIdx` when a Calyx group completes. -/
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

/-- 46. Broken `resolveTwoWireSplices` in `Obend.Hardware.ReductionMachine` that drops newly formed active pairs. -/
def resolveTwoWireSplicesDropPairs (arena : List INetNode) (_w1 _w2 : PortRef × PortRef) : List INetNode × List ActivePair :=
  (arena, [])

#tooth Obend.Hardware.ReductionMachine.inet_dynamic_splice_cascading_reduction by mutation Obend.Hardware.ReductionMachine.resolveTwoWireSplices := resolveTwoWireSplicesDropPairs

/-- 46b. Broken `commuteSpawnedNodes` port reuse. -/
def commuteSpawnedNodesPortTwice (l r : INetNode) (nextFreeId : Nat) : List INetNode :=
  let n := nextFreeId
  [ { id := n, kind := l.kind, label := l.label, immVal := 0, aux1 := ⟨n + 2, 1⟩, aux2 := ⟨n + 3, 1⟩ }
  , { id := n + 1, kind := l.kind, label := l.label, immVal := 0, aux1 := ⟨n + 2, 2⟩, aux2 := ⟨n + 3, 2⟩ }
  , { id := n + 2, kind := r.kind, label := r.label, immVal := 0, aux1 := l.aux1, aux2 := r.aux1 }
  , { id := n + 3, kind := r.kind, label := r.label, immVal := 0, aux1 := l.aux2, aux2 := r.aux2 } ]

#tooth Obend.Hardware.ReductionMachine.commute_wellformed by mutation Obend.Hardware.ReductionMachine.commuteSpawnedNodes := commuteSpawnedNodesPortTwice

/-- 47. Broken `ivMinChoice` in `Obend.Hardware.GeometryCAM` that returns `.right` when `a.hi ≤ b.lo` instead of `.left`. -/
def ivMinChoiceInverted (a b : FloatInterval) : FidgetChoice :=
  if decide (a.hi ≤ b.lo) then .right
  else if decide (b.hi ≤ a.lo) then .left
  else .both

#tooth Obend.Hardware.GeometryCAM.pruneFRepTape_sound by mutation Obend.Hardware.GeometryCAM.ivMinChoice := ivMinChoiceInverted

/-- 48. Broken `AffineForm3D.toInterval` in `Obend.Hardware.OpenUSD` that adds `af.radius` on `lo` instead of subtracting it. -/
def affine3dToIntervalCollapsed (af : AffineForm3D) : FloatInterval where
  lo := af.c0 + af.radius
  hi := af.c0 + af.radius

#tooth Obend.Hardware.OpenUSD.affine3d_to_interval_encloses_eval by mutation Obend.Hardware.OpenUSD.AffineForm3D.toInterval := affine3dToIntervalCollapsed

/-- 49. Broken `evalRuckigProfile7` in `Obend.Hardware.Kinematics` that applies `+jMax` instead of `-jMax` in Phase 3. -/
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

/-- 50. Broken `cborDecodeU32List` in `Obend.Hardware.Codec` that drops the decoded head element `x`. -/
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

/-- 51. Broken `cellRowSum` in `Obend.Analysis.Equitable` that returns `0`. -/
def cellRowSumZero (_H : Nat → Nat → Int) (_cellJ : List Nat) (_u : Nat) : Int := 0

#tooth Obend.Analysis.equitable_handshake_identity by mutation Obend.Analysis.cellRowSum := cellRowSumZero

/-- 52. Broken `evalPhotonicArray4LayerEven` in `Obend.Hardware.QuantumMatter` that duplicates `c01.1` on waveguide 1. -/
def evalPhotonicArray4LayerEvenDuplicatePort
    (t01 k01 t23 k23 : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let c01 := evalDirectionalCoupler2x2 t01 k01 e0 e1
  let c23 := evalDirectionalCoupler2x2 t23 k23 e2 e3
  (c01.1, c01.1, c23.1, c23.2)

#tooth Obend.Hardware.QuantumMatter.photonic_ctqw_array_power_conserved by mutation Obend.Hardware.QuantumMatter.evalPhotonicArray4LayerEven := evalPhotonicArray4LayerEvenDuplicatePort

/-- 53. Broken mutant of `runVerilatorCoSimModel` in `Obend.Apps.SiliconKernelVerilator` that fails to refuse `#tooth` mutants (`toothMutantRefused := false`). -/
def runVerilatorCoSimModelAcceptMutant : Obend.Apps.SiliconKernelVerilator.VerilatorCoSimTrace :=
  { status               := "FAIL"
  , cycles               := 45
  , camHits              := 18
  , betaBypasses         := 2
  , nocFlits             := 6
  , lutHits              := 2
  , epoch1LutOut         := 42#64
  , epoch2LutOut         := 70#64
  , movedPinFallback1Cyc := true
  , dprGlitchFreeClamped := true
  , toothMutantRefused   := false
  , sorryRefused         := true
  , vcdPath              := "silicon_elab_wave.vcd" }

#tooth Obend.Apps.SiliconKernelVerilator.silicon_kernel_verilator_cosim_verified
  by mutation Obend.Apps.SiliconKernelVerilator.runVerilatorCoSimModel := runVerilatorCoSimModelAcceptMutant

end Obend.Teeth.Hardware

open Obend.Vault.HardwareProjection in
#tooth pnrLayoutToData_binds_routedNets_and_bitstreamFrames by
  mutation pnrLayoutToData := fun c =>
    Obend.Core.Data.Data.record [("net_count", .natural c.routedNets.length),
      ("frames", dataSeq bitstreamFrameToData c.bitstreamFrames)]

open Obend.Vault.HardwareProjection in
#tooth pnrLayoutToData_binds_routedNets_and_bitstreamFrames by
  mutation pnrLayoutToData := fun c =>
    Obend.Core.Data.Data.record [("nets", dataSeq routedNetToData c.routedNets),
      ("frame_count", .natural c.bitstreamFrames.length)]

open Obend.Hardware.Device in
#tooth sky130Diode_recipe_implant_inhabited by
  mutation sky130DiodeRecipe := fun _ nPlusDose =>
    [.implant .boron 160 1.3e13, .implant .arsenic 50 nPlusDose]
