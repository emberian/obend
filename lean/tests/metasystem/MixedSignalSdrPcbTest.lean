module

public import Obend.Tactic.Tooth
public import Obend.Hardware.Analog
public import Obend.Hardware.DSP
public import Obend.Hardware.PCB
public import Obend.Hardware.Datasheet
public import Obend.Hardware.Circuits
import all Obend.Hardware.Analog
import all Obend.Hardware.DSP
import all Obend.Hardware.PCB
import all Obend.Hardware.Datasheet
import all Obend.Hardware.Circuits

/-!
# Metasystem Test Suite — Mixed-Signal AMS Silicon, $N$-Bit SAR ADC, Synchronous SDR DSP & Hammerstad–Jensen PCB (`WS-N`)

Comprehensive universal theorem checks, boundary & multi-resolution quantization checks,
negative refusal poles, and `#tooth` kernel mutation-killing probes (`0 sorry`) across:
1. `Obend.Hardware.Analog`:
   - `runSarAdcN`, `evalSarAdcN`, `runSarAdcN_matches_runSarAdc4`, `runSarAdcN_lower_bound`,
     `runSarAdcN_exact_quantization_bounds`,
   - `prouhetThueMorse_cancels_linear_and_quadratic_bow`,
     `crossCoupledQuad2D_cancels_gradients_and_axial_bow`,
     `octuple2DCells_nodup`, `chiralityBalanced2D_cancels_full_hessian`,
   - `eval2DCommonCentroidMismatch`, `commonCentroid2D_cancels_planar_gradient`,
     `unmatched2D_suffers_planar_gradient`.
2. `Obend.Hardware.DSP`:
   - `runCordicPipeline`, `runCordicPipeline_append`, `stepCordicStage1`, `cordic_stage1_norm_identity`,
     `stepCordicTwoStage`, `cordic_twoStage_exact_gain_10x`,
   - `nco_phase_in_bounds`, `cic_register_width_sound`, `firSymmetric_folds_multipliers`,
   - `rollettStability_sound`, `ula_4elem_matched_beamformer_coherent`.
3. `Obend.Hardware.PCB`, `Obend.Hardware.Datasheet` & `Obend.Hardware.Circuits`:
   - Hammerstad–Jensen / Bahl–Garg fixed-point microstrip `microstripZ0MilliOhm`,
     `fxSqrt_enclosure`, `microstripEffWidthUm_ge_width`, `microstripEpsEffFx_enclosure_and_mono`,
     `singleEndedZ0_sound`, `microstripZ0_reference_enclosure`,
   - `ina_common_mode_cancelled_at_matched_bridge`, `buck_ccm_safe_prevents_core_saturation`,
     `datasheet_fit_signoff_poles`.
-/

@[expose] public section
namespace Obend.Tests.Metasystem.MixedSignalSdrPcbTest

open Obend.Hardware.Analog
open Obend.Hardware.DSP
open Obend.Hardware.PCB
open Obend.Hardware.Datasheet
open Obend.Hardware.Circuits
set_option autoImplicit false

/-! ## 1. Parametric $N$-Bit SAR ADC & 2D Octuple Hessian-Canceling Array (`Obend.Hardware.Analog`) -/

-- 1.1 Universal agreement with 4-bit SAR ADC and exact quantization bounds
example :
    (∀ vInMv vLsbMv : Nat, runSarAdcN 4 0 vInMv vLsbMv = runSarAdc4 vInMv vLsbMv) ∧
    (∀ q ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat),
      runSarAdcN 4 0 (q * 100) 100 = runSarAdc4 (q * 100) 100 ∧
      runSarAdcN 4 0 (q * 100) 100 = q ∧
      runSarAdcN 4 0 (q * 100 + 50) 100 = q ∧
      runSarAdcN 4 0 (q * 100 + 99) 100 = q) :=
  runSarAdcN_matches_runSarAdc4

example (bits vInMv vLsbMv : Nat) (hPos : 0 < vLsbMv) :
    (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits ∧
    (vInMv < 2 ^ bits * vLsbMv →
      vInMv < (runSarAdcN bits 0 vInMv vLsbMv + 1) * vLsbMv) :=
  runSarAdcN_exact_quantization_bounds bits vInMv vLsbMv hPos

-- 1.2 Boundary & multi-resolution SAR ADC tests (0-bit, 1-bit, 8-bit, 10-bit, 12-bit)
#guard runSarAdcN 0 0 500 100 == 0
#guard runSarAdcN 1 0 99 100 == 0
#guard runSarAdcN 1 0 100 100 == 1
#guard runSarAdcN 8 0 0 10 == 0
#guard runSarAdcN 8 0 1279 10 == 127
#guard runSarAdcN 8 0 1280 10 == 128
#guard runSarAdcN 8 0 2559 10 == 255
#guard runSarAdcN 8 0 9999 10 == 255
#guard runSarAdcN 10 0 5125 5 == 1023
#guard runSarAdcN 12 0 2048 1 == 2048
#guard runSarAdcN 12 0 4095 1 == 4095

-- 1.3 Prouhet–Thue–Morse 1D bow + 8-cell 2D Octuple full-Hessian cancellation
example (p0 gx cxx pitch : Int) :
    prouhetThueMorseMismatch1D p0 gx cxx pitch = 0 :=
  prouhetThueMorse_cancels_linear_and_quadratic_bow p0 gx cxx pitch

example : (octuple2DCellsA ++ octuple2DCellsB).Nodup :=
  octuple2DCells_nodup

example (p0 gx gy cxx cxy cyy px py : Int) :
    chiralityBalanced2DMismatch p0 gx gy cxx cxy cyy px py = 0 :=
  chiralityBalanced2D_cancels_full_hessian p0 gx gy cxx cxy cyy px py

example (p0 gx gy x0 y0 dx dy : Int) :
    eval2DCommonCentroidMismatch p0 gx gy x0 y0 dx dy = 0 :=
  commonCentroid2D_cancels_planar_gradient p0 gx gy x0 y0 dx dy

example (p0 gx gy x0 y0 dx dy : Int) :
    eval2DUnmatchedMismatch p0 gx gy x0 y0 dx dy = -2 * (gy * dy) :=
  unmatched2D_suffers_planar_gradient p0 gx gy x0 y0 dx dy

-- `#tooth` mutation probes on `runSarAdcN`, `eval2DCommonCentroidMismatch`, and `chiralityBalanced2DMismatch`
def runSarAdcNBrokenAlwaysMax (bits accCode _vInMv _vLsbMv : Nat) : Nat :=
  accCode + 2 ^ bits

def runSarAdcNBrokenAlwaysZero (_bits accCode _vInMv _vLsbMv : Nat) : Nat :=
  accCode

#tooth Obend.Hardware.Analog.runSarAdcN_matches_runSarAdc4 by mutation
  Obend.Hardware.Analog.runSarAdcN := runSarAdcNBrokenAlwaysMax

#tooth Obend.Hardware.Analog.runSarAdcN_acc_upper_bound by mutation
  Obend.Hardware.Analog.runSarAdcN := runSarAdcNBrokenAlwaysZero

#tooth Obend.Hardware.Analog.commonCentroid2D_cancels_planar_gradient by mutation
  Obend.Hardware.Analog.eval2DCommonCentroidMismatch := eval2DUnmatchedMismatch

#tooth Obend.Hardware.Analog.chiralityBalanced2D_cancels_full_hessian by mutation
  Obend.Hardware.Analog.chiralityBalanced2DMismatch := crossCoupledQuad2DMismatch

/-! ## 2. Multi-Stage CORDIC, CIC/FIR Datapaths, Phased-Array ULA & Rollett LNA (`Obend.Hardware.DSP`) -/

example (v : CordicVec) (dirPos : Bool) :
    evalCordicNormSq (stepCordicStage1 v dirPos) = 5 * evalCordicNormSq v :=
  cordic_stage1_norm_identity v dirPos

example (v : CordicVec) (dir0 dir1 : Bool) :
    evalCordicNormSq (stepCordicTwoStage v dir0 dir1) = 10 * evalCordicNormSq v :=
  cordic_twoStage_exact_gain_10x v dir0 dir1

example (s1 s2 : List (Bool × Int)) (v : CordicVec) :
    runCordicPipeline v (s1 ++ s2) = runCordicPipeline (runCordicPipeline v s1) s2 :=
  runCordicPipeline_append s1 s2 v

example (cic : CicFilterSpec) (allocatedBits : Nat)
    (hOk : checkCicOverflowFree cic allocatedBits = true) :
    cic.inputWidthBits ≤ evalCicRequiredWidthBits cic ∧
    evalCicRequiredWidthBits cic ≤ allocatedBits :=
  cic_register_width_sound cic allocatedBits hOk

example (coeff xEarly xLate : Int) :
    evalFoldedSymmetricFirTapPair coeff xEarly xLate =
      evalDirectFirTapPair coeff xEarly xLate :=
  firSymmetric_folds_multipliers coeff xEarly xLate

example (sp : TwoPortSParams) (hOk : checkRollettUnconditionalStability sp = true) :
    sp.s11MagSqPermilleSq < 1000000 ∧
    sp.s22MagSqPermilleSq < 1000000 ∧
    sp.deltaMagSqPermilleSq < 1000000 ∧
    0 < evalRollettDenominator sp ∧
    evalRollettDenominator sp < evalRollettNumerator sp :=
  rollettStability_sound sp hOk

example (s : IqPhasor) :
    (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).i =
      4 * (s.i * s.i + s.q * s.q) ∧
    0 ≤ (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).i ∧
    (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).q = 0 :=
  ula_4elem_matched_beamformer_coherent s

#guard runCordicPipeline ⟨100, 0⟩ [] == ⟨100, 0⟩
#guard runCordicPipeline ⟨100, 0⟩ [(true, 1), (false, 2)] == ⟨150, 50⟩
#guard evalCordicNormSq (stepCordicTwoStage ⟨30, 40⟩ true false) == 10 * evalCordicNormSq ⟨30, 40⟩
#guard checkRollettUnconditionalStability golden2mHamLnaSParams == true
#guard checkRollettUnconditionalStability unstableFeedbackLnaSParams == false

def stepCordicStage1BrokenSign (v : CordicVec) (_dirPos : Bool) : CordicVec :=
  { x := 2 * v.x + v.y, y := 2 * v.y + v.x }

#tooth Obend.Hardware.DSP.cordic_stage1_norm_identity by mutation
  Obend.Hardware.DSP.stepCordicStage1 := stepCordicStage1BrokenSign

/-! ## 3. Hammerstad–Jensen Microstrip $Z_0$ & Mixed-Signal Datasheet Calibration (`PCB`, `Datasheet`, `Circuits`) -/

example (a : Nat) :
    fxSqrt a * fxSqrt a ≤ a * fxS ∧
    a * fxS < (fxSqrt a + 1) * (fxSqrt a + 1) ∧
    (0 < a → 0 < fxSqrt a) :=
  fxSqrt_enclosure a

example (w h t : Nat) :
    w ≤ microstripEffWidthUm w h t ∧
    microstripEffWidthUm w h 0 = w :=
  microstripEffWidthUm_ge_width w h t

example (u er1 er2 : Nat) :
    (er1 + fxS) / 2 ≤ microstripEpsEffFx u er1 ∧
    (fxS ≤ er1 → 0 < microstripEpsEffFx u er1) ∧
    (er1 ≤ er2 → microstripEpsEffFx u er1 ≤ microstripEpsEffFx u er2) :=
  microstripEpsEffFx_enclosure_and_mono u er1 er2

example (w h t dk zExt zTgt zTol : Nat)
    (hOk : checkSingleEndedZ0 w h t dk zExt zTgt zTol = true) :
    75 ≤ w ∧
    natAbsDiff zExt zTgt ≤ zTol ∧
    natAbsDiff (microstripZ0MilliOhm w h t dk) zTgt ≤ zTol :=
  singleEndedZ0_sound w h t dk zExt zTgt zTol hOk

example :
    48000 ≤ microstripZ0MilliOhm 330 152 35 3480 ∧
    microstripZ0MilliOhm 330 152 35 3480 ≤ 52000 ∧
    175000 ≤ microstripZ0MilliOhm 80 500 0 2200 ∧
    microstripZ0MilliOhm 80 500 0 2200 ≤ 185000 ∧
    checkSingleEndedZ0 330 152 35 3480 50000 50000 3000 = true ∧
    checkSingleEndedZ0 80 500 35 2200 50000 50000 3000 = false :=
  microstripZ0_reference_enclosure

example (p : InaParams) (vDiffUv vCmUv deltaTC : Int)
    (hTrim : p.gainCmRaw = p.trimCmCancel) :
    evalInaOutputUv p vDiffUv vCmUv deltaTC =
      p.gainDiff * (vDiffUv + p.vos0Uv + p.dVosDtUvPerC * deltaTC) :=
  ina_common_mode_cancelled_at_matched_bridge p vDiffUv vCmUv deltaTC hTrim

example (b : BuckSpec) (hOk : checkBuckCcmSafe b = true) :
    evalBuckRippleMa b ≤ 2 * b.iLoadMa ∧
    evalBuckPeakInductorMa b ≤ b.iSatMaxMa :=
  buck_ccm_safe_prevents_core_saturation b hOk

#guard checkDatasheetFitSignoff goldenDatasheetFitCert == true
#guard checkDatasheetFitSignoff badDirect74HcFitCert == false
#guard checkDatasheetFitSignoff badUncalibratedDriftFitCert == false

def fxSqrtBrokenPlusOne (a : Nat) : Nat := Nat.sqrt (a * fxS) + 1

#tooth Obend.Hardware.PCB.fxSqrt_enclosure by mutation
  Obend.Hardware.PCB.fxSqrt := fxSqrtBrokenPlusOne

def evalInaOutputBrokenLeak (p : InaParams) (vDiffUv vCmUv deltaTC : Int) : Int :=
  p.gainDiff * (vDiffUv + p.vos0Uv + p.dVosDtUvPerC * deltaTC) + vCmUv

#tooth Obend.Hardware.Circuits.ina_common_mode_cancelled_at_matched_bridge by mutation
  Obend.Hardware.Circuits.evalInaOutputUv := evalInaOutputBrokenLeak

end Obend.Tests.Metasystem.MixedSignalSdrPcbTest
end
