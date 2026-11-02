module

public import Obend.Tactic.Tooth
public import Obend.Hardware.Analog
public import Obend.Hardware.RF
public import Obend.Hardware.DSP
public import Obend.Hardware.PCB
public import Obend.Hardware.Datasheet
public import Obend.Hardware.Circuits
import all Obend.Hardware.Analog
import all Obend.Hardware.RF
import all Obend.Hardware.DSP
import all Obend.Hardware.PCB
import all Obend.Hardware.Datasheet
import all Obend.Hardware.Circuits

/-!
# Metasystem Test Suite — Mixed-Signal AMS Silicon, $N$-Bit SAR ADC, Connected SDR Digital Downconverter & High-Speed SerDes PCB Co-Design (`WS-N`)

Comprehensive universal theorem checks, boundary & multi-resolution quantization checks,
negative refusal poles, and `#tooth` kernel mutation-killing probes (`0 sorry`) across:
1. `Obend.Hardware.Analog`:
   - `runSarAdcN`, `evalSarAdcN`, `runSarAdcN_matches_runSarAdc4`, `runSarAdcN_lower_bound`,
   - `eval2DCommonCentroidMismatch`, `commonCentroid2D_cancels_planar_gradient`, `unmatched2D_suffers_planar_gradient`.
2. `Obend.Hardware.DSP` & `Obend.Hardware.RF`:
   - `runCordicPipeline`, `runCordicPipeline_append`, `stepCordicStage1`, `cordic_stage1_norm_identity`,
     `stepCordicTwoStage`, `cordic_twoStage_exact_gain_10x`,
   - `SdrDdcChainSpec`, `evalSdrDdcSample`, `checkSdrDdcSignoff`, `sdrDdcChain_signoff_sound`, `sdrDdcChain_signoff_poles`,
   - `RfStageSpec`, `evalCascadedGainDbTenths`, `cascadedGainDbTenths_append`, `cascadedGainDbTenths_monotone`,
     `checkCascadedSensitivity`, `checkCascadedSensitivity_sound`.
3. `Obend.Hardware.PCB`, `Obend.Hardware.Datasheet` & `Obend.Hardware.Circuits`:
   - `evalChannelInsertionLossMdB`, `channelInsertionLoss_monotone`,
   - `EyeDiagramSpec`, `evalEyeHeightMv`, `evalEyeWidthFs`, `checkEyeOpeningSignoff`, `eyeOpeningSignoff_sound`,
   - `LvdsIoSpec`, `checkLvdsIoCompatibility`, `lvdsIoCompatibility_sound`,
   - `AsicToPcbChannelSpec`, `checkAsicToPcbChannelSignoff`, `asicToPcbChannelSignoff_sound`, `asicToPcbChannelSignoff_poles`.
-/

@[expose] public section
namespace Obend.Tests.Metasystem.MixedSignalSdrPcbTest

open Obend.Hardware.Analog
open Obend.Hardware.RF
open Obend.Hardware.DSP
open Obend.Hardware.PCB
open Obend.Hardware.Datasheet
open Obend.Hardware.Circuits
set_option autoImplicit false

/-! ## 1. Parametric $N$-Bit SAR ADC & 2D Planar Common-Centroid Capacitor Array (`Obend.Hardware.Analog`) -/

-- 1.1 Universal agreement with 4-bit SAR ADC and lower/upper bound invariant
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
    runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits :=
  runSarAdcN_lower_bound bits vInMv vLsbMv hPos

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
#guard runSarAdcN 8 0 9999 10 == 255 -- full-scale saturation to 2^8 - 1 = 255
#guard runSarAdcN 10 0 5125 5 == 1023 -- full-scale saturation to 2^10 - 1 = 1023
#guard runSarAdcN 12 0 2048 1 == 2048
#guard runSarAdcN 12 0 4095 1 == 4095

-- 1.3 2D Planar Common-Centroid Capacitor Array gradient cancellation
example (p0 gx gy x0 y0 dx dy : Int) :
    eval2DCommonCentroidMismatch p0 gx gy x0 y0 dx dy = 0 :=
  commonCentroid2D_cancels_planar_gradient p0 gx gy x0 y0 dx dy

example (p0 gx gy x0 y0 dx dy : Int) :
    eval2DUnmatchedMismatch p0 gx gy x0 y0 dx dy = -2 * (gy * dy) :=
  unmatched2D_suffers_planar_gradient p0 gx gy x0 y0 dx dy

-- `#tooth` mutation probes on `runSarAdcN` and `eval2DCommonCentroidMismatch`
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

/-! ## 2. Multi-Stage CORDIC, Connected SDR DDC & Cascaded $N$-Stage Friis Chain (`Obend.Hardware.DSP`, `Obend.Hardware.RF`) -/

-- 2.1 Stage-1 and 2-Stage CORDIC exact norm scaling identities
example (v : CordicVec) (dirPos : Bool) :
    evalCordicNormSq (stepCordicStage1 v dirPos) = 5 * evalCordicNormSq v :=
  cordic_stage1_norm_identity v dirPos

example (v : CordicVec) (dir0 dir1 : Bool) :
    evalCordicNormSq (stepCordicTwoStage v dir0 dir1) = 10 * evalCordicNormSq v :=
  cordic_twoStage_exact_gain_10x v dir0 dir1

example (s1 s2 : List (Bool × Int)) (v : CordicVec) :
    runCordicPipeline v (s1 ++ s2) = runCordicPipeline (runCordicPipeline v s1) s2 :=
  runCordicPipeline_append s1 s2 v

-- Concrete evaluation of `runCordicPipeline` and `stepCordicTwoStage`
#guard runCordicPipeline ⟨100, 0⟩ [] == ⟨100, 0⟩
#guard runCordicPipeline ⟨100, 0⟩ [(true, 1), (false, 2)] == ⟨150, 50⟩
#guard evalCordicNormSq (stepCordicTwoStage ⟨30, 40⟩ true false) == 10 * evalCordicNormSq ⟨30, 40⟩
#guard evalCordicNormSq (stepCordicTwoStage ⟨-12, 5⟩ false true) == 1690

-- 2.2 Connected SDR Digital Downconverter (`SdrDdcChainSpec`, `checkSdrDdcSignoff`, `sdrDdcChain_signoff_sound`)
example (spec : SdrDdcChainSpec) (rfSigAmp xEarly xLate : Int)
    (hOk : checkSdrDdcSignoff spec = true) :
    (stepNco spec.nco).phaseWord < spec.nco.phaseModulus ∧
    evalCordicNormSq (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1) =
      10 * evalCordicNormSq spec.loInitVec ∧
    evalQuadratureImagePhaseCancel spec.iqGainI spec.iqGainQ spec.iqPhaseErr rfSigAmp = 0 ∧
    spec.cic.inputWidthBits ≤ cicRequiredBitWidth spec.cic ∧
    cicRequiredBitWidth spec.cic ≤ spec.cicAllocatedBits ∧
    evalSymmetricFirTapPair spec.firTapCoeff xEarly xLate =
      evalDirectFirTapPair spec.firTapCoeff xEarly xLate ∧
    evalSdrDdcSample spec rfSigAmp xLate =
      evalDirectFirTapPair spec.firTapCoeff
        (2 * spec.iqGainI * (rfSigAmp * (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1).x))
        xLate :=
  sdrDdcChain_signoff_sound spec rfSigAmp xEarly xLate hOk

example (spec : SdrDdcChainSpec) (hOk : checkSdrDdcSignoff spec = true) :
    0 < spec.iqGainI ∧
    0 < evalCordicNormSq (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1) :=
  sdrDdcChain_positive_lo_and_gain spec hOk

#guard checkSdrDdcSignoff goldenSdrDdcChainSpec == true
#guard checkSdrDdcSignoff unbalancedIqSdrDdcSpec == false
#guard checkSdrDdcSignoff deadMixerSdrDdcSpec == false
#guard checkSdrDdcSignoff underAllocatedCicSdrDdcSpec == false
#guard evalSdrDdcSample goldenSdrDdcChainSpec 10 500 == 36006000

-- 2.3 Cascaded $N$-Stage Friis Noise Figure / Gain Chain (`RfStageSpec`, `evalCascadedGainDbTenths`, `checkCascadedSensitivity`)
example (c1 c2 : List RfStageSpec) :
    evalCascadedGainDbTenths (c1 ++ c2) =
      evalCascadedGainDbTenths c1 + evalCascadedGainDbTenths c2 :=
  cascadedGainDbTenths_append c1 c2

example (s1 s2 st : RfStageSpec) (rest : List RfStageSpec)
    (hLe : s1.gainDbTenths ≤ s2.gainDbTenths) (hNonneg : 0 ≤ st.gainDbTenths) :
    evalCascadedGainDbTenths (s1 :: rest) ≤ evalCascadedGainDbTenths (s2 :: rest) ∧
    evalCascadedGainDbTenths rest ≤ evalCascadedGainDbTenths (st :: rest) :=
  cascadedGainDbTenths_monotone s1 s2 st rest hLe hNonneg

example (s1 s2 : RfStageSpec) (hNf1 : 1000 ≤ s1.noiseFactorMilli) :
    evalCascadedFriisMilliNf [s1, s2] =
      evalFriisTwoStageMilliNf s1.noiseFactorMilli s2.noiseFactorMilli s1.linearGain :=
  cascadedFriis_matches_twoStage s1 s2 hNf1

example (s1 s1' s2 : RfStageSpec)
    (hSameNf : s1.noiseFactorMilli = s1'.noiseFactorMilli)
    (hPos : 0 < s1.linearGain) (hGainLe : s1.linearGain ≤ s1'.linearGain) :
    evalCascadedFriisMilliNf [s1', s2] ≤ evalCascadedFriisMilliNf [s1, s2] :=
  cascadedFriis_lna_gain_monotone s1 s1' s2 hSameNf hPos hGainLe

#guard evalCascadedGainDbTenths [] == 0
#guard evalCascadedGainDbTenths golden3StageSdrRxChain == 380
#guard checkCascadedSensitivity golden3StageSdrRxChain 300 1800 == true
#guard checkCascadedSensitivity golden3StageSdrRxChain 400 1800 == false
#guard checkCascadedSensitivity [] 0 2000 == false

-- `#tooth` mutation probes on `stepCordicStage1`, `checkSdrDdcSignoff`, and `evalCascadedGainDbTenths`
def stepCordicStage1BrokenSign (v : CordicVec) (_dirPos : Bool) : CordicVec :=
  { x := 2 * v.x + v.y, y := 2 * v.y + v.x }

#tooth Obend.Hardware.DSP.cordic_stage1_norm_identity by mutation
  Obend.Hardware.DSP.stepCordicStage1 := stepCordicStage1BrokenSign

def checkSdrDdcSignoffIgnoreIq (spec : SdrDdcChainSpec) : Bool :=
  decide (0 < spec.nco.phaseModulus) &&
  checkCicOverflowFree spec.cic spec.cicAllocatedBits

#tooth Obend.Hardware.DSP.sdrDdcChain_signoff_poles by mutation
  Obend.Hardware.DSP.checkSdrDdcSignoff := checkSdrDdcSignoffIgnoreIq

def evalCascadedGainSubInsteadOfAdd : List RfStageSpec → Int
  | [] => 0
  | st :: rest => st.gainDbTenths - evalCascadedGainSubInsteadOfAdd rest

#tooth Obend.Hardware.RF.cascadedGainDbTenths_append by mutation
  Obend.Hardware.RF.evalCascadedGainDbTenths := evalCascadedGainSubInsteadOfAdd

/-! ## 3. High-Speed SerDes PCB Eye-Opening & Unified Mixed-Signal ASIC-to-PCB Signoff (`PCB`, `Datasheet`, `Circuits`) -/

-- 3.1 Dielectric + Skin-Effect Insertion Loss & Eye-Diagram Opening Signoff
example (diel1 diel2 : PcbDielectric) (len1 len2 freqMhz skinCoeff : Nat)
    (hLen : len1 ≤ len2) (hDf : diel1.dfPpm ≤ diel2.dfPpm) :
    evalChannelInsertionLossMdB diel1 len1 freqMhz skinCoeff ≤
      evalChannelInsertionLossMdB diel2 len2 freqMhz skinCoeff :=
  channelInsertionLoss_monotone diel1 diel2 len1 len2 freqMhz skinCoeff hLen hDf

example (spec : EyeDiagramSpec) (hOk : checkEyeOpeningSignoff spec = true) :
    evalChannelInsertionLossMdB spec.dielectric (evalSerpentineTotalLengthUm spec.meander) spec.freqMhz spec.skinCoeff ≤
      spec.maxInsertionLossMdB ∧
    natAbsDiff (evalDiffImpedanceMilliOhm spec.diffPair) spec.diffPair.zDiffTargetMilliOhm ≤
      spec.diffPair.zDiffTolMilliOhm ∧
    spec.minEyeHeightMv ≤ evalEyeHeightMv spec ∧
    spec.minEyeWidthFs ≤ evalEyeWidthFs spec :=
  eyeOpeningSignoff_sound spec hOk

example (spec : EyeDiagramSpec) (hOk : checkEyeOpeningSignoff spec = true) :
    0 < evalEyeHeightMv spec ∧
    0 < evalEyeWidthFs spec ∧
    evalEyeHeightMv spec + evalEyeVerticalLossMv spec = spec.txLaunchSwingMv ∧
    evalEyeWidthFs spec + spec.rjDjJitterFs +
      evalFlightTimeSkewFs spec.refLengthUm (evalSerpentineTotalLengthUm spec.meander) spec.dielectric.propDelayFsPerUm =
      spec.unitIntervalFs :=
  eyeOpeningSignoff_positive_and_exact spec hOk

example (spec : LvdsIoSpec) (rxEyeHeightMv gndShiftMv minDiffMarginMv vOcmMv deltaGndMv : Int)
    (hOk : checkLvdsIoCompatibility spec rxEyeHeightMv gndShiftMv minDiffMarginMv = true)
    (hVocm : spec.vocmMinMv ≤ vOcmMv ∧ vOcmMv ≤ spec.vocmMaxMv)
    (hDelta : -gndShiftMv ≤ deltaGndMv ∧ deltaGndMv ≤ gndShiftMv) :
    0 ≤ gndShiftMv ∧
    spec.vicmMinMv ≤ vOcmMv + deltaGndMv ∧
    vOcmMv + deltaGndMv ≤ spec.vicmMaxMv :=
  lvdsIoCompatibility_commonMode_enclosure spec rxEyeHeightMv gndShiftMv minDiffMarginMv vOcmMv deltaGndMv hOk hVocm hDelta

#guard evalChannelInsertionLossMdB rogers4350bDielectric 30000 5000 4 == 1155
#guard evalChannelInsertionLossMdB fr4StandardDielectric 30000 5000 4 == 3600
#guard evalEyeHeightMv goldenSerdesEyeSpec == 742
#guard evalEyeWidthFs goldenSerdesEyeSpec == 80000
#guard checkEyeOpeningSignoff goldenSerdesEyeSpec == true
#guard checkEyeOpeningSignoff highLossFr4EyeSpec == false
#guard checkEyeOpeningSignoff unmatchedSkewEyeSpec == false
#guard checkEyeOpeningSignoff zeroHeightClosedEyeSpec == false
#guard checkLvdsIoCompatibility lvdsAnsi644Spec 742 50 100 == true
#guard checkLvdsIoCompatibility lvdsAnsi644Spec 400 (-5000) 100 == false

-- 3.2 Unified Mixed-Signal ASIC-to-PCB Transceiver Board Signoff (`checkAsicToPcbChannelSignoff`, `asicToPcbChannelSignoff_sound`)
example (spec : AsicToPcbChannelSpec) (hOk : checkAsicToPcbChannelSignoff spec = true) :
    (spec.cmosRcv.vihMinMv + spec.minCmosMarginMv ≤ spec.cmosDrv.vohMinMv + spec.pullupBoostMv ∧
     spec.cmosDrv.volMaxMv + spec.minCmosMarginMv ≤ spec.cmosRcv.vilMaxMv) ∧
    spec.lvdsSpec.vthMaxMv + spec.minDiffMarginMv ≤ Int.ofNat (evalEyeHeightMv spec.eyeSpec) ∧
    (∀ c ∈ spec.upfChecks,
      c.appliedSwingMv ≤ c.oxideRatingMv ∧
      (c.srcDomainMv ≠ c.dstDomainMv → c.hasLevelShifter = true)) ∧
    (evalChannelInsertionLossMdB spec.eyeSpec.dielectric
        (evalSerpentineTotalLengthUm spec.eyeSpec.meander)
        spec.eyeSpec.freqMhz spec.eyeSpec.skinCoeff ≤ spec.eyeSpec.maxInsertionLossMdB ∧
     natAbsDiff (evalDiffImpedanceMilliOhm spec.eyeSpec.diffPair) spec.eyeSpec.diffPair.zDiffTargetMilliOhm ≤
        spec.eyeSpec.diffPair.zDiffTolMilliOhm ∧
     spec.eyeSpec.minEyeHeightMv ≤ evalEyeHeightMv spec.eyeSpec ∧
     spec.eyeSpec.minEyeWidthFs ≤ evalEyeWidthFs spec.eyeSpec) ∧
    25 * gammaMagSqNum spec.rfZ0Ohm spec.rfLoad ≤ gammaMagSqDen spec.rfZ0Ohm spec.rfLoad ∧
    evalBuckPeakInductorMa spec.buckStage ≤ spec.buckStage.iSatMaxMa :=
  asicToPcbChannelSignoff_sound spec hOk

#guard checkAsicToPcbChannelSignoff goldenAsicToPcbChannelSpec == true
#guard checkAsicToPcbChannelSignoff badOxideAsicToPcbSpec == false
#guard checkAsicToPcbChannelSignoff badEmptyUpfAsicToPcbSpec == false
#guard checkAsicToPcbChannelSignoff badLvdsGndShiftAsicToPcbSpec == false
#guard checkAsicToPcbChannelSignoff badEyeClosureAsicToPcbSpec == false
#guard checkAsicToPcbChannelSignoff badVswrAsicToPcbSpec == false

-- `#tooth` mutation probes on `checkEyeOpeningSignoff` and `checkAsicToPcbChannelSignoff`
def checkEyeOpeningIgnoreSkew (spec : EyeDiagramSpec) : Bool :=
  let routedLenUm := evalSerpentineTotalLengthUm spec.meander
  let ilMdB := evalChannelInsertionLossMdB spec.dielectric routedLenUm spec.freqMhz spec.skinCoeff
  decide (ilMdB ≤ spec.maxInsertionLossMdB)

#tooth Obend.Hardware.PCB.eyeOpeningSignoff_poles by mutation
  Obend.Hardware.PCB.checkEyeOpeningSignoff := checkEyeOpeningIgnoreSkew

def checkAsicToPcbIgnoreUpf (spec : AsicToPcbChannelSpec) : Bool :=
  checkLogicInterface spec.cmosDrv spec.cmosRcv spec.pullupBoostMv spec.minCmosMarginMv &&
  checkEyeOpeningSignoff spec.eyeSpec &&
  checkVswrUnder3To2 spec.rfZ0Ohm spec.rfLoad &&
  checkBuckCcmSafe spec.buckStage

#tooth Obend.Hardware.Circuits.asicToPcbChannelSignoff_poles by mutation
  Obend.Hardware.Circuits.checkAsicToPcbChannelSignoff := checkAsicToPcbIgnoreUpf

end Obend.Tests.Metasystem.MixedSignalSdrPcbTest
end
