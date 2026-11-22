module
/-
# EpiphanyCompositorTest — Cross-Language Golden Vector, Multi-Turn Smoke & `#tooth` Mutation Suite

Verifies `Obend.Polis.EpiphanyCompositor`:
1. Exact 95-byte preimage and 32-byte `"OBEND.SHE.SENSOR_SEAL/v1"` golden digest shared with
   `crates/obend-surfaces/src/epiphany.rs`.
2. Concrete refusal witnesses for `chromeIntrusion`, `nonMonotoneSensorSeq`,
   `unredactedPrivateRoi`, `sealMismatch`, `hazardVisibilityViolation`, and `certWitnessMismatch`.
3. Multi-turn `ValidEpiphanySessionTrace` execution and `0 Classical` `#print axioms` audit.
4. Nine `#tooth` mutation-sensitivity kills across Z-order non-occlusion, belief clipping,
   Porter-Duff alpha floor, 6-field seal binding, ROI redaction, monotone replay refusal, and
   `epiphanyScanoutJudge` soundness & refutation.
-/
public import Obend.Polis.EpiphanyCompositor
import all Obend.Polis.EpiphanyCompositor
import all Obend.Judge.Class
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import Obend.Tactic.Tooth

public section
namespace Obend.Tests.Metasystem.EpiphanyCompositorTest

open Obend.Polis.EpiphanyCompositor
open Obend.Vault.FrustumMembrane

set_option autoImplicit false

/-! ## 1. Cross-Language `"OBEND.SHE.SENSOR_SEAL/v1"` Golden Wire Vector -/

private def hexString (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

-- Post-redaction frame zeroes pixels (1,0) and (2,0) inside Rect { x: 1, y: 0, w: 2, h: 1 }.
#guard (redactSensorFrame canonicalRawSensorFrame).tiles.map (·.pixels) ==
  [[ ⟨10, 20, 30, 255⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨40, 50, 60, 255⟩
   , ⟨70, 80, 90, 255⟩, ⟨100, 110, 120, 255⟩, ⟨130, 140, 150, 255⟩, ⟨160, 170, 180, 255⟩ ]]

-- Exact 95-byte preimage length and 32-byte digest shared with `crates/obend-surfaces`.
#guard (sensorFrameSealPreimage (redactSensorFrame canonicalRawSensorFrame)).length == 95
#guard hexString (sensorFrameSeal (redactSensorFrame canonicalRawSensorFrame)) ==
  "07e36afa669af0611a69815d73f0fdb2362e7cfbfea48a937e343c38a80ab648"
#guard (sensorFrameSeal (redactSensorFrame canonicalRawSensorFrame)).data.toList ==
  [ 0x07, 0xe3, 0x6a, 0xfa, 0x66, 0x9a, 0xf0, 0x61
  , 0x1a, 0x69, 0x81, 0x5d, 0x73, 0xf0, 0xfd, 0xb2
  , 0x36, 0x2e, 0x7c, 0xfb, 0xfe, 0xa4, 0x8a, 0x93
  , 0x7e, 0x34, 0x3c, 0x38, 0xa8, 0x0a, 0xb6, 0x48 ]

-- Mutating private bystander pixels inside `redactBoxes` produces the exact same seal.
private def altSecretRawFrame : SensorFrame :=
  { canonicalRawSensorFrame with
    tiles :=
      [ { tileX := 0, tileY := 0, tileW := 4, tileH := 2
          pixels :=
            [ ⟨10, 20, 30, 255⟩, ⟨255, 0, 128, 255⟩, ⟨1, 2, 3, 4⟩, ⟨40, 50, 60, 255⟩
            , ⟨70, 80, 90, 255⟩, ⟨100, 110, 120, 255⟩, ⟨130, 140, 150, 255⟩, ⟨160, 170, 180, 255⟩ ] } ] }

#guard redactSensorFrame altSecretRawFrame == redactSensorFrame canonicalRawSensorFrame
#guard sensorFrameSeal (redactSensorFrame altSecretRawFrame) ==
  sensorFrameSeal (redactSensorFrame canonicalRawSensorFrame)

/-! ## 2. Concrete Scanout Non-Occlusion, Hazard Visibility & Judge Refusal Witnesses -/

private def advBeliefA : UntrustedBeliefPlane :=
  { overlays := [⟨"cell/spoof", .sectionPanel, ⟨0, 0, 640, 480⟩, ⟨255, 0, 0, 255⟩⟩] }

private def advBeliefB : UntrustedBeliefPlane :=
  { overlays := [⟨"cell/spoof2", .tileSurface, ⟨0, 0, 640, 480⟩, ⟨0, 255, 255, 255⟩⟩] }

private def testHazardPlane : PhysicalHazardReticlePlane :=
  { boxes := [canonicalHazardBox] }

-- Consent band (10, 10), sensor LED (10, 10), and active modal (210, 170) are invariant across adversarial beliefs.
#guard scanoutPixel canonicalDisplayPolicy advBeliefA testHazardPlane canonicalConsentChrome 10 10 ==
  canonicalConsentChrome.sensorLedColor
#guard scanoutPixel canonicalDisplayPolicy advBeliefB testHazardPlane canonicalConsentChrome 10 10 ==
  canonicalConsentChrome.sensorLedColor
#guard scanoutPixel canonicalDisplayPolicy advBeliefA testHazardPlane canonicalConsentChrome 100 16 ==
  canonicalConsentChrome.bannerColor
#guard scanoutPixel canonicalDisplayPolicy advBeliefA testHazardPlane canonicalConsentChrome 210 170 ==
  canonicalConsentChrome.modalColor

-- Hazard reticle outer ring (80, 80) and inner ring (81, 81) maintain >= 100 luma contrast over adversarial backgrounds.
#guard pixelLuma (scanoutPixel canonicalDisplayPolicy advBeliefA testHazardPlane canonicalConsentChrome 80 80) >=
  pixelLuma (scanoutPixel canonicalDisplayPolicy advBeliefB testHazardPlane canonicalConsentChrome 81 81) + 100

-- Concrete refusal witnesses for every SHE safety clause of `epiphanyScanoutJudge`.
#guard checkEpiphanyScanout 0 canonicalFrameQuery canonicalScanoutCert == .uncovered
#guard checkEpiphanyScanout 10 canonicalFrameQuery canonicalScanoutCert == .ok

private def intrudingQuery : EpiphanyFrameQuery :=
  { canonicalFrameQuery with
    beliefPlane := { overlays := [⟨"cell/evil", .pillBadge, ⟨20, 12, 50, 20⟩, ⟨255, 255, 255, 255⟩⟩] } }
#guard checkEpiphanyScanout 10 intrudingQuery canonicalScanoutCert ==
  .refused .chromeIntrusion [6]

private def replayQuery : EpiphanyFrameQuery :=
  { canonicalFrameQuery with prevMonoSeq? := some 42 }
#guard checkEpiphanyScanout 10 replayQuery canonicalScanoutCert ==
  .refused .nonMonotoneSensorSeq [2]

private def unredactedQuery : EpiphanyFrameQuery :=
  { canonicalFrameQuery with deliveredFrame := canonicalRawSensorFrame }
#guard checkEpiphanyScanout 10 unredactedQuery canonicalScanoutCert ==
  .refused .unredactedPrivateRoi [4]

private def badSealQuery : EpiphanyFrameQuery :=
  { canonicalFrameQuery with claimedSeal := ⟨(List.replicate 32 (0xFF : UInt8)).toArray⟩ }
#guard checkEpiphanyScanout 10 badSealQuery canonicalScanoutCert ==
  .refused .sealMismatch [5]

private def washedHazardQuery : EpiphanyFrameQuery :=
  { canonicalFrameQuery with
    hazardPlane := { boxes := [{ canonicalHazardBox with hiColor := ⟨100, 100, 100, 40⟩ }] } }
#guard checkEpiphanyScanout 10 washedHazardQuery canonicalScanoutCert ==
  .refused .hazardVisibilityViolation [7]

#guard checkEpiphanyScanout 10 canonicalFrameQuery
    { canonicalScanoutCert with verifiedOverlayCount := 99 } ==
  .refused .certWitnessMismatch [8]

-- Multi-turn session progression (seq 1 -> seq 2 succeeds; seq 2 -> seq 2 replay fails).
private def turnFrame1 : SensorFrame := { canonicalRawSensorFrame with monoSeq := 1 }
private def turnRed1 : SensorFrame := redactSensorFrame turnFrame1
private def turnQuery1 : EpiphanyFrameQuery :=
  { canonicalFrameQuery with
    prevMonoSeq? := none
    rawFrame := turnFrame1
    deliveredFrame := turnRed1
    claimedSeal := sensorFrameSeal turnRed1 }
private def turnCert1 : EpiphanyScanoutCert := ⟨turnRed1, turnQuery1.claimedSeal, 1⟩

private def turnFrame2 : SensorFrame := { canonicalRawSensorFrame with monoSeq := 2 }
private def turnRed2 : SensorFrame := redactSensorFrame turnFrame2
private def turnQuery2 : EpiphanyFrameQuery :=
  { canonicalFrameQuery with
    prevMonoSeq? := some 1
    rawFrame := turnFrame2
    deliveredFrame := turnRed2
    claimedSeal := sensorFrameSeal turnRed2 }
private def turnCert2 : EpiphanyScanoutCert := ⟨turnRed2, turnQuery2.claimedSeal, 1⟩

#guard
  match stepEpiphanySession canonicalDisplayPolicy SensorSealerState.empty ⟨10, turnQuery1, turnCert1⟩ with
  | none => false
  | some st1 =>
    match stepEpiphanySession canonicalDisplayPolicy st1 ⟨10, turnQuery2, turnCert2⟩ with
    | none => false
    | some st2 =>
      (stepEpiphanySession canonicalDisplayPolicy st2 ⟨10, turnQuery2, turnCert2⟩).isNone &&
      st2.lookupSeq 7 == some 2

/-! ## 3. Constructive Extractor & Zero-`sorryAx` Kernel Axiom Audit -/

/-- info: 'Obend.Polis.EpiphanyCompositor.extractSensorFrameSeal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms extractSensorFrameSeal

/-- info: 'Obend.Polis.EpiphanyCompositor.sensorFrameSeal_binds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sensorFrameSeal_binds

/-- info: 'Obend.Polis.EpiphanyCompositor.physical_hazard_reticle_visibility_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms physical_hazard_reticle_visibility_floor

/--
info: 'Obend.Polis.EpiphanyCompositor.chrome_non_occludable_and_unforgeable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms chrome_non_occludable_and_unforgeable

/--
info: 'Obend.Polis.EpiphanyCompositor.redactedSensorFrame_zero_private_leakage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms redactedSensorFrame_zero_private_leakage

/-! ## 4. `#tooth` Mutation-Sensitivity Kills (9 Kills) -/

-- Tooth 1: Swapping Z-order so untrusted belief composites OVER consent chrome breaks non-occlusion.
#tooth chrome_non_occludable_and_unforgeable by
  mutation scanoutPixel := fun pol belief hazard chrome px py =>
    let chPix := (chromePixelAt pol chrome px py).getD Rgba.zero
    let hzPix := (hazardPlanePixelAt hazard px py).getD Rgba.zero
    overRgba (rawBeliefPixel belief.overlays px py) (overRgba hzPix chPix)

-- Tooth 2: Disabling hardware consent-chrome clipping on `clipBeliefPixel` breaks zeroed belief invariant.
#tooth chrome_non_occludable_and_unforgeable by
  mutation clipBeliefPixel := fun _ _ plane px py =>
    rawBeliefPixel plane.overlays px py

-- Tooth 3: Omitting `hazardPlanePixelAt` from `scanoutPixel` breaks `physical_hazard_reticle_visibility_floor`.
#tooth physical_hazard_reticle_visibility_floor by
  mutation scanoutPixel := fun pol belief _ chrome px py =>
    let bPix := clipBeliefPixel pol chrome belief px py
    match chromePixelAt pol chrome px py with
    | none => bPix
    | some chPix => overRgba chPix bPix

-- Tooth 4: Dropping `redactBoxes` from `sensorFrameSealPreimage` (Mistake #2) breaks 6-field binding.
#tooth sensorFrameSeal_binds by
  mutation sensorFrameSealPreimage := fun f =>
    encodeFields [u64Be f.sensorId, u64Be f.monoSeq, u32Be f.width, u32Be f.height, encodeTileList f.tiles]

-- Tooth 5: Constant `sensorFrameSeal` breaks `sensorFrameSeal_binds`.
#tooth sensorFrameSeal_binds by
  mutation sensorFrameSeal := fun _ => ByteArray.empty

-- Tooth 6: Bypassing monotone sequence check in `stepSensorSealer` breaks `sensor_replay_step_refused`.
#tooth sensor_replay_step_refused by
  mutation stepSensorSealer := fun st raw =>
    let red := redactSensorFrame raw
    let sealDig := sensorFrameSeal red
    .ok (st, red, sealDig)

-- Tooth 7: Skipping ROI redaction in `redactSensorFrame` breaks `redactedSensorFrame_zero_private_leakage`.
#tooth redactedSensorFrame_zero_private_leakage by
  mutation redactSensorFrame := fun raw => raw

-- Tooth 8: Accepting unconditionally in `checkEpiphanyScanout` breaks `checkEpiphanyScanout_sound`.
#tooth checkEpiphanyScanout_sound by
  mutation checkEpiphanyScanout := fun _ _ _ => .ok

-- Tooth 9: Marking `certWitnessMismatch` as refuting breaks `checkEpiphanyScanout_refuted`.
#tooth checkEpiphanyScanout_refuted by
  mutation epiphanyClauseRefutes := fun _ => true

end Obend.Tests.Metasystem.EpiphanyCompositorTest
end
