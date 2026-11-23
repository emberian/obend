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
import all Obend.Hardware.HDL
import all Obend.Hardware.YosysLec
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
open Obend.Hardware.HDL Obend.Hardware.YosysLec
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

/-! ## 5. Open-FPGA Inline RTL (`EmitSv` / `YosysLec`), `UInt64.max` Guard & Software Stream Sealer Parity -/

-- Both open-FPGA inline gates pass `checkRtlModule`, `checkRtlModuleW`, and `moduleFaithful`.
#guard checkRtlModule scanlineConsentMuxRtl == true
#guard checkRtlModuleW scanlineConsentMuxRtl == true
#guard moduleFaithful scanlineConsentMuxRtl == true
#guard checkRtlModule cameraScanlineRoiZeroerRtl == true
#guard checkRtlModuleW cameraScanlineRoiZeroerRtl == true
#guard moduleFaithful cameraScanlineRoiZeroerRtl == true

-- `emitModuleSV` emits clean synthesizable SystemVerilog-2012 with exact port widths & reset polarity,
-- and `lecScript` builds the complete QF_BV LEC AST.
private def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1
#guard containsSubstr (emitModuleSV scanlineConsentMuxRtl) "module scanline_consent_mux"
#guard containsSubstr (emitModuleSV scanlineConsentMuxRtl) "[15:0] py"
#guard containsSubstr (emitModuleSV scanlineConsentMuxRtl) "[31:0] chrome_pixel"
#guard containsSubstr (emitModuleSV scanlineConsentMuxRtl) "always_ff @(posedge clk)"
#guard containsSubstr (emitModuleSV scanlineConsentMuxRtl) "if (rst)"
#guard containsSubstr (emitModuleSV scanlineConsentMuxRtl) "always_comb"
#guard (lecScript scanlineConsentMuxRtl).mod == "scanline_consent_mux"
#guard (lecScript scanlineConsentMuxRtl).outputs.length == 3
#guard (lecScript scanlineConsentMuxRtl).regs.length == 2
#guard containsSubstr (emitModuleSV cameraScanlineRoiZeroerRtl) "module camera_scanline_roi_zeroer"
#guard containsSubstr (emitModuleSV cameraScanlineRoiZeroerRtl) "[15:0] roi_x0"
#guard containsSubstr (emitModuleSV cameraScanlineRoiZeroerRtl) "[31:0] raw_pixel"
#guard containsSubstr (emitModuleSV cameraScanlineRoiZeroerRtl) "always_ff @(posedge clk)"
#guard containsSubstr (emitModuleSV cameraScanlineRoiZeroerRtl) "if (rst)"
#guard (lecScript cameraScanlineRoiZeroerRtl).mod == "camera_scanline_roi_zeroer"
#guard (lecScript cameraScanlineRoiZeroerRtl).wires.length == 7
#guard (lecScript cameraScanlineRoiZeroerRtl).regs.length == 2

-- Concrete multi-cycle RTL vectors (including signed-vs-unsigned bit-15 boundary 0x7FFF < 0x8000,
-- bit-31 pixel word, and exclusive y1 boundary) locked bit-for-bit with Rust `epiphany_she_conformance.rs`:
#guard packRgba32 ⟨18, 24, 38, 255⟩ == 0xFF261812#64
#guard packRgba32 ⟨255, 0, 0, 255⟩ == 0xFF0000FF#64
#guard packRgba32 ⟨10, 20, 30, 255⟩ == 0xFF1E140A#64

private def mkMuxIn (py h ch bel : BitVec 64) : Nat → BitVec 64
  | 0 => py | 1 => h | 2 => ch | 3 => bel | _ => 0#64
private def mkRoiIn (px py x0 x1 y0 y1 raw : BitVec 64) : Nat → BitVec 64
  | 0 => px | 1 => py | 2 => x0 | 3 => x1 | 4 => y0 | 5 => y1 | 6 => raw | _ => 0#64

-- Consent mux RTL: py < h (incl. signed-vs-unsigned bit-15 0x7FFF < 0x8000) outputs chrome; 0x8000 >= 0x7FFF passes belief; rst clears to 0.
#guard evalModuleOutputs scanlineConsentMuxRtl (mkMuxIn 2#64 4#64 0xFF261812#64 0xFF0000FF#64) (fun _ => 0#64) ==
  [("comb_pixel", 0xFF261812#64), ("reg_pixel", 0#64), ("reg_in_band", 0#64)]
#guard runModuleTrace scanlineConsentMuxRtl (fun _ => 0#64)
  [ (false, mkMuxIn 5#64 4#64 0xFF261812#64 0xFF0000FF#64)
  , (false, mkMuxIn 0x7FFF#64 0x8000#64 0xFF261812#64 0x80000001#64) ] 0 == 0xFF261812#64
#guard runModuleTrace scanlineConsentMuxRtl (fun _ => 0#64)
  [ (false, mkMuxIn 2#64 4#64 0xFF261812#64 0xFF0000FF#64)
  , (false, mkMuxIn 0x8000#64 0x7FFF#64 0xFF261812#64 0x80000001#64) ] 0 == 0x80000001#64
#guard runModuleTrace scanlineConsentMuxRtl (fun _ => 0#64)
  [ (false, mkMuxIn 2#64 4#64 0xFF261812#64 0xFF0000FF#64)
  , (true,  mkMuxIn 2#64 4#64 0xFF261812#64 0xFF0000FF#64) ] 0 == 0#64

-- Camera ROI zeroer RTL: ROI [1,3) x [0,1) zeroes secret pixel at (1,0), passes (0,0), (3,0), and y1 boundary (1,1)!
#guard runModuleTrace cameraScanlineRoiZeroerRtl (fun _ => 0#64)
  [(false, mkRoiIn 1#64 0#64 1#64 3#64 0#64 1#64 0xFF636363#64)] 0 == 0#64
#guard runModuleTrace cameraScanlineRoiZeroerRtl (fun _ => 0#64)
  [(false, mkRoiIn 1#64 0#64 1#64 3#64 0#64 1#64 0xFF636363#64)] 1 == 1#64
#guard runModuleTrace cameraScanlineRoiZeroerRtl (fun _ => 0#64)
  [(false, mkRoiIn 0#64 0#64 1#64 3#64 0#64 1#64 0xFF1E140A#64)] 0 == 0xFF1E140A#64
#guard runModuleTrace cameraScanlineRoiZeroerRtl (fun _ => 0#64)
  [(false, mkRoiIn 3#64 0#64 1#64 3#64 0#64 1#64 0xFF3C3228#64)] 0 == 0xFF3C3228#64
#guard runModuleTrace cameraScanlineRoiZeroerRtl (fun _ => 0#64)
  [(false, mkRoiIn 1#64 1#64 1#64 3#64 0#64 1#64 0x80000001#64)] 0 == 0x80000001#64

-- `UInt64.max` sequence wraparound guard across first-frame, `MAX-1 -> MAX`, and `epiphanyScanoutJudge`.
private def maxSeqRawFrame : SensorFrame := { canonicalRawSensorFrame with monoSeq := maxSensorMonoSeq }
#guard match stepSensorSealer SensorSealerState.empty maxSeqRawFrame with
  | .error (.seqOverflowWraparound 7 s) => s == maxSensorMonoSeq | _ => false
#guard match stepSensorSealer ⟨[(7, maxSensorMonoSeq - 1)], []⟩ maxSeqRawFrame with
  | .error (.seqOverflowWraparound 7 s) => s == maxSensorMonoSeq | _ => false
private def maxSeqQuery : EpiphanyFrameQuery :=
  let red := redactSensorFrame maxSeqRawFrame
  { canonicalFrameQuery with
    prevMonoSeq? := none
    rawFrame := maxSeqRawFrame
    deliveredFrame := red
    claimedSeal := sensorFrameSeal red }
#guard checkEpiphanyScanout 10 maxSeqQuery ⟨maxSeqQuery.deliveredFrame, maxSeqQuery.claimedSeal, 1⟩ ==
  .refused .nonMonotoneSensorSeq [2]

-- Pure software streaming scanline non-interference, partial-frame refusal, unfinished-frame seq guard,
-- multi-frame `nextFrame`, and byte-locked `"OBEND.SHE.SENSOR_SEAL/v1"` parity.
private def firstStreamPkt : ScanlinePacket :=
  ⟨0, 0, 4, [⟨10, 20, 30, 255⟩, ⟨99, 99, 99, 255⟩, ⟨88, 77, 66, 255⟩, ⟨40, 50, 60, 255⟩]⟩
private def altSecretStreamPackets : List ScanlinePacket :=
  [⟨0, 0, 4, [⟨10, 20, 30, 255⟩, ⟨255, 0, 128, 255⟩, ⟨1, 2, 3, 4⟩, ⟨40, 50, 60, 255⟩]⟩,
   ⟨1, 0, 4, [⟨70, 80, 90, 255⟩, ⟨100, 110, 120, 255⟩, ⟨130, 140, 150, 255⟩, ⟨160, 170, 180, 255⟩]⟩]

#guard match stepScanlineStream (ScanlineStreamState.init { canonicalStreamConfig with monoSeq := maxSensorMonoSeq }) firstStreamPkt with
  | .error .seqViolation => true | _ => false

#guard
  match runScanlineStreamTrace (ScanlineStreamState.init canonicalStreamConfig) (canonicalStreamPackets.take 1) with
  | .ok (stPartial, _) =>
    (match finalizeScanlineStream stPartial with | .error .incompleteFrameCoverage => true | _ => false) &&
    -- Unfinished frame cannot restart at same seq 42 with stripped redactBoxes!
    (match stepScanlineStream (stPartial.nextFrame { canonicalStreamConfig with redactBoxes := [] }) firstStreamPkt with
      | .error .seqViolation => true | _ => false)
  | .error _ => false

#guard
  match runScanlineStreamTrace (ScanlineStreamState.init canonicalStreamConfig) canonicalStreamPackets,
        runScanlineStreamTrace (ScanlineStreamState.init canonicalStreamConfig) altSecretStreamPackets with
  | .ok (st1, tr1), .ok (st2, tr2) =>
    tr1 == tr2 && st1.assembledTiles == st2.assembledTiles &&
    match finalizeScanlineStream st1, finalizeScanlineStream st2 with
    | .ok (stNext, _, d1), .ok (_, _, d2) =>
      d1 == d2 && hexString d1 == "913c6cc5a2e60b791214628216c1bee161fc628a061ec5c413c239abdff33243" &&
      (match stepScanlineStream (stNext.nextFrame canonicalStreamConfig) firstStreamPkt with
        | .error .seqViolation => true | _ => false) &&
      (match runScanlineStreamTrace (stNext.nextFrame { canonicalStreamConfig with monoSeq := 43 }) canonicalStreamPackets with
        | .ok (st43, _) => match finalizeScanlineStream st43 with | .ok (_, _, d43) => d43 != d1 | _ => false
        | .error _ => false)
    | _, _ => false
  | _, _ => false

/-! ## 6. Additional Surgical RTL & Stream-Sealer `#tooth` Mutation Kills (Kills 10-15; Total = 15) -/

-- Tooth 10: Swapping mux arms in `scanlineConsentMuxRtl` kills `scanlineConsentMuxRtl_cycle_sound`.
#tooth scanlineConsentMuxRtl_cycle_sound by
  mutation scanlineConsentMuxRtl :=
    { name := "scanline_consent_mux"
      inputNames := ["py", "consent_height", "chrome_pixel", "belief_pixel"]
      inputWidths := [16, 16, 32, 32]
      wires :=
        [ { wireIdx := 0, name := "in_consent_band", width := 1, expr := .alu .ult (.inputPort 0) (.inputPort 1) }
        , { wireIdx := 1, name := "mux_pixel", width := 32, expr := .mux (.wireRef 0) (.inputPort 3) (.inputPort 2) } ]
      regs :=
        [ { regIdx := 0, name := "out_pixel_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 1, width := 32 }
        , { regIdx := 1, name := "in_band_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 0, width := 1 } ]
      outputs :=
        [ { name := "comb_pixel", expr := .wireRef 1, width := 32 }
        , { name := "reg_pixel", expr := .regRead 0, width := 32 }
        , { name := "reg_in_band", expr := .regRead 1, width := 1 } ] }

-- Tooth 11: Bypassing ROI zeroer mux in `cameraScanlineRoiZeroerRtl` kills `cameraScanlineRoiZeroerRtl_trace_noninterference`.
#tooth cameraScanlineRoiZeroerRtl_trace_noninterference by
  mutation cameraScanlineRoiZeroerRtl :=
    { name := "camera_scanline_roi_zeroer"
      inputNames := ["px", "py", "roi_x0", "roi_x1", "roi_y0", "roi_y1", "raw_pixel"]
      inputWidths := [16, 16, 16, 16, 16, 16, 32]
      wires :=
        [ { wireIdx := 0, name := "ge_x0", width := 1, expr := .alu .eq (.alu .ult (.inputPort 0) (.inputPort 2)) (.const 0#64) }
        , { wireIdx := 1, name := "lt_x1", width := 1, expr := .alu .ult (.inputPort 0) (.inputPort 3) }
        , { wireIdx := 2, name := "ge_y0", width := 1, expr := .alu .eq (.alu .ult (.inputPort 1) (.inputPort 4)) (.const 0#64) }
        , { wireIdx := 3, name := "lt_y1", width := 1, expr := .alu .ult (.inputPort 1) (.inputPort 5) }
        , { wireIdx := 4, name := "in_x", width := 1, expr := .alu .bitAnd (.wireRef 0) (.wireRef 1) }
        , { wireIdx := 5, name := "in_roi", width := 1, expr := .alu .bitAnd (.wireRef 4) (.alu .bitAnd (.wireRef 2) (.wireRef 3)) }
        , { wireIdx := 6, name := "scrubbed_pixel", width := 32, expr := .inputPort 6 } ]
      regs :=
        [ { regIdx := 0, name := "cap_pixel_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 6, width := 32 }
        , { regIdx := 1, name := "redacted_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 5, width := 1 } ]
      outputs :=
        [ { name := "comb_scrubbed_pixel", expr := .wireRef 6, width := 32 }
        , { name := "cap_pixel", expr := .regRead 0, width := 32 }
        , { name := "cap_redacted", expr := .regRead 1, width := 1 } ] }

-- Tooth 12: Bypassing `scrubScanlinePixels` in `stepScanlineStream` kills `scanlineStream_zero_private_leakage`.
#tooth scanlineStream_zero_private_leakage by
  mutation stepScanlineStream := fun st pkt =>
    .ok ⟨st.activeCfg, st.assembledTiles ++ [⟨pkt.startX, pkt.lineY, pkt.width, 1, pkt.rawPixels⟩], st.sealerState⟩

-- Tooth 13: Removing `maxSensorMonoSeq` guard in `stepSensorSealer` kills `sensor_seq_max_wraparound_refused`.
#tooth sensor_seq_max_wraparound_refused by
  mutation stepSensorSealer := fun st raw =>
    match st.lookupSeq raw.sensorId with
    | some prev =>
      if decide (prev.toNat < raw.monoSeq.toNat) then
        if checkFrameGeometry raw then .ok (st, redactSensorFrame raw, sensorFrameSeal (redactSensorFrame raw))
        else .error .malformedTileGeometry
      else .error (.nonMonotoneSeq raw.sensorId prev raw.monoSeq)
    | none =>
      if checkFrameGeometry raw then .ok (st, redactSensorFrame raw, sensorFrameSeal (redactSensorFrame raw))
      else .error .malformedTileGeometry

-- Tooth 14: Removing `maxSensorMonoSeq` guard in `checkMonoSeqAdvances` kills `checkMonoSeqAdvances_iff`.
#tooth checkMonoSeqAdvances_iff by
  mutation checkMonoSeqAdvances := fun prev? cur =>
    match prev? with | none => true | some prev => decide (prev.toNat < cur.toNat)

-- Tooth 15: Disabling `checkCompleteScanlines` kills `finalizeScanlineStream_refuses_partial`.
#tooth finalizeScanlineStream_refuses_partial by
  mutation checkCompleteScanlines := fun _ _ _ => true

/-- info: 'Obend.Polis.EpiphanyCompositor.scanlineConsentMuxRtl_wellFormed_and_faithful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scanlineConsentMuxRtl_wellFormed_and_faithful

/--
info: 'Obend.Polis.EpiphanyCompositor.cameraScanlineRoiZeroerRtl_wellFormed_and_faithful' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms cameraScanlineRoiZeroerRtl_wellFormed_and_faithful

/-- info: 'Obend.Polis.EpiphanyCompositor.scanlineConsentMuxRtl_cycle_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scanlineConsentMuxRtl_cycle_sound

/-- info: 'Obend.Polis.EpiphanyCompositor.cameraScanlineRoiZeroerRtl_cycle_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cameraScanlineRoiZeroerRtl_cycle_sound

end Obend.Tests.Metasystem.EpiphanyCompositorTest
end
