module
/-
# Obend.Hardware.DRC — 4-Zone FabuBlox Cleanroom Lattice, ALD/PVD Step Coverage, Litho Overlay/Undercut & GDS Cutline DRC

Extends `Obend.Hardware.FabuBlox` with deep physical design rules and cleanroom `Facility OS`
contamination laws (`fabublox.com`):

1. **4-Zone Cleanroom Contamination Lattice (`CleanroomZone`, `zoneRank`, `checkToolZoneAdmissible`)**:
   - Models the strict 4-tier cleanroom hierarchy:
     `feolCmosClean (0) < meolBarrier (1) < beolMetals (2) < nobleAndIIIV (3)`,
   - Proves `zone_monotonicity_sound`: wafer contamination rank never decreases across material
     depositions, and once a wafer enters `nobleAndIIIV` (`Au`), it is permanently barred from
     FEOL/MEOL/BEOL CMOS tools.
2. **Conformal ALD vs Directional PVD Trench Step-Coverage & Keyhole Void Checker (`checkTrenchFillVoidFree`)**:
   - Models sidewall step coverage $\eta \in [0, 100]\%$ in a trench of depth $H$ and width $W$,
   - Proves `conformal_ald_void_free` ($\eta = 100\%$ ALD $\text{HfO}_2/\text{TiN}$ fills without
     premature top pinch-off) and `pvd_high_ar_keyhole_refused` (directional PVD on a narrow deep
     via pinches off the top opening before the bottom fills).
3. **Lithography Overlay Tolerance + Isotropic/Anisotropic Etch Undercut Enclosure (`checkLithoOverlayAndUndercut`)**:
   - Proves `overlay_enclosure_prevents_short`: if a mask window $[x_L, x_R]$ satisfies the overlay
     + lateral-undercut enclosure rule inside landing pad $[p_L, p_R]$, then under ANY physical
     stepper misalignment $|\delta| \le \Delta_{\text{ovl}}$, the etched opening stays strictly inside $[p_L, p_R]$.
4. **GDS Cutline Design Rule Checker (DRC) & Parasitic RC Extraction (`checkCutlineDRC`, `extractDrcCorner`)**:
   - Proves `drc_clean_implies_min_pitch`, `drc_clean_implies_via_landed`, and
     `extracted_corner_monotone_in_oxide`.
-/
public import Obend.Hardware.FabuBlox
@[expose] public section

namespace Obend.Hardware.DRC
open Obend.Hardware.Process Obend.Hardware.FabuBlox
set_option autoImplicit false

/-! ## 1. 4-Zone FabuBlox Cleanroom Contamination Lattice (`CleanroomZone`) -/

/-- 4-tier cleanroom equipment & wafer contamination hierarchy managed by FabuBlox `Facility OS`. -/
inductive CleanroomZone where
  | feolCmosClean -- Rank 0: Si, SiO2, Si3N4, PolySi, HfO2 only
  | meolBarrier   -- Rank 1: adds Ti, TiN, W, Co
  | beolMetals    -- Rank 2: adds Al, Cu
  | nobleAndIIIV  -- Rank 3: adds Au, Pt, GaN, InP (strictly one-way!)
  deriving DecidableEq, Repr

/-- Numeric lattice rank `0 ≤ 1 ≤ 2 ≤ 3` of a `CleanroomZone`. -/
def zoneRank : CleanroomZone → Nat
  | .feolCmosClean => 0
  | .meolBarrier   => 1
  | .beolMetals    => 2
  | .nobleAndIIIV  => 3

/-- Minimum cleanroom zone required as soon as `mat` is exposed on a wafer. -/
def materialZone : FabMaterial → CleanroomZone
  | .siSubstrate => .feolCmosClean
  | .sio2        => .feolCmosClean
  | .si3n4       => .feolCmosClean
  | .hfo2        => .feolCmosClean
  | .polySi      => .feolCmosClean
  | .tiN         => .meolBarrier
  | .wPlug       => .meolBarrier
  | .alMetal     => .beolMetals
  | .cuMetal     => .beolMetals
  | .auMetal     => .nobleAndIIIV

/-- Lattice join (`⊔`) of two `CleanroomZone`s: a wafer takes the highest contamination rank of
its history and the newly introduced material. -/
def joinZone (z1 z2 : CleanroomZone) : CleanroomZone :=
  if zoneRank z1 ≥ zoneRank z2 then z1 else z2

/-- Update a wafer's contamination zone after introducing `mat`. -/
def stepWaferZone (curZone : CleanroomZone) (mat : FabMaterial) : CleanroomZone :=
  joinZone curZone (materialZone mat)

/-- Check whether a tool assigned to `toolZone` is allowed to process a wafer in `waferZone`:
A tool only accepts wafers whose contamination rank is `≤ zoneRank toolZone`. -/
def checkToolZoneAdmissible (waferZone toolZone : CleanroomZone) : Bool :=
  decide (zoneRank waferZone ≤ zoneRank toolZone)

/-- Theorem (`zone_monotonicity_sound`):
1. Stepping a wafer's zone with any material `mat` never decreases `zoneRank`
   (`zoneRank curZone ≤ zoneRank (stepWaferZone curZone mat)`), and
2. Once a wafer is exposed to gold (`FabMaterial.auMetal`), it is rejected by every FEOL, MEOL,
   and BEOL CMOS tool! -/
theorem zone_monotonicity_sound (curZone : CleanroomZone) (mat : FabMaterial) :
    zoneRank curZone ≤ zoneRank (stepWaferZone curZone mat) ∧
    checkToolZoneAdmissible (stepWaferZone curZone .auMetal) .feolCmosClean = false ∧
    checkToolZoneAdmissible (stepWaferZone curZone .auMetal) .meolBarrier = false ∧
    checkToolZoneAdmissible (stepWaferZone curZone .auMetal) .beolMetals = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [stepWaferZone, joinZone]
    by_cases h : zoneRank curZone ≥ zoneRank (materialZone mat)
    · simp [h]
    · simp only [h, ↓reduceIte]
      omega
  · cases curZone <;> rfl
  · cases curZone <;> rfl
  · cases curZone <;> rfl

/-! ## 2. Conformal ALD vs Directional PVD Trench Step Coverage & Keyhole Void Checker -/

/-- Deposition conformality profile in a trench of depth `trenchDepthNm` ($H$) and width `trenchWidthNm` ($W$):
* `stepCoveragePct` ($\eta \in [0, 100]$): ratio of sidewall/bottom deposition rate to top surface rate,
* `topCornerOverhangPct` ($\kappa \ge \eta$): bread-loafing overhang rate at the top trench corners.
When the top opening pinches shut (`2 * topCornerThickness ≥ W`) before the trench bottom fills
(`bottomThickness < H`), a trapped **keyhole void** is formed inside the dielectric/via! -/
structure TrenchFillSpec where
  trenchDepthNm        : Nat
  trenchWidthNm        : Nat
  stepCoveragePct      : Nat
  topCornerOverhangPct : Nat
  deriving DecidableEq, Repr

/-- Check that a trench fill completes without pinching off into a keyhole void:
Requires positive trench width, valid step coverage $\eta \in [1, 100]$, and that the bottom fill
rate (`stepCoveragePct * trenchWidthNm`) exceeds or matches the top corner pinch-off rate
(`2 * topCornerOverhangPct * trenchDepthNm` scaled, or $\eta = 100\%$ conformal ALD). -/
def checkTrenchFillVoidFree (spec : TrenchFillSpec) : Bool :=
  (spec.trenchWidthNm > 0) &&
  (spec.stepCoveragePct > 0) &&
  (spec.stepCoveragePct ≤ 100) &&
  ((spec.stepCoveragePct == 100 && spec.topCornerOverhangPct == 100) ||
   decide (2 * spec.topCornerOverhangPct * spec.trenchDepthNm ≤ spec.stepCoveragePct * spec.trenchWidthNm))

/-- Theorem (`conformal_ald_void_free`):
Ideal conformal Atomic Layer Deposition (`ALD`, `stepCoveragePct = 100`, `topCornerOverhangPct = 100`)
is void-free for ANY trench depth `H` and positive trench width `W > 0`. -/
theorem conformal_ald_void_free (depthNm widthNm : Nat) (hWidth : widthNm > 0) :
    checkTrenchFillVoidFree
      { trenchDepthNm := depthNm
      , trenchWidthNm := widthNm
      , stepCoveragePct := 100
      , topCornerOverhangPct := 100 } = true := by
  simp [checkTrenchFillVoidFree, hWidth]

/-- Theorem (`pvd_high_ar_keyhole_refused`):
Directional PVD sputtering (`stepCoveragePct = 20`, `topCornerOverhangPct = 60`) into a high-aspect-ratio
trench (`depth = 200 nm`, `width = 50 nm`, $\text{AR} = 4:1$) pinches off the top corners and is
refused by `checkTrenchFillVoidFree`. -/
theorem pvd_high_ar_keyhole_refused :
    checkTrenchFillVoidFree
      { trenchDepthNm := 200
      , trenchWidthNm := 50
      , stepCoveragePct := 20
      , topCornerOverhangPct := 60 } = false := by
  rfl

/-! ## 3. Lithography Overlay Tolerance & Isotropic/Anisotropic Etch Undercut Enclosure -/

/-- Lithography & etch enclosure parameters for a contact/via window `[maskLeftNm, maskRightNm]`
landing on an underlying metal/barrier pad `[padLeftNm, padRightNm]`:
* `maxOverlayErrNm` ($\Delta_{\text{ovl}}$): worst-case stepper mask-to-wafer alignment error,
* `lateralUndercutNm` ($u_{\text{lat}}$): lateral etch undercut beneath the resist edge (`0` for ideal
  anisotropic RIE, `> 0` for isotropic wet HF/BOE etch). -/
structure OverlayEnclosureSpec where
  padLeftNm         : Nat
  padRightNm        : Nat
  maskLeftNm        : Nat
  maskRightNm       : Nat
  maxOverlayErrNm   : Nat
  lateralUndercutNm : Nat
  deriving DecidableEq, Repr

/-- Verify that the mask window `[maskLeftNm, maskRightNm]` is non-empty and enclosed inside
`[padLeftNm, padRightNm]` by at least `maxOverlayErrNm + lateralUndercutNm` on both sides. -/
def checkLithoOverlayAndUndercut (s : OverlayEnclosureSpec) : Bool :=
  decide (s.maskLeftNm < s.maskRightNm) &&
  decide (s.padLeftNm + s.maxOverlayErrNm + s.lateralUndercutNm ≤ s.maskLeftNm) &&
  decide (s.maskRightNm + s.maxOverlayErrNm + s.lateralUndercutNm ≤ s.padRightNm)

/-- Theorem (`overlay_enclosure_prevents_short`):
If `checkLithoOverlayAndUndercut s = true`, then for ANY physical stepper alignment shift
`shiftLeft shiftRight : Nat` bounded by `maxOverlayErrNm` (`shiftLeft ≤ s.maxOverlayErrNm` and
`shiftRight ≤ s.maxOverlayErrNm`), the actual etched feature `[maskLeft - shiftLeft - undercut,
maskRight + shiftRight + undercut]` lands strictly within the underlying pad `[padLeftNm, padRightNm]`
(preventing borderless via substrate shorts)! -/
theorem overlay_enclosure_prevents_short
    (s : OverlayEnclosureSpec)
    (shiftLeft shiftRight : Nat)
    (hOk : checkLithoOverlayAndUndercut s = true)
    (hSL : shiftLeft ≤ s.maxOverlayErrNm)
    (hSR : shiftRight ≤ s.maxOverlayErrNm) :
    s.padLeftNm ≤ s.maskLeftNm - shiftLeft - s.lateralUndercutNm ∧
    s.maskRightNm + shiftRight + s.lateralUndercutNm ≤ s.padRightNm := by
  simp only [checkLithoOverlayAndUndercut, Bool.and_eq_true, decide_eq_true_eq] at hOk
  omega

/-! ## 4. Multi-Layer GDS Cutline DRC Checker & Parasitic RC Extraction (`checkCutlineDRC`) -/

/-- Foundry Design Rule Check (DRC) deck constraints (in nanometers). -/
structure FoundryDrcDeck where
  deckName          : String
  minMetalWidthNm   : Nat
  minMetalSpacingNm : Nat
  minViaWidthNm     : Nat
  minViaEnclosureNm : Nat
  maxResistAspect   : Nat
  deriving DecidableEq, Repr

/-- Physical layout feature candidate along a 2D GDS cutline verified against a `FoundryDrcDeck`. -/
structure CutlineDrcFeature where
  metalWidthNm     : Nat
  metalSpacingNm   : Nat
  viaWidthNm       : Nat
  viaEnclosureNm   : Nat
  resistHeightNm   : Nat
  resistOpeningNm  : Nat
  ildThicknessNm   : Nat
  deriving DecidableEq, Repr

/-- Complete GDS cutline DRC verifier checking:
1. Minimum metal line width (`metalWidthNm ≥ minMetalWidthNm`),
2. Minimum metal-to-metal spacing (`metalSpacingNm ≥ minMetalSpacingNm`),
3. Minimum via width (`viaWidthNm ≥ minViaWidthNm`),
4. Minimum metal enclosure around via (`viaEnclosureNm ≥ minViaEnclosureNm`),
5. Photoresist collapse aspect-ratio limit (`resistHeightNm ≤ maxResistAspect * resistOpeningNm`). -/
def checkCutlineDRC (deck : FoundryDrcDeck) (feat : CutlineDrcFeature) : Bool :=
  decide (deck.minMetalWidthNm ≤ feat.metalWidthNm) &&
  decide (deck.minMetalSpacingNm ≤ feat.metalSpacingNm) &&
  decide (deck.minViaWidthNm ≤ feat.viaWidthNm) &&
  decide (deck.minViaEnclosureNm ≤ feat.viaEnclosureNm) &&
  decide (feat.resistOpeningNm > 0) &&
  decide (feat.resistHeightNm ≤ deck.maxResistAspect * feat.resistOpeningNm)

/-- Theorem (`drc_clean_implies_min_pitch`):
Any layout feature that passes `checkCutlineDRC` has total metal pitch
`metalWidthNm + metalSpacingNm ≥ deck.minMetalWidthNm + deck.minMetalSpacingNm`. -/
theorem drc_clean_implies_min_pitch
    (deck : FoundryDrcDeck) (feat : CutlineDrcFeature)
    (hDrc : checkCutlineDRC deck feat = true) :
    deck.minMetalWidthNm + deck.minMetalSpacingNm ≤ feat.metalWidthNm + feat.metalSpacingNm := by
  simp only [checkCutlineDRC, Bool.and_eq_true, decide_eq_true_eq] at hDrc
  omega

/-- Theorem (`drc_clean_implies_via_landed`):
Any layout feature that passes `checkCutlineDRC` has total landing pad width
`viaWidthNm + 2 * viaEnclosureNm ≥ deck.minViaWidthNm + 2 * deck.minViaEnclosureNm`. -/
theorem drc_clean_implies_via_landed
    (deck : FoundryDrcDeck) (feat : CutlineDrcFeature)
    (hDrc : checkCutlineDRC deck feat = true) :
    deck.minViaWidthNm + 2 * deck.minViaEnclosureNm ≤ feat.metalWidthNm ∨
    deck.minViaWidthNm + 2 * deck.minViaEnclosureNm ≤ feat.viaWidthNm + 2 * feat.viaEnclosureNm := by
  simp only [checkCutlineDRC, Bool.and_eq_true, decide_eq_true_eq] at hDrc
  right
  omega

/-- Extract a parasitic-adjusted `ProcessCorner` from a DRC-verified `CutlineDrcFeature`:
Thicker interlayer dielectric (`ildThicknessNm`) reduces parallel-plate wire capacitance and lowers
wire-hop delay; wider metal lines (`metalWidthNm`) reduce sheet resistance. -/
def extractDrcCorner (base : ProcessCorner) (feat : CutlineDrcFeature) : ProcessCorner :=
  let rawReduction   := feat.ildThicknessNm / 10
  let capReductionPs := if rawReduction ≤ 40 then rawReduction else 40
  let resPenaltyPs   := if feat.metalWidthNm ≥ 100 then 0 else 25
  { base with
    tWireHopPs := (base.tWireHopPs - capReductionPs) + resPenaltyPs }

/-- Theorem (`extracted_corner_monotone_in_oxide`):
Increasing the interlayer dielectric oxide thickness (`ild1 ≤ ild2`, holding metal width fixed)
monotonically reduces or preserves the extracted wire-hop delay `tWireHopPs`! -/
theorem extracted_corner_monotone_in_oxide
    (base : ProcessCorner) (f1 f2 : CutlineDrcFeature)
    (hSameWidth : f1.metalWidthNm = f2.metalWidthNm)
    (hOxideLe   : f1.ildThicknessNm ≤ f2.ildThicknessNm) :
    (extractDrcCorner base f2).tWireHopPs ≤ (extractDrcCorner base f1).tWireHopPs := by
  have hDiv : f1.ildThicknessNm / 10 ≤ f2.ildThicknessNm / 10 := Nat.div_le_div_right hOxideLe
  simp only [extractDrcCorner, hSameWidth]
  by_cases h1 : f1.ildThicknessNm / 10 ≤ 40 <;> by_cases h2 : f2.ildThicknessNm / 10 ≤ 40 <;>
    simp only [h1, h2, ite_true, ite_false] <;> omega

end Obend.Hardware.DRC
