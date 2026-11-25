module
/-
# Obend.Polis.EpiphanyCompositor — Open-FPGA Inline Scanline/ROI RTL & Software Sensor Sealer
1. **Pure Software Three-Plane Scanout & `OBEND.SHE.SENSOR_SEAL/v1`**: `[0, 255]` Porter-Duff `over`
   (`chrome_non_occludable_and_unforgeable`, `physical_hazard_reticle_visibility_floor`), 6-field
   `cSHAKE256` commitment (`sensorFrameSeal_binds`, `redactedSensorFrame_zero_private_leakage`),
   monotone + `UInt64.max`-guarded streaming scanline sealer (`scanlineStream_zero_private_leakage`),
   and `epiphanyScanoutJudge` (`validEpiphanySessionTrace_sound`).
2. **Synthesizable Open-FPGA Inline Scanline & ROI Gates (`Obend.Hardware.HDL.RtlModule`)**:
   Clock-synchronous `scanlineConsentMuxRtl` and `cameraScanlineRoiZeroerRtl` verified with
   `checkRtlModuleW = true`, `YosysLec.moduleFaithful = true`, `emitModuleSV`, and cycle-exact
   multi-cycle non-occlusion / pre-capture zero-leakage proofs (`scanlineConsentMuxRtl_cycle_sound`,
   `cameraScanlineRoiZeroerRtl_trace_noninterference`). External display/camera links are untrusted I/O. -/
public import Obend.Crypto.Transcript
public import Obend.Hardware.HDL
public import Obend.Hardware.YosysLec
public import Obend.Judge.Class
public import Obend.Vault.FrustumMembrane
import all Obend.Vault.FrustumMembrane
public section
namespace Obend.Polis.EpiphanyCompositor
open Obend.Crypto Obend.Digest.Cshake256 Obend.Digest.HashBytes
open Obend.Hardware.HDL Obend.Hardware.YosysLec
open Obend.Vault.FrustumMembrane (CellId World Reach)
set_option autoImplicit false

/-! ## 1. Fixed-Width RGBA Pixels, Viewport Rects & `[0, 255]` Porter-Duff `over` Compositing -/
structure Rgba where (r g b a : UInt8) deriving DecidableEq, Repr
@[expose] def Rgba.zero : Rgba := ⟨0, 0, 0, 0⟩
@[expose] def Rgba.opaqueWhite : Rgba := ⟨255, 255, 255, 255⟩
/-- Half-open discrete viewport rectangle `[x, x + w) × [y, y + h)`. -/
structure Rect where (x y w h : UInt32) deriving DecidableEq, Repr
def Rect.contains (rect : Rect) (px py : Nat) : Bool :=
  decide (rect.x.toNat ≤ px ∧ px < rect.x.toNat + rect.w.toNat ∧ rect.y.toNat ≤ py ∧ py < rect.y.toNat + rect.h.toNat)
def Rect.intersects (a b : Rect) : Bool :=
  decide (0 < a.w.toNat ∧ 0 < a.h.toNat ∧ 0 < b.w.toNat ∧ 0 < b.h.toNat ∧
    a.x.toNat < b.x.toNat + b.w.toNat ∧ b.x.toNat < a.x.toNat + a.w.toNat ∧
    a.y.toNat < b.y.toNat + b.h.toNat ∧ b.y.toNat < a.y.toNat + a.h.toNat)
theorem Rect.disjoint_of_intersects_false {a b : Rect} (hDisj : a.intersects b = false)
    {px py : Nat} (ha : a.contains px py = true) : b.contains px py = false := by
  cases hb : b.contains px py with
  | false => rfl
  | true =>
    have haP := of_decide_eq_true ha; have hbP := of_decide_eq_true hb
    have hInt : a.intersects b = true := decide_eq_true (by omega); rw [hInt] at hDisj; cases hDisj
@[expose] def blendChannel (sc dc sa : Nat) : Nat := (sc * sa + dc * (255 - sa)) / 255
@[expose] def blendAlpha (sa da : Nat) : Nat := sa + (da * (255 - sa)) / 255
/-- Exact `[0, 255]` Porter-Duff `over` operator (`src` composited over `dst`). -/
@[expose] def overRgba (src dst : Rgba) : Rgba :=
  let sa := src.a.toNat
  ⟨UInt8.ofNat (blendChannel src.r.toNat dst.r.toNat sa), UInt8.ofNat (blendChannel src.g.toNat dst.g.toNat sa),
   UInt8.ofNat (blendChannel src.b.toNat dst.b.toNat sa), UInt8.ofNat (blendAlpha sa dst.a.toNat)⟩
/-- Integer BT.601 luminance in `[0, 255]` (`77 + 150 + 29 = 256`). -/
@[expose] def pixelLuma (p : Rgba) : Nat := (77 * p.r.toNat + 150 * p.g.toNat + 29 * p.b.toNat) / 256
theorem blendChannel_le_255 {sc dc sa : Nat} (hsc : sc ≤ 255) (hdc : dc ≤ 255) (hsa : sa ≤ 255) : blendChannel sc dc sa ≤ 255 := by
  unfold blendChannel; have h1 := Nat.mul_le_mul_right sa hsc; have h2 := Nat.mul_le_mul_right (255 - sa) hdc
  exact Nat.le_trans (Nat.div_le_div_right (by omega : sc * sa + dc * (255 - sa) ≤ 255 * 255)) (by decide)
theorem blendAlpha_le_255 {sa da : Nat} (hsa : sa ≤ 255) (hda : da ≤ 255) : blendAlpha sa da ≤ 255 := by
  unfold blendAlpha
  have hdiv : (da * (255 - sa)) / 255 ≤ 255 - sa :=
    Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_right (255 - sa) hda)) (Nat.le_of_eq (Nat.mul_div_right (255 - sa) (by decide)))
  omega
private theorem uint8_ofNat_toNat_le {n : Nat} (hn : n ≤ 255) : (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat']; have h8 : (2 : Nat) ^ 8 = 256 := (by decide); rw [h8]; exact Nat.mod_eq_of_lt (by omega)
private theorem uint8_le_255 (b : UInt8) : b.toNat ≤ 255 := by
  have h := b.toBitVec.isLt; change b.toNat < 2 ^ 8 at h; omega
private theorem overRgba_channels (src dst : Rgba) :
    (overRgba src dst).r.toNat = blendChannel src.r.toNat dst.r.toNat src.a.toNat ∧
    (overRgba src dst).g.toNat = blendChannel src.g.toNat dst.g.toNat src.a.toNat ∧
    (overRgba src dst).b.toNat = blendChannel src.b.toNat dst.b.toNat src.a.toNat := by
  have hsa := uint8_le_255 src.a
  exact ⟨uint8_ofNat_toNat_le (blendChannel_le_255 (uint8_le_255 src.r) (uint8_le_255 dst.r) hsa),
    uint8_ofNat_toNat_le (blendChannel_le_255 (uint8_le_255 src.g) (uint8_le_255 dst.g) hsa),
    uint8_ofNat_toNat_le (blendChannel_le_255 (uint8_le_255 src.b) (uint8_le_255 dst.b) hsa)⟩
theorem overRgba_opaque {src : Rgba} (hOpaque : src.a = 255) (dst : Rgba) : overRgba src dst = src := by
  have hsa : src.a.toNat = 255 := by rw [hOpaque]; decide
  have hch : ∀ c d : Nat, blendChannel c d 255 = c := fun c _ => by
    unfold blendChannel; simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact Nat.mul_div_left c (by decide)
  have hal : ∀ d : Nat, blendAlpha 255 d = 255 := fun _ => by unfold blendAlpha; simp
  cases src with | mk r g b a =>
    simp only [overRgba]; simp only [hsa] at hOpaque ⊢; rw [hch, hch, hch, hal]; simp only [UInt8.ofNat_toNat]
    congr 1; exact UInt8.toNat_inj.mp hsa.symm
theorem overRgba_transparent {src : Rgba} (hZero : src.a = 0) (dst : Rgba) : overRgba src dst = dst := by
  have hsa : src.a.toNat = 0 := by rw [hZero]; decide
  have hch : ∀ c d : Nat, blendChannel c d 0 = d := fun _ d => by
    unfold blendChannel; simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_zero]; exact Nat.mul_div_left d (by decide)
  have hal : ∀ d : Nat, blendAlpha 0 d = d := fun d => by
    unfold blendAlpha; simp only [Nat.zero_add, Nat.sub_zero]; exact Nat.mul_div_left d (by decide)
  cases dst; simp only [overRgba, hsa, hch, hal, UInt8.ofNat_toNat]
theorem overRgba_alpha_ge_src (src dst : Rgba) : src.a.toNat ≤ (overRgba src dst).a.toNat := by
  have hle := blendAlpha_le_255 (uint8_le_255 src.a) (uint8_le_255 dst.a)
  simp only [overRgba, uint8_ofNat_toNat_le hle]; unfold blendAlpha; omega
theorem blendChannel_mono_dst {sc dc₁ dc₂ sa : Nat} (hle : dc₁ ≤ dc₂) : blendChannel sc dc₁ sa ≤ blendChannel sc dc₂ sa :=
  Nat.div_le_div_right (Nat.add_le_add_left (Nat.mul_le_mul_right (255 - sa) hle) (sc * sa))
theorem pixelLuma_mono {p q : Rgba} (hr : p.r.toNat ≤ q.r.toNat) (hg : p.g.toNat ≤ q.g.toNat) (hb : p.b.toNat ≤ q.b.toNat) :
    pixelLuma p ≤ pixelLuma q := by unfold pixelLuma; apply Nat.div_le_div_right; omega
theorem pixelLuma_overRgba_ge_zero (src bg : Rgba) : pixelLuma (overRgba src Rgba.zero) ≤ pixelLuma (overRgba src bg) := by
  obtain ⟨hr0, hg0, hb0⟩ := overRgba_channels src Rgba.zero; obtain ⟨hr1, hg1, hb1⟩ := overRgba_channels src bg
  have hz : Rgba.zero.r.toNat = 0 ∧ Rgba.zero.g.toNat = 0 ∧ Rgba.zero.b.toNat = 0 := by decide
  exact pixelLuma_mono (by rw [hr0, hr1, hz.1]; exact blendChannel_mono_dst (Nat.zero_le _))
    (by rw [hg0, hg1, hz.2.1]; exact blendChannel_mono_dst (Nat.zero_le _))
    (by rw [hb0, hb1, hz.2.2]; exact blendChannel_mono_dst (Nat.zero_le _))
theorem pixelLuma_overRgba_le_white (src bg : Rgba) : pixelLuma (overRgba src bg) ≤ pixelLuma (overRgba src Rgba.opaqueWhite) := by
  obtain ⟨hr0, hg0, hb0⟩ := overRgba_channels src bg; obtain ⟨hr1, hg1, hb1⟩ := overRgba_channels src Rgba.opaqueWhite
  have hw : Rgba.opaqueWhite.r.toNat = 255 ∧ Rgba.opaqueWhite.g.toNat = 255 ∧ Rgba.opaqueWhite.b.toNat = 255 := by decide
  exact pixelLuma_mono (by rw [hr0, hr1, hw.1]; exact blendChannel_mono_dst (uint8_le_255 bg.r))
    (by rw [hg0, hg1, hw.2.1]; exact blendChannel_mono_dst (uint8_le_255 bg.g))
    (by rw [hb0, hb1, hw.2.2]; exact blendChannel_mono_dst (uint8_le_255 bg.b))

/-! ## 2. Three-Plane Hardware Scanout, `ViewNode` Belief Clipper & Non-Occlusion / Visibility -/
structure EpiphanyDisplayPolicy where
  (viewportW viewportH consentBandHeight borderMargin : UInt32) (minHazardAlpha : UInt8) (minContrastFloor : Nat)
  deriving DecidableEq, Repr
structure ValidDisplayPolicy (pol : EpiphanyDisplayPolicy) : Prop where
  (posWidth : 0 < pol.viewportW.toNat) (posConsentBand : 0 < pol.consentBandHeight.toNat)
  (bandFitsHeight : pol.consentBandHeight.toNat + pol.borderMargin.toNat < pol.viewportH.toNat)
  (marginFitsWidth : 2 * pol.borderMargin.toNat < pol.viewportW.toNat)
  (posHazardAlpha : 0 < pol.minHazardAlpha.toNat) (posContrast : 0 < pol.minContrastFloor)
def checkDisplayPolicy (pol : EpiphanyDisplayPolicy) : Bool :=
  decide (0 < pol.viewportW.toNat ∧ 0 < pol.consentBandHeight.toNat ∧
    pol.consentBandHeight.toNat + pol.borderMargin.toNat < pol.viewportH.toNat ∧
    2 * pol.borderMargin.toNat < pol.viewportW.toNat ∧ 0 < pol.minHazardAlpha.toNat ∧ 0 < pol.minContrastFloor)
theorem checkDisplayPolicy_iff (pol : EpiphanyDisplayPolicy) : checkDisplayPolicy pol = true ↔ ValidDisplayPolicy pol := by
  unfold checkDisplayPolicy; simp only [decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩, fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩
def trustedConsentBandRect (pol : EpiphanyDisplayPolicy) : Rect := ⟨0, 0, pol.viewportW, pol.consentBandHeight⟩
def inTrustedConsentBand (pol : EpiphanyDisplayPolicy) (px py : Nat) : Bool :=
  decide (px < pol.viewportW.toNat ∧ py < pol.viewportH.toNat ∧
    (py < pol.consentBandHeight.toNat ∨ px < pol.borderMargin.toNat ∨ py < pol.borderMargin.toNat ∨
     pol.viewportW.toNat ≤ px + pol.borderMargin.toNat ∨ pol.viewportH.toNat ≤ py + pol.borderMargin.toNat))
structure TrustedConsentChromePlane where
  (bannerColor : Rgba) (sensorLedRect : Rect) (sensorLedActive : Bool) (sensorLedColor : Rgba)
  (modalRect? : Option Rect) (modalColor : Rgba) (quorumPromptDigest : ByteArray)
  deriving DecidableEq, Repr
structure OpaqueConsentChrome (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane) : Prop where
  (bannerOpaque : chrome.bannerColor.a = 255) (ledOpaque : chrome.sensorLedColor.a = 255) (modalOpaque : chrome.modalColor.a = 255)
  (ledInBand : chrome.sensorLedRect.y.toNat + chrome.sensorLedRect.h.toNat ≤ pol.consentBandHeight.toNat)
  (ledNonEmpty : 0 < chrome.sensorLedRect.w.toNat ∧ 0 < chrome.sensorLedRect.h.toNat) (digestWidth : chrome.quorumPromptDigest.size = 32)
def checkOpaqueConsentChrome (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane) : Bool :=
  decide (chrome.bannerColor.a = 255 ∧ chrome.sensorLedColor.a = 255 ∧ chrome.modalColor.a = 255 ∧
    chrome.sensorLedRect.y.toNat + chrome.sensorLedRect.h.toNat ≤ pol.consentBandHeight.toNat ∧
    0 < chrome.sensorLedRect.w.toNat ∧ 0 < chrome.sensorLedRect.h.toNat ∧ chrome.quorumPromptDigest.size = 32)
theorem checkOpaqueConsentChrome_iff (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane) :
    checkOpaqueConsentChrome pol chrome = true ↔ OpaqueConsentChrome pol chrome := by
  unfold checkOpaqueConsentChrome; simp only [decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, ⟨h5, h6⟩, h7⟩,
    fun ⟨h1, h2, h3, h4, ⟨h5, h6⟩, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
def inConsentChromeRegion (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane) (px py : Nat) : Bool :=
  inTrustedConsentBand pol px py ||
    match chrome.modalRect? with
    | none => false | some mr => mr.contains px py && decide (px < pol.viewportW.toNat ∧ py < pol.viewportH.toNat)
def chromePixelAt (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane) (px py : Nat) : Option Rgba :=
  if inConsentChromeRegion pol chrome px py then
    if chrome.sensorLedActive && chrome.sensorLedRect.contains px py then some chrome.sensorLedColor
    else match chrome.modalRect? with
      | some mr => if mr.contains px py then some chrome.modalColor else some chrome.bannerColor
      | none => some chrome.bannerColor
  else none
theorem chromePixelAt_eq_none_of_outside (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane) {px py : Nat}
    (hOut : inConsentChromeRegion pol chrome px py = false) : chromePixelAt pol chrome px py = none := by
  simp [chromePixelAt, hOut]
theorem chromePixelAt_opaque_of_inside {pol : EpiphanyDisplayPolicy} {chrome : TrustedConsentChromePlane}
    (hOpaque : OpaqueConsentChrome pol chrome) {px py : Nat} (hIn : inConsentChromeRegion pol chrome px py = true) :
    ∃ chPix : Rgba, chromePixelAt pol chrome px py = some chPix ∧ chPix.a = 255 := by
  unfold chromePixelAt; rw [hIn]; simp only [↓reduceIte]
  cases hLed : (chrome.sensorLedActive && chrome.sensorLedRect.contains px py)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases chrome.modalRect? with
    | none => exact ⟨chrome.bannerColor, rfl, hOpaque.bannerOpaque⟩
    | some mr => dsimp only; cases mr.contains px py with | false => exact ⟨chrome.bannerColor, rfl, hOpaque.bannerOpaque⟩ | true => exact ⟨chrome.modalColor, rfl, hOpaque.modalOpaque⟩
  · simp only [↓reduceIte]; exact ⟨chrome.sensorLedColor, rfl, hOpaque.ledOpaque⟩
inductive BeliefSurfaceKind where
  | text | pillBadge | sectionPanel | tileSurface | hostPortal | interactiveControl deriving DecidableEq, Repr
structure BeliefViewOverlay where
  (cellId : CellId) (kind : BeliefSurfaceKind) (rect : Rect) (fill : Rgba) deriving DecidableEq, Repr
structure UntrustedBeliefPlane where (overlays : List BeliefViewOverlay) deriving DecidableEq, Repr
def scrubBeliefPlane (w : World) (viewer : CellId) (plane : UntrustedBeliefPlane) : UntrustedBeliefPlane :=
  { overlays := plane.overlays.filter (fun ov => w.canObserve viewer ov.cellId) }
theorem frustum_unreachable_belief_scrubbed (w : World) (viewer : CellId) (plane : UntrustedBeliefPlane)
    (ov : BeliefViewOverlay) (hUnreach : ¬ Reach w viewer ov.cellId) : ov ∉ (scrubBeliefPlane w viewer plane).overlays :=
  fun hMem => hUnreach (Obend.Vault.FrustumMembrane.canObserve_iff.mp (List.mem_filter.mp hMem).2)
def overlayBadBounds (pol : EpiphanyDisplayPolicy) (r : Rect) : Bool :=
  decide (r.x.toNat < pol.borderMargin.toNat ∨ r.y.toNat < pol.consentBandHeight.toNat ∨
    r.y.toNat < pol.borderMargin.toNat ∨ pol.viewportW.toNat < r.x.toNat + r.w.toNat + pol.borderMargin.toNat ∨
    pol.viewportH.toNat < r.y.toNat + r.h.toNat + pol.borderMargin.toNat)
def overlayBadModal (chrome : TrustedConsentChromePlane) (r : Rect) : Bool :=
  match chrome.modalRect? with | none => false | some mr => r.intersects mr
def overlayIntrudesChrome (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane) (ov : BeliefViewOverlay) : Bool :=
  if ov.rect.w == 0 || ov.rect.h == 0 then false else overlayBadBounds pol ov.rect || overlayBadModal chrome ov.rect
def anyOverlayIntrudesChrome (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane)
    (overlays : List BeliefViewOverlay) : Bool := overlays.any (overlayIntrudesChrome pol chrome)
theorem overlayIntrudesChrome_false_disjoint {pol : EpiphanyDisplayPolicy} {chrome : TrustedConsentChromePlane}
    {ov : BeliefViewOverlay} (hSafe : overlayIntrudesChrome pol chrome ov = false)
    {px py : Nat} (hCont : ov.rect.contains px py = true) : inConsentChromeRegion pol chrome px py = false := by
  have hContProp := of_decide_eq_true hCont
  have hwPos : (ov.rect.w == 0) = false := by
    cases h : (ov.rect.w == 0) with | false => rfl | true => have hz : ov.rect.w.toNat = 0 := (by rw [beq_iff_eq.mp h]; decide); omega
  have hhPos : (ov.rect.h == 0) = false := by
    cases h : (ov.rect.h == 0) with | false => rfl | true => have hz : ov.rect.h.toNat = 0 := (by rw [beq_iff_eq.mp h]; decide); omega
  unfold overlayIntrudesChrome at hSafe; rw [hwPos, hhPos] at hSafe
  obtain ⟨hBounds, hModal⟩ := Bool.or_eq_false_iff.mp hSafe
  have hBoundsProp := decide_eq_false_iff_not.mp hBounds
  have hNoBand : inTrustedConsentBand pol px py = false := decide_eq_false (by omega)
  unfold inConsentChromeRegion; rw [hNoBand, Bool.false_or]
  cases hmr : chrome.modalRect? with
  | none => rfl
  | some mr => unfold overlayBadModal at hModal; rw [hmr] at hModal; dsimp only; rw [Rect.disjoint_of_intersects_false hModal hCont, Bool.false_and]
def rawBeliefPixel (overlays : List BeliefViewOverlay) (px py : Nat) : Rgba :=
  overlays.foldl (fun acc ov => if ov.rect.contains px py then overRgba ov.fill acc else acc) Rgba.zero
def clipBeliefPixel (pol : EpiphanyDisplayPolicy) (chrome : TrustedConsentChromePlane)
    (plane : UntrustedBeliefPlane) (px py : Nat) : Rgba :=
  if inConsentChromeRegion pol chrome px py then Rgba.zero else rawBeliefPixel plane.overlays px py
structure PhysicalHazardBox where (hazardId : UInt64) (rect : Rect) (hiColor loColor : Rgba) deriving DecidableEq, Repr
structure PhysicalHazardReticlePlane where (boxes : List PhysicalHazardBox) deriving DecidableEq, Repr
structure ValidHazardBox (pol : EpiphanyDisplayPolicy) (box : PhysicalHazardBox) : Prop where
  (minWidth : 4 ≤ box.rect.w.toNat) (minHeight : 4 ≤ box.rect.h.toNat)
  (hiAlphaFloor : pol.minHazardAlpha.toNat ≤ box.hiColor.a.toNat) (loAlphaFloor : pol.minHazardAlpha.toNat ≤ box.loColor.a.toNat)
  (contrastMargin : pixelLuma (overRgba box.loColor Rgba.opaqueWhite) + pol.minContrastFloor ≤ pixelLuma (overRgba box.hiColor Rgba.zero))
def checkHazardBox (pol : EpiphanyDisplayPolicy) (box : PhysicalHazardBox) : Bool :=
  decide (4 ≤ box.rect.w.toNat ∧ 4 ≤ box.rect.h.toNat ∧ pol.minHazardAlpha.toNat ≤ box.hiColor.a.toNat ∧
    pol.minHazardAlpha.toNat ≤ box.loColor.a.toNat ∧
    pixelLuma (overRgba box.loColor Rgba.opaqueWhite) + pol.minContrastFloor ≤ pixelLuma (overRgba box.hiColor Rgba.zero))
theorem checkHazardBox_iff (pol : EpiphanyDisplayPolicy) (box : PhysicalHazardBox) :
    checkHazardBox pol box = true ↔ ValidHazardBox pol box := by
  unfold checkHazardBox; simp only [decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩, fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩
def AllHazardsValid (pol : EpiphanyDisplayPolicy) (plane : PhysicalHazardReticlePlane) : Prop :=
  ∀ box ∈ plane.boxes, ValidHazardBox pol box
def checkAllHazards (pol : EpiphanyDisplayPolicy) (plane : PhysicalHazardReticlePlane) : Bool :=
  plane.boxes.all (checkHazardBox pol)
theorem checkAllHazards_iff (pol : EpiphanyDisplayPolicy) (plane : PhysicalHazardReticlePlane) :
    checkAllHazards pol plane = true ↔ AllHazardsValid pol plane := by
  unfold checkAllHazards AllHazardsValid; rw [List.all_eq_true]
  exact ⟨fun h box hb => (checkHazardBox_iff pol box).mp (h box hb),
    fun h box hb => (checkHazardBox_iff pol box).mpr (h box hb)⟩
def inOuterRing (r : Rect) (px py : Nat) : Bool :=
  r.contains px py &&
    decide (px = r.x.toNat ∨ px + 1 = r.x.toNat + r.w.toNat ∨
      py = r.y.toNat ∨ py + 1 = r.y.toNat + r.h.toNat)
def inInnerRing (r : Rect) (px py : Nat) : Bool :=
  decide (r.x.toNat + 1 ≤ px ∧ px + 1 < r.x.toNat + r.w.toNat ∧
    r.y.toNat + 1 ≤ py ∧ py + 1 < r.y.toNat + r.h.toNat ∧
    (px = r.x.toNat + 1 ∨ px + 2 = r.x.toNat + r.w.toNat ∨
     py = r.y.toNat + 1 ∨ py + 2 = r.y.toNat + r.h.toNat))
def hazardBoxPixelAt (box : PhysicalHazardBox) (px py : Nat) : Option Rgba :=
  if inOuterRing box.rect px py then some box.hiColor
  else if inInnerRing box.rect px py then some box.loColor else none
def hazardPlanePixelAt (plane : PhysicalHazardReticlePlane) (px py : Nat) : Option Rgba :=
  plane.boxes.findSome? (fun box => hazardBoxPixelAt box px py)
theorem hazardBoxPixelAt_corners {pol : EpiphanyDisplayPolicy} {box : PhysicalHazardBox}
    (hValid : ValidHazardBox pol box) :
    hazardBoxPixelAt box box.rect.x.toNat box.rect.y.toNat = some box.hiColor ∧
    hazardBoxPixelAt box (box.rect.x.toNat + 1) (box.rect.y.toNat + 1) = some box.loColor := by
  have hw := hValid.minWidth; have hh := hValid.minHeight
  constructor
  · have hOut : inOuterRing box.rect box.rect.x.toNat box.rect.y.toNat = true :=
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true (by omega), decide_eq_true (.inl rfl)⟩
    unfold hazardBoxPixelAt; rw [hOut]; rfl
  · have hOutF : inOuterRing box.rect (box.rect.x.toNat + 1) (box.rect.y.toNat + 1) = false :=
      Bool.and_eq_false_iff.mpr (.inr (decide_eq_false (by omega)))
    have hInT : inInnerRing box.rect (box.rect.x.toNat + 1) (box.rect.y.toNat + 1) = true :=
      decide_eq_true ⟨Nat.le_refl _, by omega, Nat.le_refl _, by omega, .inl rfl⟩
    unfold hazardBoxPixelAt; rw [hOutF, hInT]; rfl
private theorem boxes_findSome_alpha_floor {pol : EpiphanyDisplayPolicy} :
    ∀ (boxes : List PhysicalHazardBox), (∀ b ∈ boxes, ValidHazardBox pol b) →
      ∀ {px py : Nat} {hzPix : Rgba}, boxes.findSome? (fun b => hazardBoxPixelAt b px py) = some hzPix →
        pol.minHazardAlpha.toNat ≤ hzPix.a.toNat
  | [], _, _, _, _, hSome => by cases hSome
  | box :: rest, hAll, px, py, _, hSome => by
    have hBox := hAll box List.mem_cons_self; simp only [List.findSome?_cons] at hSome
    cases hAt : hazardBoxPixelAt box px py with
    | none => rw [hAt] at hSome; exact boxes_findSome_alpha_floor rest (fun b hb => hAll b (List.mem_cons_of_mem _ hb)) hSome
    | some _ =>
      rw [hAt] at hSome; cases hSome; unfold hazardBoxPixelAt at hAt
      cases h1 : inOuterRing box.rect px py
      · rw [h1] at hAt; cases h2 : inInnerRing box.rect px py <;> rw [h2] at hAt <;> cases hAt; exact hBox.loAlphaFloor
      · rw [h1] at hAt; cases hAt; exact hBox.hiAlphaFloor
theorem hazardPlanePixelAt_alpha_floor {pol : EpiphanyDisplayPolicy}
    {plane : PhysicalHazardReticlePlane} (hAll : AllHazardsValid pol plane)
    {px py : Nat} {hzPix : Rgba} (hSome : hazardPlanePixelAt plane px py = some hzPix) :
    pol.minHazardAlpha.toNat ≤ hzPix.a.toNat :=
  boxes_findSome_alpha_floor plane.boxes hAll hSome
/-- Three-plane hardware scanout compositor (`UntrustedBeliefPlane` → `PhysicalHazardReticlePlane`
    → `TrustedConsentChromePlane`). -/
def scanoutPixel (pol : EpiphanyDisplayPolicy) (belief : UntrustedBeliefPlane)
    (hazard : PhysicalHazardReticlePlane) (chrome : TrustedConsentChromePlane) (px py : Nat) : Rgba :=
  let bPix := clipBeliefPixel pol chrome belief px py
  let bhPix := match hazardPlanePixelAt hazard px py with
    | none => bPix | some hzPix => overRgba hzPix bPix
  match chromePixelAt pol chrome px py with
  | none => bhPix | some chPix => overRgba chPix bhPix
/-- **Trusted Chrome Non-Occlusion & Unforgeability (`chrome_non_occludable_and_unforgeable`)**. -/
theorem chrome_non_occludable_and_unforgeable
    {pol : EpiphanyDisplayPolicy} {chrome : TrustedConsentChromePlane}
    (hChrome : OpaqueConsentChrome pol chrome)
    (b₁ b₂ : UntrustedBeliefPlane) (hazard : PhysicalHazardReticlePlane)
    {px py : Nat} (hIn : inConsentChromeRegion pol chrome px py = true) :
    clipBeliefPixel pol chrome b₁ px py = Rgba.zero ∧
    (∃ chPix : Rgba, chromePixelAt pol chrome px py = some chPix ∧
      scanoutPixel pol b₁ hazard chrome px py = chPix ∧
      scanoutPixel pol b₂ hazard chrome px py = chPix) ∧
    (∀ ov ∈ b₁.overlays, overlayIntrudesChrome pol chrome ov = false →
      ov.rect.contains px py = false) := by
  refine ⟨by simp [clipBeliefPixel, hIn], ?_, ?_⟩
  · obtain ⟨chPix, hAt, hOp⟩ := chromePixelAt_opaque_of_inside hChrome hIn
    exact ⟨chPix, hAt, by simp only [scanoutPixel, hAt, overRgba_opaque hOp],
      by simp only [scanoutPixel, hAt, overRgba_opaque hOp]⟩
  · intro ov _ hSafe
    cases hCont : ov.rect.contains px py with
    | false => rfl
    | true => have hOut := overlayIntrudesChrome_false_disjoint hSafe hCont; rw [hIn] at hOut; cases hOut
theorem trusted_consent_band_unforgeable
    {pol : EpiphanyDisplayPolicy} (hPol : ValidDisplayPolicy pol)
    {chrome : TrustedConsentChromePlane} (hChrome : OpaqueConsentChrome pol chrome)
    (b₁ b₂ : UntrustedBeliefPlane) (hazard : PhysicalHazardReticlePlane)
    {px py : Nat} (hBand : (trustedConsentBandRect pol).contains px py = true) :
    scanoutPixel pol b₁ hazard chrome px py = scanoutPixel pol b₂ hazard chrome px py := by
  have hb := of_decide_eq_true hBand
  simp only [trustedConsentBandRect, UInt32.toNat_zero, Nat.zero_add] at hb
  have hVh := hPol.bandFitsHeight
  have hBandB : inTrustedConsentBand pol px py = true := decide_eq_true ⟨hb.2.1, by omega, .inl hb.2.2.2⟩
  obtain ⟨_, ⟨_, _, h1, h2⟩, _⟩ := chrome_non_occludable_and_unforgeable (px := px) (py := py)
    hChrome b₁ b₂ hazard (by simp [inConsentChromeRegion, hBandB])
  exact h1.trans h2.symm
theorem physical_hazard_reticle_visibility_floor
    {pol : EpiphanyDisplayPolicy} {hazard : PhysicalHazardReticlePlane} {chrome : TrustedConsentChromePlane}
    (hHaz : AllHazardsValid pol hazard) (b₁ b₂ : UntrustedBeliefPlane) {box : PhysicalHazardBox} (hMem : box ∈ hazard.boxes)
    {pxHi pyHi pxLo pyLo : Nat} (hOutHi : inConsentChromeRegion pol chrome pxHi pyHi = false)
    (hOutLo : inConsentChromeRegion pol chrome pxLo pyLo = false)
    (hPixHi : hazardPlanePixelAt hazard pxHi pyHi = some box.hiColor) (hPixLo : hazardPlanePixelAt hazard pxLo pyLo = some box.loColor) :
    pol.minHazardAlpha.toNat ≤ (scanoutPixel pol b₁ hazard chrome pxHi pyHi).a.toNat ∧
    pol.minHazardAlpha.toNat ≤ (scanoutPixel pol b₂ hazard chrome pxLo pyLo).a.toNat ∧
    pixelLuma (scanoutPixel pol b₂ hazard chrome pxLo pyLo) + pol.minContrastFloor ≤
      pixelLuma (scanoutPixel pol b₁ hazard chrome pxHi pyHi) := by
  have hBox := hHaz box hMem
  simp only [scanoutPixel, hPixHi, hPixLo, chromePixelAt_eq_none_of_outside pol chrome hOutHi, chromePixelAt_eq_none_of_outside pol chrome hOutLo]
  refine ⟨Nat.le_trans hBox.hiAlphaFloor (overRgba_alpha_ge_src box.hiColor _),
    Nat.le_trans hBox.loAlphaFloor (overRgba_alpha_ge_src box.loColor _), ?_⟩
  have hLoLe := pixelLuma_overRgba_le_white box.loColor (clipBeliefPixel pol chrome b₂ pxLo pyLo)
  have hHiGe := pixelLuma_overRgba_ge_zero box.hiColor (clipBeliefPixel pol chrome b₁ pxHi pyHi)
  have hGap := hBox.contrastMargin; omega
theorem hazard_pixel_alpha_floor {pol : EpiphanyDisplayPolicy} {hazard : PhysicalHazardReticlePlane}
    {chrome : TrustedConsentChromePlane} (hHaz : AllHazardsValid pol hazard) (belief : UntrustedBeliefPlane)
    {px py : Nat} {hzPix : Rgba} (hOut : inConsentChromeRegion pol chrome px py = false)
    (hPix : hazardPlanePixelAt hazard px py = some hzPix) :
    pol.minHazardAlpha.toNat ≤ (scanoutPixel pol belief hazard chrome px py).a.toNat := by
  simp only [scanoutPixel, hPix, chromePixelAt_eq_none_of_outside pol chrome hOut]
  exact Nat.le_trans (hazardPlanePixelAt_alpha_floor hHaz hPix) (overRgba_alpha_ge_src hzPix _)

/-! ## 3. Monotone CSI-2 Sensor-Frame Sealing & ROI Redaction (`OBEND.SHE.SENSOR_SEAL/v1`) -/
structure SensorTile where (tileX tileY tileW tileH : UInt32) (pixels : List Rgba) deriving DecidableEq, Repr
structure SensorFrame where
  (sensorId monoSeq : UInt64) (width height : UInt32) (tiles : List SensorTile) (redactBoxes : List Rect)
  deriving DecidableEq, Repr
def checkFrameGeometry (f : SensorFrame) : Bool :=
  decide (0 < f.width.toNat ∧ 0 < f.height.toNat) &&
    f.tiles.all (fun t => decide (0 < t.tileW.toNat ∧ 0 < t.tileH.toNat ∧
      t.tileX.toNat + t.tileW.toNat ≤ f.width.toNat ∧ t.tileY.toNat + t.tileH.toNat ≤ f.height.toNat ∧
      t.pixels.length = t.tileW.toNat * t.tileH.toNat))
def tilePixelCoord (tileX tileY tileW : UInt32) (idx : Nat) : Nat × Nat :=
  let w := tileW.toNat; if w = 0 then (tileX.toNat, tileY.toNat) else (tileX.toNat + idx % w, tileY.toNat + idx / w)
def inRedactRoi (boxes : List Rect) (px py : Nat) : Bool := boxes.any (fun r => r.contains px py)
def redactTilePixels (boxes : List Rect) (tileX tileY tileW : UInt32) : Nat → List Rgba → List Rgba
  | _, [] => []
  | idx, p :: ps =>
    let coord := tilePixelCoord tileX tileY tileW idx
    (if inRedactRoi boxes coord.1 coord.2 then Rgba.zero else p) :: redactTilePixels boxes tileX tileY tileW (idx + 1) ps
def redactSensorTile (boxes : List Rect) (t : SensorTile) : SensorTile :=
  { t with pixels := redactTilePixels boxes t.tileX t.tileY t.tileW 0 t.pixels }
/-- Zero all private bystander/document ROI pixels BEFORE untrusted grains or LLMs receive data. -/
def redactSensorFrame (raw : SensorFrame) : SensorFrame :=
  { raw with tiles := raw.tiles.map (redactSensorTile raw.redactBoxes) }
theorem redactTilePixels_length (boxes : List Rect) (tx ty tw : UInt32) :
    ∀ (idx : Nat) (ps : List Rgba), (redactTilePixels boxes tx ty tw idx ps).length = ps.length
  | _, [] => rfl
  | idx, _ :: ps => by simp [redactTilePixels, redactTilePixels_length boxes tx ty tw (idx + 1) ps]
theorem redactTilePixels_idempotent (boxes : List Rect) (tx ty tw : UInt32) :
    ∀ (idx : Nat) (ps : List Rgba), redactTilePixels boxes tx ty tw idx (redactTilePixels boxes tx ty tw idx ps) =
      redactTilePixels boxes tx ty tw idx ps
  | _, [] => rfl
  | idx, _ :: ps => by
    simp only [redactTilePixels]; have ih := redactTilePixels_idempotent boxes tx ty tw (idx + 1) ps; split <;> simp [ih]
theorem redactSensorFrame_idempotent (raw : SensorFrame) : redactSensorFrame (redactSensorFrame raw) = redactSensorFrame raw := by
  unfold redactSensorFrame; simp only [List.map_map]; congr 1
  exact List.map_congr_left (fun t _ => by unfold redactSensorTile Function.comp; simp [redactTilePixels_idempotent])
theorem redactTilePixels_zero_inside (boxes : List Rect) (tx ty tw : UInt32) :
    ∀ (idx k : Nat) (ps : List Rgba), k < ps.length →
      inRedactRoi boxes (tilePixelCoord tx ty tw (idx + k)).1 (tilePixelCoord tx ty tw (idx + k)).2 = true →
      (redactTilePixels boxes tx ty tw idx ps)[k]? = some Rgba.zero
  | _, _, [], hk, _ => by simp at hk
  | idx, 0, _ :: _, _, hIn => by simp only [Nat.add_zero] at hIn; simp [redactTilePixels, hIn]
  | idx, k + 1, _ :: ps, hk, hIn => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
    have hShift : idx + (k + 1) = (idx + 1) + k := by omega
    rw [hShift] at hIn; simpa [redactTilePixels] using redactTilePixels_zero_inside boxes tx ty tw (idx + 1) k ps hk hIn
theorem redactTilePixels_congr_outside (boxes : List Rect) (tx ty tw : UInt32) :
    ∀ (idx : Nat) (ps₁ ps₂ : List Rgba), ps₁.length = ps₂.length →
      (∀ k, k < ps₁.length → inRedactRoi boxes (tilePixelCoord tx ty tw (idx + k)).1
        (tilePixelCoord tx ty tw (idx + k)).2 = false → ps₁[k]? = ps₂[k]?) →
      redactTilePixels boxes tx ty tw idx ps₁ = redactTilePixels boxes tx ty tw idx ps₂
  | _, [], [], _, _ => rfl | _, [], _ :: _, hlen, _ => by simp at hlen | _, _ :: _, [], hlen, _ => by simp at hlen
  | idx, p₁ :: ps₁, p₂ :: ps₂, hlen, hOut => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen; simp only [redactTilePixels]
    have hTail := redactTilePixels_congr_outside boxes tx ty tw (idx + 1) ps₁ ps₂ hlen (fun k hk hFalse => by
      have hShift : (idx + 1) + k = idx + (k + 1) := by omega
      rw [hShift] at hFalse; simpa using hOut (k + 1) (by simp [hk]) hFalse)
    cases hRoi : inRedactRoi boxes (tilePixelCoord tx ty tw idx).1 (tilePixelCoord tx ty tw idx).2 with
    | true => simp [hTail]
    | false => have hHead : some p₁ = some p₂ := by simpa using hOut 0 (by simp) (by simpa using hRoi)
               cases hHead; simp [hTail]

/-! ### Exact `OBEND.SHE.SENSOR_SEAL/v1` Wire Framing & `0 Classical` Binding -/
def sensorSealDomainTag : String := "OBEND.SHE.SENSOR_SEAL/v1"
def sensorSealCustomization : List UInt8 := sensorSealDomainTag.toUTF8.data.toList
def u64Be (v : UInt64) : List UInt8 := be 8 v.toNat
def u32Be (v : UInt32) : List UInt8 := be 4 v.toNat
theorem u64Be_length (v : UInt64) : (u64Be v).length = 8 := length_be 8 v.toNat
theorem u32Be_length (v : UInt32) : (u32Be v).length = 4 := length_be 4 v.toNat
theorem u64Be_injective {a b : UInt64} (h : u64Be a = u64Be b) : a = b := by
  have hpow : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  exact UInt64.toNat_inj.mp (be_injective (w := 8) (hpow ▸ a.toBitVec.isLt) (hpow ▸ b.toBitVec.isLt) h)
theorem u32Be_injective {a b : UInt32} (h : u32Be a = u32Be b) : a = b := by
  have hpow : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
  exact UInt32.toNat_inj.mp (be_injective (w := 4) (hpow ▸ a.toBitVec.isLt) (hpow ▸ b.toBitVec.isLt) h)
def encodeFields : List (List UInt8) → List UInt8 | [] => [] | f :: fs => encodeListField f ++ encodeFields fs
private theorem encodeListField_ne_nil (f : List UInt8) : encodeListField f ≠ [] := by
  unfold encodeListField leb128; cases f.length with | zero => simp [leb128Aux] | succ _ => simp only [leb128Aux]; split <;> simp
theorem encodeFields_injective : ∀ {fs₁ fs₂ : List (List UInt8)}, encodeFields fs₁ = encodeFields fs₂ → fs₁ = fs₂
  | [], [], _ => rfl
  | [], b :: _, h => False.elim (encodeListField_ne_nil b (List.append_eq_nil_iff.mp h.symm).1)
  | a :: _, [], h => False.elim (encodeListField_ne_nil a (List.append_eq_nil_iff.mp h).1)
  | _ :: _, _ :: _, h => by simp only [encodeFields] at h; obtain ⟨hab, hrest⟩ := encodeListField_prefix_inj h; rw [hab, encodeFields_injective hrest]
def encodeRgba (p : Rgba) : List UInt8 := [p.r, p.g, p.b, p.a]
def encodeRgbaList : List Rgba → List UInt8 | [] => [] | p :: ps => encodeRgba p ++ encodeRgbaList ps
theorem encodeRgbaList_injective : ∀ {ps₁ ps₂ : List Rgba}, encodeRgbaList ps₁ = encodeRgbaList ps₂ → ps₁ = ps₂
  | [], [], _ => rfl | [], _ :: _, h => by simp [encodeRgbaList, encodeRgba] at h | _ :: _, [], h => by simp [encodeRgbaList, encodeRgba] at h
  | p₁ :: _, p₂ :: _, h => by
    simp only [encodeRgbaList, encodeRgba, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨hr, hg, hb, ha, hrest⟩ := h; cases p₁; cases p₂; simp only [Rgba.mk.injEq, List.cons.injEq]
    exact ⟨⟨hr, hg, hb, ha⟩, encodeRgbaList_injective hrest⟩
def encodeRect (r : Rect) : List UInt8 := u32Be r.x ++ (u32Be r.y ++ (u32Be r.w ++ u32Be r.h))
theorem encodeRect_length (r : Rect) : (encodeRect r).length = 16 := by simp [encodeRect, u32Be_length]
theorem encodeRect_injective {r₁ r₂ : Rect} (h : encodeRect r₁ = encodeRect r₂) : r₁ = r₂ := by
  unfold encodeRect at h
  obtain ⟨hx, h⟩ := List.append_inj h (by simp [u32Be_length]); obtain ⟨hy, h⟩ := List.append_inj h (by simp [u32Be_length])
  obtain ⟨hw, hh⟩ := List.append_inj h (by simp [u32Be_length]); cases r₁; cases r₂; simp only [Rect.mk.injEq]
  exact ⟨u32Be_injective hx, u32Be_injective hy, u32Be_injective hw, u32Be_injective hh⟩
def encodeRectList : List Rect → List UInt8 | [] => [] | r :: rs => encodeRect r ++ encodeRectList rs
theorem encodeRectList_injective : ∀ {rs₁ rs₂ : List Rect}, encodeRectList rs₁ = encodeRectList rs₂ → rs₁ = rs₂
  | [], [], _ => rfl
  | [], _ :: _, h => by have hlen := congrArg List.length h; simp only [encodeRectList, List.length_nil, List.length_append, encodeRect_length] at hlen; omega
  | _ :: _, [], h => by have hlen := congrArg List.length h; simp only [encodeRectList, List.length_nil, List.length_append, encodeRect_length] at hlen; omega
  | _ :: _, _ :: _, h => by simp only [encodeRectList] at h; obtain ⟨hr, hrs⟩ := List.append_inj h (by simp [encodeRect_length]); rw [encodeRect_injective hr, encodeRectList_injective hrs]
def encodeSensorTile (t : SensorTile) : List UInt8 := encodeRect ⟨t.tileX, t.tileY, t.tileW, t.tileH⟩ ++ encodeRgbaList t.pixels
theorem encodeSensorTile_injective {t₁ t₂ : SensorTile} (h : encodeSensorTile t₁ = encodeSensorTile t₂) : t₁ = t₂ := by
  unfold encodeSensorTile at h; obtain ⟨hHdr, hPix⟩ := List.append_inj h (by simp [encodeRect_length])
  have hRect := encodeRect_injective hHdr; simp only [Rect.mk.injEq] at hRect; cases t₁; cases t₂; simp only [SensorTile.mk.injEq]
  exact ⟨hRect.1, hRect.2.1, hRect.2.2.1, hRect.2.2.2, encodeRgbaList_injective hPix⟩
def encodeTileList (ts : List SensorTile) : List UInt8 := encodeFields (ts.map encodeSensorTile)
theorem encodeTileList_injective {ts₁ ts₂ : List SensorTile} (h : encodeTileList ts₁ = encodeTileList ts₂) : ts₁ = ts₂ :=
  (List.map_inj_right (fun _ _ => encodeSensorTile_injective)).mp (encodeFields_injective h)
def sensorFrameSealPreimage (f : SensorFrame) : List UInt8 :=
  encodeFields [u64Be f.sensorId, u64Be f.monoSeq, u32Be f.width, u32Be f.height, encodeRectList f.redactBoxes, encodeTileList f.tiles]
theorem sensorFrameSealPreimage_injective {f₁ f₂ : SensorFrame} (h : sensorFrameSealPreimage f₁ = sensorFrameSealPreimage f₂) : f₁ = f₂ := by
  have hf := encodeFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨hSid, hSeq, hW, hH, hRed, hTiles⟩ := hf
  cases f₁; cases f₂; simp only [SensorFrame.mk.injEq]
  exact ⟨u64Be_injective hSid, u64Be_injective hSeq, u32Be_injective hW, u32Be_injective hH, encodeTileList_injective hTiles, encodeRectList_injective hRed⟩
def sensorFrameSeal (f : SensorFrame) : ByteArray := cshake32ByteArray sensorSealCustomization (sensorFrameSealPreimage f)
theorem sensorFrameSeal_size (f : SensorFrame) : (sensorFrameSeal f).size = 32 := cshake32ByteArray_size _ _
def extractSensorFrameSeal (f₁ f₂ : SensorFrame) (h : sensorFrameSeal f₁ = sensorFrameSeal f₂) :
    PSum (PLift (f₁ = f₂))
      (PLift (CollisionAmong (cshake256Bytes sensorSealCustomization) (fun x => x = sensorFrameSealPreimage f₁ ∨ x = sensorFrameSealPreimage f₂))) :=
  if hp : sensorFrameSealPreimage f₁ = sensorFrameSealPreimage f₂ then .inl ⟨sensorFrameSealPreimage_injective hp⟩
  else .inr ⟨by
    have hl := congrArg (fun (b : ByteArray) => b.data.toList) h
    simp only [sensorFrameSeal, cshake32ByteArray, Native.bytesOfList_toList] at hl
    exact ⟨sensorFrameSealPreimage f₁, sensorFrameSealPreimage f₂, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩⟩
/-- **6-Field Sensor-Frame Seal Binding (`sensorFrameSeal_binds`, `0 Classical`)**. -/
theorem sensorFrameSeal_binds {f₁ f₂ : SensorFrame} (h : sensorFrameSeal f₁ = sensorFrameSeal f₂) :
    f₁ = f₂ ∨ CollisionAmong (cshake256Bytes sensorSealCustomization)
      (fun x => x = sensorFrameSealPreimage f₁ ∨ x = sensorFrameSealPreimage f₂) := by
  cases extractSensorFrameSeal f₁ f₂ h with | inl heq => exact .inl heq.down | inr hcol => exact .inr hcol.down
structure PublicTileEquiv (boxes : List Rect) (t₁ t₂ : SensorTile) : Prop where
  (sameX : t₁.tileX = t₂.tileX) (sameY : t₁.tileY = t₂.tileY) (sameW : t₁.tileW = t₂.tileW)
  (sameH : t₁.tileH = t₂.tileH) (sameLen : t₁.pixels.length = t₂.pixels.length)
  (agreeOutside : ∀ k, k < t₁.pixels.length →
    inRedactRoi boxes (tilePixelCoord t₁.tileX t₁.tileY t₁.tileW k).1 (tilePixelCoord t₁.tileX t₁.tileY t₁.tileW k).2 = false → t₁.pixels[k]? = t₂.pixels[k]?)
inductive TilesPublicEquiv (boxes : List Rect) : List SensorTile → List SensorTile → Prop where
  | nil : TilesPublicEquiv boxes [] []
  | cons {t₁ t₂ : SensorTile} {ts₁ ts₂ : List SensorTile} :
      PublicTileEquiv boxes t₁ t₂ → TilesPublicEquiv boxes ts₁ ts₂ → TilesPublicEquiv boxes (t₁ :: ts₁) (t₂ :: ts₂)
structure PublicSensorEquiv (raw₁ raw₂ : SensorFrame) : Prop where
  (sameSensorId : raw₁.sensorId = raw₂.sensorId) (sameMonoSeq : raw₁.monoSeq = raw₂.monoSeq)
  (sameWidth : raw₁.width = raw₂.width) (sameHeight : raw₁.height = raw₂.height)
  (sameBoxes : raw₁.redactBoxes = raw₂.redactBoxes) (tilesRel : TilesPublicEquiv raw₁.redactBoxes raw₁.tiles raw₂.tiles)
private theorem map_redactTile_eq_of_equiv (boxes : List Rect) :
    ∀ {ts₁ ts₂ : List SensorTile}, TilesPublicEquiv boxes ts₁ ts₂ → ts₁.map (redactSensorTile boxes) = ts₂.map (redactSensorTile boxes)
  | [], [], .nil => rfl
  | t₁ :: _, t₂ :: _, .cons ht hrest => by
    simp only [List.map_cons, List.cons.injEq]; refine ⟨?_, map_redactTile_eq_of_equiv boxes hrest⟩
    have hpix : redactTilePixels boxes t₁.tileX t₁.tileY t₁.tileW 0 t₁.pixels = redactTilePixels boxes t₂.tileX t₂.tileY t₂.tileW 0 t₂.pixels := by
      rw [← ht.sameX, ← ht.sameY, ← ht.sameW]
      exact redactTilePixels_congr_outside boxes t₁.tileX t₁.tileY t₁.tileW 0 t₁.pixels t₂.pixels ht.sameLen (fun k hk hOut => ht.agreeOutside k hk (by simpa using hOut))
    cases t₁; cases t₂; simp only [redactSensorTile, SensorTile.mk.injEq] at ht hpix ⊢; exact ⟨ht.sameX, ht.sameY, ht.sameW, ht.sameH, hpix⟩
/-- **Zero Private ROI Leakage (`redactedSensorFrame_zero_private_leakage`)**. -/
theorem redactedSensorFrame_zero_private_leakage {raw₁ raw₂ : SensorFrame} (hEq : PublicSensorEquiv raw₁ raw₂) :
    redactSensorFrame raw₁ = redactSensorFrame raw₂ ∧ sensorFrameSeal (redactSensorFrame raw₁) = sensorFrameSeal (redactSensorFrame raw₂) ∧
    (∀ t ∈ raw₁.tiles, ∀ k, k < t.pixels.length →
      inRedactRoi raw₁.redactBoxes (tilePixelCoord t.tileX t.tileY t.tileW k).1 (tilePixelCoord t.tileX t.tileY t.tileW k).2 = true →
      (redactSensorTile raw₁.redactBoxes t).pixels[k]? = some Rgba.zero) := by
  have hRedEq : redactSensorFrame raw₁ = redactSensorFrame raw₂ := by
    have hTiles := map_redactTile_eq_of_equiv raw₁.redactBoxes hEq.tilesRel; obtain ⟨hSid, hSeq, hW, hH, hBoxes, _⟩ := hEq
    cases raw₁; cases raw₂; simp only [redactSensorFrame, SensorFrame.mk.injEq] at hSid hSeq hW hH hBoxes hTiles ⊢
    subst hBoxes; exact ⟨hSid, hSeq, hW, hH, hTiles, rfl⟩
  refine ⟨hRedEq, congrArg sensorFrameSeal hRedEq, fun t _ k hk hIn => ?_⟩
  unfold redactSensorTile; simpa using redactTilePixels_zero_inside raw₁.redactBoxes t.tileX t.tileY t.tileW 0 k t.pixels hk (by simpa using hIn)

/-! ### Stateful Monotone Sensor-Frame Sealer & Multi-Frame Trace Invariant -/
def maxSensorMonoSeq : UInt64 := 0xFFFFFFFFFFFFFFFF
inductive SensorSealError where
  | nonMonotoneSeq (sensorId prevSeq attemptedSeq : UInt64)
  | seqOverflowWraparound (sensorId attemptedSeq : UInt64)
  | malformedTileGeometry | incompleteFrameCoverage deriving DecidableEq, Repr
structure SensorSealerState where
  (lastSeqBySensor : List (UInt64 × UInt64)) (sealedLog : List (UInt64 × UInt64 × ByteArray)) deriving DecidableEq, Repr
def SensorSealerState.empty : SensorSealerState := ⟨[], []⟩
def SensorSealerState.lookupSeq (st : SensorSealerState) (sid : UInt64) : Option UInt64 := st.lastSeqBySensor.lookup sid
private def putSensorSeq : List (UInt64 × UInt64) → UInt64 → UInt64 → List (UInt64 × UInt64)
  | [], sid, seq => [(sid, seq)]
  | (k, v) :: rest, sid, seq => if sid == k then (sid, seq) :: rest else (k, v) :: putSensorSeq rest sid seq
private theorem lookup_putSensorSeq (xs : List (UInt64 × UInt64)) (sid q seq : UInt64) :
    (putSensorSeq xs sid seq).lookup q = if q == sid then some seq else xs.lookup q := by
  induction xs with
  | nil => simp only [putSensorSeq, List.lookup]; cases (q == sid) <;> rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩; simp only [putSensorSeq]
    by_cases hsk : sid = k
    · subst hsk; simp only [beq_self_eq_true, ↓reduceIte, List.lookup]; cases (q == sid) <;> rfl
    · rw [beq_false_of_ne hsk]; simp only [Bool.false_eq_true, ↓reduceIte, List.lookup]
      by_cases hqk : q = k
      · subst hqk; rw [beq_self_eq_true, beq_false_of_ne (Ne.symm hsk)]; rfl
      · rw [beq_false_of_ne hqk, ih]
private def commitValidSensorFrame (st : SensorSealerState) (raw : SensorFrame) :
    Except SensorSealError (SensorSealerState × SensorFrame × ByteArray) :=
  if raw.monoSeq == maxSensorMonoSeq then .error (.seqOverflowWraparound raw.sensorId raw.monoSeq)
  else if checkFrameGeometry raw then
    let red := redactSensorFrame raw; let sealDig := sensorFrameSeal red
    .ok (⟨putSensorSeq st.lastSeqBySensor raw.sensorId raw.monoSeq, st.sealedLog ++ [(raw.sensorId, raw.monoSeq, sealDig)]⟩, red, sealDig)
  else .error .malformedTileGeometry
def stepSensorSealer (st : SensorSealerState) (raw : SensorFrame) :
    Except SensorSealError (SensorSealerState × SensorFrame × ByteArray) :=
  match st.lookupSeq raw.sensorId with
  | some prev => if decide (prev.toNat < raw.monoSeq.toNat) then commitValidSensorFrame st raw
      else .error (.nonMonotoneSeq raw.sensorId prev raw.monoSeq)
  | none => commitValidSensorFrame st raw
inductive ValidSensorSealTrace : SensorSealerState → List SensorFrame → SensorSealerState → Prop where
  | nil (st : SensorSealerState) : ValidSensorSealTrace st [] st
  | cons {st stMid stEnd : SensorSealerState} {f : SensorFrame} {fs : List SensorFrame} {red : SensorFrame} {sealDig : ByteArray} :
      stepSensorSealer st f = .ok (stMid, red, sealDig) → ValidSensorSealTrace stMid fs stEnd → ValidSensorSealTrace st (f :: fs) stEnd
def sensorSeqsFor (sid : UInt64) : List SensorFrame → List UInt64
  | [] => [] | f :: fs => if f.sensorId == sid then f.monoSeq :: sensorSeqsFor sid fs else sensorSeqsFor sid fs
private theorem commitValid_updates_lookup {st stMid : SensorSealerState} {f red : SensorFrame} {sealDig : ByteArray}
    (hOk : commitValidSensorFrame st f = .ok (stMid, red, sealDig)) (q : UInt64) :
    stMid.lookupSeq q = if q == f.sensorId then some f.monoSeq else st.lookupSeq q := by
  unfold commitValidSensorFrame at hOk
  cases hMax : (f.monoSeq == maxSensorMonoSeq) <;> rw [hMax] at hOk
  · simp only [Bool.false_eq_true, ↓reduceIte] at hOk
    cases hG : checkFrameGeometry f <;> rw [hG] at hOk
    · cases hOk
    · simp only [↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hOk; rcases hOk with ⟨rfl, _, _⟩
      exact lookup_putSensorSeq st.lastSeqBySensor f.sensorId q f.monoSeq
  · cases hOk
private theorem stepSensorSealer_updates_lookup {st stMid : SensorSealerState} {f red : SensorFrame} {sealDig : ByteArray}
    (hStep : stepSensorSealer st f = .ok (stMid, red, sealDig)) (q : UInt64) :
    stMid.lookupSeq q = if q == f.sensorId then some f.monoSeq else st.lookupSeq q := by
  unfold stepSensorSealer at hStep
  cases hL : st.lookupSeq f.sensorId <;> rw [hL] at hStep <;> dsimp only at hStep
  · exact commitValid_updates_lookup hStep q
  · rename_i prev; cases hD : decide (prev.toNat < f.monoSeq.toNat) with
    | false => rw [hD] at hStep; cases hStep | true => rw [hD] at hStep; exact commitValid_updates_lookup hStep q
private theorem trace_seqs_gt_bound {sid : UInt64} :
    ∀ {st stEnd : SensorSealerState} {frames : List SensorFrame} {bound : UInt64},
      ValidSensorSealTrace st frames stEnd → st.lookupSeq sid = some bound → ∀ s ∈ sensorSeqsFor sid frames, bound.toNat < s.toNat
  | _, _, [], _, .nil _, _, _, hs => by simp [sensorSeqsFor] at hs
  | st, _, f :: fs, bound, .cons hStep hRest, hLook, s, hs => by
    have hUpd := stepSensorSealer_updates_lookup hStep sid
    by_cases hSid : f.sensorId = sid
    · subst hSid
      have hLt : bound.toNat < f.monoSeq.toNat := by
        unfold stepSensorSealer at hStep; rw [hLook] at hStep; dsimp only at hStep
        cases hDec : decide (bound.toNat < f.monoSeq.toNat)
        · rw [hDec] at hStep; cases hStep
        · exact of_decide_eq_true hDec
      simp only [beq_self_eq_true, ↓reduceIte] at hUpd; simp only [sensorSeqsFor, beq_self_eq_true, ↓reduceIte, List.mem_cons] at hs
      rcases hs with rfl | hsTail
      · exact hLt
      · exact Nat.lt_trans hLt (trace_seqs_gt_bound hRest hUpd s hsTail)
    · simp only [beq_false_of_ne (Ne.symm hSid), Bool.false_eq_true, ↓reduceIte, hLook] at hUpd
      simp only [sensorSeqsFor, beq_false_of_ne hSid, Bool.false_eq_true, ↓reduceIte] at hs
      exact trace_seqs_gt_bound hRest hUpd s hs
theorem validSensorSealTrace_pairwise_lt (sid : UInt64) :
    ∀ {st stEnd : SensorSealerState} {frames : List SensorFrame}, ValidSensorSealTrace st frames stEnd →
      List.Pairwise (fun a b : UInt64 => a.toNat < b.toNat) (sensorSeqsFor sid frames)
  | _, _, [], .nil _ => .nil
  | _, _, f :: _, .cons hStep hRest => by
    have ih := validSensorSealTrace_pairwise_lt sid hRest
    by_cases hSid : f.sensorId = sid
    · subst hSid; have hUpd := stepSensorSealer_updates_lookup hStep f.sensorId
      simp only [beq_self_eq_true, ↓reduceIte] at hUpd; simp only [sensorSeqsFor, beq_self_eq_true, ↓reduceIte]
      exact .cons (fun s hs => trace_seqs_gt_bound hRest hUpd s hs) ih
    · simp only [sensorSeqsFor, beq_false_of_ne hSid, Bool.false_eq_true, ↓reduceIte]; exact ih
/-- **Monotone Sensor Step Refusal (`sensor_replay_step_refused`)**. -/
theorem sensor_replay_step_refused {st : SensorSealerState} {raw : SensorFrame} {prev : UInt64}
    (hPrev : st.lookupSeq raw.sensorId = some prev) (hRollback : raw.monoSeq.toNat ≤ prev.toNat) :
    stepSensorSealer st raw = .error (.nonMonotoneSeq raw.sensorId prev raw.monoSeq) := by
  unfold stepSensorSealer; rw [hPrev]; dsimp only; rw [decide_eq_false (by omega)]; rfl
/-- **Monotone Sensor Replay & Rollback Refusal (`sensor_replay_or_rollback_refused`)**. -/
theorem sensor_replay_or_rollback_refused {st : SensorSealerState} {raw : SensorFrame} {prev : UInt64}
    (hPrev : st.lookupSeq raw.sensorId = some prev) (hRollback : raw.monoSeq.toNat ≤ prev.toNat) :
    stepSensorSealer st raw = .error (.nonMonotoneSeq raw.sensorId prev raw.monoSeq) ∧
    (∀ {st₀ stEnd : SensorSealerState} {frames : List SensorFrame}, ValidSensorSealTrace st₀ frames stEnd →
      List.Pairwise (fun a b : UInt64 => a.toNat < b.toNat) (sensorSeqsFor raw.sensorId frames)) :=
  ⟨sensor_replay_step_refused hPrev hRollback, fun hTr => validSensorSealTrace_pairwise_lt raw.sensorId hTr⟩
theorem sensor_seq_max_wraparound_refused {st : SensorSealerState} {raw : SensorFrame}
    (hMax : raw.monoSeq = maxSensorMonoSeq)
    (hAdv : ∀ prev, st.lookupSeq raw.sensorId = some prev → prev.toNat < raw.monoSeq.toNat) :
    stepSensorSealer st raw = .error (.seqOverflowWraparound raw.sensorId raw.monoSeq) := by
  unfold stepSensorSealer commitValidSensorFrame
  cases hL : st.lookupSeq raw.sensorId with
  | none => simp [hMax] | some prev => have hlt := hAdv prev hL; rw [hMax] at hlt; simp [hlt, hMax]
inductive SensorContractViolation (st : SensorSealerState) (raw : SensorFrame) : Prop where
  | seqNotAdvancing (prev : UInt64) : st.lookupSeq raw.sensorId = some prev → raw.monoSeq.toNat ≤ prev.toNat → SensorContractViolation st raw
  | seqOverflowWraparound : raw.monoSeq = maxSensorMonoSeq → SensorContractViolation st raw
  | badTileGeometry : checkFrameGeometry raw = false → SensorContractViolation st raw
/-- **Environment Anti-Narrowing Completeness (`stepSensorSealer_error_iff_violation`)**. -/
theorem stepSensorSealer_error_iff_violation (st : SensorSealerState) (raw : SensorFrame) :
    (∃ err, stepSensorSealer st raw = .error err) ↔ SensorContractViolation st raw := by
  unfold stepSensorSealer commitValidSensorFrame
  cases hLook : st.lookupSeq raw.sensorId with
  | none =>
    dsimp only
    by_cases hMax : raw.monoSeq = maxSensorMonoSeq
    · simp only [hMax, beq_self_eq_true, ↓reduceIte]
      exact ⟨fun _ => .seqOverflowWraparound hMax, fun _ => ⟨.seqOverflowWraparound raw.sensorId maxSensorMonoSeq, rfl⟩⟩
    · rw [beq_false_of_ne hMax]; simp only [Bool.false_eq_true, ↓reduceIte]
      cases hGeom : checkFrameGeometry raw with
      | false => exact ⟨fun _ => .badTileGeometry hGeom, fun _ => ⟨.malformedTileGeometry, rfl⟩⟩
      | true =>
        refine ⟨(fun ⟨_, hErr⟩ => by cases hErr), fun hViol => ?_⟩
        cases hViol with
        | seqNotAdvancing _ hp _ => rw [hLook] at hp; cases hp
        | seqOverflowWraparound hm => exact False.elim (hMax hm)
        | badTileGeometry hg => rw [hGeom] at hg; cases hg
  | some prev =>
    dsimp only
    by_cases hLt : prev.toNat < raw.monoSeq.toNat
    · rw [decide_eq_true hLt]; simp only [↓reduceIte]
      by_cases hMax : raw.monoSeq = maxSensorMonoSeq
      · simp only [hMax, beq_self_eq_true, ↓reduceIte]
        exact ⟨fun _ => .seqOverflowWraparound hMax, fun _ => ⟨.seqOverflowWraparound raw.sensorId maxSensorMonoSeq, rfl⟩⟩
      · rw [beq_false_of_ne hMax]; simp only [Bool.false_eq_true, ↓reduceIte]
        cases hGeom : checkFrameGeometry raw with
        | false => exact ⟨fun _ => .badTileGeometry hGeom, fun _ => ⟨.malformedTileGeometry, rfl⟩⟩
        | true =>
          refine ⟨(fun ⟨_, hErr⟩ => by cases hErr), fun hViol => ?_⟩
          cases hViol with
          | seqNotAdvancing _ hp hle => rw [hLook] at hp; cases hp; omega
          | seqOverflowWraparound hm => exact False.elim (hMax hm)
          | badTileGeometry hg => rw [hGeom] at hg; cases hg
    · rw [decide_eq_false hLt]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun _ => .seqNotAdvancing prev hLook (by omega), fun _ => ⟨.nonMonotoneSeq raw.sensorId prev raw.monoSeq, rfl⟩⟩
theorem concurrent_sensors_independent_progress {st st' : SensorSealerState} {raw₁ red : SensorFrame} {sealDig : ByteArray}
    (hStep : stepSensorSealer st raw₁ = .ok (st', red, sealDig)) {sid₂ : UInt64} (hNe : sid₂ ≠ raw₁.sensorId) :
    st'.lookupSeq sid₂ = st.lookupSeq sid₂ := by simpa [beq_false_of_ne hNe] using stepSensorSealer_updates_lookup hStep sid₂

/-! ## 4. Multi-Turn Epiphany Session Trace & First-Class `epiphanyScanoutJudge` -/
def maxEpiphanyViewNodes : Nat := 4096
def maxEpiphanySensorTiles : Nat := 1024
def bytesEq (a b : ByteArray) : Bool := a.data.toList == b.data.toList
theorem bytesEq_iff (a b : ByteArray) : bytesEq a b = true ↔ a = b := by
  unfold bytesEq; rw [beq_iff_eq]
  exact ⟨byteArray_eq_of_toList_eq, congrArg (fun (x : ByteArray) => x.data.toList)⟩
variable {w : World} {viewer : CellId}

/-- The caller chooses the authority snapshot for the entire session. -/
structure EpiphanyFrameQuery (w : World) (viewer : CellId) where
  (policy : EpiphanyDisplayPolicy) (prevMonoSeq? : Option UInt64) (rawFrame deliveredFrame : SensorFrame)
  (claimedSeal : ByteArray) (beliefPlane : UntrustedBeliefPlane)
  (hazardPlane : PhysicalHazardReticlePlane) (chromePlane : TrustedConsentChromePlane)
  deriving DecidableEq, Repr
structure EpiphanyScanoutCert where
  (auditedRedactedFrame : SensorFrame) (auditedSeal : ByteArray) (verifiedOverlayCount : Nat)
  deriving DecidableEq, Repr
inductive EpiphanyRefusalClause where
  | invalidDisplayPolicy | nonOpaqueConsentChrome | nonMonotoneSensorSeq
  | malformedSensorGeometry | unredactedPrivateRoi | sealMismatch
  | unauthorizedBeliefOverlay | chromeIntrusion | hazardVisibilityViolation | certWitnessMismatch deriving DecidableEq, Repr
def MonoSeqAdvances (prev? : Option UInt64) (cur : UInt64) : Prop :=
  cur ≠ maxSensorMonoSeq ∧ match prev? with | none => True | some prev => prev.toNat < cur.toNat
def checkMonoSeqAdvances (prev? : Option UInt64) (cur : UInt64) : Bool :=
  (cur != maxSensorMonoSeq) && match prev? with | none => true | some prev => decide (prev.toNat < cur.toNat)
theorem checkMonoSeqAdvances_iff (prev? : Option UInt64) (cur : UInt64) :
    checkMonoSeqAdvances prev? cur = true ↔ MonoSeqAdvances prev? cur := by
  cases prev? <;> simp [checkMonoSeqAdvances, MonoSeqAdvances, bne_iff_ne]
/-- Declarative semantic meaning established by `epiphanyScanoutJudge` (never restates `check`). -/
structure EpiphanyScanoutMeaning (q : EpiphanyFrameQuery w viewer) (c : EpiphanyScanoutCert) : Prop where
  (validPolicy : ValidDisplayPolicy q.policy) (opaqueChrome : OpaqueConsentChrome q.policy q.chromePlane)
  (ledHonest : q.rawFrame.tiles ≠ [] → q.chromePlane.sensorLedActive = true)
  (seqMonotone : MonoSeqAdvances q.prevMonoSeq? q.rawFrame.monoSeq) (frameGeometry : checkFrameGeometry q.rawFrame = true)
  (roiRedacted : q.deliveredFrame = redactSensorFrame q.rawFrame)
  (sealAuthentic : q.claimedSeal = sensorFrameSeal (redactSensorFrame q.rawFrame))
  (observable : ∀ ov ∈ q.beliefPlane.overlays, Reach w viewer ov.cellId)
  (noIntrusion : ∀ ov ∈ q.beliefPlane.overlays, overlayIntrudesChrome q.policy q.chromePlane ov = false)
  (hazardsValid : AllHazardsValid q.policy q.hazardPlane)
  (certMatchesRed : c.auditedRedactedFrame = q.deliveredFrame) (certMatchesSeal : c.auditedSeal = q.claimedSeal)
  (certMatchesCnt : c.verifiedOverlayCount = q.beliefPlane.overlays.length)
structure EpiphanyDecidableFragment (q : EpiphanyFrameQuery w viewer) : Prop where
  (overlayBudget : q.beliefPlane.overlays.length ≤ maxEpiphanyViewNodes)
  (tileBudget : q.rawFrame.tiles.length ≤ maxEpiphanySensorTiles)
def epiphanyWorkCost (q : EpiphanyFrameQuery w viewer) : Nat :=
  q.beliefPlane.overlays.length + q.hazardPlane.boxes.length + q.rawFrame.tiles.length
/-- Share the viewer's capability crawl across the plane. -/
def overlaysObservable (q : EpiphanyFrameQuery w viewer) : Bool :=
  let visible := w.visible viewer
  q.beliefPlane.overlays.all fun ov => visible.contains ov.cellId

theorem overlaysObservable_iff (q : EpiphanyFrameQuery w viewer) :
    overlaysObservable q = true ↔ ∀ ov ∈ q.beliefPlane.overlays, Reach w viewer ov.cellId := by
  unfold overlaysObservable
  rw [List.all_eq_true]
  exact ⟨fun h ov hm => Obend.Vault.FrustumMembrane.canObserve_iff.mp (h ov hm),
    fun h ov hm => Obend.Vault.FrustumMembrane.canObserve_iff.mpr (h ov hm)⟩

def checkEpiphanyScanout (grade : Nat) (q : EpiphanyFrameQuery w viewer) (c : EpiphanyScanoutCert) :
    Obend.Judge.Verdict EpiphanyRefusalClause :=
  if decide (grade < epiphanyWorkCost q) then .uncovered
  else if !overlaysObservable q then .refused .unauthorizedBeliefOverlay [9]
  else if !checkDisplayPolicy q.policy then .refused .invalidDisplayPolicy [0]
  else if !(checkOpaqueConsentChrome q.policy q.chromePlane && (q.rawFrame.tiles.isEmpty || q.chromePlane.sensorLedActive)) then
    .refused .nonOpaqueConsentChrome [1]
  else if !checkMonoSeqAdvances q.prevMonoSeq? q.rawFrame.monoSeq then .refused .nonMonotoneSensorSeq [2]
  else if !checkFrameGeometry q.rawFrame then .refused .malformedSensorGeometry [3]
  else if !(q.deliveredFrame == redactSensorFrame q.rawFrame) then .refused .unredactedPrivateRoi [4]
  else if !bytesEq q.claimedSeal (sensorFrameSeal (redactSensorFrame q.rawFrame)) then .refused .sealMismatch [5]
  else if anyOverlayIntrudesChrome q.policy q.chromePlane q.beliefPlane.overlays then .refused .chromeIntrusion [6]
  else if !checkAllHazards q.policy q.hazardPlane then .refused .hazardVisibilityViolation [7]
  else if !(c.auditedRedactedFrame == q.deliveredFrame && bytesEq c.auditedSeal q.claimedSeal &&
      c.verifiedOverlayCount == q.beliefPlane.overlays.length) then .refused .certWitnessMismatch [8]
  else .ok
def epiphanyClauseRefutes : EpiphanyRefusalClause → Bool | .certWitnessMismatch => false | _ => true
private theorem guard_refused_ok {C : Type} {cond : Bool} {cl : C} {p : List Nat} {rest : Obend.Judge.Verdict C}
    (h : (if cond then Obend.Judge.Verdict.refused cl p else rest) = .ok) : cond = false ∧ rest = .ok := by
  cases cond with | true => cases h | false => exact ⟨rfl, h⟩
private theorem of_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b with | true => rfl | false => cases h
private theorem meaning_implies_query_checks {q : EpiphanyFrameQuery w viewer} {c : EpiphanyScanoutCert} (hm : EpiphanyScanoutMeaning q c) :
    checkDisplayPolicy q.policy = true ∧
    (checkOpaqueConsentChrome q.policy q.chromePlane && (q.rawFrame.tiles.isEmpty || q.chromePlane.sensorLedActive)) = true ∧
    checkMonoSeqAdvances q.prevMonoSeq? q.rawFrame.monoSeq = true ∧ checkFrameGeometry q.rawFrame = true ∧
    (q.deliveredFrame == redactSensorFrame q.rawFrame) = true ∧
    bytesEq q.claimedSeal (sensorFrameSeal (redactSensorFrame q.rawFrame)) = true ∧
    anyOverlayIntrudesChrome q.policy q.chromePlane q.beliefPlane.overlays = false ∧ checkAllHazards q.policy q.hazardPlane = true := by
  refine ⟨(checkDisplayPolicy_iff _).mpr hm.validPolicy, ?_, (checkMonoSeqAdvances_iff _ _).mpr hm.seqMonotone,
    hm.frameGeometry, beq_iff_eq.mpr hm.roiRedacted, (bytesEq_iff _ _).mpr hm.sealAuthentic, ?_, (checkAllHazards_iff _ _).mpr hm.hazardsValid⟩
  · rw [Bool.and_eq_true_iff]; refine ⟨(checkOpaqueConsentChrome_iff _ _).mpr hm.opaqueChrome, ?_⟩
    cases hT : q.rawFrame.tiles with | nil => rfl | cons _ _ => simp [hm.ledHonest (by simp [hT])]
  · unfold anyOverlayIntrudesChrome; rw [List.any_eq_false]; intro ov hMem; simp [hm.noIntrusion ov hMem]
theorem checkEpiphanyScanout_ok_iff (r : Nat) (q : EpiphanyFrameQuery w viewer) (c : EpiphanyScanoutCert) :
    checkEpiphanyScanout r q c = .ok ↔ epiphanyWorkCost q ≤ r ∧ EpiphanyScanoutMeaning q c := by
  constructor
  · intro hOk; unfold checkEpiphanyScanout at hOk
    cases hGrade : decide (r < epiphanyWorkCost q)
    · rw [hGrade] at hOk; simp only [Bool.false_eq_true, ↓reduceIte] at hOk
      obtain ⟨hObsN, hOk⟩ := guard_refused_ok hOk
      obtain ⟨hPolN, hOk⟩ := guard_refused_ok hOk; obtain ⟨hChN, hOk⟩ := guard_refused_ok hOk
      obtain ⟨hSeqN, hOk⟩ := guard_refused_ok hOk; obtain ⟨hGeomN, hOk⟩ := guard_refused_ok hOk
      obtain ⟨hRedN, hOk⟩ := guard_refused_ok hOk; obtain ⟨hSealN, hOk⟩ := guard_refused_ok hOk
      obtain ⟨hIntr, hOk⟩ := guard_refused_ok hOk; obtain ⟨hHazN, hOk⟩ := guard_refused_ok hOk
      obtain ⟨hCertN, _⟩ := guard_refused_ok hOk
      obtain ⟨hChOp, hLedOr⟩ := Bool.and_eq_true_iff.mp (of_not_eq_false hChN)
      obtain ⟨⟨hCRed, hCSeal⟩, hCCnt⟩ := (Bool.and_eq_true_iff.mp (of_not_eq_false hCertN)).imp Bool.and_eq_true_iff.mp id
      refine ⟨by have := decide_eq_false_iff_not.mp hGrade; omega,
        { observable := (overlaysObservable_iff q).mp (of_not_eq_false hObsN)
          validPolicy := (checkDisplayPolicy_iff _).mp (of_not_eq_false hPolN)
          opaqueChrome := (checkOpaqueConsentChrome_iff _ _).mp hChOp
          ledHonest := fun hNe => by cases hT : q.rawFrame.tiles with | nil => exact False.elim (hNe hT) | cons _ _ => simpa [hT] using hLedOr
          seqMonotone := (checkMonoSeqAdvances_iff _ _).mp (of_not_eq_false hSeqN)
          frameGeometry := of_not_eq_false hGeomN, roiRedacted := beq_iff_eq.mp (of_not_eq_false hRedN)
          sealAuthentic := (bytesEq_iff _ _).mp (of_not_eq_false hSealN)
          noIntrusion := fun ov hMem => by
            cases hb : overlayIntrudesChrome q.policy q.chromePlane ov
            · rfl
            · have hAny : anyOverlayIntrudesChrome q.policy q.chromePlane q.beliefPlane.overlays = true := List.any_eq_true.mpr ⟨ov, hMem, hb⟩
              rw [hIntr] at hAny; cases hAny
          hazardsValid := (checkAllHazards_iff _ _).mp (of_not_eq_false hHazN)
          certMatchesRed := beq_iff_eq.mp hCRed, certMatchesSeal := (bytesEq_iff _ _).mp hCSeal
          certMatchesCnt := beq_iff_eq.mp hCCnt }⟩
    · rw [hGrade] at hOk; cases hOk
  · rintro ⟨hCost, hm⟩
    obtain ⟨hPol, hCh, hSeq, hGeom, hRed, hSeal, hIntr, hHaz⟩ := meaning_implies_query_checks hm
    have hGrade : decide (r < epiphanyWorkCost q) = false := decide_eq_false (by omega)
    have hCRed : (c.auditedRedactedFrame == q.deliveredFrame) = true := beq_iff_eq.mpr hm.certMatchesRed
    have hCSeal : bytesEq c.auditedSeal q.claimedSeal = true := (bytesEq_iff _ _).mpr hm.certMatchesSeal
    have hCCnt : (c.verifiedOverlayCount == q.beliefPlane.overlays.length) = true := beq_iff_eq.mpr hm.certMatchesCnt
    unfold checkEpiphanyScanout; rw [hGrade, (overlaysObservable_iff q).mpr hm.observable, hPol, hCh, hSeq, hGeom, hRed, hSeal, hIntr, hHaz, hCRed, hCSeal, hCCnt]; rfl
theorem checkEpiphanyScanout_sound {r : Nat} {q : EpiphanyFrameQuery w viewer} {c : EpiphanyScanoutCert}
    (hOk : checkEpiphanyScanout r q c = .ok) : EpiphanyScanoutMeaning q c := ((checkEpiphanyScanout_ok_iff r q c).mp hOk).2
theorem checkEpiphanyScanout_refuted {r : Nat} {q : EpiphanyFrameQuery w viewer} {c : EpiphanyScanoutCert}
    {k : EpiphanyRefusalClause} {p : List Nat}
    (hRef : checkEpiphanyScanout r q c = .refused k p) (hRefutes : epiphanyClauseRefutes k = true) :
    ∀ c', ¬ EpiphanyScanoutMeaning q c' := by
  intro c' hm; obtain ⟨hPol, hCh, hSeq, hGeom, hRed, hSeal, hIntr, hHaz⟩ := meaning_implies_query_checks hm
  unfold checkEpiphanyScanout at hRef
  cases hGrade : decide (r < epiphanyWorkCost q)
  · rw [hGrade, (overlaysObservable_iff q).mpr hm.observable, hPol, hCh, hSeq, hGeom, hRed, hSeal, hIntr, hHaz] at hRef
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
    cases hCert : (c.auditedRedactedFrame == q.deliveredFrame && bytesEq c.auditedSeal q.claimedSeal &&
        c.verifiedOverlayCount == q.beliefPlane.overlays.length) <;> rw [hCert] at hRef
    · simp only [Bool.not_false, ↓reduceIte] at hRef; cases hRef; cases hRefutes
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef; cases hRef
  · rw [hGrade] at hRef; cases hRef
/-- **First-Class Epiphany Lens Scanout & Sensor-Sealing Judge (`epiphanyScanoutJudge`)**. -/
instance epiphanyScanoutJudge : Obend.Judge (EpiphanyFrameQuery w viewer) EpiphanyScanoutCert where
  Clause := EpiphanyRefusalClause; Meaning := EpiphanyScanoutMeaning; check := checkEpiphanyScanout
  sound := checkEpiphanyScanout_sound; refutes := epiphanyClauseRefutes; refuted := checkEpiphanyScanout_refuted
  Fragment := EpiphanyDecidableFragment
  complete := by
    intro q _ ⟨_, hm⟩
    refine ⟨⟨q.deliveredFrame, q.claimedSeal, q.beliefPlane.overlays.length⟩, epiphanyWorkCost q,
      (checkEpiphanyScanout_ok_iff _ _ _).mpr ⟨Nat.le_refl _,
        ⟨hm.validPolicy, hm.opaqueChrome, hm.ledHonest, hm.seqMonotone, hm.frameGeometry, hm.roiRedacted,
         hm.sealAuthentic, hm.observable, hm.noIntrusion, hm.hazardsValid, rfl, rfl, rfl⟩⟩⟩
  mono := by
    intro r r' q c hle hDecided; unfold checkEpiphanyScanout at hDecided ⊢
    cases hLt : decide (r < epiphanyWorkCost q) with
    | true => rw [hLt] at hDecided; exact False.elim (hDecided rfl)
    | false => have hNotLt := decide_eq_false_iff_not.mp hLt; rw [decide_eq_false (by omega : ¬ r' < epiphanyWorkCost q)]
structure EpiphanySessionTurn (w : World) (viewer : CellId) where (grade : Nat) (query : EpiphanyFrameQuery w viewer) (cert : EpiphanyScanoutCert) deriving DecidableEq, Repr
def stepEpiphanySession (policy : EpiphanyDisplayPolicy) (st : SensorSealerState) (turn : EpiphanySessionTurn w viewer) : Option SensorSealerState :=
  if turn.query.policy == policy && turn.query.prevMonoSeq? == st.lookupSeq turn.query.rawFrame.sensorId then
    match checkEpiphanyScanout turn.grade turn.query turn.cert, stepSensorSealer st turn.query.rawFrame with
    | .ok, .ok (st', _, _) => some st' | _, _ => none
  else none
inductive ValidEpiphanySessionTrace {w : World} {viewer : CellId} (policy : EpiphanyDisplayPolicy) :
    SensorSealerState → List (EpiphanySessionTurn w viewer) → SensorSealerState → Prop where
  | nil (st : SensorSealerState) : ValidEpiphanySessionTrace (w := w) (viewer := viewer) policy st [] st
  | cons {st stMid stEnd : SensorSealerState} {t : EpiphanySessionTurn w viewer} {ts : List (EpiphanySessionTurn w viewer)} :
      stepEpiphanySession policy st t = some stMid → ValidEpiphanySessionTrace (w := w) (viewer := viewer) policy stMid ts stEnd →
      ValidEpiphanySessionTrace (w := w) (viewer := viewer) policy st (t :: ts) stEnd
theorem validEpiphanySessionTrace_sound {policy : EpiphanyDisplayPolicy} :
    ∀ {turns : List (EpiphanySessionTurn w viewer)} {st₀ stEnd : SensorSealerState},
      ValidEpiphanySessionTrace (w := w) (viewer := viewer) policy st₀ turns stEnd →
      (∀ t ∈ turns, EpiphanyScanoutMeaning t.query t.cert) ∧ ValidSensorSealTrace st₀ (turns.map (·.query.rawFrame)) stEnd
  | [], _, _, .nil st => ⟨(fun _ hm => nomatch hm), ValidSensorSealTrace.nil st⟩
  | t :: _, st, _, .cons hStep hRest => by
    have ih := validEpiphanySessionTrace_sound hRest; unfold stepEpiphanySession at hStep
    cases hGuard : (t.query.policy == policy && t.query.prevMonoSeq? == st.lookupSeq t.query.rawFrame.sensorId)
    · rw [hGuard] at hStep; cases hStep
    · rw [hGuard] at hStep
      cases hChk : checkEpiphanyScanout t.grade t.query t.cert with
      | uncovered | refused _ _ => rw [hChk] at hStep; cases hStep
      | ok =>
        rw [hChk] at hStep
        cases hSealStep : stepSensorSealer st t.query.rawFrame with
        | error _ => rw [hSealStep] at hStep; cases hStep
        | ok res =>
          rcases res with ⟨stNext, red, sealDig⟩; rw [hSealStep] at hStep
          simp only [↓reduceIte, Option.some.injEq] at hStep; subst hStep
          exact ⟨fun x hx => by rcases List.mem_cons.mp hx with rfl | hxTail; exact checkEpiphanyScanout_sound hChk; exact ih.1 x hxTail,
            ValidSensorSealTrace.cons hSealStep ih.2⟩

/-! ## 5. Canonical Inhabitedness Witnesses (`0` `uninhabited-premise-risk`) -/
def canonicalDisplayPolicy : EpiphanyDisplayPolicy := ⟨640, 480, 32, 4, 192, 100⟩
def canonicalConsentChrome : TrustedConsentChromePlane :=
  ⟨⟨16, 24, 40, 255⟩, ⟨8, 8, 12, 12⟩, true, ⟨0, 230, 118, 255⟩,
   some ⟨200, 160, 240, 120⟩, ⟨24, 32, 48, 255⟩, ⟨(List.replicate 32 (0xAA : UInt8)).toArray⟩⟩
def canonicalHazardBox : PhysicalHazardBox := ⟨1, ⟨80, 80, 48, 48⟩, ⟨255, 220, 0, 220⟩, ⟨0, 0, 0, 220⟩⟩
def canonicalRawSensorFrame : SensorFrame :=
  { sensorId := 7, monoSeq := 42, width := 4, height := 2, redactBoxes := [⟨1, 0, 2, 1⟩]
    tiles := [⟨0, 0, 4, 2,
      [ ⟨10, 20, 30, 255⟩, ⟨99, 99, 99, 255⟩, ⟨88, 77, 66, 255⟩, ⟨40, 50, 60, 255⟩
      , ⟨70, 80, 90, 255⟩, ⟨100, 110, 120, 255⟩, ⟨130, 140, 150, 255⟩, ⟨160, 170, 180, 255⟩ ]⟩] }
def canonicalFrameQuery : EpiphanyFrameQuery Obend.Vault.FrustumMembrane.demoWorld "alice" :=
  let red := redactSensorFrame canonicalRawSensorFrame
  ⟨canonicalDisplayPolicy, some 41, canonicalRawSensorFrame, red, sensorFrameSeal red,
   ⟨[⟨"bob", .pillBadge, ⟨40, 60, 30, 20⟩, ⟨80, 160, 255, 180⟩⟩]⟩,
   ⟨[canonicalHazardBox]⟩, canonicalConsentChrome⟩
def canonicalScanoutCert : EpiphanyScanoutCert :=
  ⟨canonicalFrameQuery.deliveredFrame, canonicalFrameQuery.claimedSeal, 1⟩
theorem canonicalDisplayPolicy_valid : ValidDisplayPolicy canonicalDisplayPolicy :=
  (checkDisplayPolicy_iff canonicalDisplayPolicy).mp (by decide)
theorem canonicalConsentChrome_opaque : OpaqueConsentChrome canonicalDisplayPolicy canonicalConsentChrome :=
  (checkOpaqueConsentChrome_iff canonicalDisplayPolicy canonicalConsentChrome).mp (by decide)
theorem canonicalHazardBox_valid : ValidHazardBox canonicalDisplayPolicy canonicalHazardBox :=
  (checkHazardBox_iff canonicalDisplayPolicy canonicalHazardBox).mp (by decide)
theorem epiphanyScanoutJudge_inhabited_ok :
    EpiphanyDecidableFragment canonicalFrameQuery ∧
    Obend.Judge.check 10 canonicalFrameQuery canonicalScanoutCert = .ok ∧
    EpiphanyScanoutMeaning canonicalFrameQuery canonicalScanoutCert := by
  have hFrag : EpiphanyDecidableFragment canonicalFrameQuery := ⟨by decide, by decide⟩
  have hm : EpiphanyScanoutMeaning canonicalFrameQuery canonicalScanoutCert :=
    { validPolicy := canonicalDisplayPolicy_valid, opaqueChrome := canonicalConsentChrome_opaque
      ledHonest := fun _ => rfl, seqMonotone := (checkMonoSeqAdvances_iff _ _).mp (by decide)
      frameGeometry := by decide, roiRedacted := rfl, sealAuthentic := rfl
      observable := (overlaysObservable_iff _).mp (by decide)
      noIntrusion := fun ov hMem => by
        simp only [canonicalFrameQuery, List.mem_singleton] at hMem; subst hMem; decide
      hazardsValid := fun box hMem => by
        simp only [canonicalFrameQuery, List.mem_singleton] at hMem; subst hMem; exact canonicalHazardBox_valid
      certMatchesRed := rfl, certMatchesSeal := rfl, certMatchesCnt := rfl }
  exact ⟨hFrag, (checkEpiphanyScanout_ok_iff 10 _ _).mpr ⟨by decide, hm⟩, hm⟩
theorem checkEpiphanyScanout_unreachable (q : EpiphanyFrameQuery w viewer)
    (c : EpiphanyScanoutCert) (grade : Nat) (budget : epiphanyWorkCost q ≤ grade)
    {ov : BeliefViewOverlay} (member : ov ∈ q.beliefPlane.overlays) (hidden : ¬ Reach w viewer ov.cellId) :
    checkEpiphanyScanout grade q c = .refused .unauthorizedBeliefOverlay [9] := by
  have no : overlaysObservable q = false := Bool.eq_false_iff.mpr
    (fun h => hidden ((overlaysObservable_iff q).mp h ov member))
  simp [checkEpiphanyScanout, Nat.not_lt_of_ge budget, no]

theorem epiphanyScanoutJudge_refutes_nonconstant (w : World) (viewer : CellId) :
    (epiphanyScanoutJudge (w := w) (viewer := viewer)).refutes .chromeIntrusion = true ∧
    (epiphanyScanoutJudge (w := w) (viewer := viewer)).refutes .nonMonotoneSensorSeq = true ∧
    (epiphanyScanoutJudge (w := w) (viewer := viewer)).refutes .unredactedPrivateRoi = true ∧
    (epiphanyScanoutJudge (w := w) (viewer := viewer)).refutes .sealMismatch = true ∧
    (epiphanyScanoutJudge (w := w) (viewer := viewer)).refutes .certWitnessMismatch = false := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem validEpiphanySessionTrace_inhabited :
    ∃ st₀ turns stEnd, 0 < turns.length ∧ ValidEpiphanySessionTrace (w := Obend.Vault.FrustumMembrane.demoWorld) (viewer := "alice") canonicalDisplayPolicy st₀ turns stEnd := by
  have hChk : checkEpiphanyScanout 10 canonicalFrameQuery canonicalScanoutCert = .ok := epiphanyScanoutJudge_inhabited_ok.2.1
  have hStep : stepEpiphanySession canonicalDisplayPolicy ⟨[(7, 41)], []⟩ ⟨10, canonicalFrameQuery, canonicalScanoutCert⟩ =
      some ⟨[(7, 42)], [(7, 42, canonicalFrameQuery.claimedSeal)]⟩ := by
    unfold stepEpiphanySession
    have hG : (canonicalFrameQuery.policy == canonicalDisplayPolicy && canonicalFrameQuery.prevMonoSeq? ==
        (⟨[(7, 41)], []⟩ : SensorSealerState).lookupSeq canonicalFrameQuery.rawFrame.sensorId) = true := by decide
    have hS : stepSensorSealer ⟨[(7, 41)], []⟩ canonicalFrameQuery.rawFrame =
        .ok (⟨[(7, 42)], [(7, 42, canonicalFrameQuery.claimedSeal)]⟩, canonicalFrameQuery.deliveredFrame, canonicalFrameQuery.claimedSeal) := by
      have hNe : (canonicalRawSensorFrame.monoSeq == maxSensorMonoSeq) = false := by decide
      have hGm : checkFrameGeometry canonicalRawSensorFrame = true := by decide
      have hLt : decide ((41 : UInt64).toNat < canonicalRawSensorFrame.monoSeq.toNat) = true := by decide
      have hLk : (⟨[(7, 41)], []⟩ : SensorSealerState).lookupSeq canonicalRawSensorFrame.sensorId = some 41 := by decide
      have hPut : putSensorSeq [(7, 41)] canonicalRawSensorFrame.sensorId canonicalRawSensorFrame.monoSeq = [(7, 42)] := by decide
      change stepSensorSealer ⟨[(7, 41)], []⟩ canonicalRawSensorFrame = _
      simp only [stepSensorSealer, commitValidSensorFrame, hLk, hLt, hNe, hGm, hPut, Bool.false_eq_true, ↓reduceIte]; rfl
    rw [hG, hChk, hS]; rfl
  exact ⟨_, [_], _, Nat.zero_lt_succ 0, .cons hStep (.nil _)⟩

/-! ## 6. Synthesizable Open-FPGA Inline Scanline & ROI Gates (`Obend.Hardware.HDL.RtlModule`) -/
/-- Pack an `Rgba` pixel into a 32-bit RGBA8888 word inside the 64-bit `RtlModule` carrier. -/
def packRgba32 (p : Rgba) : BitVec 64 :=
  BitVec.ofNat 64 (p.r.toNat + p.g.toNat * 256 + p.b.toNat * 65536 + p.a.toNat * 16777216)
theorem packRgba32_zero : packRgba32 Rgba.zero = 0#64 := by decide

/-- **Synthesizable Open-FPGA Inline Display Scanline Consent Mux (`scanlineConsentMuxRtl`)**.
    Clock-synchronous `RtlModule` (`ECP5`/`FABulous` ready via `emitModuleSV` & `YosysLec.emitYosysLecSmt2`):
    - Inputs: `0: py[16]`, `1: consent_height[16]`, `2: chrome_pixel[32]`, `3: belief_pixel[32]`.
    - Whenever unsigned `py < consent_height`, both combinational `comb_pixel` and 1-cycle clocked
      register `out_pixel_q` (`reg_pixel`) unconditionally output `chrome_pixel`, ignoring `belief_pixel`. -/
def scanlineConsentMuxRtl : RtlModule :=
  { name := "scanline_consent_mux"
    inputNames := ["py", "consent_height", "chrome_pixel", "belief_pixel"]
    inputWidths := [16, 16, 32, 32]
    wires :=
      [ { wireIdx := 0, name := "in_consent_band", width := 1
          expr := .alu .ult (.inputPort 0) (.inputPort 1) }
      , { wireIdx := 1, name := "mux_pixel", width := 32
          expr := .mux (.wireRef 0) (.inputPort 2) (.inputPort 3) } ]
    regs :=
      [ { regIdx := 0, name := "out_pixel_q", domain := .coreClk, resetKind := .syncReset 0#64
          isSynchronizer := false, nextExpr := .wireRef 1, width := 32 }
      , { regIdx := 1, name := "in_band_q", domain := .coreClk, resetKind := .syncReset 0#64
          isSynchronizer := false, nextExpr := .wireRef 0, width := 1 } ]
    outputs :=
      [ { name := "comb_pixel", expr := .wireRef 1, width := 32 }
      , { name := "reg_pixel", expr := .regRead 0, width := 32 }
      , { name := "reg_in_band", expr := .regRead 1, width := 1 } ] }

theorem scanlineConsentMuxRtl_wellFormed_and_faithful :
    checkRtlModule scanlineConsentMuxRtl = true ∧
    checkRtlModuleW scanlineConsentMuxRtl = true ∧
    moduleFaithful scanlineConsentMuxRtl = true := by
  have h1 : checkRtlModule scanlineConsentMuxRtl = true := by decide
  have h2 : checkRtlModuleW scanlineConsentMuxRtl = true := by decide
  have hW : checkWidths scanlineConsentMuxRtl = true := by decide
  exact ⟨h1, h2, moduleFaithful_of_checkWidths scanlineConsentMuxRtl hW⟩

private theorem scanlineConsentMuxRtl_wires (ins regs : Nat → BitVec 64) :
    evalWireTable ins regs scanlineConsentMuxRtl.wires 0 =
      (if BitVec.ult (ins 0) (ins 1) then 1#64 else 0#64) ∧
    evalWireTable ins regs scanlineConsentMuxRtl.wires 1 =
      (if BitVec.ult (ins 0) (ins 1) then ins 2 else ins 3) := by
  refine ⟨by rfl, ?_⟩
  have hAux : ∀ (b : Bool) (t f : BitVec 64),
      (if ((if b = true then 1#64 else 0#64) != 0#64) = true then t else f) = if b = true then t else f := by
    intro b t f; cases b <;> rfl
  simp only [evalWireTable, scanlineConsentMuxRtl, List.foldl_cons, List.foldl_nil,
    evalRtlExpr, evalAluOp, ↓reduceIte, beq_iff_eq]
  exact hAux _ _ _

/-- **Universal Cycle-Exact Scanline Consent Mux Theorem (`scanlineConsentMuxRtl_cycle_sound`)**:
    for all 64-bit input words, register states, and reset values, whenever `py < consent_height`,
    the synthesized RTL mux unconditionally outputs `chrome_pixel` regardless of untrusted `belief_pixel`. -/
theorem scanlineConsentMuxRtl_cycle_sound (rst : Bool) (ins regState : Nat → BitVec 64) :
    evalModuleOutputs scanlineConsentMuxRtl ins regState =
      [ ("comb_pixel", if BitVec.ult (ins 0) (ins 1) then ins 2 else ins 3)
      , ("reg_pixel", regState 0)
      , ("reg_in_band", regState 1) ] ∧
    stepModuleRegs scanlineConsentMuxRtl rst ins regState 0 =
      (if rst then 0#64 else if BitVec.ult (ins 0) (ins 1) then ins 2 else ins 3) ∧
    stepModuleRegs scanlineConsentMuxRtl rst ins regState 1 =
      (if rst then 0#64 else if BitVec.ult (ins 0) (ins 1) then 1#64 else 0#64) := by
  obtain ⟨hw0, hw1⟩ := scanlineConsentMuxRtl_wires ins regState
  refine ⟨?_, ?_, ?_⟩
  · simp only [evalModuleOutputs, scanlineConsentMuxRtl, List.map_cons, List.map_nil, evalRtlExpr]
    exact congrArg (fun x => [("comb_pixel", x), ("reg_pixel", regState 0), ("reg_in_band", regState 1)]) hw1
  · simp only [stepModuleRegs, scanlineConsentMuxRtl, List.foldl_cons, List.foldl_nil,
      evalRtlExpr, Nat.zero_ne_one, beq_iff_eq, ↓reduceIte]
    change (if rst = true then 0#64 else evalWireTable ins regState scanlineConsentMuxRtl.wires 1) = _
    rw [hw1]
  · simp only [stepModuleRegs, scanlineConsentMuxRtl, List.foldl_cons, List.foldl_nil,
      evalRtlExpr, beq_self_eq_true, ↓reduceIte]
    change (if rst = true then 0#64 else evalWireTable ins regState scanlineConsentMuxRtl.wires 0) = _
    rw [hw0]

/-- **Multi-Cycle Non-Occlusion & Belief Independence (`scanlineConsentMuxRtl_trace_nonoccludable`)**:
    after any arbitrary prefix trace, any non-reset clock cycle with `py < consent_height` latches
    `chrome_pixel` into `out_pixel_q` identically for any two untrusted `belief_pixel` inputs. -/
theorem scanlineConsentMuxRtl_trace_nonoccludable (initRegs : Nat → BitVec 64)
    (prefixTrace : List (Bool × (Nat → BitVec 64))) (ins₁ ins₂ : Nat → BitVec 64)
    (hPy : ins₁ 0 = ins₂ 0) (hH : ins₁ 1 = ins₂ 1) (hCh : ins₁ 2 = ins₂ 2)
    (hBand : BitVec.ult (ins₁ 0) (ins₁ 1) = true) :
    runModuleTrace scanlineConsentMuxRtl initRegs (prefixTrace ++ [(false, ins₁)]) 0 = ins₁ 2 ∧
    runModuleTrace scanlineConsentMuxRtl initRegs (prefixTrace ++ [(false, ins₂)]) 0 = ins₁ 2 ∧
    runModuleTrace scanlineConsentMuxRtl initRegs (prefixTrace ++ [(false, ins₁)]) 1 = 1#64 := by
  have hBand₂ : BitVec.ult (ins₂ 0) (ins₂ 1) = true := by rw [← hPy, ← hH]; exact hBand
  simp only [runModuleTrace, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have h1 := scanlineConsentMuxRtl_cycle_sound false ins₁ (runModuleTrace scanlineConsentMuxRtl initRegs prefixTrace)
  have h2 := scanlineConsentMuxRtl_cycle_sound false ins₂ (runModuleTrace scanlineConsentMuxRtl initRegs prefixTrace)
  unfold runModuleTrace at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [h1.2.1, hBand]; rfl
  · rw [h2.2.1, hBand₂, ← hCh]; rfl
  · rw [h1.2.2, hBand]; rfl

/-- **Refinement Bridge: `scanlineConsentMuxRtl` Enforces Software `TrustedConsentBand` (`scanlineConsentMuxRtl_refines_consentBand`)**:
    for any 16-bit viewport (`viewportH < 2^16`, `consentBandHeight < 2^16`) and pixel `(px, py)` inside
    the top consent band (`py < consentBandHeight`), the synthesized RTL mux's combinational and clocked
    outputs equal `packRgba32 (scanoutPixel pol belief hazard chrome px py)` independently of `belief`. -/
theorem scanlineConsentMuxRtl_refines_consentBand
    {pol : EpiphanyDisplayPolicy} {chrome : TrustedConsentChromePlane}
    (hChrome : OpaqueConsentChrome pol chrome)
    (belief : UntrustedBeliefPlane) (hazard : PhysicalHazardReticlePlane)
    {px py : Nat} (hPx : px < pol.viewportW.toNat) (hPy : py < pol.viewportH.toNat)
    (hBand : py < pol.consentBandHeight.toNat) (hH16 : pol.consentBandHeight.toNat < 2 ^ 16)
    (beliefWord : BitVec 64) (regState : Nat → BitVec 64) :
    ∃ chPix : Rgba,
      chromePixelAt pol chrome px py = some chPix ∧
      scanoutPixel pol belief hazard chrome px py = chPix ∧
      let ins : Nat → BitVec 64 := fun
        | 0 => BitVec.ofNat 64 py
        | 1 => BitVec.ofNat 64 pol.consentBandHeight.toNat
        | 2 => packRgba32 chPix
        | 3 => beliefWord
        | _ => 0#64
      evalModuleOutputs scanlineConsentMuxRtl ins regState =
        [("comb_pixel", packRgba32 (scanoutPixel pol belief hazard chrome px py)),
         ("reg_pixel", regState 0), ("reg_in_band", regState 1)] ∧
      stepModuleRegs scanlineConsentMuxRtl false ins regState 0 =
        packRgba32 (scanoutPixel pol belief hazard chrome px py) := by
  have hInBand : inTrustedConsentBand pol px py = true := decide_eq_true ⟨hPx, hPy, .inl hBand⟩
  have hIn : inConsentChromeRegion pol chrome px py = true := by simp [inConsentChromeRegion, hInBand]
  obtain ⟨chPix, hAt, hOp⟩ := chromePixelAt_opaque_of_inside hChrome hIn
  have hScan : scanoutPixel pol belief hazard chrome px py = chPix := by
    simp only [scanoutPixel, hAt, overRgba_opaque hOp]
  have hUlt : BitVec.ult (BitVec.ofNat 64 py) (BitVec.ofNat 64 pol.consentBandHeight.toNat) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : py < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : pol.consentBandHeight.toNat < 2 ^ 64)]
    exact decide_eq_true hBand
  refine ⟨chPix, hAt, hScan, ?_⟩
  let ins : Nat → BitVec 64 := fun
    | 0 => BitVec.ofNat 64 py | 1 => BitVec.ofNat 64 pol.consentBandHeight.toNat
    | 2 => packRgba32 chPix | 3 => beliefWord | _ => 0#64
  have hCyc := scanlineConsentMuxRtl_cycle_sound false ins regState
  rw [hScan]
  exact ⟨by simpa [ins, hUlt] using hCyc.1, by simpa [ins, hUlt] using hCyc.2.1⟩

/-- Unsigned RTL box-membership predicate `(px, py) ∈ [roi_x0, roi_x1) × [roi_y0, roi_y1)`. -/
def rtlInRoiBox (ins : Nat → BitVec 64) : Bool :=
  (!BitVec.ult (ins 0) (ins 2)) && BitVec.ult (ins 0) (ins 3) &&
    ((!BitVec.ult (ins 1) (ins 4)) && BitVec.ult (ins 1) (ins 5))

/-- **Synthesizable Open-FPGA Inline Camera Scanline ROI Zeroer (`cameraScanlineRoiZeroerRtl`)**.
    Clock-synchronous `RtlModule` (`ECP5`/`FABulous` ready via `emitModuleSV` & `YosysLec.emitYosysLecSmt2`):
    - Inputs: `0: px[16]`, `1: py[16]`, `2: roi_x0[16]`, `3: roi_x1[16]`, `4: roi_y0[16]`, `5: roi_y1[16]`, `6: raw_pixel[32]`.
    - Whenever `(px, py) ∈ [roi_x0, roi_x1) × [roi_y0, roi_y1)`, the synthesized RTL pipeline
      unconditionally zeroes the pixel word (`0#64`) before downstream capture. -/
def cameraScanlineRoiZeroerRtl : RtlModule :=
  { name := "camera_scanline_roi_zeroer"
    inputNames := ["px", "py", "roi_x0", "roi_x1", "roi_y0", "roi_y1", "raw_pixel"]
    inputWidths := [16, 16, 16, 16, 16, 16, 32]
    wires :=
      [ { wireIdx := 0, name := "ge_x0", width := 1
          expr := .alu .eq (.alu .ult (.inputPort 0) (.inputPort 2)) (.const 0#64) }
      , { wireIdx := 1, name := "lt_x1", width := 1
          expr := .alu .ult (.inputPort 0) (.inputPort 3) }
      , { wireIdx := 2, name := "ge_y0", width := 1
          expr := .alu .eq (.alu .ult (.inputPort 1) (.inputPort 4)) (.const 0#64) }
      , { wireIdx := 3, name := "lt_y1", width := 1
          expr := .alu .ult (.inputPort 1) (.inputPort 5) }
      , { wireIdx := 4, name := "in_x", width := 1
          expr := .alu .bitAnd (.wireRef 0) (.wireRef 1) }
      , { wireIdx := 5, name := "in_roi", width := 1
          expr := .alu .bitAnd (.wireRef 4) (.alu .bitAnd (.wireRef 2) (.wireRef 3)) }
      , { wireIdx := 6, name := "scrubbed_pixel", width := 32
          expr := .mux (.wireRef 5) (.const 0#64) (.inputPort 6) } ]
    regs :=
      [ { regIdx := 0, name := "cap_pixel_q", domain := .coreClk, resetKind := .syncReset 0#64
          isSynchronizer := false, nextExpr := .wireRef 6, width := 32 }
      , { regIdx := 1, name := "redacted_q", domain := .coreClk, resetKind := .syncReset 0#64
          isSynchronizer := false, nextExpr := .wireRef 5, width := 1 } ]
    outputs :=
      [ { name := "comb_scrubbed_pixel", expr := .wireRef 6, width := 32 }
      , { name := "cap_pixel", expr := .regRead 0, width := 32 }
      , { name := "cap_redacted", expr := .regRead 1, width := 1 } ] }

theorem cameraScanlineRoiZeroerRtl_wellFormed_and_faithful :
    checkRtlModule cameraScanlineRoiZeroerRtl = true ∧
    checkRtlModuleW cameraScanlineRoiZeroerRtl = true ∧
    moduleFaithful cameraScanlineRoiZeroerRtl = true := by
  have h1 : checkRtlModule cameraScanlineRoiZeroerRtl = true := by decide
  have h2 : checkRtlModuleW cameraScanlineRoiZeroerRtl = true := by decide
  have hW : checkWidths cameraScanlineRoiZeroerRtl = true := by decide
  exact ⟨h1, h2, moduleFaithful_of_checkWidths cameraScanlineRoiZeroerRtl hW⟩

private theorem cameraScanlineRoiZeroerRtl_wires (ins regs : Nat → BitVec 64) :
    evalWireTable ins regs cameraScanlineRoiZeroerRtl.wires 5 =
      (if rtlInRoiBox ins then 1#64 else 0#64) ∧
    evalWireTable ins regs cameraScanlineRoiZeroerRtl.wires 6 =
      (if rtlInRoiBox ins then 0#64 else ins 6) := by
  have h5 : ∀ b0 b1 b2 b3 : Bool,
      ((if (if b0 = true then 1#64 else 0#64) = 0#64 then 1#64 else 0#64) &&&
        (if b1 = true then 1#64 else 0#64)) &&&
      ((if (if b2 = true then 1#64 else 0#64) = 0#64 then 1#64 else 0#64) &&&
        (if b3 = true then 1#64 else 0#64)) =
      if (!b0 && b1 && (!b2 && b3)) = true then 1#64 else 0#64 := by
    intro b0 b1 b2 b3; cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl
  have h6 : ∀ (b0 b1 b2 b3 : Bool) (raw : BitVec 64),
      (if ((((if (if b0 = true then 1#64 else 0#64) = 0#64 then 1#64 else 0#64) &&&
              (if b1 = true then 1#64 else 0#64)) &&&
            ((if (if b2 = true then 1#64 else 0#64) = 0#64 then 1#64 else 0#64) &&&
              (if b3 = true then 1#64 else 0#64))) != 0#64) = true then 0#64 else raw) =
      if (!b0 && b1 && (!b2 && b3)) = true then 0#64 else raw := by
    intro b0 b1 b2 b3 raw; cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl
  constructor
  · simp only [evalWireTable, cameraScanlineRoiZeroerRtl, List.foldl_cons, List.foldl_nil,
      evalRtlExpr, evalAluOp, rtlInRoiBox, beq_iff_eq, Nat.reduceEqDiff, ↓reduceIte]
    exact h5 _ _ _ _
  · simp only [evalWireTable, cameraScanlineRoiZeroerRtl, List.foldl_cons, List.foldl_nil,
      evalRtlExpr, evalAluOp, rtlInRoiBox, beq_iff_eq, Nat.reduceEqDiff, ↓reduceIte]
    exact h6 _ _ _ _ _

/-- **Universal Cycle-Exact Camera ROI Zeroer Theorem (`cameraScanlineRoiZeroerRtl_cycle_sound`)**:
    for all 64-bit input words, register states, and reset values, whenever `(px, py)` lies inside
    `[roi_x0, roi_x1) × [roi_y0, roi_y1)`, both combinational output and clocked capture register
    unconditionally output `0#64` (zeroing secret pixels before downstream capture). -/
theorem cameraScanlineRoiZeroerRtl_cycle_sound (rst : Bool) (ins regState : Nat → BitVec 64) :
    evalModuleOutputs cameraScanlineRoiZeroerRtl ins regState =
      [ ("comb_scrubbed_pixel", if rtlInRoiBox ins then 0#64 else ins 6)
      , ("cap_pixel", regState 0)
      , ("cap_redacted", regState 1) ] ∧
    stepModuleRegs cameraScanlineRoiZeroerRtl rst ins regState 0 =
      (if rst then 0#64 else if rtlInRoiBox ins then 0#64 else ins 6) ∧
    stepModuleRegs cameraScanlineRoiZeroerRtl rst ins regState 1 =
      (if rst then 0#64 else if rtlInRoiBox ins then 1#64 else 0#64) := by
  obtain ⟨hw5, hw6⟩ := cameraScanlineRoiZeroerRtl_wires ins regState
  refine ⟨?_, ?_, ?_⟩
  · simp only [evalModuleOutputs, cameraScanlineRoiZeroerRtl, List.map_cons, List.map_nil, evalRtlExpr]
    exact congrArg (fun x => [("comb_scrubbed_pixel", x), ("cap_pixel", regState 0), ("cap_redacted", regState 1)]) hw6
  · simp only [stepModuleRegs, cameraScanlineRoiZeroerRtl, List.foldl_cons, List.foldl_nil,
      evalRtlExpr, Nat.zero_ne_one, beq_iff_eq, ↓reduceIte]
    change (if rst = true then 0#64 else evalWireTable ins regState cameraScanlineRoiZeroerRtl.wires 6) = _
    rw [hw6]
  · simp only [stepModuleRegs, cameraScanlineRoiZeroerRtl, List.foldl_cons, List.foldl_nil,
      evalRtlExpr, beq_self_eq_true, ↓reduceIte]
    change (if rst = true then 0#64 else evalWireTable ins regState cameraScanlineRoiZeroerRtl.wires 5) = _
    rw [hw5]

/-- Two RTL camera input cycles agree on coordinates/ROI and on `raw_pixel` outside the ROI box. -/
structure RoiCyclePublicEquiv (c₁ c₂ : Bool × (Nat → BitVec 64)) : Prop where
  (sameRst : c₁.1 = c₂.1)
  (sameCoords : ∀ i < 6, c₁.2 i = c₂.2 i)
  (sameOutside : rtlInRoiBox c₁.2 = false → c₁.2 6 = c₂.2 6)

inductive RoiStreamPublicEquiv : List (Bool × (Nat → BitVec 64)) → List (Bool × (Nat → BitVec 64)) → Prop where
  | nil : RoiStreamPublicEquiv [] []
  | cons {c₁ c₂ : Bool × (Nat → BitVec 64)} {t₁ t₂ : List (Bool × (Nat → BitVec 64))} :
      RoiCyclePublicEquiv c₁ c₂ → RoiStreamPublicEquiv t₁ t₂ → RoiStreamPublicEquiv (c₁ :: t₁) (c₂ :: t₂)

private theorem stepCameraRoi_eq_of_publicEquiv {c₁ c₂ : Bool × (Nat → BitVec 64)}
    (hEq : RoiCyclePublicEquiv c₁ c₂) (st : Nat → BitVec 64) :
    stepModuleRegs cameraScanlineRoiZeroerRtl c₁.1 c₁.2 st =
      stepModuleRegs cameraScanlineRoiZeroerRtl c₂.1 c₂.2 st := by
  have hRoi : rtlInRoiBox c₁.2 = rtlInRoiBox c₂.2 := by
    unfold rtlInRoiBox
    rw [hEq.sameCoords 0 (by decide), hEq.sameCoords 1 (by decide), hEq.sameCoords 2 (by decide),
      hEq.sameCoords 3 (by decide), hEq.sameCoords 4 (by decide), hEq.sameCoords 5 (by decide)]
  have h1 := cameraScanlineRoiZeroerRtl_cycle_sound c₁.1 c₁.2 st
  have h2 := cameraScanlineRoiZeroerRtl_cycle_sound c₂.1 c₂.2 st
  funext i
  cases i with
  | zero =>
    rw [h1.2.1, h2.2.1, hEq.sameRst, hRoi]
    cases hr : rtlInRoiBox c₂.2 with
    | true => rfl
    | false => rw [hEq.sameOutside (hRoi.trans hr)]
  | succ j =>
    cases j with
    | zero => rw [h1.2.2, h2.2.2, hEq.sameRst, hRoi]
    | succ k =>
      simp only [stepModuleRegs, cameraScanlineRoiZeroerRtl, List.foldl_cons, List.foldl_nil]
      rfl

/-- **Multi-Cycle Pre-Capture RTL Non-Interference (`cameraScanlineRoiZeroerRtl_trace_noninterference`)**:
    for ANY two multi-cycle camera pixel streams agreeing outside `[roi_x0, roi_x1) × [roi_y0, roi_y1)`,
    the synthesized RTL capture pipeline produces identically equal register states across the entire
    trace. -/
theorem cameraScanlineRoiZeroerRtl_trace_noninterference :
    ∀ {t₁ t₂ : List (Bool × (Nat → BitVec 64))} (initRegs : Nat → BitVec 64),
      RoiStreamPublicEquiv t₁ t₂ →
      runModuleTrace cameraScanlineRoiZeroerRtl initRegs t₁ =
        runModuleTrace cameraScanlineRoiZeroerRtl initRegs t₂
  | [], [], _, .nil => rfl
  | c₁ :: t₁, c₂ :: t₂, initRegs, .cons hc ht => by
    simp only [runModuleTrace, List.foldl_cons]
    rw [stepCameraRoi_eq_of_publicEquiv hc initRegs]
    exact cameraScanlineRoiZeroerRtl_trace_noninterference _ ht

/-- **Refinement Bridge: `cameraScanlineRoiZeroerRtl` Exactly Matches Software `inRedactRoi [box]`
    (`cameraScanlineRoiZeroerRtl_refines_redactRoi`)** on all 16-bit non-wrapping coordinates. -/
theorem cameraScanlineRoiZeroerRtl_refines_redactRoi (box : Rect) (px py : Nat) (raw : Rgba)
    (hPx : px < 2 ^ 16) (hPy : py < 2 ^ 16)
    (hX1 : box.x.toNat + box.w.toNat < 2 ^ 16) (hY1 : box.y.toNat + box.h.toNat < 2 ^ 16)
    (regState : Nat → BitVec 64) :
    let ins : Nat → BitVec 64 := fun
      | 0 => BitVec.ofNat 64 px | 1 => BitVec.ofNat 64 py
      | 2 => BitVec.ofNat 64 box.x.toNat | 3 => BitVec.ofNat 64 (box.x.toNat + box.w.toNat)
      | 4 => BitVec.ofNat 64 box.y.toNat | 5 => BitVec.ofNat 64 (box.y.toNat + box.h.toNat)
      | 6 => packRgba32 raw | _ => 0#64
    rtlInRoiBox ins = inRedactRoi [box] px py ∧
    stepModuleRegs cameraScanlineRoiZeroerRtl false ins regState 0 =
      packRgba32 (if inRedactRoi [box] px py then Rgba.zero else raw) := by
  let ins : Nat → BitVec 64 := fun
    | 0 => BitVec.ofNat 64 px | 1 => BitVec.ofNat 64 py
    | 2 => BitVec.ofNat 64 box.x.toNat | 3 => BitVec.ofNat 64 (box.x.toNat + box.w.toNat)
    | 4 => BitVec.ofNat 64 box.y.toNat | 5 => BitVec.ofNat 64 (box.y.toNat + box.h.toNat)
    | 6 => packRgba32 raw | _ => 0#64
  have hInEq : rtlInRoiBox ins = inRedactRoi [box] px py := by
    have hu : ∀ a b : Nat, a < 2 ^ 16 → b < 2 ^ 16 →
        BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := fun a b ha hb => by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
    have h0 : BitVec.ult (ins 0) (ins 2) = decide (px < box.x.toNat) := hu _ _ hPx (by omega)
    have h1 : BitVec.ult (ins 0) (ins 3) = decide (px < box.x.toNat + box.w.toNat) := hu _ _ hPx hX1
    have h2 : BitVec.ult (ins 1) (ins 4) = decide (py < box.y.toNat) := hu _ _ hPy (by omega)
    have h3 : BitVec.ult (ins 1) (ins 5) = decide (py < box.y.toNat + box.h.toNat) := hu _ _ hPy hY1
    unfold rtlInRoiBox inRedactRoi Rect.contains
    rw [h0, h1, h2, h3, List.any_cons, List.any_nil, Bool.or_false]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  have hCyc := (cameraScanlineRoiZeroerRtl_cycle_sound false ins regState).2.1
  refine ⟨hInEq, ?_⟩
  rw [hCyc, hInEq]
  cases inRedactRoi [box] px py <;> simp [ins, packRgba32_zero]

/-! ## 7. Pure Software Streaming Scanline Sealer (`OBEND.SHE.SENSOR_SEAL/v1`, Untrusted I/O Stream) -/
structure ScanlinePacket where (lineY startX width : UInt32) (rawPixels : List Rgba) deriving DecidableEq, Repr
structure ScanlineStreamConfig where
  (sensorId monoSeq : UInt64) (frameWidth frameHeight : UInt32) (redactBoxes : List Rect) deriving DecidableEq, Repr
structure ScanlineStreamState where
  (activeCfg : ScanlineStreamConfig) (assembledTiles : List SensorTile) (sealerState : SensorSealerState)
  deriving DecidableEq, Repr
def ScanlineStreamState.init (cfg : ScanlineStreamConfig) (sealer : SensorSealerState := SensorSealerState.empty) : ScanlineStreamState :=
  ⟨cfg, [], sealer⟩
def ScanlineStreamState.nextFrame (st : ScanlineStreamState) (cfg : ScanlineStreamConfig) : ScanlineStreamState :=
  let hi := match st.sealerState.lookupSeq st.activeCfg.sensorId with
    | none => st.activeCfg.monoSeq
    | some prev => if prev.toNat < st.activeCfg.monoSeq.toNat then st.activeCfg.monoSeq else prev
  ⟨cfg, [], { st.sealerState with lastSeqBySensor := putSensorSeq st.sealerState.lastSeqBySensor st.activeCfg.sensorId hi }⟩
inductive ScanlineStreamError where | seqViolation | malformedScanline | duplicateScanline deriving DecidableEq, Repr
def scrubScanlinePixels (boxes : List Rect) (startX lineY : UInt32) : Nat → List Rgba → List Rgba
  | _, [] => []
  | idx, p :: ps => (if inRedactRoi boxes (startX.toNat + idx) lineY.toNat then Rgba.zero else p) ::
      scrubScanlinePixels boxes startX lineY (idx + 1) ps
private theorem scrubScanlinePixels_zero_inside (boxes : List Rect) (sx ly : UInt32) :
    ∀ (idx k : Nat) (ps : List Rgba), k < ps.length →
      inRedactRoi boxes (sx.toNat + (idx + k)) ly.toNat = true → (scrubScanlinePixels boxes sx ly idx ps)[k]? = some Rgba.zero
  | _, _, [], hk, _ => by simp at hk
  | idx, 0, _ :: _, _, hIn => by simp only [Nat.add_zero] at hIn; simp [scrubScanlinePixels, hIn]
  | idx, k + 1, _ :: ps, hk, hIn => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
    have hShift : idx + (k + 1) = (idx + 1) + k := by omega
    rw [hShift] at hIn; simpa [scrubScanlinePixels] using scrubScanlinePixels_zero_inside boxes sx ly (idx + 1) k ps hk hIn
private theorem scrubScanlinePixels_congr_outside (boxes : List Rect) (sx ly : UInt32) :
    ∀ (idx : Nat) (ps₁ ps₂ : List Rgba), ps₁.length = ps₂.length →
      (∀ k, k < ps₁.length → inRedactRoi boxes (sx.toNat + (idx + k)) ly.toNat = false → ps₁[k]? = ps₂[k]?) →
      scrubScanlinePixels boxes sx ly idx ps₁ = scrubScanlinePixels boxes sx ly idx ps₂
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, _ => by simp at h
  | _, _ :: _, [], h, _ => by simp at h
  | idx, p₁ :: ps₁, p₂ :: ps₂, hlen, hOut => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen; simp only [scrubScanlinePixels]
    have hTail := scrubScanlinePixels_congr_outside boxes sx ly (idx + 1) ps₁ ps₂ hlen (fun k hk hf => by
      have hs : (idx + 1) + k = idx + (k + 1) := by omega
      rw [hs] at hf; simpa using hOut (k + 1) (by simp [hk]) hf)
    cases hR : inRedactRoi boxes (sx.toNat + idx) ly.toNat with
    | true => simp [hTail]
    | false =>
      have hh : some p₁ = some p₂ := by simpa using hOut 0 (by simp) (by simpa using hR)
      cases hh; simp [hTail]
def stepScanlineStream (st : ScanlineStreamState) (pkt : ScanlinePacket) :
    Except ScanlineStreamError ScanlineStreamState :=
  let cfg := st.activeCfg
  if !checkMonoSeqAdvances (st.sealerState.lookupSeq cfg.sensorId) cfg.monoSeq then .error .seqViolation
  else if !decide (0 < cfg.frameWidth.toNat ∧ 0 < cfg.frameHeight.toNat ∧ 0 < pkt.width.toNat ∧
      pkt.startX.toNat + pkt.width.toNat ≤ cfg.frameWidth.toNat ∧ pkt.lineY.toNat < cfg.frameHeight.toNat ∧
      pkt.rawPixels.length = pkt.width.toNat) then .error .malformedScanline
  else if !st.assembledTiles.all (fun t => t.tileY != pkt.lineY) then .error .duplicateScanline
  else
    let scrubbed := scrubScanlinePixels cfg.redactBoxes pkt.startX pkt.lineY 0 pkt.rawPixels
    .ok ⟨cfg, st.assembledTiles ++ [⟨pkt.startX, pkt.lineY, pkt.width, 1, scrubbed⟩], st.sealerState⟩
def runScanlineStreamTrace (st : ScanlineStreamState) :
    List ScanlinePacket → Except ScanlineStreamError (ScanlineStreamState × List (List SensorTile))
  | [] => .ok (st, [st.assembledTiles])
  | p :: ps => match stepScanlineStream st p with
    | .error e => .error e
    | .ok st1 => match runScanlineStreamTrace st1 ps with
      | .error e => .error e | .ok (stEnd, hist) => .ok (stEnd, st.assembledTiles :: hist)
def checkCompleteScanlinesAux (w : UInt32) : Nat → List SensorTile → Bool
  | _, [] => true
  | y, t :: ts => (t.tileX == 0) && (t.tileY == UInt32.ofNat y) && (t.tileW == w) && (t.tileH == 1) && checkCompleteScanlinesAux w (y + 1) ts
def checkCompleteScanlines (w h : UInt32) (tiles : List SensorTile) : Bool :=
  (tiles.length == h.toNat) && checkCompleteScanlinesAux w 0 tiles
def finalizeScanlineStream (st : ScanlineStreamState) : Except SensorSealError (ScanlineStreamState × SensorFrame × ByteArray) :=
  let cfg := st.activeCfg
  if !checkCompleteScanlines cfg.frameWidth cfg.frameHeight st.assembledTiles then .error .incompleteFrameCoverage
  else match stepSensorSealer st.sealerState ⟨cfg.sensorId, cfg.monoSeq, cfg.frameWidth, cfg.frameHeight, st.assembledTiles, cfg.redactBoxes⟩ with
    | .error e => .error e | .ok (sealer', red, dig) => .ok (⟨cfg, [], sealer'⟩, red, dig)
theorem finalizeScanlineStream_refuses_incomplete {st : ScanlineStreamState}
    (hInc : checkCompleteScanlines st.activeCfg.frameWidth st.activeCfg.frameHeight st.assembledTiles = false) :
    finalizeScanlineStream st = .error .incompleteFrameCoverage := by simp [finalizeScanlineStream, hInc]
theorem finalizeScanlineStream_refuses_partial {st : ScanlineStreamState}
    (hPart : st.assembledTiles.length < st.activeCfg.frameHeight.toNat) :
    finalizeScanlineStream st = .error .incompleteFrameCoverage := by
  have hNe : (st.assembledTiles.length == st.activeCfg.frameHeight.toNat) = false :=
    beq_false_of_ne (by omega : st.assembledTiles.length ≠ st.activeCfg.frameHeight.toNat)
  simp [finalizeScanlineStream, checkCompleteScanlines, hNe]
private theorem stepScanlineStream_cfg {st st1 : ScanlineStreamState} {p : ScanlinePacket}
    (hOk : stepScanlineStream st p = .ok st1) : st1.activeCfg = st.activeCfg := by
  unfold stepScanlineStream at hOk; dsimp only at hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  cases hOk; rfl
theorem finalizeScanlineStream_ok_sound {st stNext : ScanlineStreamState} {red : SensorFrame} {dig : ByteArray}
    (hOk : finalizeScanlineStream st = .ok (stNext, red, dig)) :
    let raw : SensorFrame := ⟨st.activeCfg.sensorId, st.activeCfg.monoSeq, st.activeCfg.frameWidth, st.activeCfg.frameHeight, st.assembledTiles, st.activeCfg.redactBoxes⟩
    checkCompleteScanlines st.activeCfg.frameWidth st.activeCfg.frameHeight st.assembledTiles = true ∧
    stNext.assembledTiles = [] ∧
    red = redactSensorFrame raw ∧ dig = sensorFrameSeal red ∧
    stNext.sealerState.lookupSeq st.activeCfg.sensorId = some st.activeCfg.monoSeq ∧
    st.activeCfg.monoSeq ≠ maxSensorMonoSeq := by
  unfold finalizeScanlineStream at hOk; dsimp only at hOk
  cases hComp : checkCompleteScanlines st.activeCfg.frameWidth st.activeCfg.frameHeight st.assembledTiles with
  | false => rw [hComp] at hOk; simp at hOk
  | true =>
    rw [hComp] at hOk; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    let raw : SensorFrame := ⟨st.activeCfg.sensorId, st.activeCfg.monoSeq, st.activeCfg.frameWidth, st.activeCfg.frameHeight, st.assembledTiles, st.activeCfg.redactBoxes⟩
    cases hStep : stepSensorSealer st.sealerState raw with
    | error _ => rw [hStep] at hOk; cases hOk
    | ok res =>
      rcases res with ⟨sealer', r', d'⟩; rw [hStep] at hOk; simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rcases hOk with ⟨rfl, rfl, rfl⟩
      have hLook := stepSensorSealer_updates_lookup hStep st.activeCfg.sensorId
      simp only [raw, beq_self_eq_true, ↓reduceIte] at hLook
      have hCommit : commitValidSensorFrame st.sealerState raw = .ok (sealer', r', d') := by
        unfold stepSensorSealer at hStep
        cases hL : st.sealerState.lookupSeq raw.sensorId with
        | none => simpa [hL] using hStep
        | some prev =>
          rw [hL] at hStep; dsimp only at hStep
          cases hD : decide (prev.toNat < raw.monoSeq.toNat) with
          | false => rw [hD] at hStep; cases hStep
          | true => simpa [hD] using hStep
      unfold commitValidSensorFrame at hCommit
      cases hMax : (raw.monoSeq == maxSensorMonoSeq) with
      | true => rw [hMax] at hCommit; simp at hCommit
      | false =>
        rw [hMax] at hCommit; simp only [Bool.false_eq_true, ↓reduceIte] at hCommit
        cases hGm : checkFrameGeometry raw with
        | false => rw [hGm] at hCommit; cases hCommit
        | true =>
          rw [hGm] at hCommit; simp only [↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hCommit
          rcases hCommit with ⟨_, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl, hLook, fun hEq => by simp [raw, hEq] at hMax⟩
/-- Multi-frame scanline stream session: ingests a sequence of `(cfg, packets)` frames and seals each. -/
inductive ValidScanlineSessionTrace :
    SensorSealerState → List (ScanlineStreamConfig × List ScanlinePacket) → SensorSealerState → Prop where
  | nil (st : SensorSealerState) : ValidScanlineSessionTrace st [] st
  | cons {st stMid stEnd : SensorSealerState} {cfg : ScanlineStreamConfig} {pkts : List ScanlinePacket}
      {rest : List (ScanlineStreamConfig × List ScanlinePacket)} {streamMid streamDone : ScanlineStreamState}
      {hist : List (List SensorTile)} {red : SensorFrame} {dig : ByteArray} :
      runScanlineStreamTrace (ScanlineStreamState.init cfg st) pkts = .ok (streamMid, hist) →
      finalizeScanlineStream streamMid = .ok (streamDone, red, dig) →
      streamDone.sealerState = stMid →
      ValidScanlineSessionTrace stMid rest stEnd →
      ValidScanlineSessionTrace st ((cfg, pkts) :: rest) stEnd
theorem validScanlineSessionTrace_sound :
    ∀ {frames : List (ScanlineStreamConfig × List ScanlinePacket)} {st₀ stEnd : SensorSealerState},
      ValidScanlineSessionTrace st₀ frames stEnd →
      ∀ f ∈ frames, f.1.monoSeq ≠ maxSensorMonoSeq
  | [], _, _, .nil _, _, hm => nomatch hm
  | (cfg, pkts) :: rest, st₀, stEnd, .cons hRun hFin hEq hRest, f, hm => by
    have hCfgSame : ∀ (s0 s1 : ScanlineStreamState) (ps : List ScanlinePacket) (h : List (List SensorTile)),
        runScanlineStreamTrace s0 ps = .ok (s1, h) → s1.activeCfg = s0.activeCfg := by
      intro s0 s1 ps; induction ps generalizing s0 s1 with
      | nil => intro h hOk; simp only [runScanlineStreamTrace, Except.ok.injEq, Prod.mk.injEq] at hOk; exact hOk.1 ▸ rfl
      | cons p ps ih =>
        intro h hOk; simp only [runScanlineStreamTrace] at hOk
        cases h1 : stepScanlineStream s0 p with
        | error _ => rw [h1] at hOk; cases hOk
        | ok sa =>
          rw [h1] at hOk; dsimp only at hOk
          cases h2 : runScanlineStreamTrace sa ps with
          | error _ => rw [h2] at hOk; cases hOk
          | ok res =>
            rcases res with ⟨se, he⟩; rw [h2] at hOk; simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
            exact (hOk.1 ▸ ih sa se he h2).trans (stepScanlineStream_cfg h1)
    rcases List.mem_cons.mp hm with rfl | hTail
    · have hNm := (finalizeScanlineStream_ok_sound hFin).2.2.2.2.2
      rw [hCfgSame _ _ _ _ hRun] at hNm; exact hNm
    · exact validScanlineSessionTrace_sound hRest f hTail
structure ScanlinePacketPublicEquiv (boxes : List Rect) (p₁ p₂ : ScanlinePacket) : Prop where
  (sameY : p₁.lineY = p₂.lineY) (sameX : p₁.startX = p₂.startX) (sameW : p₁.width = p₂.width)
  (sameLen : p₁.rawPixels.length = p₂.rawPixels.length)
  (agreeOutside : ∀ k, k < p₁.rawPixels.length →
    inRedactRoi boxes (p₁.startX.toNat + k) p₁.lineY.toNat = false → p₁.rawPixels[k]? = p₂.rawPixels[k]?)
inductive ScanlineStreamPublicEquiv (boxes : List Rect) : List ScanlinePacket → List ScanlinePacket → Prop where
  | nil : ScanlineStreamPublicEquiv boxes [] []
  | cons {p₁ p₂ : ScanlinePacket} {ps₁ ps₂ : List ScanlinePacket} :
      ScanlinePacketPublicEquiv boxes p₁ p₂ → ScanlineStreamPublicEquiv boxes ps₁ ps₂ → ScanlineStreamPublicEquiv boxes (p₁ :: ps₁) (p₂ :: ps₂)
private theorem stepScanlineStream_congr_public {st : ScanlineStreamState} {p₁ p₂ : ScanlinePacket}
    (hEq : ScanlinePacketPublicEquiv st.activeCfg.redactBoxes p₁ p₂) :
    stepScanlineStream st p₁ = stepScanlineStream st p₂ := by
  have hScrub : scrubScanlinePixels st.activeCfg.redactBoxes p₁.startX p₁.lineY 0 p₁.rawPixels =
      scrubScanlinePixels st.activeCfg.redactBoxes p₂.startX p₂.lineY 0 p₂.rawPixels := by
    rw [← hEq.sameX, ← hEq.sameY]
    exact scrubScanlinePixels_congr_outside st.activeCfg.redactBoxes p₁.startX p₁.lineY 0 p₁.rawPixels
      p₂.rawPixels hEq.sameLen (fun k hk hf => hEq.agreeOutside k hk (by simpa using hf))
  simp only [stepScanlineStream]; rw [hScrub, hEq.sameX, hEq.sameY, hEq.sameW, hEq.sameLen]
private theorem runScanlineStreamTrace_congr_public :
    ∀ {st : ScanlineStreamState} {s₁ s₂ : List ScanlinePacket},
      ScanlineStreamPublicEquiv st.activeCfg.redactBoxes s₁ s₂ → runScanlineStreamTrace st s₁ = runScanlineStreamTrace st s₂
  | _, [], [], .nil => rfl
  | st, p₁ :: ps₁, p₂ :: ps₂, .cons hp hps => by
    simp only [runScanlineStreamTrace, stepScanlineStream_congr_public (st := st) hp]
    cases h1 : stepScanlineStream st p₂ with
    | error _ => rfl
    | ok st1 => dsimp only; rw [runScanlineStreamTrace_congr_public ((stepScanlineStream_cfg h1).symm ▸ hps)]
/-- **Pure Software Streaming Scanline Pre-Seal Non-Interference (`scanlineStream_zero_private_leakage`)**. -/
theorem scanlineStream_zero_private_leakage {st₀ st₁ st₂ : ScanlineStreamState}
    {s₁ s₂ : List ScanlinePacket} {trace₁ trace₂ : List (List SensorTile)}
    (hEq : ScanlineStreamPublicEquiv st₀.activeCfg.redactBoxes s₁ s₂)
    (hRun₁ : runScanlineStreamTrace st₀ s₁ = .ok (st₁, trace₁))
    (hRun₂ : runScanlineStreamTrace st₀ s₂ = .ok (st₂, trace₂)) :
    trace₁ = trace₂ ∧ st₁.assembledTiles = st₂.assembledTiles ∧
    finalizeScanlineStream st₁ = finalizeScanlineStream st₂ ∧
    (∀ p ∈ s₁, ∀ k, k < p.rawPixels.length →
      inRedactRoi st₀.activeCfg.redactBoxes (p.startX.toNat + k) p.lineY.toNat = true →
      (scrubScanlinePixels st₀.activeCfg.redactBoxes p.startX p.lineY 0 p.rawPixels)[k]? = some Rgba.zero) := by
  have hSame := runScanlineStreamTrace_congr_public (st := st₀) hEq
  rw [hRun₁, hRun₂] at hSame; cases hSame
  refine ⟨rfl, rfl, rfl, fun p _ k hk hIn => ?_⟩
  simpa using scrubScanlinePixels_zero_inside st₀.activeCfg.redactBoxes p.startX p.lineY 0 k p.rawPixels hk (by simpa using hIn)
def canonicalStreamConfig : ScanlineStreamConfig := ⟨7, 42, 4, 2, [⟨1, 0, 2, 1⟩]⟩
def canonicalStreamPackets : List ScanlinePacket :=
  [⟨0, 0, 4, [⟨10, 20, 30, 255⟩, ⟨99, 99, 99, 255⟩, ⟨88, 77, 66, 255⟩, ⟨40, 50, 60, 255⟩]⟩,
   ⟨1, 0, 4, [⟨70, 80, 90, 255⟩, ⟨100, 110, 120, 255⟩, ⟨130, 140, 150, 255⟩, ⟨160, 170, 180, 255⟩]⟩]
private def isOkNonEmptyStream : Except ScanlineStreamError (ScanlineStreamState × List (List SensorTile)) → Bool
  | .ok (s, _) => decide (0 < s.assembledTiles.length) | .error _ => false
theorem rtlAndStreamSealer_inhabited :
    checkRtlModuleW scanlineConsentMuxRtl = true ∧
    moduleFaithful scanlineConsentMuxRtl = true ∧
    checkRtlModuleW cameraScanlineRoiZeroerRtl = true ∧
    moduleFaithful cameraScanlineRoiZeroerRtl = true ∧
    (∃ stEnd hist, runScanlineStreamTrace (ScanlineStreamState.init canonicalStreamConfig)
      canonicalStreamPackets = .ok (stEnd, hist) ∧ 0 < stEnd.assembledTiles.length) := by
  refine ⟨scanlineConsentMuxRtl_wellFormed_and_faithful.2.1, scanlineConsentMuxRtl_wellFormed_and_faithful.2.2,
    cameraScanlineRoiZeroerRtl_wellFormed_and_faithful.2.1, cameraScanlineRoiZeroerRtl_wellFormed_and_faithful.2.2, ?_⟩
  have hOk : isOkNonEmptyStream (runScanlineStreamTrace (ScanlineStreamState.init canonicalStreamConfig) canonicalStreamPackets) = true := by decide
  cases h : runScanlineStreamTrace (ScanlineStreamState.init canonicalStreamConfig) canonicalStreamPackets with
  | error _ => rw [h] at hOk; cases hOk
  | ok res => rw [h] at hOk; exact ⟨res.1, res.2, rfl, of_decide_eq_true hOk⟩
private def isReadyScanlineStream :
    Except ScanlineStreamError (ScanlineStreamState × List (List SensorTile)) → Bool
  | .ok (s, _) =>
    let cfg := s.activeCfg
    checkCompleteScanlines cfg.frameWidth cfg.frameHeight s.assembledTiles &&
    (s.sealerState.lookupSeq cfg.sensorId == none) &&
    !(cfg.monoSeq == maxSensorMonoSeq) &&
    checkFrameGeometry ⟨cfg.sensorId, cfg.monoSeq, cfg.frameWidth, cfg.frameHeight,
      s.assembledTiles, cfg.redactBoxes⟩
  | .error _ => false

/-- Constructive inhabitedness witness for `validScanlineSessionTrace_sound` on a non-empty
    1-frame streaming session using `canonicalStreamConfig` and `canonicalStreamPackets`. -/
private theorem validScanlineSessionTrace_inhabited :
    ∃ stEnd,
      ValidScanlineSessionTrace SensorSealerState.empty
        [(canonicalStreamConfig, canonicalStreamPackets)] stEnd ∧
      canonicalStreamConfig.monoSeq.toNat < maxSensorMonoSeq.toNat := by
  have hR : isReadyScanlineStream
      (runScanlineStreamTrace (ScanlineStreamState.init canonicalStreamConfig SensorSealerState.empty)
        canonicalStreamPackets) = true := by
    decide
  cases hRun : runScanlineStreamTrace
      (ScanlineStreamState.init canonicalStreamConfig SensorSealerState.empty)
      canonicalStreamPackets with
  | error _ =>
    rw [hRun] at hR
    cases hR
  | ok res =>
    rcases res with ⟨stMid, hist⟩
    rw [hRun] at hR
    simp only [isReadyScanlineStream, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hR
    obtain ⟨⟨⟨hComp, hNone⟩, hMax⟩, hGeom⟩ := hR
    have hFin : ∃ stDone red dig, finalizeScanlineStream stMid = .ok (stDone, red, dig) := by
      unfold finalizeScanlineStream stepSensorSealer commitValidSensorFrame
      simp only [hComp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNone, hMax, hGeom]
      exact ⟨_, _, _, rfl⟩
    obtain ⟨stDone, red, dig, hFin⟩ := hFin
    have hTr : ValidScanlineSessionTrace SensorSealerState.empty
        [(canonicalStreamConfig, canonicalStreamPackets)] stDone.sealerState :=
      .cons hRun hFin rfl (.nil _)
    have _ := validScanlineSessionTrace_sound hTr (canonicalStreamConfig, canonicalStreamPackets) List.mem_cons_self
    exact ⟨stDone.sealerState, hTr, by decide⟩
end Obend.Polis.EpiphanyCompositor
end
