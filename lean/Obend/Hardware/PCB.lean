module
/-
# Obend.Hardware.PCB — Closed-Form Microstrip Impedance, FEM-Bracketed Coupled Multiphysics & DFM Envelopes

1. **Legacy Single-Ended Microstrip (`fxS = 10^6`):** Hammerstad–Jensen / Pozar §3.8 closed-form
   characteristic impedance `microstripZ0MilliOhm` with Bahl–Garg strip thickness correction,
   universal `fxSqrt_enclosure`, strip widening, and permittivity monotonicity.
2. **PCB Design-for-Manufacturability (`PcbFabCapabilities`, `PcbLayoutRules`, `checkPcbDfmEnvelope`):**
   Trapezoidal copper etch undercut intervals (`dfm_etch_prevents_open_and_short`), plated-through
   drill aspect ratio and via annular-ring registration (`dfm_via_breakout_impossible`), acute-angle
   acid-trap refusal, solder-mask sliver prevention, and stackup copper-balance thieving.
3. **FEM-Bracketed Coupled Differential $(\mathbf{L}, \mathbf{C})$, Return-Path & 2D PDN Multiphysics:**
   Welds `Obend.Analysis.SimplicialFeecFem` Thomson–Dirichlet two-sided capacitance brackets into
   guaranteed odd/even/differential/common-mode impedance intervals, DFM corner impedance and
   capacitive-skew mode-conversion bounds (`dfm_differential_zdiff_and_skew_sound`), split
   return-plane slot inductance refusal (`checkHighSpeedReturnPathContinuity`), $\lambda_{\min}/20$
   stitching-via Faraday fence shielding, and continuous-band 2D plane-pair PDN target impedance.
-/
public import Obend.Analysis.SimplicialFeecFem
import all Obend.Analysis.SimplicialFeecFem
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Accelerators

public section

namespace Obend.Hardware.PCB

open Obend.Analysis.SimplicialFeecFem

set_option autoImplicit false

/-! ## 1. Closed-Form Microstrip Impedance (Hammerstad–Jensen, Bahl–Garg Thickness Correction)

Fixed point with scale `fxS = 10⁶`; `Nat.sqrt` and an `atanh`-series logarithm, so the kernel can
evaluate it. The formulas follow Pozar, *Microwave Engineering*, §3.8; Hammerstad (1975); and
Bahl–Garg strip thickness correction, with $u = W_{\text{eff}}/H$:
$$\varepsilon_{\text{eff}} = \tfrac{\varepsilon_r+1}{2} + \tfrac{\varepsilon_r-1}{2}\Bigl[(1 + 12/u)^{-1/2} + [u<1]\,0.04(1-u)^2\Bigr],$$
$$Z_0 = \begin{cases} \dfrac{60}{\sqrt{\varepsilon_{\text{eff}}}} \ln\!\bigl(\tfrac{8}{u} + \tfrac{u}{4}\bigr) & u \le 1\\[4pt]
\dfrac{120\pi}{\sqrt{\varepsilon_{\text{eff}}}\,\bigl(u + 1.393 + 0.667 \ln(u + 1.444)\bigr)} & u \ge 1\end{cases}
\qquad W_{\text{eff}} = W + \tfrac{T}{\pi}\bigl(1 + \ln\tfrac{2H}{T}\bigr).$$ -/

@[expose] def fxS : Nat := 1000000

/-- `⌊√(a·S)⌋`: the square root of the fixed-point value `a`. -/
@[expose] def fxSqrt (a : Nat) : Nat := Nat.sqrt (a * fxS)

/-- Halve until below `2S` and double until at least `S`, counting the exponent (fuel-bounded). -/
@[expose] def fxLnNorm : Nat → Nat → Int → Nat × Int
  | 0, m, k => (m, k)
  | fuel + 1, m, k =>
    if 2 * fxS ≤ m then fxLnNorm fuel (m / 2) (k + 1)
    else if m < fxS ∧ 0 < m then fxLnNorm fuel (2 * m) (k - 1)
    else (m, k)

/-- `ln(a/S)·S` for `a > 0`, from `ln m = 2 atanh((m-1)/(m+1))` on `m ∈ [1, 2)` (six terms; the
truncation error is below `2·(1/3)¹³/13 < 10⁻⁷`). Returns `0` at `a = 0`. -/
@[expose] def fxLn (a : Nat) : Int :=
  if a = 0 then 0 else
  let (m, k) := fxLnNorm 128 a 0
  let y : Nat := (m - fxS) * fxS / (m + fxS)
  let y2 := y * y / fxS
  let t1 := y
  let t3 := t1 * y2 / fxS
  let t5 := t3 * y2 / fxS
  let t7 := t5 * y2 / fxS
  let t9 := t7 * y2 / fxS
  let t11 := t9 * y2 / fxS
  let s : Nat := t1 + t3 / 3 + t5 / 5 + t7 / 7 + t9 / 9 + t11 / 11
  k * 693147 + 2 * (s : Int)

/-- Effective strip width in µm after the thickness correction (`T = 0` leaves `W`). -/
@[expose] def microstripEffWidthUm (widthUm heightUm copperThickUm : Nat) : Nat :=
  if copperThickUm = 0 then widthUm else
  let lnTerm := fxLn (2 * heightUm * fxS / copperThickUm)
  let dw : Int := (copperThickUm : Int) * ((fxS : Int) + lnTerm) / 3141593
  widthUm + dw.toNat

/-- Effective permittivity ×10⁶ for `u = Weff/H` ×10⁶ and `εr` ×10⁶. -/
@[expose] def microstripEpsEffFx (u er : Nat) : Nat :=
  let q := fxS + 12 * fxS * fxS / u
  let inv := fxS * fxS / fxSqrt q
  let low := if u < fxS then 40000 * (fxS - u) * (fxS - u) / (fxS * fxS) else 0
  (er + fxS) / 2 + (er - fxS) * (inv + low) / (2 * fxS)

/-- **Closed-form microstrip `Z₀` in mΩ** from geometry (µm) and `εr` ×1000. -/
@[expose] def microstripZ0MilliOhm (widthUm heightUm copperThickUm erPermille : Nat) : Nat :=
  if widthUm = 0 ∨ heightUm = 0 then 0 else
  let wEff := microstripEffWidthUm widthUm heightUm copperThickUm
  let u := wEff * fxS / heightUm
  let er := erPermille * 1000
  let sq := fxSqrt (microstripEpsEffFx u er)
  if u ≤ fxS then
    let arg := 8 * fxS * fxS / u + u / 4
    (60 * 1000 * fxLn arg / (sq : Int)).toNat
  else
    let d : Int := (u : Int) + 1393000 + 667 * fxLn (u + 1444000) / 1000
    if d ≤ 0 then 0 else (376991 * (fxS : Int) * fxS / ((sq : Int) * d)).toNat

/-- Absolute difference $|a - b|$ on natural numbers. -/
@[expose] def natAbsDiff (a b : Nat) : Nat :=
  if b ≤ a then a - b else b - a

/-- Verify that a single-ended microstrip trace satisfies minimum fab width ($\ge 75\,\mu\text{m} \approx 3\,\text{mil}$)
and that both the field-solver value and the closed form from its own geometry are within
`z0MaxTolMilliOhm` of `z0TargetMilliOhm`: an extracted number that the geometry contradicts is refused. -/
@[expose] def checkSingleEndedZ0
    (widthUm heightUm copperThicknessUm dkPermille z0ExtractedMilliOhm z0TargetMilliOhm z0MaxTolMilliOhm : Nat) : Bool :=
  decide (75 ≤ widthUm) &&
  decide (heightUm > 0) &&
  decide (copperThicknessUm > 0) &&
  decide (natAbsDiff z0ExtractedMilliOhm z0TargetMilliOhm ≤ z0MaxTolMilliOhm) &&
  decide (natAbsDiff (microstripZ0MilliOhm widthUm heightUm copperThicknessUm dkPermille)
    z0TargetMilliOhm ≤ z0MaxTolMilliOhm)

example : checkSingleEndedZ0 330 152 35 3480 50000 50000 3000 = true := by decide +kernel

/-- Theorem (`singleEndedZ0_sound`):
If `checkSingleEndedZ0` returns `true`, then the trace width is at least $75\,\mu\text{m}$ ($3\,\text{mil}$)
and both the field-solver impedance and the closed-form Hammerstad–Jensen impedance lie within
`z0MaxTolMilliOhm` of `z0TargetMilliOhm`. -/
theorem singleEndedZ0_sound
    (widthUm heightUm copperThicknessUm dkPermille z0ExtractedMilliOhm z0TargetMilliOhm z0MaxTolMilliOhm : Nat)
    (hOk : checkSingleEndedZ0 widthUm heightUm copperThicknessUm dkPermille
             z0ExtractedMilliOhm z0TargetMilliOhm z0MaxTolMilliOhm = true) :
    75 ≤ widthUm ∧
    natAbsDiff z0ExtractedMilliOhm z0TargetMilliOhm ≤ z0MaxTolMilliOhm ∧
    natAbsDiff (microstripZ0MilliOhm widthUm heightUm copperThicknessUm dkPermille)
      z0TargetMilliOhm ≤ z0MaxTolMilliOhm := by
  unfold checkSingleEndedZ0 at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.1.1.1, hOk.1.2, hOk.2⟩

/-- **Certified Fixed-Point Square-Root Enclosure (`fxSqrt_enclosure`)**:
For every fixed-point input `a : Nat`, `s = fxSqrt a` brackets `a * fxS` tightly within one integer unit:
$$s^2 \le a \cdot 10^6 < (s + 1)^2,$$
and is strictly positive whenever `0 < a`. -/
theorem fxSqrt_enclosure (a : Nat) :
    fxSqrt a * fxSqrt a ≤ a * fxS ∧
    a * fxS < (fxSqrt a + 1) * (fxSqrt a + 1) ∧
    (0 < a → 0 < fxSqrt a) := by
  have hLe := Nat.sqrt_le (a * fxS)
  have hLt := Nat.lt_succ_sqrt (a * fxS)
  refine ⟨hLe, hLt, ?_⟩
  intro ha
  by_cases hZero : fxSqrt a = 0
  · unfold fxSqrt at hZero
    rw [hZero] at hLt
    unfold fxS at hLt
    omega
  · omega

/-- **Bahl–Garg Strip-Thickness Widening (`microstripEffWidthUm_ge_width`)**:
For all `widthUm, heightUm, copperThickUm : Nat`, the effective strip width is at least the physical
trace width (`widthUm ≤ microstripEffWidthUm widthUm heightUm copperThickUm`), with equality at `T = 0`. -/
theorem microstripEffWidthUm_ge_width (widthUm heightUm copperThickUm : Nat) :
    widthUm ≤ microstripEffWidthUm widthUm heightUm copperThickUm ∧
    microstripEffWidthUm widthUm heightUm 0 = widthUm := by
  refine ⟨?_, by simp [microstripEffWidthUm]⟩
  unfold microstripEffWidthUm
  split
  · exact Nat.le_refl widthUm
  · exact Nat.le_add_right widthUm _

/-- **Hammerstad–Jensen Effective-Permittivity Lower Enclosure & Monotonicity (`microstripEpsEffFx_enclosure_and_mono`)**. -/
theorem microstripEpsEffFx_enclosure_and_mono (u er1 er2 : Nat) :
    (er1 + fxS) / 2 ≤ microstripEpsEffFx u er1 ∧
    (fxS ≤ er1 → 0 < microstripEpsEffFx u er1) ∧
    (er1 ≤ er2 → microstripEpsEffFx u er1 ≤ microstripEpsEffFx u er2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold microstripEpsEffFx
    exact Nat.le_add_right _ _
  · intro hGe
    have hHalf : 0 < (er1 + fxS) / 2 := by
      unfold fxS at *
      omega
    unfold microstripEpsEffFx
    exact Nat.lt_of_lt_of_le hHalf (Nat.le_add_right _ _)
  · intro hLe
    unfold microstripEpsEffFx
    have hAvg : (er1 + fxS) / 2 ≤ (er2 + fxS) / 2 := Nat.div_le_div_right (by omega)
    have hDiff : er1 - fxS ≤ er2 - fxS := by omega
    have hTerm :
        (er1 - fxS) * (fxS * fxS / fxSqrt (fxS + 12 * fxS * fxS / u) +
          if u < fxS then 40000 * (fxS - u) * (fxS - u) / (fxS * fxS) else 0) / (2 * fxS) ≤
        (er2 - fxS) * (fxS * fxS / fxSqrt (fxS + 12 * fxS * fxS / u) +
          if u < fxS then 40000 * (fxS - u) * (fxS - u) / (fxS * fxS) else 0) / (2 * fxS) :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ hDiff)
    exact Nat.add_le_add hAvg hTerm

/-- Reference sanity check across standard $50\,\Omega$ Rogers RO4350B (`330 µm` on `152 µm`, `35 µm` Cu,
$\varepsilon_r = 3.48$) and high-impedance PTFE (`80 µm` on `500 µm`, $\varepsilon_r = 2.20$). -/
theorem microstripZ0_reference_enclosure :
    48000 ≤ microstripZ0MilliOhm 330 152 35 3480 ∧
    microstripZ0MilliOhm 330 152 35 3480 ≤ 52000 ∧
    175000 ≤ microstripZ0MilliOhm 80 500 0 2200 ∧
    microstripZ0MilliOhm 80 500 0 2200 ≤ 185000 ∧
    checkSingleEndedZ0 330 152 35 3480 50000 50000 3000 = true ∧
    checkSingleEndedZ0 80 500 35 2200 50000 50000 3000 = false := by
  decide +kernel

/-! ## 2. PCB Design-for-Manufacturability (`PcbFabCapabilities`, `PcbLayoutRules`, `checkPcbDfmEnvelope`) -/

/-- Physical PCB fabrication house process capability and tolerance envelope (nanometers & permille). -/
structure PcbFabCapabilities where
  minTraceWidthNm : Nat
  minTraceSpacingNm : Nat
  copperThickNm : Nat
  etchFactorMilli : Nat
  etchBiasTolNm : Nat
  localEtchMatchTolNm : Nat
  lamHeightTolNm : Nat
  maxDrillAspectRatio : Nat
  drillWanderNm : Nat
  layerRegTolNm : Nat
  minAnnularRingNm : Nat
  solderMaskExpansionNm : Nat
  minSolderMaskWebNm : Nat
  minJunctionAngleDeg : Nat
  maxCopperImbalancePermille : Nat
  deriving DecidableEq, Repr

/-- Candidate PCB layout geometry and copper balance parameters audited against `PcbFabCapabilities`. -/
structure PcbLayoutRules where
  nomTraceWidthNm : Nat
  nomTraceSpacingNm : Nat
  boardThicknessNm : Nat
  viaDrillRadiusNm : Nat
  viaPadRadiusNm : Nat
  minTraceAngleDeg : Nat
  padPitchNm : Nat
  padWidthNm : Nat
  symLayerCopperPairsPermille : List (Nat × Nat)
  regionCopperTilesPermille : List Nat
  deriving DecidableEq, Repr

/-- Per-side trapezoidal lateral etch undercut $\lceil T_{\text{Cu}} \cdot 1000 / E_{\text{etch,milli}} \rceil$ (nm). -/
def trapezoidalUndercutPerSideNm (fab : PcbFabCapabilities) : Nat :=
  (fab.copperThickNm * 1000 + fab.etchFactorMilli - 1) / fab.etchFactorMilli

/-- Worst-case two-sided trace width / spacing etch variation $\delta_{\text{etch}}$ (nm). -/
def etchVariationBoundNm (fab : PcbFabCapabilities) : Nat :=
  2 * trapezoidalUndercutPerSideNm fab + fab.etchBiasTolNm

/-- Remaining photoimageable solder-mask dam width between adjacent SMT pads (nm, signed). -/
def solderMaskWebNm (fab : PcbFabCapabilities) (layout : PcbLayoutRules) : Int :=
  (layout.padPitchNm : Int) - ((layout.padWidthNm : Int) + 2 * (fab.solderMaskExpansionNm : Int))

/-- Verify stackup mirror-layer symmetry and in-plane copper thieving balance to prevent reflow bow/twist. -/
def checkCopperDensityBalanced
    (maxDeltaPermille : Nat) (symPairs : List (Nat × Nat)) (regionTiles : List Nat) : Bool :=
  !symPairs.isEmpty &&
  !regionTiles.isEmpty &&
  symPairs.all (fun p =>
    decide (p.1 ≤ 1000 ∧ p.2 ≤ 1000) && decide (natAbsDiff p.1 p.2 ≤ maxDeltaPermille)) &&
  regionTiles.all (fun t1 =>
    decide (t1 ≤ 1000) &&
    regionTiles.all (fun t2 => decide (natAbsDiff t1 t2 ≤ maxDeltaPermille)))

example : checkCopperDensityBalanced 100 [(620, 600), (750, 720)] [580, 610, 640] = true := by
  decide +kernel

theorem checkCopperDensityBalanced_sound
    (maxDeltaPermille : Nat) (symPairs : List (Nat × Nat)) (regionTiles : List Nat)
    (hOk : checkCopperDensityBalanced maxDeltaPermille symPairs regionTiles = true) :
    symPairs ≠ [] ∧ regionTiles ≠ [] ∧
    (∀ p ∈ symPairs, p.1 ≤ 1000 ∧ p.2 ≤ 1000 ∧ natAbsDiff p.1 p.2 ≤ maxDeltaPermille) ∧
    (∀ t1 ∈ regionTiles, ∀ t2 ∈ regionTiles, t1 ≤ 1000 ∧ natAbsDiff t1 t2 ≤ maxDeltaPermille) := by
  unfold checkCopperDensityBalanced at hOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨hsNe, hrNe⟩, hSym⟩, hReg⟩ := hOk
  refine ⟨fun h => by rw [h] at hsNe; simp at hsNe,
          fun h => by rw [h] at hrNe; simp at hrNe,
          fun p hp => ⟨(hSym p hp).1.1, (hSym p hp).1.2, (hSym p hp).2⟩,
          fun t1 ht1 t2 ht2 => ⟨(hReg t1 ht1).1, (hReg t1 ht1).2 t2 ht2⟩⟩

/-- Full PCB DFM & fab-tolerance envelope checker (`checkPcbDfmEnvelope`). -/
@[expose] def checkPcbDfmEnvelope (fab : PcbFabCapabilities) (layout : PcbLayoutRules) : Bool :=
  let dEtch := etchVariationBoundNm fab
  let dDrill := 2 * layout.viaDrillRadiusNm
  decide (0 < fab.minTraceWidthNm ∧ 0 < fab.minTraceSpacingNm) &&
  decide (0 < fab.copperThickNm ∧ 0 < fab.etchFactorMilli) &&
  decide (0 < fab.maxDrillAspectRatio ∧ 0 < fab.minAnnularRingNm) &&
  decide (0 < fab.minSolderMaskWebNm ∧ 90 ≤ fab.minJunctionAngleDeg) &&
  decide (fab.localEtchMatchTolNm ≤ dEtch) &&
  decide (fab.minTraceWidthNm + dEtch ≤ layout.nomTraceWidthNm) &&
  decide (fab.minTraceSpacingNm + dEtch ≤ layout.nomTraceSpacingNm) &&
  decide (0 < layout.viaDrillRadiusNm) &&
  decide (layout.boardThicknessNm ≤ fab.maxDrillAspectRatio * dDrill) &&
  decide (layout.viaDrillRadiusNm + fab.drillWanderNm + fab.layerRegTolNm + fab.minAnnularRingNm ≤
    layout.viaPadRadiusNm) &&
  decide (fab.minJunctionAngleDeg ≤ layout.minTraceAngleDeg) &&
  decide ((fab.minSolderMaskWebNm : Int) ≤ solderMaskWebNm fab layout) &&
  checkCopperDensityBalanced fab.maxCopperImbalancePermille
    layout.symLayerCopperPairsPermille layout.regionCopperTilesPermille

def ipcClass3RfFab : PcbFabCapabilities where
  minTraceWidthNm := 75000
  minTraceSpacingNm := 75000
  copperThickNm := 35000
  etchFactorMilli := 3500
  etchBiasTolNm := 5000
  localEtchMatchTolNm := 4000
  lamHeightTolNm := 10000
  maxDrillAspectRatio := 10
  drillWanderNm := 25000
  layerRegTolNm := 35000
  minAnnularRingNm := 50000
  solderMaskExpansionNm := 40000
  minSolderMaskWebNm := 75000
  minJunctionAngleDeg := 90
  maxCopperImbalancePermille := 100

def ipcClass3RfLayout : PcbLayoutRules where
  nomTraceWidthNm := 160000
  nomTraceSpacingNm := 150000
  boardThicknessNm := 1600000
  viaDrillRadiusNm := 100000
  viaPadRadiusNm := 225000
  minTraceAngleDeg := 135
  padPitchNm := 500000
  padWidthNm := 250000
  symLayerCopperPairsPermille := [(640, 610), (780, 760)]
  regionCopperTilesPermille := [600, 630, 650]

example : checkPcbDfmEnvelope ipcClass3RfFab ipcClass3RfLayout = true := by decide +kernel

/-- **Copper Etch & Trapezoidal Undercut Open/Short Immunity (`dfm_etch_prevents_open_and_short`)**:
Across every signed etch process corner $|\Delta_w| \le \delta_{\text{etch}}, |\Delta_s| \le \delta_{\text{etch}}$,
the trapezoidal lateral undercut is upper-bounded by `trapezoidalUndercutPerSideNm`, actual trace width
stays inside $[w_{\text{nom}} - \delta_{\text{etch}}, w_{\text{nom}} + \delta_{\text{etch}}]$ above $w_{\text{minFab}} > 0$
(preventing neck-opens), and actual spacing stays above $s_{\text{minFab}} > 0$ (preventing copper bridges). -/
theorem dfm_etch_prevents_open_and_short
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (hOk : checkPcbDfmEnvelope fab layout = true)
    (dw ds : Int)
    (hdw : dw.natAbs ≤ etchVariationBoundNm fab)
    (hds : ds.natAbs ≤ etchVariationBoundNm fab) :
    fab.copperThickNm * 1000 ≤ trapezoidalUndercutPerSideNm fab * fab.etchFactorMilli ∧
    (layout.nomTraceWidthNm : Int) - (etchVariationBoundNm fab : Int) ≤ (layout.nomTraceWidthNm : Int) + dw ∧
    (layout.nomTraceWidthNm : Int) + dw ≤ (layout.nomTraceWidthNm : Int) + (etchVariationBoundNm fab : Int) ∧
    (fab.minTraceWidthNm : Int) ≤ (layout.nomTraceWidthNm : Int) + dw ∧
    0 < (layout.nomTraceWidthNm : Int) + dw ∧
    (fab.minTraceSpacingNm : Int) ≤ (layout.nomTraceSpacingNm : Int) + ds ∧
    0 < (layout.nomTraceSpacingNm : Int) + ds := by
  unfold checkPcbDfmEnvelope at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hMinW : 0 < fab.minTraceWidthNm := hOk.1.1.1.1.1.1.1.1.1.1.1.1.1
  have hMinS : 0 < fab.minTraceSpacingNm := hOk.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hEtchPos : 0 < fab.etchFactorMilli := hOk.1.1.1.1.1.1.1.1.1.1.1.2.2
  have hNomW : fab.minTraceWidthNm + etchVariationBoundNm fab ≤ layout.nomTraceWidthNm :=
    hOk.1.1.1.1.1.1.1.2
  have hNomS : fab.minTraceSpacingNm + etchVariationBoundNm fab ≤ layout.nomTraceSpacingNm :=
    hOk.1.1.1.1.1.1.2
  have hCeil : fab.copperThickNm * 1000 ≤ trapezoidalUndercutPerSideNm fab * fab.etchFactorMilli := by
    let num := fab.copperThickNm * 1000 + fab.etchFactorMilli - 1
    have hDivMod := Nat.div_add_mod num fab.etchFactorMilli
    have hModLt := Nat.mod_lt num hEtchPos
    have hComm : fab.etchFactorMilli * (num / fab.etchFactorMilli) =
        (num / fab.etchFactorMilli) * fab.etchFactorMilli := Nat.mul_comm _ _
    change fab.copperThickNm * 1000 ≤ (num / fab.etchFactorMilli) * fab.etchFactorMilli
    dsimp only [num] at hDivMod hModLt hComm ⊢
    omega
  refine ⟨hCeil, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **Drill Aspect Ratio & Via Annular-Ring Breakout Impossibility (`dfm_via_breakout_impossible`)**:
Plated-through-hole aspect ratio satisfies $H_{\text{board}} \le \text{AR}_{\max} \cdot d_{\text{drill}}$,
and across every signed drill wander $|\Delta_{\text{wander}}| \le \delta_{\text{drillWander}}$ and
layer registration shift $|\Delta_{\text{reg}}| \le \delta_{\text{layerReg}}$, the remaining copper
annular ring is at least $w_{\text{minAnnularRing}} > 0$ (zero tangency or breakout). -/
theorem dfm_via_breakout_impossible
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (hOk : checkPcbDfmEnvelope fab layout = true)
    (dWander dReg : Int)
    (hWander : dWander.natAbs ≤ fab.drillWanderNm)
    (hReg : dReg.natAbs ≤ fab.layerRegTolNm) :
    0 < 2 * layout.viaDrillRadiusNm ∧
    layout.boardThicknessNm ≤ fab.maxDrillAspectRatio * (2 * layout.viaDrillRadiusNm) ∧
    0 < fab.minAnnularRingNm ∧
    (fab.minAnnularRingNm : Int) ≤
      (layout.viaPadRadiusNm : Int) -
        ((layout.viaDrillRadiusNm : Int) + ((dWander + dReg).natAbs : Int)) := by
  unfold checkPcbDfmEnvelope at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hRingPos : 0 < fab.minAnnularRingNm := hOk.1.1.1.1.1.1.1.1.1.1.2.2
  have hDrillPos : 0 < layout.viaDrillRadiusNm := hOk.1.1.1.1.1.2
  have hAr : layout.boardThicknessNm ≤ fab.maxDrillAspectRatio * (2 * layout.viaDrillRadiusNm) :=
    hOk.1.1.1.1.2
  have hPad : layout.viaDrillRadiusNm + fab.drillWanderNm + fab.layerRegTolNm + fab.minAnnularRingNm ≤
      layout.viaPadRadiusNm := hOk.1.1.1.2
  exact ⟨by omega, hAr, hRingPos, by omega⟩

/-- **Acid-Trap Refusal, Solder-Mask Sliver Immunity & Copper-Balance Soundness (`dfm_acid_trap_sliver_and_thieving_sound`)**. -/
theorem dfm_acid_trap_sliver_and_thieving_sound
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (hOk : checkPcbDfmEnvelope fab layout = true) :
    90 ≤ layout.minTraceAngleDeg ∧
    (fab.minSolderMaskWebNm : Int) ≤ solderMaskWebNm fab layout ∧
    0 < solderMaskWebNm fab layout ∧
    (∀ p ∈ layout.symLayerCopperPairsPermille, natAbsDiff p.1 p.2 ≤ fab.maxCopperImbalancePermille) ∧
    (∀ t1 ∈ layout.regionCopperTilesPermille, ∀ t2 ∈ layout.regionCopperTilesPermille,
      natAbsDiff t1 t2 ≤ fab.maxCopperImbalancePermille) := by
  unfold checkPcbDfmEnvelope at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hMinWeb : 0 < fab.minSolderMaskWebNm := hOk.1.1.1.1.1.1.1.1.1.2.1
  have hMinAng : 90 ≤ fab.minJunctionAngleDeg := hOk.1.1.1.1.1.1.1.1.1.2.2
  have hAng : fab.minJunctionAngleDeg ≤ layout.minTraceAngleDeg := hOk.1.1.2
  have hWeb : (fab.minSolderMaskWebNm : Int) ≤ solderMaskWebNm fab layout := hOk.1.2
  have hCu := checkCopperDensityBalanced_sound fab.maxCopperImbalancePermille
    layout.symLayerCopperPairsPermille layout.regionCopperTilesPermille hOk.2
  refine ⟨by omega, hWeb, by omega,
    fun p hp => (hCu.2.2.1 p hp).2.2,
    fun t1 ht1 t2 ht2 => (hCu.2.2.2 t1 ht1 t2 ht2).2⟩

/-! ## 3. FEM-Bracketed Coupled Differential $(\mathbf{L}, \mathbf{C})$ & DFM-Propagated Skew / Mode Conversion -/

private theorem rat_div_mono_interval {nLo nHi dLo dHi n d : Rat}
    (hnLo : 0 ≤ nLo) (hn : nLo ≤ n ∧ n ≤ nHi)
    (hdLo : 0 < dLo) (hd : dLo ≤ d ∧ d ≤ dHi) :
    nLo / dHi ≤ n / d ∧ n / d ≤ nHi / dLo := by
  have hdPos : 0 < d := by grind
  have hdHiPos : 0 < dHi := by grind
  have hnPos : 0 ≤ n := by grind
  constructor
  · apply rat_div_le_of_mul_le hdHiPos
    have h1 : nLo ≤ (n / d) * d := by rw [Rat.div_mul_cancel (Rat.ne_of_gt hdPos)]; exact hn.1
    have hndNonneg : 0 ≤ n / d := rat_div_nonneg hnPos hdPos
    have h2 : (n / d) * d ≤ (n / d) * dHi := Rat.mul_le_mul_of_nonneg_left hd.2 hndNonneg
    grind
  · apply rat_le_div_of_mul_le hdLo
    have h1 : (n / d) * dLo ≤ (n / d) * d :=
      Rat.mul_le_mul_of_nonneg_left hd.1 (rat_div_nonneg hnPos hdPos)
    have h2 : (n / d) * d = n := Rat.div_mul_cancel (Rat.ne_of_gt hdPos)
    grind

private theorem rat_le_of_sq_le_sq {a b : Rat} (hb : 0 ≤ b) (hsq : a * a ≤ b * b) :
    a ≤ b := by
  rcases @Rat.le_total a b with hle | hge
  · exact hle
  · by_cases heq : a = b
    · grind
    · have hlt : b < a := by grind
      have h1 : b * b ≤ a * b := Rat.mul_le_mul_of_nonneg_right hge hb
      have h2 : a * b < a * a := Rat.mul_lt_mul_of_pos_left hlt (by grind)
      grind

/-- SI vacuum permittivity scale $\varepsilon_0 \approx 8{,}854{,}187\,\text{aF/m}$ converting dimensionless
2D FEM energy $\int_\Omega \varepsilon_r |\nabla u|^2 \, dx\,dy$ to physical per-unit-length capacitance ($\text{aF/m}$). -/
def eps0AttoFPerMeter : Rat := 8854187

/-- Coupled 2-conductor even/odd cross-section FEEC Prager–Synge problems & per-unit-length inductance brackets. -/
structure CoupledFemExtraction2D where
  evenProb : FeecPdeProblem2D
  evenCert : FeecPragerSyngeCert2D
  oddProb : FeecPdeProblem2D
  oddCert : FeecPragerSyngeCert2D
  capUnitScaleAttoF : Rat
  lEvenLoPicoH : Rat
  lEvenHiPicoH : Rat
  lOddLoPicoH : Rat
  lOddHiPicoH : Rat
  deriving DecidableEq, Repr

def cEvenLoAttoF (ext : CoupledFemExtraction2D) : Rat :=
  ext.capUnitScaleAttoF * capacitanceLowerBound ext.evenProb.mesh ext.evenCert.uh ext.evenCert.flux
def cEvenHiAttoF (ext : CoupledFemExtraction2D) : Rat :=
  ext.capUnitScaleAttoF * capacitanceUpperBound ext.evenProb.mesh ext.evenCert.uh
def cOddLoAttoF (ext : CoupledFemExtraction2D) : Rat :=
  ext.capUnitScaleAttoF * capacitanceLowerBound ext.oddProb.mesh ext.oddCert.uh ext.oddCert.flux
def cOddHiAttoF (ext : CoupledFemExtraction2D) : Rat :=
  ext.capUnitScaleAttoF * capacitanceUpperBound ext.oddProb.mesh ext.oddCert.uh

/-- Squared modal & differential/common-mode impedance bounds in $(\text{m}\Omega)^2$, using exact SI identity
$(1000\,\text{m}\Omega/\Omega)^2 \cdot (10^{-12}\,\text{H/pH}) / (10^{-18}\,\text{F/aF}) = 10^{12}$. -/
def mOhmSqPerPicoHAttoF : Rat := 1000000000000

def zOddSqLoMilliOhmSq (ext : CoupledFemExtraction2D) : Rat :=
  (mOhmSqPerPicoHAttoF * ext.lOddLoPicoH) / cOddHiAttoF ext
def zOddSqHiMilliOhmSq (ext : CoupledFemExtraction2D) : Rat :=
  (mOhmSqPerPicoHAttoF * ext.lOddHiPicoH) / cOddLoAttoF ext
def zDiffSqLoMilliOhmSq (ext : CoupledFemExtraction2D) : Rat :=
  (4 * mOhmSqPerPicoHAttoF * ext.lOddLoPicoH) / cOddHiAttoF ext
def zDiffSqHiMilliOhmSq (ext : CoupledFemExtraction2D) : Rat :=
  (4 * mOhmSqPerPicoHAttoF * ext.lOddHiPicoH) / cOddLoAttoF ext
def zCommSqLoMilliOhmSq (ext : CoupledFemExtraction2D) : Rat :=
  (mOhmSqPerPicoHAttoF * ext.lEvenLoPicoH) / (4 * cEvenHiAttoF ext)
def zCommSqHiMilliOhmSq (ext : CoupledFemExtraction2D) : Rat :=
  (mOhmSqPerPicoHAttoF * ext.lEvenHiPicoH) / (4 * cEvenLoAttoF ext)

def checkCoupledFemExtraction (ext : CoupledFemExtraction2D) : Bool :=
  decide (checkFeecPragerSynge ext.evenProb ext.evenCert = .ok) &&
  decide (checkFeecPragerSynge ext.oddProb ext.oddCert = .ok) &&
  decide (0 < ext.capUnitScaleAttoF) &&
  decide (0 < dualComplementaryEnergy ext.evenProb.mesh ext.evenCert.flux) &&
  decide (0 < dualComplementaryEnergy ext.oddProb.mesh ext.oddCert.flux) &&
  decide (0 < cEvenLoAttoF ext) &&
  decide (cEvenHiAttoF ext < cOddLoAttoF ext) &&
  decide (0 < ext.lEvenLoPicoH ∧ ext.lEvenLoPicoH ≤ ext.lEvenHiPicoH) &&
  decide (0 < ext.lOddLoPicoH ∧ ext.lOddLoPicoH ≤ ext.lOddHiPicoH)

def coupledEvenCapMesh : SimplexMesh2D where
  verts := [⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩]
  vertRoles := [.outerBoundary, .outerBoundary, .conductorBoundary 1, .conductorBoundary 1]
  tris :=
    [ { i0 := 0, i1 := 1, i2 := 2, eps := Mat2Q.isotropic 3, sourceF := 0 }
    , { i0 := 0, i1 := 2, i2 := 3, eps := Mat2Q.isotropic 3, sourceF := 0 } ]
  dirichletEdges := [(0, 1), (2, 3)]
  neumannEdges := [(1, 2), (3, 0)]

def coupledOddCapMesh : SimplexMesh2D where
  verts := [⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩]
  vertRoles := [.outerBoundary, .outerBoundary, .conductorBoundary 1, .conductorBoundary 1]
  tris :=
    [ { i0 := 0, i1 := 1, i2 := 2, eps := Mat2Q.isotropic 5, sourceF := 0 }
    , { i0 := 0, i1 := 2, i2 := 3, eps := Mat2Q.isotropic 5, sourceF := 0 } ]
  dirichletEdges := [(0, 1), (2, 3)]
  neumannEdges := [(1, 2), (3, 0)]

def coupledDiffSampleExtraction : CoupledFemExtraction2D where
  evenProb := { unitSquareCapProblem with mesh := coupledEvenCapMesh }
  evenCert := { uh := [0, 0, 1, 1], flux := [⟨0, -3, 0⟩, ⟨0, -3, 0⟩] }
  oddProb := { unitSquareCapProblem with mesh := coupledOddCapMesh }
  oddCert := { uh := [0, 0, 1, 1], flux := [⟨0, -5, 0⟩, ⟨0, -5, 0⟩] }
  capUnitScaleAttoF := 20000000
  lEvenLoPicoH := 330000
  lEvenHiPicoH := 340000
  lOddLoPicoH := 248000
  lOddHiPicoH := 252000

example : checkCoupledFemExtraction coupledDiffSampleExtraction = true := by decide +kernel

/-- **FEM-Bracketed Coupled Differential $(\mathbf{L}, \mathbf{C})$ Soundness (`coupledFem_thomsonDirichlet_impedance_brackets_sound`)**:
Welds `Obend.Analysis.SimplicialFeecFem.thomsonDirichlet_capacitance_bracket` on the even and odd
eigenmodes of $\mathbf{C} = \begin{bmatrix} C_{11} & -C_m \\ -C_m & C_{22} \end{bmatrix}$ into certified
two-sided continuum brackets on $C_{\text{even}}, C_{\text{odd}}$, mutual coupling $C_m = (C_{\text{odd}} - C_{\text{even}})/2 > 0$,
and squared impedances $Z_{\text{odd}}^2, Z_{\text{diff}}^2 = (2 Z_{\text{odd}})^2, Z_{\text{comm}}^2 = (Z_{\text{even}}/2)^2$. -/
theorem coupledFem_thomsonDirichlet_impedance_brackets_sound
    (ext : CoupledFemExtraction2D)
    (hOk : checkCoupledFemExtraction ext = true)
    {FieldE FieldO : Type}
    (HE : ContinuumEnergySpace FieldE) (HO : ContinuumEnergySpace FieldO)
    (gradUE gradUhE epsInvSigmaE : FieldE) (gradUO gradUhO epsInvSigmaO : FieldO)
    (cEvenDimless cOddDimless lEvenTruePicoH lOddTruePicoH : Rat)
    (hcEven : cEvenDimless = HE.normSq gradUE)
    (hPrimalE : HE.normSq gradUhE = capacitanceUpperBound ext.evenProb.mesh ext.evenCert.uh)
    (hDualE : HE.normSq epsInvSigmaE = dualComplementaryEnergy ext.evenProb.mesh ext.evenCert.flux)
    (hWeakE : HE.innerEps gradUE (HE.sub gradUhE gradUE) = 0)
    (hChargeE : HE.innerEps gradUE epsInvSigmaE =
      -dualNetElectrodeCharge ext.evenProb.mesh ext.evenCert.uh ext.evenCert.flux)
    (hcOdd : cOddDimless = HO.normSq gradUO)
    (hPrimalO : HO.normSq gradUhO = capacitanceUpperBound ext.oddProb.mesh ext.oddCert.uh)
    (hDualO : HO.normSq epsInvSigmaO = dualComplementaryEnergy ext.oddProb.mesh ext.oddCert.flux)
    (hWeakO : HO.innerEps gradUO (HO.sub gradUhO gradUO) = 0)
    (hChargeO : HO.innerEps gradUO epsInvSigmaO =
      -dualNetElectrodeCharge ext.oddProb.mesh ext.oddCert.uh ext.oddCert.flux)
    (hlEven : ext.lEvenLoPicoH ≤ lEvenTruePicoH ∧ lEvenTruePicoH ≤ ext.lEvenHiPicoH)
    (hlOdd : ext.lOddLoPicoH ≤ lOddTruePicoH ∧ lOddTruePicoH ≤ ext.lOddHiPicoH) :
    let cEvenTrue := ext.capUnitScaleAttoF * cEvenDimless
    let cOddTrue := ext.capUnitScaleAttoF * cOddDimless
    let cMutual := (cOddTrue - cEvenTrue) / 2
    CertifiedFeecPde ext.evenProb ext.evenCert ∧
    CertifiedFeecPde ext.oddProb ext.oddCert ∧
    (cEvenLoAttoF ext ≤ cEvenTrue ∧ cEvenTrue ≤ cEvenHiAttoF ext) ∧
    (cOddLoAttoF ext ≤ cOddTrue ∧ cOddTrue ≤ cOddHiAttoF ext) ∧
    0 < cMutual ∧
    (zOddSqLoMilliOhmSq ext ≤ (mOhmSqPerPicoHAttoF * lOddTruePicoH) / cOddTrue ∧
      (mOhmSqPerPicoHAttoF * lOddTruePicoH) / cOddTrue ≤ zOddSqHiMilliOhmSq ext) ∧
    (zDiffSqLoMilliOhmSq ext ≤ (4 * mOhmSqPerPicoHAttoF * lOddTruePicoH) / cOddTrue ∧
      (4 * mOhmSqPerPicoHAttoF * lOddTruePicoH) / cOddTrue ≤ zDiffSqHiMilliOhmSq ext) ∧
    (zCommSqLoMilliOhmSq ext ≤ (mOhmSqPerPicoHAttoF * lEvenTruePicoH) / (4 * cEvenTrue) ∧
      (mOhmSqPerPicoHAttoF * lEvenTruePicoH) / (4 * cEvenTrue) ≤ zCommSqHiMilliOhmSq ext) := by
  unfold checkCoupledFemExtraction at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hFeecE := checkFeecPragerSynge_sound hOk.1.1.1.1.1.1.1.1
  have hFeecO := checkFeecPragerSynge_sound hOk.1.1.1.1.1.1.1.2
  have hScalePos : 0 < ext.capUnitScaleAttoF := hOk.1.1.1.1.1.1.2
  have hDualPosE : 0 < dualComplementaryEnergy ext.evenProb.mesh ext.evenCert.flux := hOk.1.1.1.1.1.2
  have hDualPosO : 0 < dualComplementaryEnergy ext.oddProb.mesh ext.oddCert.flux := hOk.1.1.1.1.2
  have hcEvenLoPos : 0 < cEvenLoAttoF ext := hOk.1.1.1.2
  have hcSep : cEvenHiAttoF ext < cOddLoAttoF ext := hOk.1.1.2
  have hlEvenPos : 0 < ext.lEvenLoPicoH := hOk.1.2.1
  have hlOddPos : 0 < ext.lOddLoPicoH := hOk.2.1
  have hBrE := thomsonDirichlet_capacitance_bracket HE ext.evenProb.mesh ext.evenCert.uh ext.evenCert.flux
    gradUE gradUhE epsInvSigmaE cEvenDimless hcEven hPrimalE hDualE hDualPosE hWeakE hChargeE
  have hBrO := thomsonDirichlet_capacitance_bracket HO ext.oddProb.mesh ext.oddCert.uh ext.oddCert.flux
    gradUO gradUhO epsInvSigmaO cOddDimless hcOdd hPrimalO hDualO hDualPosO hWeakO hChargeO
  have hcE : cEvenLoAttoF ext ≤ ext.capUnitScaleAttoF * cEvenDimless ∧
      ext.capUnitScaleAttoF * cEvenDimless ≤ cEvenHiAttoF ext :=
    ⟨Rat.mul_le_mul_of_nonneg_left hBrE.1 (Rat.le_of_lt hScalePos),
     Rat.mul_le_mul_of_nonneg_left hBrE.2 (Rat.le_of_lt hScalePos)⟩
  have hcO : cOddLoAttoF ext ≤ ext.capUnitScaleAttoF * cOddDimless ∧
      ext.capUnitScaleAttoF * cOddDimless ≤ cOddHiAttoF ext :=
    ⟨Rat.mul_le_mul_of_nonneg_left hBrO.1 (Rat.le_of_lt hScalePos),
     Rat.mul_le_mul_of_nonneg_left hBrO.2 (Rat.le_of_lt hScalePos)⟩
  have hcOddLoPos : 0 < cOddLoAttoF ext := by grind
  have hmPos : 0 ≤ mOhmSqPerPicoHAttoF := by unfold mOhmSqPerPicoHAttoF; grind
  have h4mPos : 0 ≤ 4 * mOhmSqPerPicoHAttoF := by unfold mOhmSqPerPicoHAttoF; grind
  have hzOdd := rat_div_mono_interval
    (Rat.mul_nonneg hmPos (Rat.le_of_lt hlOddPos))
    ⟨Rat.mul_le_mul_of_nonneg_left hlOdd.1 hmPos, Rat.mul_le_mul_of_nonneg_left hlOdd.2 hmPos⟩
    hcOddLoPos hcO
  have hzDiff := rat_div_mono_interval
    (Rat.mul_nonneg h4mPos (Rat.le_of_lt hlOddPos))
    ⟨Rat.mul_le_mul_of_nonneg_left hlOdd.1 h4mPos, Rat.mul_le_mul_of_nonneg_left hlOdd.2 h4mPos⟩
    hcOddLoPos hcO
  have hzComm := rat_div_mono_interval
    (Rat.mul_nonneg hmPos (Rat.le_of_lt hlEvenPos))
    ⟨Rat.mul_le_mul_of_nonneg_left hlEven.1 hmPos, Rat.mul_le_mul_of_nonneg_left hlEven.2 hmPos⟩
    (show 0 < 4 * cEvenLoAttoF ext by grind) (show 4 * cEvenLoAttoF ext ≤ 4 * (ext.capUnitScaleAttoF * cEvenDimless) ∧
      4 * (ext.capUnitScaleAttoF * cEvenDimless) ≤ 4 * cEvenHiAttoF ext by grind)
  refine ⟨hFeecE, hFeecO, hcE, hcO, ?_, hzOdd, hzDiff, hzComm⟩
  exact rat_div_pos (by grind) (by grind)

/-- Exact SI vacuum speed of light $c_0 = 299{,}792{,}458\,\text{m/s}$ for quasi-TEM $(\mathbf{L}, \mathbf{C}_{\text{air}})$ duality. -/
def c0MetersPerSec : Nat := 299792458

/-- Quasi-TEM $L \cdot C_{\text{air}} = \ell^2 / c_0^2$ constant in $\text{pH} \cdot \text{aF}$ over segment length `lenNm` ($\text{nm}$). -/
def temKappaPicoHAttoF (lenNm : Nat) : Rat :=
  (1000000000000 * (lenNm : Rat) * (lenNm : Rat)) / ((c0MetersPerSec : Rat) * (c0MetersPerSec : Rat))

/-- Derive rigorous two-sided quasi-TEM inductance brackets $[L_{\text{lo}}, L_{\text{hi}}]$ ($\text{pH}$)
directly from an air-filled ($\varepsilon_r = 1$) FEEC Thomson–Dirichlet capacitance certificate via $L = \kappa / C_{\text{air}}$. -/
def deriveTemInductanceBrackets
    (kappaPicoHAttoF : Rat) (airProb : FeecPdeProblem2D)
    (airCert : FeecPragerSyngeCert2D) (capUnitScaleAttoF : Rat) : Rat × Rat :=
  let cAirLo := capUnitScaleAttoF * capacitanceLowerBound airProb.mesh airCert.uh airCert.flux
  let cAirHi := capUnitScaleAttoF * capacitanceUpperBound airProb.mesh airCert.uh
  (kappaPicoHAttoF / cAirHi, kappaPicoHAttoF / cAirLo)

/-- **Quasi-TEM Inductance Bracket Derivation Soundness (`deriveTemInductanceBrackets_sound`)**:
Welds `thomsonDirichlet_capacitance_bracket` on the air-filled cross-section ($\varepsilon_r = 1$) with
order-reversing reciprocal interval arithmetic $L = \kappa / C_{\text{air}}$ to certify rigorous two-sided
continuum inductance bounds $L_{\text{lo}} \le L_{\text{true}} \le L_{\text{hi}}$. -/
theorem deriveTemInductanceBrackets_sound
    (kappaPicoHAttoF : Rat) (airProb : FeecPdeProblem2D)
    (airCert : FeecPragerSyngeCert2D) (capUnitScaleAttoF : Rat)
    (hAirOk : checkFeecPragerSynge airProb airCert = .ok)
    (hKappaPos : 0 < kappaPicoHAttoF) (hScalePos : 0 < capUnitScaleAttoF)
    (hDualPos : 0 < dualComplementaryEnergy airProb.mesh airCert.flux)
    (hcLoPos : 0 < capacitanceLowerBound airProb.mesh airCert.uh airCert.flux)
    {FieldA : Type} (HA : ContinuumEnergySpace FieldA)
    (gradUA gradUhA epsInvSigmaA : FieldA) (cAirDimless : Rat)
    (hcAir : cAirDimless = HA.normSq gradUA)
    (hPrimalA : HA.normSq gradUhA = capacitanceUpperBound airProb.mesh airCert.uh)
    (hDualA : HA.normSq epsInvSigmaA = dualComplementaryEnergy airProb.mesh airCert.flux)
    (hWeakA : HA.innerEps gradUA (HA.sub gradUhA gradUA) = 0)
    (hChargeA : HA.innerEps gradUA epsInvSigmaA =
      -dualNetElectrodeCharge airProb.mesh airCert.uh airCert.flux) :
    let brackets := deriveTemInductanceBrackets kappaPicoHAttoF airProb airCert capUnitScaleAttoF
    let lTruePicoH := kappaPicoHAttoF / (capUnitScaleAttoF * cAirDimless)
    CertifiedFeecPde airProb airCert ∧
    0 < brackets.1 ∧
    brackets.1 ≤ lTruePicoH ∧
    lTruePicoH ≤ brackets.2 := by
  have hFeec := checkFeecPragerSynge_sound hAirOk
  have hBr := thomsonDirichlet_capacitance_bracket HA airProb.mesh airCert.uh airCert.flux
    gradUA gradUhA epsInvSigmaA cAirDimless hcAir hPrimalA hDualA hDualPos hWeakA hChargeA
  have hcAirLoPos : 0 < capUnitScaleAttoF * capacitanceLowerBound airProb.mesh airCert.uh airCert.flux :=
    Rat.mul_pos hScalePos hcLoPos
  have hcAirBounds :
      capUnitScaleAttoF * capacitanceLowerBound airProb.mesh airCert.uh airCert.flux ≤
        capUnitScaleAttoF * cAirDimless ∧
      capUnitScaleAttoF * cAirDimless ≤
        capUnitScaleAttoF * capacitanceUpperBound airProb.mesh airCert.uh :=
    ⟨Rat.mul_le_mul_of_nonneg_left hBr.1 (Rat.le_of_lt hScalePos),
     Rat.mul_le_mul_of_nonneg_left hBr.2 (Rat.le_of_lt hScalePos)⟩
  have hInv := rat_div_mono_interval (Rat.le_of_lt hKappaPos) ⟨Rat.le_refl, Rat.le_refl⟩
    hcAirLoPos hcAirBounds
  have hLoPos : 0 < kappaPicoHAttoF / (capUnitScaleAttoF * capacitanceUpperBound airProb.mesh airCert.uh) :=
    rat_div_pos hKappaPos (by grind)
  exact ⟨hFeec, hLoPos, hInv.1, hInv.2⟩

private theorem coupledEvenCapMesh_geom :
    ∀ t ∈ coupledEvenCapMesh.tris,
      0 < twiceArea2D (getVert2D coupledEvenCapMesh.verts t.i0)
            (getVert2D coupledEvenCapMesh.verts t.i1)
            (getVert2D coupledEvenCapMesh.verts t.i2) ∧
      t.eps.isSpd := by
  have hS := checkMeshConformingAndCadValid_sound coupledEvenCapMesh unitSquareCadFRep
    (.sub .varY (.const 1)) 0 (1 / 100) 10 (by decide +kernel)
  exact fun t ht => ⟨(hS.2.2.2.1 t ht).1, (hS.2.2.2.1 t ht).2.2.2⟩

private theorem coupledOddCapMesh_geom :
    ∀ t ∈ coupledOddCapMesh.tris,
      0 < twiceArea2D (getVert2D coupledOddCapMesh.verts t.i0)
            (getVert2D coupledOddCapMesh.verts t.i1)
            (getVert2D coupledOddCapMesh.verts t.i2) ∧
      t.eps.isSpd := by
  have hS := checkMeshConformingAndCadValid_sound coupledOddCapMesh unitSquareCadFRep
    (.sub .varY (.const 1)) 0 (1 / 100) 10 (by decide +kernel)
  exact fun t ht => ⟨(hS.2.2.2.1 t ht).1, (hS.2.2.2.1 t ht).2.2.2⟩

/-- Non-vacuity witness instantiating `coupledFem_thomsonDirichlet_impedance_brackets_sound` on
`coupledDiffSampleExtraction` over `meshContinuumEnergySpace` (`0` vacuous hypotheses). -/
theorem coupledDiffSample_continuum_inhabited :
    CertifiedFeecPde coupledDiffSampleExtraction.evenProb coupledDiffSampleExtraction.evenCert ∧
    CertifiedFeecPde coupledDiffSampleExtraction.oddProb coupledDiffSampleExtraction.oddCert ∧
    (cEvenLoAttoF coupledDiffSampleExtraction ≤ 60000000 ∧
      60000000 ≤ cEvenHiAttoF coupledDiffSampleExtraction) ∧
    (cOddLoAttoF coupledDiffSampleExtraction ≤ 100000000 ∧
      100000000 ≤ cOddHiAttoF coupledDiffSampleExtraction) ∧
    0 < ((100000000 : Rat) - 60000000) / 2 ∧
    (zDiffSqLoMilliOhmSq coupledDiffSampleExtraction ≤
        (4 * mOhmSqPerPicoHAttoF * 250000) / 100000000 ∧
      (4 * mOhmSqPerPicoHAttoF * 250000) / 100000000 ≤
        zDiffSqHiMilliOhmSq coupledDiffSampleExtraction) := by
  let HE := meshContinuumEnergySpace coupledEvenCapMesh coupledEvenCapMesh_geom
  let HO := meshContinuumEnergySpace coupledOddCapMesh coupledOddCapMesh_geom
  let gPos : MeshMidpointField := fun _ => (⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩)
  let gNeg : MeshMidpointField := fun _ => (⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩)
  have hFull := coupledFem_thomsonDirichlet_impedance_brackets_sound
    coupledDiffSampleExtraction (by decide +kernel) HE HO
    gPos gPos gNeg gPos gPos gNeg 3 5 335000 250000
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨by decide +kernel, by decide +kernel⟩ ⟨by decide +kernel, by decide +kernel⟩
  dsimp only [coupledDiffSampleExtraction] at hFull
  rw [show (20000000 : Rat) * 3 = 60000000 by decide +kernel,
      show (20000000 : Rat) * 5 = 100000000 by decide +kernel] at hFull
  exact ⟨hFull.1, hFull.2.1, hFull.2.2.1, hFull.2.2.2.1, hFull.2.2.2.2.1, hFull.2.2.2.2.2.2.1⟩

/-- Lipschitz sensitivity bounds of coupled pair $(\mathbf{L}, \mathbf{C})$ under etch & laminate tolerances. -/
structure CoupledProcessSensitivity where
  kCapWidthAttoFPerNm : Rat
  kCapHeightAttoFPerNm : Rat
  kIndWidthPicoHPerNm : Rat
  kIndHeightPicoHPerNm : Rat
  kAsymCapAttoFPerNm : Rat
  intrinsicMeshAsymAttoF : Rat
  zDiffMinMilliOhm : Nat
  zDiffMaxMilliOhm : Nat
  maxCapImbalanceAttoF : Rat
  deriving DecidableEq, Repr

/-- Signed manufacturing corner realization $(\Delta w_1, \Delta w_2, \Delta h)$ for a coupled pair. -/
structure PcbDiffPairCorner where
  dw1Nm : Int
  dw2Nm : Int
  dhNm : Int
  cOddCornerAttoF : Rat
  lOddCornerPicoH : Rat
  c11CornerAttoF : Rat
  c22CornerAttoF : Rat
  zDiffCornerMilliOhm : Rat

def cornerInsideFabEnvelope (fab : PcbFabCapabilities) (c : PcbDiffPairCorner) : Prop :=
  c.dw1Nm.natAbs ≤ etchVariationBoundNm fab ∧
  c.dw2Nm.natAbs ≤ etchVariationBoundNm fab ∧
  (c.dw1Nm - c.dw2Nm).natAbs ≤ 2 * fab.localEtchMatchTolNm ∧
  c.dhNm.natAbs ≤ fab.lamHeightTolNm

def cornerConsistentWithFemAndSensitivity
    (ext : CoupledFemExtraction2D) (sens : CoupledProcessSensitivity) (c : PcbDiffPairCorner) : Prop :=
  let avgW : Rat := ((c.dw1Nm.natAbs : Rat) + (c.dw2Nm.natAbs : Rat)) / 2
  let absH : Rat := (c.dhNm.natAbs : Rat)
  let absDiffW : Rat := ((c.dw1Nm - c.dw2Nm).natAbs : Rat)
  let dcMax := sens.kCapWidthAttoFPerNm * avgW + sens.kCapHeightAttoFPerNm * absH
  let dlMax := sens.kIndWidthPicoHPerNm * avgW + sens.kIndHeightPicoHPerNm * absH
  cOddLoAttoF ext - dcMax ≤ c.cOddCornerAttoF ∧
  c.cOddCornerAttoF ≤ cOddHiAttoF ext + dcMax ∧
  ext.lOddLoPicoH - dlMax ≤ c.lOddCornerPicoH ∧
  c.lOddCornerPicoH ≤ ext.lOddHiPicoH + dlMax ∧
  ratAbs (c.c11CornerAttoF - c.c22CornerAttoF) ≤
    sens.intrinsicMeshAsymAttoF + sens.kAsymCapAttoFPerNm * absDiffW ∧
  0 ≤ c.zDiffCornerMilliOhm ∧
  c.zDiffCornerMilliOhm * c.zDiffCornerMilliOhm =
    (4 * mOhmSqPerPicoHAttoF * c.lOddCornerPicoH) / c.cOddCornerAttoF

def checkDfmDiffImpedanceAndSkew
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (ext : CoupledFemExtraction2D) (sens : CoupledProcessSensitivity) : Bool :=
  let dEtch : Rat := (etchVariationBoundNm fab : Rat)
  let dLam : Rat := (fab.lamHeightTolNm : Rat)
  let dLocal : Rat := (fab.localEtchMatchTolNm : Rat)
  let dcWorst := sens.kCapWidthAttoFPerNm * dEtch + sens.kCapHeightAttoFPerNm * dLam
  let dlWorst := sens.kIndWidthPicoHPerNm * dEtch + sens.kIndHeightPicoHPerNm * dLam
  let cCornerMin := cOddLoAttoF ext - dcWorst
  let cCornerMax := cOddHiAttoF ext + dcWorst
  let lCornerMin := ext.lOddLoPicoH - dlWorst
  let lCornerMax := ext.lOddHiPicoH + dlWorst
  let zMinQ : Rat := (sens.zDiffMinMilliOhm : Rat)
  let zMaxQ : Rat := (sens.zDiffMaxMilliOhm : Rat)
  checkPcbDfmEnvelope fab layout &&
  checkCoupledFemExtraction ext &&
  decide (0 ≤ sens.kCapWidthAttoFPerNm ∧ 0 ≤ sens.kCapHeightAttoFPerNm) &&
  decide (0 ≤ sens.kIndWidthPicoHPerNm ∧ 0 ≤ sens.kIndHeightPicoHPerNm) &&
  decide (0 ≤ sens.kAsymCapAttoFPerNm ∧ 0 ≤ sens.intrinsicMeshAsymAttoF) &&
  decide (0 < cCornerMin ∧ 0 < lCornerMin) &&
  decide (zMinQ * zMinQ ≤ (4 * mOhmSqPerPicoHAttoF * lCornerMin) / cCornerMax) &&
  decide ((4 * mOhmSqPerPicoHAttoF * lCornerMax) / cCornerMin ≤ zMaxQ * zMaxQ) &&
  decide (sens.intrinsicMeshAsymAttoF + 2 * sens.kAsymCapAttoFPerNm * dLocal <
    sens.maxCapImbalanceAttoF)

def sampleDiffSensitivity : CoupledProcessSensitivity where
  kCapWidthAttoFPerNm := 150
  kCapHeightAttoFPerNm := 200
  kIndWidthPicoHPerNm := 1 / 4
  kIndHeightPicoHPerNm := 1 / 2
  kAsymCapAttoFPerNm := 120
  intrinsicMeshAsymAttoF := 50000
  zDiffMinMilliOhm := 90000
  zDiffMaxMilliOhm := 110000
  maxCapImbalanceAttoF := 1500000

example :
    checkDfmDiffImpedanceAndSkew ipcClass3RfFab ipcClass3RfLayout
      coupledDiffSampleExtraction sampleDiffSensitivity = true := by
  decide +kernel

def sampleBoardCorner : PcbDiffPairCorner where
  dw1Nm := 12000
  dw2Nm := 6000
  dhNm := -8000
  cOddCornerAttoF := 100000000
  lOddCornerPicoH := 250000
  c11CornerAttoF := 80400000
  c22CornerAttoF := 79800000
  zDiffCornerMilliOhm := 100000

example : cornerInsideFabEnvelope ipcClass3RfFab sampleBoardCorner :=
  ⟨by decide, by decide, by decide, by decide⟩

example :
    cornerConsistentWithFemAndSensitivity coupledDiffSampleExtraction
      sampleDiffSensitivity sampleBoardCorner :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **DFM-Propagated Differential Impedance & Mode-Conversion Asymmetry Bound (`dfm_differential_zdiff_and_skew_sound`)**:
For EVERY manufactured board corner inside `PcbFabCapabilities` ($|\Delta w_1|, |\Delta w_2| \le \delta_{\text{etch}}$,
$|\Delta w_1 - \Delta w_2| \le 2\delta_{\text{etch,local}}$, $|\Delta h| \le \delta_{\text{lam}}$),
$Z_{\text{diff}}$ stays inside `[zDiffMinMilliOhm, zDiffMaxMilliOhm]` AND differential-to-common-mode
capacitive imbalance $|C_{11} - C_{22}|$ is strictly upper-bounded by `maxCapImbalanceAttoF`. -/
theorem dfm_differential_zdiff_and_skew_sound
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (ext : CoupledFemExtraction2D) (sens : CoupledProcessSensitivity)
    (hOk : checkDfmDiffImpedanceAndSkew fab layout ext sens = true)
    (c : PcbDiffPairCorner)
    (hFab : cornerInsideFabEnvelope fab c)
    (hPhys : cornerConsistentWithFemAndSensitivity ext sens c) :
    (sens.zDiffMinMilliOhm : Rat) ≤ c.zDiffCornerMilliOhm ∧
    c.zDiffCornerMilliOhm ≤ (sens.zDiffMaxMilliOhm : Rat) ∧
    ratAbs (c.c11CornerAttoF - c.c22CornerAttoF) < sens.maxCapImbalanceAttoF := by
  unfold checkDfmDiffImpedanceAndSkew at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hkCap⟩, hkInd⟩, hkAsym⟩, hCornerPos⟩, hzLoSq⟩, hzHiSq⟩, hSkewBound⟩ := hOk
  obtain ⟨hdw1, hdw2, hdwDiff, hdh⟩ := hFab
  obtain ⟨hcLo, hcHi, hlLo, hlHi, hAsym, hzNonneg, hzSqEq⟩ := hPhys
  let dEtch : Rat := (etchVariationBoundNm fab : Rat)
  let dLam : Rat := (fab.lamHeightTolNm : Rat)
  let dLocal : Rat := (fab.localEtchMatchTolNm : Rat)
  have hAvgWLe : ((c.dw1Nm.natAbs : Rat) + (c.dw2Nm.natAbs : Rat)) / 2 ≤ dEtch := by
    have h1 : (c.dw1Nm.natAbs : Rat) ≤ (etchVariationBoundNm fab : Rat) := by exact_mod_cast hdw1
    have h2 : (c.dw2Nm.natAbs : Rat) ≤ (etchVariationBoundNm fab : Rat) := by exact_mod_cast hdw2
    dsimp only [dEtch]; grind
  have hAbsHLe : (c.dhNm.natAbs : Rat) ≤ dLam := by
    have h : (c.dhNm.natAbs : Rat) ≤ (fab.lamHeightTolNm : Rat) := by exact_mod_cast hdh
    exact h
  have hDiffWLe : ((c.dw1Nm - c.dw2Nm).natAbs : Rat) ≤ 2 * dLocal := by
    have h : ((c.dw1Nm - c.dw2Nm).natAbs : Rat) ≤ ((2 * fab.localEtchMatchTolNm : Nat) : Rat) := by
      exact_mod_cast hdwDiff
    dsimp only [dLocal]; grind
  have hdcLe : sens.kCapWidthAttoFPerNm * (((c.dw1Nm.natAbs : Rat) + (c.dw2Nm.natAbs : Rat)) / 2) +
      sens.kCapHeightAttoFPerNm * (c.dhNm.natAbs : Rat) ≤
      sens.kCapWidthAttoFPerNm * dEtch + sens.kCapHeightAttoFPerNm * dLam := by
    have t1 := Rat.mul_le_mul_of_nonneg_left hAvgWLe hkCap.1
    have t2 := Rat.mul_le_mul_of_nonneg_left hAbsHLe hkCap.2
    grind
  have hdlLe : sens.kIndWidthPicoHPerNm * (((c.dw1Nm.natAbs : Rat) + (c.dw2Nm.natAbs : Rat)) / 2) +
      sens.kIndHeightPicoHPerNm * (c.dhNm.natAbs : Rat) ≤
      sens.kIndWidthPicoHPerNm * dEtch + sens.kIndHeightPicoHPerNm * dLam := by
    have t1 := Rat.mul_le_mul_of_nonneg_left hAvgWLe hkInd.1
    have t2 := Rat.mul_le_mul_of_nonneg_left hAbsHLe hkInd.2
    grind
  let cCornerMin := cOddLoAttoF ext - (sens.kCapWidthAttoFPerNm * dEtch + sens.kCapHeightAttoFPerNm * dLam)
  let cCornerMax := cOddHiAttoF ext + (sens.kCapWidthAttoFPerNm * dEtch + sens.kCapHeightAttoFPerNm * dLam)
  let lCornerMin := ext.lOddLoPicoH - (sens.kIndWidthPicoHPerNm * dEtch + sens.kIndHeightPicoHPerNm * dLam)
  let lCornerMax := ext.lOddHiPicoH + (sens.kIndWidthPicoHPerNm * dEtch + sens.kIndHeightPicoHPerNm * dLam)
  have hcEncl : cCornerMin ≤ c.cOddCornerAttoF ∧ c.cOddCornerAttoF ≤ cCornerMax := by
    dsimp only [cCornerMin, cCornerMax]; grind
  have hlEncl : lCornerMin ≤ c.lOddCornerPicoH ∧ c.lOddCornerPicoH ≤ lCornerMax := by
    dsimp only [lCornerMin, lCornerMax]; grind
  have h4mNonneg : 0 ≤ 4 * mOhmSqPerPicoHAttoF := by unfold mOhmSqPerPicoHAttoF; grind
  have hzRatio := rat_div_mono_interval
    (Rat.mul_nonneg h4mNonneg (Rat.le_of_lt hCornerPos.2))
    ⟨Rat.mul_le_mul_of_nonneg_left hlEncl.1 h4mNonneg,
     Rat.mul_le_mul_of_nonneg_left hlEncl.2 h4mNonneg⟩
    hCornerPos.1 hcEncl
  have hzMaxNonneg : 0 ≤ (sens.zDiffMaxMilliOhm : Rat) := by exact_mod_cast Nat.zero_le _
  have hSqLo : (sens.zDiffMinMilliOhm : Rat) * (sens.zDiffMinMilliOhm : Rat) ≤
      c.zDiffCornerMilliOhm * c.zDiffCornerMilliOhm := by
    rw [hzSqEq]; dsimp only [cCornerMin, cCornerMax, lCornerMin, lCornerMax] at hzRatio; grind
  have hSqHi : c.zDiffCornerMilliOhm * c.zDiffCornerMilliOhm ≤
      (sens.zDiffMaxMilliOhm : Rat) * (sens.zDiffMaxMilliOhm : Rat) := by
    rw [hzSqEq]; dsimp only [cCornerMin, cCornerMax, lCornerMin, lCornerMax] at hzRatio; grind
  have hAsymStep : sens.kAsymCapAttoFPerNm * ((c.dw1Nm - c.dw2Nm).natAbs : Rat) ≤
      sens.kAsymCapAttoFPerNm * (2 * dLocal) :=
    Rat.mul_le_mul_of_nonneg_left hDiffWLe hkAsym.1
  exact ⟨rat_le_of_sq_le_sq hzNonneg hSqLo,
         rat_le_of_sq_le_sq hzMaxNonneg hSqHi,
         by grind⟩

/-! ## 4. Split Return-Plane Slot Penalty, Stitching-Via Faraday Fence & 2D Plane-Pair PDN Impedance -/

/-- Excess series loop inductance $\Delta L_{\text{slot}}$ (in $\text{pH}$) incurred when a high-speed return
current detours around a reference-plane slot of width `slotGapNm` and detour span `detourSpanNm`
at dielectric height `traceHeightNm`, scaled by $\mu_0 / (2\pi) = 200{,}000\,\text{pH/m}$. -/
def slotLoopInductancePenaltyPicoH (slotGapNm detourSpanNm traceHeightNm : Nat) : Rat :=
  if slotGapNm == 0 || detourSpanNm == 0 then 0
  else
    (200000 * (slotGapNm : Rat) * (detourSpanNm : Rat)) /
      (1000000000 * ((slotGapNm : Rat) + 2 * (traceHeightNm : Rat)))

/-- **Strict Positivity of Split Return-Plane Slot Inductance Penalty (`slot_inductance_penalty_pos`)**:
Crossing any gapped reference plane ($g > 0$, detour aperture $d > 0$) adds strictly positive loop
inductance $\Delta L_{\text{slot}} > 0$, whereas a solid plane ($g = 0$) adds zero penalty. -/
theorem slot_inductance_penalty_pos (slotGapNm detourSpanNm traceHeightNm : Nat) :
    slotLoopInductancePenaltyPicoH 0 detourSpanNm traceHeightNm = 0 ∧
    (0 < slotGapNm → 0 < detourSpanNm →
      0 < slotLoopInductancePenaltyPicoH slotGapNm detourSpanNm traceHeightNm) := by
  refine ⟨by simp [slotLoopInductancePenaltyPicoH], fun hg hd => ?_⟩
  unfold slotLoopInductancePenaltyPicoH
  have hgNe : (slotGapNm == 0) = false := beq_false_of_ne (by omega)
  have hdNe : (detourSpanNm == 0) = false := beq_false_of_ne (by omega)
  simp only [hgNe, hdNe, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  have hgQ : (0 : Rat) < (slotGapNm : Rat) := by exact_mod_cast hg
  have hdQ : (0 : Rat) < (detourSpanNm : Rat) := by exact_mod_cast hd
  have hhQ : (0 : Rat) ≤ (traceHeightNm : Rat) := by exact_mod_cast Nat.zero_le _
  exact rat_div_pos (Rat.mul_pos (by grind) hdQ) (by grind)

/-- High-speed return-path continuity checker: refuses split reference planes (`slotGapNm > 0`) unless
bridged by ground stitching vias within $\lambda_{\min} / 20$ keeping $\Delta L_{\text{slot}} \le \Delta L_{\max}$. -/
@[expose] def checkHighSpeedReturnPathContinuity
    (slotGapNm unbridgedApertureNm traceHeightNm lambdaMinNm : Nat)
    (hasGroundStitchingBridge : Bool) (bridgeStitchSpanNm : Nat)
    (maxSlotInductancePicoH : Rat) : Bool :=
  decide (0 < lambdaMinNm ∧ 0 < traceHeightNm) &&
  if slotGapNm == 0 then true
  else
    hasGroundStitchingBridge &&
    decide (0 < bridgeStitchSpanNm ∧ bridgeStitchSpanNm ≤ unbridgedApertureNm) &&
    decide (20 * bridgeStitchSpanNm ≤ lambdaMinNm) &&
    decide (slotLoopInductancePenaltyPicoH slotGapNm bridgeStitchSpanNm traceHeightNm ≤
      maxSlotInductancePicoH)

example :
    checkHighSpeedReturnPathContinuity 200000 10000000 150000 16000000 true 600000 100 = true := by
  decide +kernel

theorem checkHighSpeedReturnPathContinuity_sound
    (slotGapNm unbridgedApertureNm traceHeightNm lambdaMinNm : Nat)
    (hasGroundStitchingBridge : Bool) (bridgeStitchSpanNm : Nat)
    (maxSlotInductancePicoH : Rat)
    (hOk : checkHighSpeedReturnPathContinuity slotGapNm unbridgedApertureNm traceHeightNm
             lambdaMinNm hasGroundStitchingBridge bridgeStitchSpanNm maxSlotInductancePicoH = true) :
    0 < lambdaMinNm ∧
    (slotGapNm = 0 ∨
      (hasGroundStitchingBridge = true ∧
       20 * bridgeStitchSpanNm ≤ lambdaMinNm ∧
       0 < slotLoopInductancePenaltyPicoH slotGapNm bridgeStitchSpanNm traceHeightNm ∧
       slotLoopInductancePenaltyPicoH slotGapNm bridgeStitchSpanNm traceHeightNm ≤
         maxSlotInductancePicoH)) := by
  unfold checkHighSpeedReturnPathContinuity at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  refine ⟨hOk.1.1, ?_⟩
  by_cases hg : slotGapNm = 0
  · exact Or.inl hg
  · right
    have hgB : (slotGapNm == 0) = false := beq_false_of_ne hg
    rw [hgB] at hOk; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hOk
    have hPos := (slot_inductance_penalty_pos slotGapNm bridgeStitchSpanNm traceHeightNm).2
      (by omega) hOk.2.1.1.2.1
    exact ⟨hOk.2.1.1.1, hOk.2.1.2, hPos, hOk.2.2⟩

theorem unbridged_return_slot_refused
    (slotGapNm unbridgedApertureNm traceHeightNm lambdaMinNm bridgeStitchSpanNm : Nat)
    (maxSlotInductancePicoH : Rat) (hGap : 0 < slotGapNm) :
    checkHighSpeedReturnPathContinuity slotGapNm unbridgedApertureNm traceHeightNm
      lambdaMinNm false bridgeStitchSpanNm maxSlotInductancePicoH = false := by
  unfold checkHighSpeedReturnPathContinuity
  have hgB : (slotGapNm == 0) = false := beq_false_of_ne (by omega)
  rw [hgB]; simp

/-- Stitching-via Faraday fence checker: certifies pitch $p_{\text{via}} \le \lambda_{\min} / 20$
and waveguide-below-cutoff aperture ratio $\lambda_{\min} / (2 (p_{\text{via}} - d_{\text{via}})) \ge \text{minCutoffRatio}$. -/
def checkStitchingViaFaradayFence
    (viaPitchNm viaDiamNm lambdaMinNm minCutoffRatio : Nat) : Bool :=
  decide (0 < viaDiamNm ∧ viaDiamNm < viaPitchNm) &&
  decide (20 * viaPitchNm ≤ lambdaMinNm) &&
  decide (10 ≤ minCutoffRatio) &&
  decide (minCutoffRatio * (2 * (viaPitchNm - viaDiamNm)) ≤ lambdaMinNm)

example : checkStitchingViaFaradayFence 750000 200000 16000000 10 = true := by decide +kernel

/-- **Stitching-Via Faraday Fence Waveguide-Below-Cutoff Soundness (`stitching_via_faraday_fence_sound`)**:
Certifies $p_{\text{via}} \le \lambda_{\min} / 20$ and proves that the $TE_{10}$ inter-via aperture
cutoff wavelength $\lambda_c = 2 (p_{\text{via}} - d_{\text{via}})$ satisfies
$\text{minCutoffRatio} \cdot \lambda_c \le \lambda_{\min}$ ($\ge 20\,\text{dB}$ evanescent shielding). -/
theorem stitching_via_faraday_fence_sound
    (viaPitchNm viaDiamNm lambdaMinNm minCutoffRatio : Nat)
    (hOk : checkStitchingViaFaradayFence viaPitchNm viaDiamNm lambdaMinNm minCutoffRatio = true) :
    let apertureNm := viaPitchNm - viaDiamNm
    let te10CutoffLambdaNm := 2 * apertureNm
    0 < apertureNm ∧
    20 * viaPitchNm ≤ lambdaMinNm ∧
    10 * te10CutoffLambdaNm ≤ lambdaMinNm ∧
    minCutoffRatio * te10CutoffLambdaNm ≤ lambdaMinNm := by
  unfold checkStitchingViaFaradayFence at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hdLt : viaDiamNm < viaPitchNm := hOk.1.1.1.2
  have hPitch : 20 * viaPitchNm ≤ lambdaMinNm := hOk.1.1.2
  have hMin10 : 10 ≤ minCutoffRatio := hOk.1.2
  have hRatio : minCutoffRatio * (2 * (viaPitchNm - viaDiamNm)) ≤ lambdaMinNm := hOk.2
  dsimp only
  refine ⟨by omega, hPitch, ?_, hRatio⟩
  have hMono : 10 * (2 * (viaPitchNm - viaDiamNm)) ≤ minCutoffRatio * (2 * (viaPitchNm - viaDiamNm)) :=
    Nat.mul_le_mul_right _ hMin10
  omega

/-- 2D parallel-plane power/ground cavity + decoupling network parameters over continuous band $[\omega_{\min}, \omega_{\max}]$. -/
structure PdnPlanePairSpec where
  maxRippleVolt : Rat
  maxTransientStepAmp : Rat
  esrOhm : Rat
  spreadingInductanceHenry : Rat
  planePlusDecapFarad : Rat
  omegaMinRadPerSec : Rat
  omegaMaxRadPerSec : Rat
  cavityFirstModeRadPerSec : Rat
  deriving DecidableEq, Repr

def pdnTargetImpedanceOhm (p : PdnPlanePairSpec) : Rat := p.maxRippleVolt / p.maxTransientStepAmp

def pdnReactanceOhm (p : PdnPlanePairSpec) (omega : Rat) : Rat :=
  omega * p.spreadingInductanceHenry - 1 / (omega * p.planePlusDecapFarad)

def pdnImpedanceMagSqOhmSq (p : PdnPlanePairSpec) (omega : Rat) : Rat :=
  p.esrOhm * p.esrOhm + pdnReactanceOhm p omega * pdnReactanceOhm p omega

def checkPdnTargetImpedance (p : PdnPlanePairSpec) : Bool :=
  let zT := pdnTargetImpedanceOhm p
  decide (0 < p.maxRippleVolt ∧ 0 < p.maxTransientStepAmp) &&
  decide (0 < p.esrOhm ∧ 0 ≤ p.spreadingInductanceHenry ∧ 0 < p.planePlusDecapFarad) &&
  decide (0 < p.omegaMinRadPerSec ∧ p.omegaMinRadPerSec ≤ p.omegaMaxRadPerSec) &&
  decide (2 * p.omegaMaxRadPerSec ≤ p.cavityFirstModeRadPerSec) &&
  decide (pdnImpedanceMagSqOhmSq p p.omegaMinRadPerSec ≤ zT * zT) &&
  decide (pdnImpedanceMagSqOhmSq p p.omegaMaxRadPerSec ≤ zT * zT)

def sampleCorePdnSpec : PdnPlanePairSpec where
  maxRippleVolt := 3 / 100
  maxTransientStepAmp := 2
  esrOhm := 1 / 200
  spreadingInductanceHenry := 1 / 10000000000
  planePlusDecapFarad := 1 / 100000
  omegaMinRadPerSec := 10000000
  omegaMaxRadPerSec := 100000000
  cavityFirstModeRadPerSec := 500000000

example : checkPdnTargetImpedance sampleCorePdnSpec = true := by decide +kernel

private theorem rat_sq_bounded_on_interval {a b x m : Rat}
    (ha : a ≤ x) (hb : x ≤ b) (haSq : a * a ≤ m) (hbSq : b * b ≤ m) :
    x * x ≤ m := by
  rcases @Rat.le_total 0 x with hxNonneg | hxNeg
  · have hxb : 0 ≤ b := by grind
    have h1 : x * x ≤ x * b := Rat.mul_le_mul_of_nonneg_left hb hxNonneg
    have h2 : x * b ≤ b * b := Rat.mul_le_mul_of_nonneg_right hb hxb
    grind
  · have hnxNonneg : 0 ≤ -x := by grind
    have hna : -x ≤ -a := by grind
    have hnaNonneg : 0 ≤ -a := by grind
    have h1 : (-x) * (-x) ≤ (-x) * (-a) := Rat.mul_le_mul_of_nonneg_left hna hnxNonneg
    have h2 : (-x) * (-a) ≤ (-a) * (-a) := Rat.mul_le_mul_of_nonneg_right hna hnaNonneg
    grind

private theorem pdn_impedance_sq_le_target_sq
    (p : PdnPlanePairSpec) (hOk : checkPdnTargetImpedance p = true)
    (omega : Rat) (hBand : p.omegaMinRadPerSec ≤ omega ∧ omega ≤ p.omegaMaxRadPerSec) :
    0 < p.maxRippleVolt ∧ 0 < p.maxTransientStepAmp ∧
    2 * omega ≤ p.cavityFirstModeRadPerSec ∧
    pdnImpedanceMagSqOhmSq p omega ≤ pdnTargetImpedanceOhm p * pdnTargetImpedanceOhm p := by
  unfold checkPdnTargetImpedance at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨⟨⟨hRip, hPhys⟩, hOmRange⟩, hCav⟩, hLoSq⟩, hHiSq⟩ := hOk
  have hOmPos : 0 < omega := by grind
  have hIndLo : p.omegaMinRadPerSec * p.spreadingInductanceHenry ≤ omega * p.spreadingInductanceHenry :=
    Rat.mul_le_mul_of_nonneg_right hBand.1 hPhys.2.1
  have hIndHi : omega * p.spreadingInductanceHenry ≤ p.omegaMaxRadPerSec * p.spreadingInductanceHenry :=
    Rat.mul_le_mul_of_nonneg_right hBand.2 hPhys.2.1
  have hCapDenLoPos : 0 < p.omegaMinRadPerSec * p.planePlusDecapFarad := Rat.mul_pos hOmRange.1 hPhys.2.2
  have hCapDenPos : 0 < omega * p.planePlusDecapFarad := Rat.mul_pos hOmPos hPhys.2.2
  have hInvHiLe : 1 / (omega * p.planePlusDecapFarad) ≤ 1 / (p.omegaMinRadPerSec * p.planePlusDecapFarad) :=
    (rat_div_mono_interval (by grind) ⟨Rat.le_refl, Rat.le_refl⟩ hCapDenLoPos
      ⟨Rat.mul_le_mul_of_nonneg_right hBand.1 (Rat.le_of_lt hPhys.2.2), Rat.le_refl⟩).2
  have hInvLoLe : 1 / (p.omegaMaxRadPerSec * p.planePlusDecapFarad) ≤ 1 / (omega * p.planePlusDecapFarad) :=
    (rat_div_mono_interval (by grind) ⟨Rat.le_refl, Rat.le_refl⟩ hCapDenPos
      ⟨Rat.le_refl, Rat.mul_le_mul_of_nonneg_right hBand.2 (Rat.le_of_lt hPhys.2.2)⟩).1
  have hReactLo : pdnReactanceOhm p p.omegaMinRadPerSec ≤ pdnReactanceOhm p omega := by
    unfold pdnReactanceOhm; grind
  have hReactHi : pdnReactanceOhm p omega ≤ pdnReactanceOhm p p.omegaMaxRadPerSec := by
    unfold pdnReactanceOhm; grind
  let zT := pdnTargetImpedanceOhm p
  have hReactSqBnd : pdnReactanceOhm p omega * pdnReactanceOhm p omega ≤ zT * zT - p.esrOhm * p.esrOhm :=
    rat_sq_bounded_on_interval hReactLo hReactHi
      (by unfold pdnImpedanceMagSqOhmSq at hLoSq; dsimp only [zT]; grind)
      (by unfold pdnImpedanceMagSqOhmSq at hHiSq; dsimp only [zT]; grind)
  exact ⟨hRip.1, hRip.2, by grind, by unfold pdnImpedanceMagSqOhmSq; dsimp only [zT] at hReactSqBnd ⊢; grind⟩

/-- **Continuous-Band 2D Plane-Pair PDN Target Impedance Soundness (`pdn_target_impedance_sound`)**:
Proves via reactance monotonicity and quadratic convexity that for EVERY continuous angular frequency
$\omega \in [\omega_{\min}, \omega_{\max}]$ (not merely a discrete sample grid), the PDN stays below
half the $\text{TM}_{10}$ parallel-plate cavity resonance and satisfies
$|Z_{\text{PDN}}(\omega)|^2 \le Z_{\text{target}}^2 = (\Delta V_{\max} / \Delta I_{\max})^2$ and
$|Z_{\text{PDN}}(\omega)| \le \Delta V_{\max} / \Delta I_{\max}$. -/
theorem pdn_target_impedance_sound
    (p : PdnPlanePairSpec) (hOk : checkPdnTargetImpedance p = true)
    (omega zMag : Rat)
    (hBand : p.omegaMinRadPerSec ≤ omega ∧ omega ≤ p.omegaMaxRadPerSec)
    (hzNonneg : 0 ≤ zMag)
    (hzSq : zMag * zMag = pdnImpedanceMagSqOhmSq p omega) :
    2 * omega ≤ p.cavityFirstModeRadPerSec ∧
    pdnImpedanceMagSqOhmSq p omega ≤ pdnTargetImpedanceOhm p * pdnTargetImpedanceOhm p ∧
    zMag ≤ pdnTargetImpedanceOhm p := by
  obtain ⟨hRip1, hRip2, hCav, hImpSq⟩ := pdn_impedance_sq_le_target_sq p hOk omega hBand
  have hzTNonneg : 0 ≤ pdnTargetImpedanceOhm p := Rat.le_of_lt (rat_div_pos hRip1 hRip2)
  have _ := hzNonneg
  exact ⟨hCav, hImpSq, rat_le_of_sq_le_sq hzTNonneg (by rw [hzSq]; exact hImpSq)⟩

/-- Conservative lower bound on $\pi^2$ ($\pi_{\text{lo}} = 314159 / 100000 < \pi$) for $\text{TM}_{10}$ cavity mode bounds. -/
def piLoRat : Rat := 314159 / 100000

/-- Derived physical $\text{TM}_{10}$ / $\text{TM}_{01}$ parallel-plate cavity resonance lower bound
$\omega_{10,\text{lo}}^2 = \frac{\pi_{\text{lo}}^2 c_0^2}{\varepsilon_r \max(L_x, L_y)^2}$ in $(\text{rad/s})^2$ from plane dimensions
`planeLenNm`, `planeWidNm` ($\text{nm}$) and substrate `dkPermille` ($1000 \cdot \varepsilon_r$). -/
def planePairTm10RadPerSecSqLower (planeLenNm planeWidNm dkPermille : Nat) : Rat :=
  let maxSpanNm : Nat := max planeLenNm planeWidNm
  let num : Rat := piLoRat * piLoRat * (c0MetersPerSec : Rat) * (c0MetersPerSec : Rat) *
    1000000000000000000 * 1000
  let den : Rat := (dkPermille : Rat) * (maxSpanNm : Rat) * (maxSpanNm : Rat)
  num / den

/-- Verify that `p.cavityFirstModeRadPerSec` is physically bounded by the rectangular plane-pair
$\text{TM}_{10}$ cavity resonance of `(planeLenNm, planeWidNm, dkPermille)` AND `checkPdnTargetImpedance p` holds. -/
def checkPlanePairGeometryResonance
    (p : PdnPlanePairSpec) (planeLenNm planeWidNm dkPermille : Nat) : Bool :=
  checkPdnTargetImpedance p &&
  decide (0 < planeLenNm ∧ 0 < planeWidNm ∧ 1000 ≤ dkPermille) &&
  decide (0 < p.cavityFirstModeRadPerSec) &&
  decide (p.cavityFirstModeRadPerSec * p.cavityFirstModeRadPerSec ≤
    planePairTm10RadPerSecSqLower planeLenNm planeWidNm dkPermille)

example : checkPlanePairGeometryResonance sampleCorePdnSpec 50000000 40000000 4200 = true := by
  decide +kernel

/-- **Geometry-Derived Plane-Pair $\text{TM}_{10}$ Cavity Resonance Soundness (`planePairGeometryResonance_sound`)**:
Prevents unchecked `cavityFirstModeRadPerSec` inflation by proving $(2 \omega)^2 \le \omega_{10,\text{lo}}^2(L_x, L_y, \varepsilon_r)$
across the entire continuous frequency band $\omega \in [\omega_{\min}, \omega_{\max}]$. -/
theorem planePairGeometryResonance_sound
    (p : PdnPlanePairSpec) (planeLenNm planeWidNm dkPermille : Nat)
    (hOk : checkPlanePairGeometryResonance p planeLenNm planeWidNm dkPermille = true)
    (omega : Rat) (hBand : p.omegaMinRadPerSec ≤ omega ∧ omega ≤ p.omegaMaxRadPerSec) :
    0 < planeLenNm ∧ 0 < planeWidNm ∧ 1000 ≤ dkPermille ∧
    (2 * omega) * (2 * omega) ≤ planePairTm10RadPerSecSqLower planeLenNm planeWidNm dkPermille ∧
    pdnImpedanceMagSqOhmSq p omega ≤ pdnTargetImpedanceOhm p * pdnTargetImpedanceOhm p := by
  unfold checkPlanePairGeometryResonance at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨hPdn, hGeom⟩, hCavPos⟩, hCavSq⟩ := hOk
  obtain ⟨_, _, h2OmLe, hImpSq⟩ := pdn_impedance_sq_le_target_sq p hPdn omega hBand
  have hOmPos : 0 < omega := by
    unfold checkPdnTargetImpedance at hPdn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPdn
    have := hPdn.1.1.1.2.1; grind
  have h1 : (2 * omega) * (2 * omega) ≤ (2 * omega) * p.cavityFirstModeRadPerSec :=
    Rat.mul_le_mul_of_nonneg_left h2OmLe (by grind)
  have h2 : (2 * omega) * p.cavityFirstModeRadPerSec ≤
      p.cavityFirstModeRadPerSec * p.cavityFirstModeRadPerSec :=
    Rat.mul_le_mul_of_nonneg_right h2OmLe (Rat.le_of_lt hCavPos)
  exact ⟨hGeom.1, hGeom.2.1, hGeom.2.2, by grind, hImpSq⟩

/-! ## 5. Coupled Electro-Thermal Trace Joule Self-Heating & TCR Runaway Immunity -/

/-- Coupled electro-thermal copper trace specification with linear TCR self-heating feedback
$R(\Delta T) = R_{\text{wc}} (1 + \alpha_{\text{TCR}} \Delta T)$ over the worst-case DFM over-etched cross-section. -/
structure TraceElectroThermalSpec where
  traceLengthNm : Nat
  rhoCuOhmNm : Rat
  tcrPerKelvin : Rat
  thetaJaKelvinPerWatt : Rat
  currentAmp : Rat
  ambientTempC : Rat
  maxDeltaTKelvin : Rat
  laminateTgDeratedC : Rat
  deriving DecidableEq, Repr

/-- Worst-case cold DC trace resistance $R_{\text{wc}} = \frac{\rho_0 \ell}{(w_{\text{nom}} - \delta_{\text{etch}}) t_{\text{Cu}}}$ ($\Omega$)
at maximum two-sided etch undercut $\delta_{\text{etch}}$. -/
def worstCaseTraceResistanceOhm
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules) (s : TraceElectroThermalSpec) : Rat :=
  let wWorstNm : Nat := layout.nomTraceWidthNm - etchVariationBoundNm fab
  (s.rhoCuOhmNm * (s.traceLengthNm : Rat)) / ((wWorstNm : Rat) * (fab.copperThickNm : Rat))

/-- Uncoupled cold Joule temperature rise $\Delta T_0 = \theta_{\text{JA}} I^2 R_{\text{wc}}$ ($\text{K}$). -/
def traceColdDeltaTKelvin
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules) (s : TraceElectroThermalSpec) : Rat :=
  s.thetaJaKelvinPerWatt * (s.currentAmp * s.currentAmp * worstCaseTraceResistanceOhm fab layout s)

/-- Coupled electro-thermal feedback stability denominator $D_{\text{th}} = 1 - \alpha_{\text{TCR}} \Delta T_0$. -/
def traceThermalDenom
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules) (s : TraceElectroThermalSpec) : Rat :=
  1 - s.tcrPerKelvin * traceColdDeltaTKelvin fab layout s

/-- Exact coupled electro-thermal equilibrium temperature rise $\Delta T_{\text{eq}} = \Delta T_0 / (1 - \alpha_{\text{TCR}} \Delta T_0)$ ($\text{K}$). -/
def traceEquilibriumDeltaTKelvin
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules) (s : TraceElectroThermalSpec) : Rat :=
  traceColdDeltaTKelvin fab layout s / traceThermalDenom fab layout s

/-- Coupled electro-thermal trace checker: verifies DFM trace envelope, strict thermal-runaway stability
margin $0 < 1 - \alpha_{\text{TCR}} \theta_{\text{JA}} I^2 R_{\text{wc}}$, $\Delta T_{\text{eq}} \le \Delta T_{\max}$, and $T_{\text{amb}} + \Delta T_{\text{eq}} \le T_{g,\text{derated}}$. -/
def checkTraceElectroThermal
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules) (s : TraceElectroThermalSpec) : Bool :=
  let denom := traceThermalDenom fab layout s
  let dtEq := traceEquilibriumDeltaTKelvin fab layout s
  checkPcbDfmEnvelope fab layout &&
  decide (0 < s.traceLengthNm) &&
  decide (0 < s.rhoCuOhmNm ∧ 0 < s.tcrPerKelvin ∧ 0 < s.thetaJaKelvinPerWatt) &&
  decide (0 ≤ s.currentAmp ∧ 0 < s.maxDeltaTKelvin) &&
  decide (0 < denom) &&
  decide (dtEq ≤ s.maxDeltaTKelvin) &&
  decide (s.ambientTempC + dtEq ≤ s.laminateTgDeratedC)

def sampleTraceElectroThermal : TraceElectroThermalSpec where
  traceLengthNm := 50000000
  rhoCuOhmNm := 1724 / 100
  tcrPerKelvin := 393 / 100000
  thetaJaKelvinPerWatt := 35
  currentAmp := 3 / 2
  ambientTempC := 55
  maxDeltaTKelvin := 20
  laminateTgDeratedC := 130

example :
    checkTraceElectroThermal ipcClass3RfFab ipcClass3RfLayout sampleTraceElectroThermal = true := by
  decide +kernel

/-- **Coupled Electro-Thermal Equilibrium & Runaway-Immunity Soundness (`traceElectroThermal_sound`)**:
Certifies over worst-case DFM over-etched copper geometry $w_{\text{wc}} = w_{\text{nom}} - \delta_{\text{etch}} \ge w_{\min} > 0$:
1. Positive worst-case DC resistance $R_{\text{wc}} > 0$ and thermal stability margin $0 < 1 - \alpha_{\text{TCR}} \Delta T_0$,
2. Exact coupled Joule–TCR fixed-point balance $\Delta T_{\text{eq}} = \theta_{\text{JA}} I^2 R_{\text{wc}} (1 + \alpha_{\text{TCR}} \Delta T_{\text{eq}})$,
3. Certified thermal ceiling $0 \le \Delta T_{\text{eq}} \le \Delta T_{\max}$ and $T_{\text{amb}} + \Delta T_{\text{eq}} \le T_{g,\text{derated}}$. -/
theorem traceElectroThermal_sound
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules) (s : TraceElectroThermalSpec)
    (hOk : checkTraceElectroThermal fab layout s = true) :
    let rWc := worstCaseTraceResistanceOhm fab layout s
    let dt0 := traceColdDeltaTKelvin fab layout s
    let denom := traceThermalDenom fab layout s
    let dtEq := traceEquilibriumDeltaTKelvin fab layout s
    fab.minTraceWidthNm ≤ layout.nomTraceWidthNm - etchVariationBoundNm fab ∧
    0 < rWc ∧
    0 < denom ∧
    0 ≤ dtEq ∧
    dtEq = dt0 * (1 + s.tcrPerKelvin * dtEq) ∧
    dtEq ≤ s.maxDeltaTKelvin ∧
    s.ambientTempC + dtEq ≤ s.laminateTgDeratedC := by
  unfold checkTraceElectroThermal at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨⟨⟨⟨hDfm, hLen⟩, hPhys⟩, hCur⟩, hDenPos⟩, hDtMax⟩, hTg⟩ := hOk
  unfold checkPcbDfmEnvelope at hDfm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hDfm
  have hMinWPos : 0 < fab.minTraceWidthNm := hDfm.1.1.1.1.1.1.1.1.1.1.1.1.1
  have hCuPos : 0 < fab.copperThickNm := hDfm.1.1.1.1.1.1.1.1.1.1.1.2.1
  have hWidthEtch : fab.minTraceWidthNm + etchVariationBoundNm fab ≤ layout.nomTraceWidthNm :=
    hDfm.1.1.1.1.1.1.1.2
  have hwWcPos : 0 < layout.nomTraceWidthNm - etchVariationBoundNm fab := by omega
  have hrWcPos : 0 < worstCaseTraceResistanceOhm fab layout s := by
    unfold worstCaseTraceResistanceOhm
    have hNum : 0 < s.rhoCuOhmNm * (s.traceLengthNm : Rat) :=
      Rat.mul_pos hPhys.1 (by exact_mod_cast hLen)
    have hDen : 0 < ((layout.nomTraceWidthNm - etchVariationBoundNm fab : Nat) : Rat) * (fab.copperThickNm : Rat) :=
      Rat.mul_pos (by exact_mod_cast hwWcPos) (by exact_mod_cast hCuPos)
    exact rat_div_pos hNum hDen
  have hdt0Nonneg : 0 ≤ traceColdDeltaTKelvin fab layout s := by
    unfold traceColdDeltaTKelvin
    exact Rat.mul_nonneg (Rat.le_of_lt hPhys.2.2)
      (Rat.mul_nonneg (rat_sq_nonneg s.currentAmp) (Rat.le_of_lt hrWcPos))
  have hdtEqNonneg : 0 ≤ traceEquilibriumDeltaTKelvin fab layout s :=
    rat_div_nonneg hdt0Nonneg hDenPos
  have hFixedPt : traceEquilibriumDeltaTKelvin fab layout s =
      traceColdDeltaTKelvin fab layout s *
        (1 + s.tcrPerKelvin * traceEquilibriumDeltaTKelvin fab layout s) := by
    let dt0 := traceColdDeltaTKelvin fab layout s
    let denom := traceThermalDenom fab layout s
    let dtEq := traceEquilibriumDeltaTKelvin fab layout s
    have hDenNe : denom ≠ 0 := Rat.ne_of_gt hDenPos
    have hCancel : dtEq * denom = dt0 := Rat.div_mul_cancel hDenNe
    have hDef : denom = 1 - s.tcrPerKelvin * dt0 := rfl
    have hProd : (dtEq - dt0 * (1 + s.tcrPerKelvin * dtEq)) * denom = 0 := by
      have hDist : (dtEq - dt0 * (1 + s.tcrPerKelvin * dtEq)) * denom =
          dtEq * denom - dt0 * denom - dt0 * s.tcrPerKelvin * (dtEq * denom) := by grind
      rw [hDist, hCancel, hDef]; grind
    rcases Rat.mul_eq_zero.mp hProd with hZero | hAbs
    · dsimp only [dtEq, dt0] at hZero; grind
    · exact absurd hAbs hDenNe
  exact ⟨by omega, hrWcPos, hDenPos, hdtEqNonneg, hFixedPt, hDtMax, hTg⟩

/-- **Thermal Runaway Impossibility (`traceThermalRunaway_impossible`)**:
When positive TCR loop gain reaches or exceeds unity ($1 - \alpha_{\text{TCR}} \Delta T_0 \le 0$) under
non-zero cold power ($\Delta T_0 > 0$), NO non-negative steady-state equilibrium $\Delta T \ge 0$ exists. -/
theorem traceThermalRunaway_impossible
    (dt0 tcr dt : Rat) (hDt0Pos : 0 < dt0) (hRunaway : 1 - tcr * dt0 ≤ 0) (hNonneg : 0 ≤ dt) :
    dt ≠ dt0 * (1 + tcr * dt) := by
  intro hEq
  have h1 : (1 - tcr * dt0) * dt = dt0 := by grind
  have h2 : (1 - tcr * dt0) * dt ≤ 0 := by
    have := Rat.mul_le_mul_of_nonneg_right hRunaway hNonneg; grind
  grind

/-- Unified board-level multiphysics checker combining PCB DFM, FEM-bracketed coupled differential
impedance & skew, high-speed return-path slot continuity, Faraday fence shielding, and 2D PDN target impedance. -/
@[expose] def checkPcbMultiphysicsBoard
    (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (ext : CoupledFemExtraction2D) (sens : CoupledProcessSensitivity)
    (slotGapNm unbridgedApertureNm traceHeightNm lambdaMinNm : Nat)
    (hasGroundStitchingBridge : Bool) (bridgeStitchSpanNm : Nat) (maxSlotInductancePicoH : Rat)
    (viaPitchNm viaDiamNm minCutoffRatio : Nat)
    (pdn : PdnPlanePairSpec) : Bool :=
  checkDfmDiffImpedanceAndSkew fab layout ext sens &&
  checkHighSpeedReturnPathContinuity slotGapNm unbridgedApertureNm traceHeightNm
    lambdaMinNm hasGroundStitchingBridge bridgeStitchSpanNm maxSlotInductancePicoH &&
  checkStitchingViaFaradayFence viaPitchNm viaDiamNm lambdaMinNm minCutoffRatio &&
  checkPdnTargetImpedance pdn

example :
    checkPcbMultiphysicsBoard ipcClass3RfFab ipcClass3RfLayout
      coupledDiffSampleExtraction sampleDiffSensitivity
      200000 10000000 150000 16000000 true 600000 100
      750000 200000 10 sampleCorePdnSpec = true := by
  decide +kernel

end Obend.Hardware.PCB
end
