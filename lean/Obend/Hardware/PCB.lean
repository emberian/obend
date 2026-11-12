module
/-
# Obend.Hardware.PCB — Closed-Form Microstrip Characteristic Impedance (Hammerstad–Jensen & Bahl–Garg)

Fixed-point ($S = 10^6$) microstrip characteristic impedance $Z_0$ (`microstripZ0MilliOhm`) using
`Nat.sqrt` and an `atanh`-series logarithm (`fxLn`), following Hammerstad (1975) / Pozar §3.8 with
the Bahl–Garg copper strip thickness correction, together with universal square-root enclosure,
strip-width widening, effective-permittivity enclosure, and substrate-permittivity monotonicity
theorems.
-/
@[expose] public section

namespace Obend.Hardware.PCB
set_option autoImplicit false

/-! ## Closed-form microstrip impedance (Hammerstad–Jensen, Bahl–Garg thickness correction)

Fixed point with scale `fxS = 10⁶`; `Nat.sqrt` and an `atanh`-series logarithm, so the kernel can
evaluate it. The formulas are the standard ones (Pozar, *Microwave Engineering*, §3.8; Hammerstad
1975; strip thickness after Bahl and Garg), with $u = W_{\text{eff}}/H$:
$$\varepsilon_{\text{eff}} = \tfrac{\varepsilon_r+1}{2} + \tfrac{\varepsilon_r-1}{2}\Bigl[(1 + 12/u)^{-1/2} + [u<1]\,0.04(1-u)^2\Bigr],$$
$$Z_0 = \begin{cases} \dfrac{60}{\sqrt{\varepsilon_{\text{eff}}}} \ln\!\bigl(\tfrac{8}{u} + \tfrac{u}{4}\bigr) & u \le 1\\[4pt]
\dfrac{120\pi}{\sqrt{\varepsilon_{\text{eff}}}\,\bigl(u + 1.393 + 0.667 \ln(u + 1.444)\bigr)} & u \ge 1\end{cases}
\qquad W_{\text{eff}} = W + \tfrac{T}{\pi}\bigl(1 + \ln\tfrac{2H}{T}\bigr).$$ -/

def fxS : Nat := 1000000

/-- `⌊√(a·S)⌋`: the square root of the fixed-point value `a`. -/
def fxSqrt (a : Nat) : Nat := Nat.sqrt (a * fxS)

/-- Halve until below `2S` and double until at least `S`, counting the exponent (fuel-bounded). -/
def fxLnNorm : Nat → Nat → Int → Nat × Int
  | 0, m, k => (m, k)
  | fuel + 1, m, k =>
    if 2 * fxS ≤ m then fxLnNorm fuel (m / 2) (k + 1)
    else if m < fxS ∧ 0 < m then fxLnNorm fuel (2 * m) (k - 1)
    else (m, k)

/-- `ln(a/S)·S` for `a > 0`, from `ln m = 2 atanh((m-1)/(m+1))` on `m ∈ [1, 2)` (six terms; the
truncation error is below `2·(1/3)¹³/13 < 10⁻⁷`). Returns `0` at `a = 0`. -/
def fxLn (a : Nat) : Int :=
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
def microstripEffWidthUm (widthUm heightUm copperThickUm : Nat) : Nat :=
  if copperThickUm = 0 then widthUm else
  let lnTerm := fxLn (2 * heightUm * fxS / copperThickUm)
  let dw : Int := (copperThickUm : Int) * ((fxS : Int) + lnTerm) / 3141593
  widthUm + dw.toNat

/-- Effective permittivity ×10⁶ for `u = Weff/H` ×10⁶ and `εr` ×10⁶. -/
def microstripEpsEffFx (u er : Nat) : Nat :=
  let q := fxS + 12 * fxS * fxS / u
  let inv := fxS * fxS / fxSqrt q
  let low := if u < fxS then 40000 * (fxS - u) * (fxS - u) / (fxS * fxS) else 0
  (er + fxS) / 2 + (er - fxS) * (inv + low) / (2 * fxS)

/-- **Closed-form microstrip `Z₀` in mΩ** from geometry (µm) and `εr` ×1000. -/
def microstripZ0MilliOhm (widthUm heightUm copperThickUm erPermille : Nat) : Nat :=
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
def natAbsDiff (a b : Nat) : Nat :=
  if b ≤ a then a - b else b - a

/-- Verify that a single-ended microstrip trace satisfies minimum fab width ($\ge 75\,\mu\text{m} \approx 3\,\text{mil}$)
and that both the field-solver value and the closed form from its own geometry are within
`z0MaxTolMilliOhm` of `z0TargetMilliOhm`: an extracted number that the geometry contradicts is refused. -/
def checkSingleEndedZ0
    (widthUm heightUm copperThicknessUm dkPermille z0ExtractedMilliOhm z0TargetMilliOhm z0MaxTolMilliOhm : Nat) : Bool :=
  decide (75 ≤ widthUm) &&
  decide (heightUm > 0) &&
  decide (copperThicknessUm > 0) &&
  decide (natAbsDiff z0ExtractedMilliOhm z0TargetMilliOhm ≤ z0MaxTolMilliOhm) &&
  decide (natAbsDiff (microstripZ0MilliOhm widthUm heightUm copperThicknessUm dkPermille)
    z0TargetMilliOhm ≤ z0MaxTolMilliOhm)

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

/-! ## Universal Enclosure, Positivity & Permittivity Monotonicity Theorems -/

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

/-- **Hammerstad–Jensen Effective-Permittivity Lower Enclosure & Monotonicity (`microstripEpsEffFx_enclosure_and_mono`)**:
1. For every shape ratio `u : Nat` and dielectric `er : Nat`, `microstripEpsEffFx u er` lies at or
   above the air-substrate average $\lfloor (\varepsilon_r + 1)/2 \rfloor$, and is strictly positive
   for every physical dielectric (`fxS ≤ er`, i.e. $\varepsilon_r \ge 1$).
2. Holding trace geometry `u` fixed, increasing substrate relative permittivity (`er1 ≤ er2`)
   monotonically increases `microstripEpsEffFx u er1 ≤ microstripEpsEffFx u er2`! -/
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
$\varepsilon_r = 3.48$) and high-impedance PTFE (`80 µm` on `500 µm`, $\varepsilon_r = 2.20$):
both branches of `microstripZ0MilliOhm` are strictly positive and discriminate controlled $50\,\Omega$
from mismatched $171\,\Omega$ geometry. -/
theorem microstripZ0_reference_enclosure :
    48000 ≤ microstripZ0MilliOhm 330 152 35 3480 ∧
    microstripZ0MilliOhm 330 152 35 3480 ≤ 52000 ∧
    175000 ≤ microstripZ0MilliOhm 80 500 0 2200 ∧
    microstripZ0MilliOhm 80 500 0 2200 ≤ 185000 ∧
    checkSingleEndedZ0 330 152 35 3480 50000 50000 3000 = true ∧
    checkSingleEndedZ0 80 500 35 2200 50000 50000 3000 = false := by
  decide +kernel

end Obend.Hardware.PCB
end
