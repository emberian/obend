module
/-
# Obend.Hardware.PCB — High-Speed Multi-Layer PCB Stackups, Controlled-Impedance Microstrip/Differential Pairs, Serpentine Length-Matching & IPC-2152 Ampacity DRC

Formalizes **high-speed Printed Circuit Board (PCB) electromagnetic design, signal integrity (SI),
power integrity (PI), and geometric Design Rule Checking (DRC)** (`FR-4`, `Rogers RO4350B`, and
`Isola I-Speed` multi-layer stackups):

1. **Multi-Layer PCB Stackup & Microstrip / Stripline Characteristic Impedance ($Z_0$)**:
   - Models `PcbDielectric` (`fr4Standard` $\varepsilon_r = 4.40$, `rogers4350b` $\varepsilon_r = 3.48$,
     `isolaIspeed` $\varepsilon_r = 3.62$), `PcbTraceSpec` (`widthUm`, `heightUm`, `copperThicknessUm`,
     `z0TargetMilliOhm`), and single-ended impedance tolerance checking (`checkSingleEndedZ0`).
2. **Edge-Coupled Differential Pairs ($Z_{\text{diff}} = 2 Z_{0o}$) & Spacing Monotonicity**:
   - Models `DiffPairSpec` with single-ended impedance `z0MilliOhm` and odd-mode electromagnetic
     coupling factor `couplingPermille` ($k \in [0, 500]$) where $Z_{0o} = Z_0 (1000 - k) / 1000$
     and $Z_{\text{diff}} = 2 Z_{0o}$,
   - Proves **`diffImpedance_monotone_uncoupled`** (reducing coupling $k_2 \le k_1$ by widening
     edge-to-edge trace spacing monotonically increases $Z_{\text{diff}}$ toward the uncoupled limit)
     and **`diffImpedance_uncoupled_limit`** (at $k = 0$, $Z_{\text{diff}} = 2 Z_0$).
3. **Serpentine / Trombone Length-Matching & Sub-Picosecond Flight-Time Skew**:
   - Models `SerpentineMeander` (`baseLengthUm`, `numSegments`, `meanderAmplitudeUm`) with total
     routed length $L_{\text{total}} = L_{\text{base}} + 2 \cdot N_{\text{seg}} \cdot A_{\text{um}}$,
   - Proves **`serpentine_eliminates_length_skew`**: when the trombone meander compensates the
     initial Manhattan length deficit $\Delta L = 2 \cdot N_{\text{seg}} \cdot A_{\text{um}}$, both
     the physical length skew and the propagation flight-time skew (`evalFlightTimeSkewFs`) vanish
     identically to `0`!
4. **IPC-2152 Trace / Via Current-Carrying Capacity & 2D Geometric Clearance DRC**:
   - Models `Ipc2152TraceCheck` (`widthUm`, `copperThicknessUm`, `currentMa`, `maxCurrentDensityMaPerSqUm`)
     and stitched parallel via arrays (`ViaArraySpec`), proving **`viaArray_current_safe`** and
     parallel parasitic inductance reduction (`viaArray_reduces_inductance`),
   - Formalizes complete board-level DRC & creepage/clearance signoff (`checkPcbBoardSignoff`,
     `pcbBoardSignoff_sound`).
-/
public import Obend.Hardware.Thermal
@[expose] public section

namespace Obend.Hardware.PCB
open Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. Multi-Layer PCB Dielectric Stackups & Single-Ended Characteristic Impedance ($Z_0$) -/

/-- Standard PCB core and prepreg laminate materials:
* `fr4Standard`: standard woven glass-epoxy `FR-4` ($\varepsilon_r \approx 4.40$, $\tan\delta \approx 0.020$ at $1\,\text{GHz}$),
* `rogers4350b`: hydrocarbon ceramic `Rogers RO4350B` RF/microwave laminate ($\varepsilon_r = 3.48$, $\tan\delta = 0.0037$ at $10\,\text{GHz}$),
* `isolaIspeed`: high-speed low-loss digital laminate `Isola I-Speed` ($\varepsilon_r = 3.62$, $\tan\delta = 0.0070$). -/
inductive PcbDielectricKind where
  | fr4Standard
  | rogers4350b
  | isolaIspeed
  deriving DecidableEq, Repr

/-- Physical dielectric parameters of a PCB substrate layer:
* `kind`: laminate material family,
* `dkPermille`: relative permittivity $\varepsilon_r \times 1000$ (`4400` for FR-4, `3480` for RO4350B),
* `dfPpm`: loss tangent (dissipation factor) $\tan\delta \times 10^6$ (`20000` for FR-4, `3700` for RO4350B),
* `propDelayFsPerUm`: electromagnetic signal propagation delay in femtoseconds per micrometer
  ($\tau_{\text{pd}} = \frac{\sqrt{\varepsilon_{r,\text{eff}}}}{c_0}$, $\approx 6\,\text{fs}/\mu\text{m} = 150\,\text{ps/inch}$ on outer microstrip). -/
structure PcbDielectric where
  kind             : PcbDielectricKind
  dkPermille       : Nat
  dfPpm            : Nat
  propDelayFsPerUm : Nat
  deriving DecidableEq, Repr

/-- Standard 4-layer `FR-4` dielectric ($\varepsilon_r = 4.40$, $\tan\delta = 0.020$, $\tau_{\text{pd}} = 6\,\text{fs}/\mu\text{m}$). -/
def fr4StandardDielectric : PcbDielectric where
  kind             := .fr4Standard
  dkPermille       := 4400
  dfPpm            := 20000
  propDelayFsPerUm := 6

/-- Low-loss RF `Rogers RO4350B` dielectric ($\varepsilon_r = 3.48$, $\tan\delta = 0.0037$, $\tau_{\text{pd}} = 5\,\text{fs}/\mu\text{m}$). -/
def rogers4350bDielectric : PcbDielectric where
  kind             := .rogers4350b
  dkPermille       := 3480
  dfPpm            := 3700
  propDelayFsPerUm := 5

/-- High-speed SERDES `Isola I-Speed` dielectric ($\varepsilon_r = 3.62$, $\tan\delta = 0.0070$, $\tau_{\text{pd}} = 5\,\text{fs}/\mu\text{m}$). -/
def isolaIspeedDielectric : PcbDielectric where
  kind             := .isolaIspeed
  dkPermille       := 3620
  dfPpm            := 7000
  propDelayFsPerUm := 5

abbrev fr4Standard : PcbDielectric := fr4StandardDielectric
abbrev rogers4350b : PcbDielectric := rogers4350bDielectric
abbrev isolatechIspd : PcbDielectric := isolaIspeedDielectric

/-- Controlled-impedance microstrip or stripline PCB trace geometry:
* `netName`: signal net identifier,
* `dielectric`: underlying reference-plane dielectric substrate,
* `widthUm`: copper trace width $W$ in micrometers ($\mu\text{m}$),
* `heightUm`: dielectric height $H$ above the solid GND reference plane ($\mu\text{m}$),
* `copperThicknessUm`: finished copper foil thickness $T$ ($\mu\text{m}$; $35\,\mu\text{m} = 1\,\text{oz/ft}^2$, $18\,\mu\text{m} = 0.5\,\text{oz/ft}^2$),
* `z0ExtractedMilliOhm`: 2D field-solver extracted characteristic impedance $Z_0$ in milliohms ($\text{m}\Omega$, e.g. `50000` for $50.0\,\Omega$),
* `z0TargetMilliOhm`: target single-ended characteristic impedance ($50000\,\text{m}\Omega = 50\,\Omega$),
* `z0MaxTolMilliOhm`: maximum allowable manufacturing impedance tolerance ($\pm 10\% = 5000\,\text{m}\Omega$). -/
structure PcbTraceSpec where
  netName             : String
  dielectric          : PcbDielectric
  widthUm             : Nat
  heightUm            : Nat
  copperThicknessUm   : Nat
  z0ExtractedMilliOhm : Nat
  z0TargetMilliOhm    : Nat
  z0MaxTolMilliOhm    : Nat
  deriving DecidableEq, Repr

/-- Absolute difference $|a - b|$ on natural numbers. -/
def natAbsDiff (a b : Nat) : Nat :=
  if b ≤ a then a - b else b - a

/-! ### Closed-form microstrip impedance (Hammerstad–Jensen, Wheeler thickness correction)

Fixed point with scale `fxS = 10⁶`; `Nat.sqrt` and an `atanh`-series logarithm, so the kernel can
evaluate it. The formulas are the standard ones (Pozar, *Microwave Engineering*, §3.8; Hammerstad
1975; strip thickness after Bahl and Garg), with $u = W_{\text{eff}}/H$:
$$\varepsilon_{\text{eff}} = \tfrac{\varepsilon_r+1}{2} + \tfrac{\varepsilon_r-1}{2}\Bigl[(1 + 12/u)^{-1/2} + [u<1]\,0.04(1-u)^2\Bigr],$$
$$Z_0 = \begin{cases} \dfrac{60}{\sqrt{\varepsilon_{\text{eff}}}} \ln\!\bigl(\tfrac{8}{u} + \tfrac{u}{4}\bigr) & u \le 1\\[4pt]
\dfrac{120\pi}{\sqrt{\varepsilon_{\text{eff}}}\,\bigl(u + 1.393 + 0.667 \ln(u + 1.444)\bigr)} & u \ge 1\end{cases}
\qquad W_{\text{eff}} = W + \tfrac{T}{\pi}\bigl(1 + \ln\tfrac{2H}{T}\bigr).$$
Accuracy of the closed form is about 1% against a field solver for $0.1 \le u \le 10$; this replaced,
on 2026-11-04, a ratio $(4H + W)/(2H + W)$ with neither square root nor logarithm, which gave
48.7 Ω for an 80 µm strip on 500 µm PTFE (the closed form gives 171 Ω). -/

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

/-- Verify that a single-ended microstrip trace satisfies minimum fab width ($\ge 75\,\mu\text{m} \approx 3\,\text{mil}$)
and that both the field-solver value and the closed form from its own geometry are within
`z0MaxTolMilliOhm` of the target: an extracted number that the geometry contradicts is refused. -/
def checkSingleEndedZ0 (trace : PcbTraceSpec) : Bool :=
  decide (75 ≤ trace.widthUm) &&
  decide (trace.heightUm > 0) &&
  decide (trace.copperThicknessUm > 0) &&
  decide (natAbsDiff trace.z0ExtractedMilliOhm trace.z0TargetMilliOhm ≤ trace.z0MaxTolMilliOhm) &&
  decide (natAbsDiff (microstripZ0MilliOhm trace.widthUm trace.heightUm trace.copperThicknessUm
      trace.dielectric.dkPermille) trace.z0TargetMilliOhm ≤ trace.z0MaxTolMilliOhm)

/-- Theorem (`singleEndedZ0_sound`):
If `checkSingleEndedZ0 trace = true`, then the trace width is at least $75\,\mu\text{m}$ ($3\,\text{mil}$)
and the extracted characteristic impedance lies within `trace.z0MaxTolMilliOhm` of `trace.z0TargetMilliOhm`. -/
theorem singleEndedZ0_sound
    (trace : PcbTraceSpec)
    (hOk : checkSingleEndedZ0 trace = true) :
    75 ≤ trace.widthUm ∧
    natAbsDiff trace.z0ExtractedMilliOhm trace.z0TargetMilliOhm ≤ trace.z0MaxTolMilliOhm ∧
    natAbsDiff (microstripZ0MilliOhm trace.widthUm trace.heightUm trace.copperThicknessUm
      trace.dielectric.dkPermille) trace.z0TargetMilliOhm ≤ trace.z0MaxTolMilliOhm := by
  unfold checkSingleEndedZ0 at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.1.1.1, hOk.1.2, hOk.2⟩

/-! ## 2. Edge-Coupled Differential Pairs ($Z_{\text{diff}} = 2 Z_{0o}$) & Spacing Monotonicity -/

/-- Edge-coupled high-speed differential pair specification (e.g. $100\,\Omega$ LVDS / PCIe / Ethernet
or $90\,\Omega$ USB 3.x):
* `pairName`: differential pair identifier,
* `z0MilliOhm`: uncoupled single-ended characteristic impedance $Z_0$ ($\text{m}\Omega$),
* `spacingUm`: edge-to-edge air/solder-mask gap $S$ between the $+$ and $-$ traces ($\mu\text{m}$),
* `couplingPermille`: electromagnetic odd-mode coupling factor $k \in [0, 500]$ (in permille, so
  $k = 100$ represents $10\%$ edge coupling),
* `zDiffTargetMilliOhm`: target differential impedance ($100000\,\text{m}\Omega = 100\,\Omega$ LVDS/PCIe,
  $90000\,\text{m}\Omega = 90\,\Omega$ USB). -/
structure DiffPairSpec where
  pairName            : String
  z0MilliOhm          : Nat
  spacingUm           : Nat
  couplingPermille    : Nat
  zDiffTargetMilliOhm : Nat
  zDiffTolMilliOhm    : Nat
  deriving DecidableEq, Repr

/-- Odd-mode impedance $Z_{0o} = \frac{Z_0 \cdot (1000 - k)}{1000}$ (in milliohms $\text{m}\Omega$)
of an edge-coupled differential pair when driven with equal and opposite signals ($+V, -V$). -/
def evalOddModeZ0MilliOhm (dp : DiffPairSpec) : Nat :=
  (dp.z0MilliOhm * (1000 - dp.couplingPermille)) / 1000

/-- Differential characteristic impedance $Z_{\text{diff}} = 2 Z_{0o}$ (in milliohms $\text{m}\Omega$). -/
def evalDiffImpedanceMilliOhm (dp : DiffPairSpec) : Nat :=
  2 * evalOddModeZ0MilliOhm dp

/-- Theorem (`diffImpedance_monotone_uncoupled`):
For two differential pairs with the same single-ended impedance `dp1.z0MilliOhm = dp2.z0MilliOhm`,
decreasing the electromagnetic coupling factor `dp2.couplingPermille ≤ dp1.couplingPermille`
(by widening the edge-to-edge trace spacing $S$) monotonically increases both the odd-mode impedance
`evalOddModeZ0MilliOhm` and the differential impedance `evalDiffImpedanceMilliOhm`:
$$Z_{\text{diff}}(k_1) \le Z_{\text{diff}}(k_2).$$ -/
theorem diffImpedance_monotone_uncoupled
    (dp1 dp2 : DiffPairSpec)
    (hSameZ0 : dp1.z0MilliOhm = dp2.z0MilliOhm)
    (hCoupling : dp2.couplingPermille ≤ dp1.couplingPermille) :
    evalOddModeZ0MilliOhm dp1 ≤ evalOddModeZ0MilliOhm dp2 ∧
    evalDiffImpedanceMilliOhm dp1 ≤ evalDiffImpedanceMilliOhm dp2 := by
  dsimp only [evalOddModeZ0MilliOhm, evalDiffImpedanceMilliOhm]
  rw [hSameZ0]
  have hSub : 1000 - dp1.couplingPermille ≤ 1000 - dp2.couplingPermille := by omega
  have hMul : dp2.z0MilliOhm * (1000 - dp1.couplingPermille) ≤
      dp2.z0MilliOhm * (1000 - dp2.couplingPermille) :=
    Nat.mul_le_mul_left dp2.z0MilliOhm hSub
  have hDiv : (dp2.z0MilliOhm * (1000 - dp1.couplingPermille)) / 1000 ≤
      (dp2.z0MilliOhm * (1000 - dp2.couplingPermille)) / 1000 :=
    Nat.div_le_div_right hMul
  refine ⟨hDiv, by omega⟩

/-- Theorem (`diffImpedance_uncoupled_limit`):
In the uncoupled limit (`dp.couplingPermille = 0`, where spacing $S \gg H$), the odd-mode impedance
equals the single-ended impedance $Z_0$ (`evalOddModeZ0MilliOhm dp = dp.z0MilliOhm`) and the
differential impedance equals `2 * dp.z0MilliOhm`! -/
theorem diffImpedance_uncoupled_limit
    (dp : DiffPairSpec)
    (hZeroCoupling : dp.couplingPermille = 0) :
    evalOddModeZ0MilliOhm dp = dp.z0MilliOhm ∧
    evalDiffImpedanceMilliOhm dp = 2 * dp.z0MilliOhm := by
  dsimp only [evalOddModeZ0MilliOhm, evalDiffImpedanceMilliOhm]
  rw [hZeroCoupling]
  refine ⟨by omega, by omega⟩

/-! ## 3. Serpentine / Trombone Length-Matching & Sub-Picosecond Flight-Time Skew -/

/-- Serpentine (trombone) delay-line meander inserted along the shorter trace of a differential pair
or high-speed DDR / parallel bus byte lane:
* `baseLengthUm`: initial uncompensated Manhattan/Euclidean routed trace length $L_{\text{base}}$ ($\mu\text{m}$),
* `numSegments`: number of U-turn trombone meander loops $N_{\text{seg}}$,
* `meanderAmplitudeUm`: lateral excursion amplitude $A_{\text{um}}$ of each trombone loop ($\mu\text{m}$),
* `minLoopSpacingUm`: copper-to-copper spacing between adjacent meander legs ($\ge 3 W$ to prevent self-coupling crosstalk). -/
structure SerpentineMeander where
  baseLengthUm       : Nat
  numSegments        : Nat
  meanderAmplitudeUm : Nat
  minLoopSpacingUm   : Nat
  deriving DecidableEq, Repr

/-- Total physical routed length $L_{\text{total}} = L_{\text{base}} + 2 \cdot N_{\text{seg}} \cdot A_{\text{um}}$
(in micrometers $\mu\text{m}$) after inserting the serpentine trombone delay line. -/
def evalSerpentineTotalLengthUm (m : SerpentineMeander) : Nat :=
  m.baseLengthUm + 2 * m.numSegments * m.meanderAmplitudeUm

/-- Physical length mismatch $|\Delta L| = |L_{\text{ref}} - L_{\text{routed}}|$ (in micrometers $\mu\text{m}$)
between a reference clock/strobe trace `refLengthUm` and a length-matched trace `routedLengthUm`. -/
def evalLengthSkewUm (refLengthUm routedLengthUm : Nat) : Nat :=
  natAbsDiff refLengthUm routedLengthUm

/-- Electromagnetic time-of-flight skew $\Delta t_{\text{skew}} = |\Delta L| \cdot \tau_{\text{pd}}$
(in femtoseconds $\text{fs}$) across a dielectric with propagation delay `propDelayFsPerUm` ($\text{fs}/\mu\text{m}$). -/
def evalFlightTimeSkewFs (refLengthUm routedLengthUm propDelayFsPerUm : Nat) : Nat :=
  evalLengthSkewUm refLengthUm routedLengthUm * propDelayFsPerUm

abbrev flightTimeFs := evalFlightTimeSkewFs

/-- Theorem (`serpentine_eliminates_length_skew`):
When a `SerpentineMeander` is sized such that its trombone loops compensate the initial length
deficit (`refLengthUm = m.baseLengthUm + 2 * m.numSegments * m.meanderAmplitudeUm`), the total
routed length equals `refLengthUm`, and both the physical length skew `evalLengthSkewUm` and the
electromagnetic flight-time skew `evalFlightTimeSkewFs` vanish identically to `0`! -/
theorem serpentine_eliminates_length_skew
    (refLengthUm propDelayFsPerUm : Nat)
    (m : SerpentineMeander)
    (hMatch : refLengthUm = m.baseLengthUm + 2 * m.numSegments * m.meanderAmplitudeUm) :
    evalSerpentineTotalLengthUm m = refLengthUm ∧
    evalLengthSkewUm refLengthUm (evalSerpentineTotalLengthUm m) = 0 ∧
    evalFlightTimeSkewFs refLengthUm (evalSerpentineTotalLengthUm m) propDelayFsPerUm = 0 := by
  dsimp only [evalSerpentineTotalLengthUm, evalLengthSkewUm, evalFlightTimeSkewFs, natAbsDiff]
  rw [← hMatch]
  have hSub : (if refLengthUm ≤ refLengthUm then refLengthUm - refLengthUm else refLengthUm - refLengthUm) = 0 := by
    simp
  rw [hSub]
  exact ⟨rfl, rfl, Nat.zero_mul propDelayFsPerUm⟩

/-! ## 4. IPC-2152 Trace / Via Current-Carrying Capacity & 2D Geometric Clearance DRC -/

/-- **IPC-2152** power-rail copper trace ampacity specification:
* `railName`: power supply net name (e.g. `"VDD_CORE_1V0"`, `"PA_VCC_13V8"`),
* `widthUm`: power trace width $W$ ($\mu\text{m}$),
* `copperThicknessUm`: copper foil thickness $T$ ($\mu\text{m}$; $35\,\mu\text{m} = 1\,\text{oz}$, $70\,\mu\text{m} = 2\,\text{oz}$),
* `currentMa`: peak DC + RMS load current $I_{\text{load}}$ in milliamperes ($\text{mA}$),
* `maxCurrentDensityUaPerSqUm`: maximum safe IPC-2152 current density $J_{\max}$ in $\mu\text{A}/\mu\text{m}^2$
  (for $\Delta T \le 10^\circ\text{C}$ temperature rise, $J_{\max} \approx 60\,\mu\text{A}/\mu\text{m}^2 = 60\,\text{A/mm}^2$). -/
structure Ipc2152TraceCheck where
  railName                   : String
  widthUm                    : Nat
  copperThicknessUm          : Nat
  currentMa                  : Nat
  maxCurrentDensityUaPerSqUm : Nat
  deriving DecidableEq, Repr

def Ipc2152TraceCheck.maxCurrentDensityMaPerSqUm (spec : Ipc2152TraceCheck) : Nat :=
  spec.maxCurrentDensityUaPerSqUm

/-- Cross-sectional copper area $A_{\text{Cu}} = W \cdot T$ (in square micrometers $\mu\text{m}^2$). -/
def evalTraceCrossSectionSqUm (spec : Ipc2152TraceCheck) : Nat :=
  spec.widthUm * spec.copperThicknessUm

/-- Maximum safe current capacity $I_{\max,\text{mA}} = \frac{A_{\text{Cu}} \cdot J_{\max,\mu\text{A}/\mu\text{m}^2}}{1000}$
(in milliamperes $\text{mA}$) under IPC-2152 current-density derating. -/
def evalMaxTraceCurrentMa (spec : Ipc2152TraceCheck) : Nat :=
  (evalTraceCrossSectionSqUm spec * spec.maxCurrentDensityUaPerSqUm) / 1000

/-- Check that a power trace obeys the IPC-2152 ampacity bound `spec.currentMa ≤ evalMaxTraceCurrentMa spec`. -/
def checkIpc2152TraceAmpacity (spec : Ipc2152TraceCheck) : Bool :=
  decide (spec.widthUm > 0) &&
  decide (spec.copperThicknessUm > 0) &&
  decide (spec.currentMa ≤ evalMaxTraceCurrentMa spec)

/-- Stitched parallel PTH / micro-via array connecting high-current power planes or RF ground shields:
* `numVias`: number of parallel stitched vias $N_{\text{via}}$,
* `perViaLimitMa`: maximum rated DC current per individual plated via barrel ($\text{mA}$, e.g. `1500 mA` for a $0.3\,\text{mm}$ via),
* `singleViaInductancePh`: parasitic partial inductance $L_1$ of one via barrel in picohenries ($\text{pH}$, e.g. `600 pH`),
* `totalLoadCurrentMa`: total current routed through the via array ($\text{mA}$). -/
structure ViaArraySpec where
  numVias               : Nat
  perViaLimitMa         : Nat
  singleViaInductancePh : Nat
  totalLoadCurrentMa    : Nat
  deriving DecidableEq, Repr

def ViaArraySpec.parasiticInductancePh (v : ViaArraySpec) : Nat :=
  v.singleViaInductancePh

/-- Effective parallel parasitic inductance $L_{\text{eff}} = \frac{L_1}{N_{\text{via}}}$ (in picohenries $\text{pH}$)
of an $N$-via stitched array. -/
def evalViaArrayInductancePh (v : ViaArraySpec) : Nat :=
  v.singleViaInductancePh / v.numVias

/-- Check that a stitched via array has at least 2 redundant vias and carries `totalLoadCurrentMa`
within the parallel ampacity limit `numVias * perViaLimitMa`. -/
def checkViaArraySafe (v : ViaArraySpec) : Bool :=
  decide (2 ≤ v.numVias) &&
  decide (v.totalLoadCurrentMa ≤ v.numVias * v.perViaLimitMa)

/-- Theorem (`viaArray_current_safe`):
If `checkViaArraySafe v = true`, then `v.numVias ≥ 2` and the per-via shared current
`v.totalLoadCurrentMa / v.numVias` never exceeds `v.perViaLimitMa`! -/
theorem viaArray_current_safe
    (v : ViaArraySpec)
    (hOk : checkViaArraySafe v = true) :
    2 ≤ v.numVias ∧
    v.totalLoadCurrentMa ≤ v.numVias * v.perViaLimitMa ∧
    v.totalLoadCurrentMa / v.numVias ≤ (v.numVias * v.perViaLimitMa) / v.numVias := by
  unfold checkViaArraySafe at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hDiv : v.totalLoadCurrentMa / v.numVias ≤ (v.numVias * v.perViaLimitMa) / v.numVias :=
    Nat.div_le_div_right hOk.2
  exact ⟨hOk.1, hOk.2, hDiv⟩

/-- Theorem (`viaArray_reduces_inductance`):
A parallel 2-via stitch halves the parasitic via barrel inductance (`evalViaArrayInductancePh v = v.singleViaInductancePh / 2`),
which is strictly bounded by the single-via inductance `v.singleViaInductancePh`. -/
theorem viaArray_reduces_inductance
    (v : ViaArraySpec)
    (hTwo : v.numVias = 2) :
    evalViaArrayInductancePh v = v.singleViaInductancePh / 2 ∧
    evalViaArrayInductancePh v ≤ v.singleViaInductancePh := by
  dsimp only [evalViaArrayInductancePh]
  rw [hTwo]
  refine ⟨rfl, by omega⟩

/-- 2D geometric copper-to-copper clearance, board-edge keepout, and IPC-2221 high-voltage creepage
rules on the PCB layout:
* `minCopperClearanceUm`: minimum measured trace-to-trace / trace-to-pad air gap ($\mu\text{m}$),
* `fabMinClearanceUm`: PCB fab house minimum clearance rule ($100\,\mu\text{m} \approx 4\,\text{mil}$),
* `minEdgeKeepoutUm`: minimum copper distance from routed board outline / V-score edge ($\ge 300\,\mu\text{m}$),
* `peakVoltageV`: highest DC/AC peak voltage present on the board ($\text{V}$),
* `hvCreepageUm`: measured creepage distance around high-voltage nodes ($\ge 5\,\mu\text{m/V}$). -/
structure PcbClearanceSpec where
  minCopperClearanceUm : Nat
  fabMinClearanceUm    : Nat
  minEdgeKeepoutUm     : Nat
  peakVoltageV         : Nat
  hvCreepageUm         : Nat
  deriving DecidableEq, Repr

/-- Complete multi-layer high-speed PCB signoff checker (`checkPcbBoardSignoff`):
1. Single-ended $50\,\Omega$ RF/clock trace passes `checkSingleEndedZ0`,
2. Edge-coupled differential pair matches `zDiffTargetMilliOhm` within `zDiffTolMilliOhm`,
3. Serpentine length-matching keeps flight-time skew within `maxFlightSkewFs`,
4. Power rail trace passes IPC-2152 current-density limits (`checkIpc2152TraceAmpacity`),
5. Stitched via array passes parallel current-sharing (`checkViaArraySafe`),
6. 2D copper clearance, board-edge keepout ($\ge 300\,\mu\text{m}$), and IPC-2221 voltage creepage
   (`5 * peakVoltageV ≤ hvCreepageUm`) all hold. -/
def checkPcbBoardSignoff
    (seTrace : PcbTraceSpec)
    (diffPair : DiffPairSpec)
    (meander : SerpentineMeander) (refLengthUm maxFlightSkewFs : Nat)
    (powerRail : Ipc2152TraceCheck)
    (vias : ViaArraySpec)
    (clearance : PcbClearanceSpec) : Bool :=
  let zDiff := evalDiffImpedanceMilliOhm diffPair
  let routedLen := evalSerpentineTotalLengthUm meander
  let skewFs := evalFlightTimeSkewFs refLengthUm routedLen seTrace.dielectric.propDelayFsPerUm
  decide (natAbsDiff zDiff diffPair.zDiffTargetMilliOhm ≤ diffPair.zDiffTolMilliOhm) &&
  decide (3 * seTrace.widthUm ≤ meander.minLoopSpacingUm) &&
  decide (skewFs ≤ maxFlightSkewFs) &&
  checkIpc2152TraceAmpacity powerRail &&
  checkViaArraySafe vias &&
  decide (clearance.fabMinClearanceUm ≤ clearance.minCopperClearanceUm) &&
  decide (300 ≤ clearance.minEdgeKeepoutUm) &&
  decide (5 * clearance.peakVoltageV ≤ clearance.hvCreepageUm) &&
  -- last: the closed-form impedance (`Nat.sqrt`, a logarithm) is the expensive conjunct
  checkSingleEndedZ0 seTrace

/-- Theorem (`pcbBoardSignoff_sound`):
Whenever `checkPcbBoardSignoff` returns `true`, the single-ended and differential impedances are
within tolerance, the serpentine flight-time skew is bounded by `maxFlightSkewFs`, the power rail
and stitched via array obey IPC-2152 current limits, and all copper clearances/creepages hold. -/
theorem pcbBoardSignoff_sound
    (seTrace : PcbTraceSpec) (diffPair : DiffPairSpec)
    (meander : SerpentineMeander) (refLengthUm maxFlightSkewFs : Nat)
    (powerRail : Ipc2152TraceCheck) (vias : ViaArraySpec) (clearance : PcbClearanceSpec)
    (hOk : checkPcbBoardSignoff seTrace diffPair meander refLengthUm maxFlightSkewFs powerRail vias clearance = true) :
    checkSingleEndedZ0 seTrace = true ∧
    natAbsDiff (evalDiffImpedanceMilliOhm diffPair) diffPair.zDiffTargetMilliOhm ≤ diffPair.zDiffTolMilliOhm ∧
    evalFlightTimeSkewFs refLengthUm (evalSerpentineTotalLengthUm meander) seTrace.dielectric.propDelayFsPerUm ≤
      maxFlightSkewFs ∧
    checkIpc2152TraceAmpacity powerRail = true ∧
    checkViaArraySafe vias = true ∧
    clearance.fabMinClearanceUm ≤ clearance.minCopperClearanceUm := by
  unfold checkPcbBoardSignoff at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  exact ⟨hOk.2, hOk.1.1.1.1.1.1.1.1, hOk.1.1.1.1.1.1.2, hOk.1.1.1.1.1.2, hOk.1.1.1.1.2, hOk.1.1.1.2⟩

/-- Golden 4-layer `Rogers RO4350B` + `FR-4` hybrid SDR / FPGA carrier board design. -/
def goldenRf50OhmTrace : PcbTraceSpec where
  netName             := "RF_ANT_50OHM"
  dielectric          := rogers4350bDielectric
  widthUm             := 380
  heightUm            := 170
  copperThicknessUm   := 35
  z0ExtractedMilliOhm := 50200
  z0TargetMilliOhm    := 50000
  z0MaxTolMilliOhm    := 2500

def goldenLvds100OhmPair : DiffPairSpec where
  pairName            := "ADC_LVDS_CLK"
  z0MilliOhm          := 55000
  spacingUm           := 200
  couplingPermille    := 90
  zDiffTargetMilliOhm := 100000
  zDiffTolMilliOhm    := 2000

def goldenDdrMeander : SerpentineMeander where
  baseLengthUm       := 24000
  numSegments        := 5
  meanderAmplitudeUm := 600
  minLoopSpacingUm   := 1200

def goldenPaSupplyRail : Ipc2152TraceCheck where
  railName                   := "PA_VCC_13V8_3A"
  widthUm                    := 2000
  copperThicknessUm          := 35
  currentMa                  := 3000
  maxCurrentDensityUaPerSqUm := 60

def goldenGndViaStitch : ViaArraySpec where
  numVias               := 8
  perViaLimitMa         := 1200
  singleViaInductancePh := 640
  totalLoadCurrentMa    := 3000

def goldenBoardClearance : PcbClearanceSpec where
  minCopperClearanceUm := 150
  fabMinClearanceUm    := 100
  minEdgeKeepoutUm     := 500
  peakVoltageV         := 24
  hvCreepageUm         := 400

/-- The golden 4-layer mixed-signal SDR / FPGA carrier PCB (`Rogers RO4350B` $50.2\,\Omega$ RF microstrip,
$100.1\,\Omega$ LVDS differential clock pair, zero-skew $30.0\,\text{mm}$ serpentine meander, $3\,\text{A}$
IPC-2152 power trace, 8-via stitched ground return with $80\,\text{pH}$ inductance, and $150\,\mu\text{m}$
clearance) passes `checkPcbBoardSignoff`! -/
example :
    checkPcbBoardSignoff
      goldenRf50OhmTrace
      goldenLvds100OhmPair
      goldenDdrMeander 30000 50
      goldenPaSupplyRail
      goldenGndViaStitch
      goldenBoardClearance = true := by
  decide +kernel

/-! ## 5. Microstrip impedance from geometry

The closed form is `microstripZ0MilliOhm` (§1), and `checkSingleEndedZ0` gates on it. Values the
kernel computes (an `example`, not a theorem): the golden RO4350B strip lands within its ±2.5 Ω band,
and the 80 µm strip on 500 µm PTFE is a high-impedance line, not a 50 Ω one. -/

example :
    microstripZ0MilliOhm 380 170 35 3480 = 47894 ∧ microstripZ0MilliOhm 80 500 20 2000 = 171202 := by
  decide +kernel

/-! ## 6. 2D Axis-Aligned Bounding Box (`PcbBBox`) Geometric Clearance DRC -/

/-- 2D axis-aligned copper obstacle bounding box on a PCB layer (coordinates in micrometers $\mu\text{m}$):
* `id`: unique obstacle identifier,
* `netId`: electrical net identifier (obstacles on the same net may legally touch or overlap),
* `xMinUm`, `yMinUm`, `xMaxUm`, `yMaxUm`: bounding-box coordinates $[x_{\min}, x_{\max}] \times [y_{\min}, y_{\max}]$. -/
structure PcbBBox where
  id     : Nat
  netId  : Nat
  xMinUm : Int
  yMinUm : Int
  xMaxUm : Int
  yMaxUm : Int
  deriving DecidableEq, Repr

/-- 1D interval separation gap between $[a_{\min}, a_{\max}]$ and $[b_{\min}, b_{\max}]$ in micrometers ($\mu\text{m}$):
returns `0` when the intervals overlap or touch, and the positive edge-to-edge gap otherwise. -/
def intervalGapUm (aMin aMax bMin bMax : Int) : Int :=
  max (bMin - aMax) (max (aMin - bMax) 0)

/-- 2D Chebyshev ($L_\infty$) bounding-box clearance gap between two `PcbBBox` copper features:
$$\text{gap}(A, B) = \max\bigl(\text{intervalGapUm}(A_x, B_x),\; \text{intervalGapUm}(A_y, B_y)\bigr).$$ -/
def bboxClearanceUm (a b : PcbBBox) : Int :=
  max (intervalGapUm a.xMinUm a.xMaxUm b.xMinUm b.xMaxUm)
      (intervalGapUm a.yMinUm a.yMaxUm b.yMinUm b.yMaxUm)

/-- Theorem (`bboxClearanceUm_nonneg`):
Universally for all bounding boxes `a b : PcbBBox`, the 2D geometric clearance gap is non-negative:
`0 ≤ bboxClearanceUm a b`. -/
theorem bboxClearanceUm_nonneg (a b : PcbBBox) :
    0 ≤ bboxClearanceUm a b := by
  dsimp only [bboxClearanceUm, intervalGapUm]
  omega

theorem intervalGapUm_symm (aMin aMax bMin bMax : Int) :
    intervalGapUm aMin aMax bMin bMax = intervalGapUm bMin bMax aMin aMax := by
  dsimp only [intervalGapUm]
  omega

/-- Theorem (`bboxClearanceUm_symm`):
Universally for all bounding boxes `a b : PcbBBox`, the 2D geometric clearance gap is symmetric:
`bboxClearanceUm a b = bboxClearanceUm b a`. -/
theorem bboxClearanceUm_symm (a b : PcbBBox) :
    bboxClearanceUm a b = bboxClearanceUm b a := by
  dsimp only [bboxClearanceUm]
  rw [intervalGapUm_symm a.xMinUm a.xMaxUm b.xMinUm b.xMaxUm]
  rw [intervalGapUm_symm a.yMinUm a.yMaxUm b.yMinUm b.yMaxUm]

/-- Pairwise 2D bounding-box DRC check: distinct obstacles on different electrical nets (`a.netId != b.netId`)
must be separated by at least `minClearanceUm`. -/
def checkBBoxPairDrc (minClearanceUm : Int) (a b : PcbBBox) : Bool :=
  if a.id == b.id || a.netId == b.netId then true
  else decide (minClearanceUm ≤ bboxClearanceUm a b)

/-- Complete board-level 2D bounding-box DRC checker over a list of copper obstacles `boxes`. -/
def checkBoardBBoxDrc (boxes : List PcbBBox) (minClearanceUm : Int) : Bool :=
  boxes.all fun a => boxes.all fun b => checkBBoxPairDrc minClearanceUm a b

/-- Golden 4-obstacle PCB layout with two nets (`netId = 1` RF trace + pad, `netId = 2` GND shield + via)
separated by $\ge 150\,\mu\text{m}$ clearance. -/
def goldenPcbBBoxLayout : List PcbBBox :=
  [ { id := 0, netId := 1, xMinUm := 0,   yMinUm := 0,   xMaxUm := 500, yMaxUm := 200 }
  , { id := 1, netId := 1, xMinUm := 450, yMinUm := 0,   xMaxUm := 800, yMaxUm := 200 } -- same net overlap legal
  , { id := 2, netId := 2, xMinUm := 0,   yMinUm := 380, xMaxUm := 800, yMaxUm := 600 } -- 180 um Y gap to net 1
  , { id := 3, netId := 2, xMinUm := 960, yMinUm := 0,   xMaxUm := 1200, yMaxUm := 600 } ] -- 160 um X gap to net 1

/-- Violating PCB layout where obstacle `id = 4` (`netId = 3`) encroaches within $40\,\mu\text{m} < 150\,\mu\text{m}$
of net 1 (`xMinUm = 840` vs `xMaxUm = 800`). -/
def violatingPcbBBoxLayout : List PcbBBox :=
  goldenPcbBBoxLayout ++
    [ { id := 4, netId := 3, xMinUm := 840, yMinUm := 0, xMaxUm := 1000, yMaxUm := 200 } ]

/-- Theorem (`board_bbox_drc_multi_obstacle_verified`):
`checkBoardBBoxDrc` accepts `goldenPcbBBoxLayout` at $150\,\mu\text{m}$ fab clearance (allowing
same-net pad-to-trace overlap while enforcing cross-net gaps $\ge 160\,\mu\text{m}$) and refuses
`violatingPcbBBoxLayout` ($40\,\mu\text{m} < 150\,\mu\text{m}$ encroachment)! -/
example :
    checkBoardBBoxDrc goldenPcbBBoxLayout 150 = true ∧
    checkBoardBBoxDrc violatingPcbBBoxLayout 150 = false := by
  decide +kernel

/-! ## 7. Dielectric + Skin-Effect Frequency-Dependent Insertion Loss (`evalChannelInsertionLossMdB`) & Eye-Diagram Opening Signoff (`EyeDiagramSpec`, `checkEyeOpeningSignoff`) -/

/-- Frequency-dependent high-speed PCB transmission-line insertion loss $IL(f, L)$ (in milli-decibels
$\text{mdB}$, where $1000\,\text{mdB} = 1.0\,\text{dB}$) combining dielectric loss-tangent dissipation
($\propto L \cdot f \cdot \tan\delta$) and copper conductor skin-effect attenuation ($\propto L \cdot f \cdot \alpha_{\text{skin}}$):
$$IL_{\text{mdB}} = \frac{L_{\mu\text{m}} \cdot f_{\text{MHz}} \cdot \text{dfPpm}}{10^9} + \frac{L_{\mu\text{m}} \cdot f_{\text{MHz}} \cdot \alpha_{\text{skin}}}{10^6}.$$ -/
def evalChannelInsertionLossMdB
    (diel : PcbDielectric) (lengthUm freqMhz skinCoeff : Nat) : Nat :=
  (lengthUm * freqMhz * diel.dfPpm) / 1000000000 +
  (lengthUm * freqMhz * skinCoeff) / 1000000

/-- Theorem (`channelInsertionLoss_monotone`):
Increasing either the PCB trace length (`len1 ≤ len2`) or the substrate dielectric dissipation factor
(`diel1.dfPpm ≤ diel2.dfPpm`) monotonically increases (or preserves) the channel insertion loss
`evalChannelInsertionLossMdB`! -/
theorem channelInsertionLoss_monotone
    (diel1 diel2 : PcbDielectric) (len1 len2 freqMhz skinCoeff : Nat)
    (hLen : len1 ≤ len2)
    (hDf : diel1.dfPpm ≤ diel2.dfPpm) :
    evalChannelInsertionLossMdB diel1 len1 freqMhz skinCoeff ≤
      evalChannelInsertionLossMdB diel2 len2 freqMhz skinCoeff := by
  dsimp only [evalChannelInsertionLossMdB]
  have hLf : len1 * freqMhz ≤ len2 * freqMhz := Nat.mul_le_mul_right freqMhz hLen
  have hDielProd : len1 * freqMhz * diel1.dfPpm ≤ len2 * freqMhz * diel2.dfPpm :=
    Nat.mul_le_mul hLf hDf
  have hSkinProd : len1 * freqMhz * skinCoeff ≤ len2 * freqMhz * skinCoeff :=
    Nat.mul_le_mul_right skinCoeff hLf
  have hDiv1 : (len1 * freqMhz * diel1.dfPpm) / 1000000000 ≤ (len2 * freqMhz * diel2.dfPpm) / 1000000000 :=
    Nat.div_le_div_right hDielProd
  have hDiv2 : (len1 * freqMhz * skinCoeff) / 1000000 ≤ (len2 * freqMhz * skinCoeff) / 1000000 :=
    Nat.div_le_div_right hSkinProd
  omega

/-- High-Speed SerDes / LVDS Eye-Diagram Vertical & Horizontal Opening Specification coupling:
* `channelName`: high-speed serial lane identifier,
* `dielectric`: PCB substrate layer (`rogers4350bDielectric`, `isolaIspeedDielectric`, `fr4StandardDielectric`),
* `diffPair`: edge-coupled differential pair geometry & target impedance (`DiffPairSpec`),
* `meander`: serpentine length-matching delay line (`SerpentineMeander`),
* `refLengthUm`: reference lane length ($\mu\text{m}$),
* `freqMhz`: Nyquist / fundamental signaling frequency ($\text{MHz}$),
* `skinCoeff`: copper skin-effect loss coefficient,
* `txLaunchSwingMv`: transmitter differential launch voltage swing $V_{\text{tx}}$ ($\text{mV}$),
* `isiPenaltyMvPerDb`: vertical eye closure per dB ($1000\,\text{mdB}$) of channel insertion loss ($\text{mV/dB}$),
* `minEyeHeightMv`: minimum required vertical eye opening at the receiver slicer ($\text{mV}$),
* `unitIntervalFs`: 1 Unit Interval ($1\,\text{UI} = 1 / R_{\text{bit}}$) in femtoseconds ($\text{fs}$),
* `rjDjJitterFs`: combined random + deterministic TX/RX clock jitter budget ($\text{fs}$),
* `minEyeWidthFs`: minimum required horizontal eye opening ($t_{\text{eye}} = \text{UI} - t_{\text{jitter}} - t_{\text{skew}}$, in $\text{fs}$),
* `maxInsertionLossMdB`: maximum allowable channel insertion loss ($\text{mdB}$). -/
structure EyeDiagramSpec where
  channelName         : String
  dielectric          : PcbDielectric
  diffPair            : DiffPairSpec
  meander             : SerpentineMeander
  refLengthUm         : Nat
  freqMhz             : Nat
  skinCoeff           : Nat
  txLaunchSwingMv     : Nat
  isiPenaltyMvPerDb   : Nat
  minEyeHeightMv      : Nat
  unitIntervalFs      : Nat
  rjDjJitterFs        : Nat
  minEyeWidthFs       : Nat
  maxInsertionLossMdB : Nat
  deriving DecidableEq, Repr

/-- Total vertical eye-closure penalty (in millivolts $\text{mV}$) due to frequency-dependent
ISI insertion loss and differential impedance mismatch reflection. -/
def evalEyeVerticalLossMv (spec : EyeDiagramSpec) : Nat :=
  let routedLenUm := evalSerpentineTotalLengthUm spec.meander
  let ilMdB := evalChannelInsertionLossMdB spec.dielectric routedLenUm spec.freqMhz spec.skinCoeff
  let zDiffErrMilliOhm := natAbsDiff (evalDiffImpedanceMilliOhm spec.diffPair) spec.diffPair.zDiffTargetMilliOhm
  (ilMdB * spec.isiPenaltyMvPerDb) / 1000 + zDiffErrMilliOhm / 100

/-- Vertical eye opening $V_{\text{eye}} = V_{\text{tx}} - \Delta V_{\text{ISI+refl}}$ (in millivolts $\text{mV}$)
at the receiver decision latch. -/
def evalEyeHeightMv (spec : EyeDiagramSpec) : Nat :=
  spec.txLaunchSwingMv - evalEyeVerticalLossMv spec

/-- Horizontal eye opening $t_{\text{eye}} = \text{UI} - (t_{\text{RJ+DJ}} + \Delta t_{\text{skew}})$
(in femtoseconds $\text{fs}$) at the receiver CDR sampling phase. -/
def evalEyeWidthFs (spec : EyeDiagramSpec) : Nat :=
  let routedLenUm := evalSerpentineTotalLengthUm spec.meander
  let skewFs := evalFlightTimeSkewFs spec.refLengthUm routedLenUm spec.dielectric.propDelayFsPerUm
  spec.unitIntervalFs - (spec.rjDjJitterFs + skewFs)

/-- Complete High-Speed SerDes / LVDS Eye-Diagram Opening Signoff Checker (`checkEyeOpeningSignoff`):
1. Channel insertion loss across the serpentine-routed trace length is at most `maxInsertionLossMdB`,
2. Edge-coupled differential pair impedance matches `zDiffTargetMilliOhm` within `zDiffTolMilliOhm`,
3. Strictly positive vertical eye opening (`0 < spec.minEyeHeightMv`), vertical loss does not collapse
   the launch swing, and `minEyeHeightMv ≤ evalEyeHeightMv spec`,
4. Strictly positive horizontal eye opening (`0 < spec.minEyeWidthFs`), total jitter plus flight-time
   skew does not collapse the unit interval, and `minEyeWidthFs ≤ evalEyeWidthFs spec`. -/
def checkEyeOpeningSignoff (spec : EyeDiagramSpec) : Bool :=
  let routedLenUm := evalSerpentineTotalLengthUm spec.meander
  let ilMdB := evalChannelInsertionLossMdB spec.dielectric routedLenUm spec.freqMhz spec.skinCoeff
  let zDiffErr := natAbsDiff (evalDiffImpedanceMilliOhm spec.diffPair) spec.diffPair.zDiffTargetMilliOhm
  let vertLossMv := evalEyeVerticalLossMv spec
  let skewFs := evalFlightTimeSkewFs spec.refLengthUm routedLenUm spec.dielectric.propDelayFsPerUm
  decide (ilMdB ≤ spec.maxInsertionLossMdB) &&
  decide (zDiffErr ≤ spec.diffPair.zDiffTolMilliOhm) &&
  decide (0 < spec.minEyeHeightMv) &&
  decide (vertLossMv ≤ spec.txLaunchSwingMv) &&
  decide (spec.minEyeHeightMv ≤ evalEyeHeightMv spec) &&
  decide (0 < spec.minEyeWidthFs) &&
  decide (spec.rjDjJitterFs + skewFs ≤ spec.unitIntervalFs) &&
  decide (spec.minEyeWidthFs ≤ evalEyeWidthFs spec)

/-- Theorem (`eyeOpeningSignoff_sound`):
Whenever `checkEyeOpeningSignoff spec = true`, the high-speed PCB channel satisfies:
1. Bounded dielectric + skin-effect insertion loss (`evalChannelInsertionLossMdB ... ≤ spec.maxInsertionLossMdB`),
2. Bounded differential impedance reflection mismatch (`natAbsDiff ... ≤ spec.diffPair.zDiffTolMilliOhm`),
3. Certified vertical voltage eye opening (`spec.minEyeHeightMv ≤ evalEyeHeightMv spec`), and
4. Certified horizontal timing eye opening (`spec.minEyeWidthFs ≤ evalEyeWidthFs spec`). -/
theorem eyeOpeningSignoff_sound
    (spec : EyeDiagramSpec)
    (hOk : checkEyeOpeningSignoff spec = true) :
    evalChannelInsertionLossMdB spec.dielectric (evalSerpentineTotalLengthUm spec.meander) spec.freqMhz spec.skinCoeff ≤
      spec.maxInsertionLossMdB ∧
    natAbsDiff (evalDiffImpedanceMilliOhm spec.diffPair) spec.diffPair.zDiffTargetMilliOhm ≤
      spec.diffPair.zDiffTolMilliOhm ∧
    spec.minEyeHeightMv ≤ evalEyeHeightMv spec ∧
    spec.minEyeWidthFs ≤ evalEyeWidthFs spec := by
  dsimp only [checkEyeOpeningSignoff] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq,
      decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.1.1.1.1.1.1, hOk.1.1.1.1.1.1.2, hOk.1.1.1.2, hOk.2⟩

/-- Theorem (`eyeOpeningSignoff_positive_and_exact`):
Whenever `checkEyeOpeningSignoff spec = true`, both the vertical and horizontal eye openings are
strictly positive (`0 < evalEyeHeightMv spec`, `0 < evalEyeWidthFs spec`), and the `Nat` voltage
and timing subtractions are exact without truncation (`evalEyeHeightMv spec + evalEyeVerticalLossMv spec = spec.txLaunchSwingMv`
and `evalEyeWidthFs spec + spec.rjDjJitterFs + skewFs = spec.unitIntervalFs`). -/
theorem eyeOpeningSignoff_positive_and_exact
    (spec : EyeDiagramSpec)
    (hOk : checkEyeOpeningSignoff spec = true) :
    0 < evalEyeHeightMv spec ∧
    0 < evalEyeWidthFs spec ∧
    evalEyeHeightMv spec + evalEyeVerticalLossMv spec = spec.txLaunchSwingMv ∧
    evalEyeWidthFs spec + spec.rjDjJitterFs +
      evalFlightTimeSkewFs spec.refLengthUm (evalSerpentineTotalLengthUm spec.meander) spec.dielectric.propDelayFsPerUm =
      spec.unitIntervalFs := by
  dsimp only [checkEyeOpeningSignoff] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq,
      decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hOk
  have hMinH : 0 < spec.minEyeHeightMv := hOk.1.1.1.1.1.2
  have hNoTruncH : evalEyeVerticalLossMv spec ≤ spec.txLaunchSwingMv := hOk.1.1.1.1.2
  have hGeH : spec.minEyeHeightMv ≤ evalEyeHeightMv spec := hOk.1.1.1.2
  have hMinW : 0 < spec.minEyeWidthFs := hOk.1.1.2
  have hNoTruncW := hOk.1.2
  have hGeW : spec.minEyeWidthFs ≤ evalEyeWidthFs spec := hOk.2
  dsimp only [evalEyeHeightMv, evalEyeWidthFs] at hGeH hGeW ⊢
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Golden $10\,\text{Gbps}$ ($f_{\text{Nyquist}} = 5000\,\text{MHz}$, $\text{UI} = 100000\,\text{fs} = 100\,\text{ps}$)
`Rogers RO4350B` $30\,\text{mm}$ differential SerDes lane (`800 mV` launch swing, `1155 mdB` insertion
loss, `742 mV ≥ 400 mV` vertical eye opening, `80000 fs ≥ 60000 fs` horizontal eye opening). -/
def goldenSerdesEyeSpec : EyeDiagramSpec where
  channelName         := "SERDES_10G_RX0_RO4350B"
  dielectric          := rogers4350bDielectric
  diffPair            := goldenLvds100OhmPair
  meander             := goldenDdrMeander
  refLengthUm         := 30000
  freqMhz             := 5000
  skinCoeff           := 4
  txLaunchSwingMv     := 800
  isiPenaltyMvPerDb   := 50
  minEyeHeightMv      := 400
  unitIntervalFs      := 100000
  rjDjJitterFs        := 20000
  minEyeWidthFs       := 60000
  maxInsertionLossMdB := 3000

/-- Lossy $120\,\text{mm}$ `FR-4` lane at $5\,\text{GHz}$ whose dielectric loss tangent ($\tan\delta = 0.020$)
causes $14400\,\text{mdB} = 14.4\,\text{dB} > 3.0\,\text{dB}$ insertion loss and closes the vertical eye! -/
def highLossFr4EyeSpec : EyeDiagramSpec :=
  { goldenSerdesEyeSpec with
    channelName := "SERDES_10G_FR4_LOSSY"
    dielectric  := fr4StandardDielectric
    meander     := { goldenDdrMeander with baseLengthUm := 114000 }
    refLengthUm := 120000 }

/-- Uncompensated length-skewed lane (`baseLengthUm = 12000` vs `refLengthUm = 30000`, `numSegments = 0`)
suffering $90000\,\text{fs}$ P/N skew that collapses the $100000\,\text{fs}$ unit interval! -/
def unmatchedSkewEyeSpec : EyeDiagramSpec :=
  { goldenSerdesEyeSpec with
    channelName := "SERDES_10G_UNMATCHED_SKEW"
    meander     := { goldenDdrMeander with baseLengthUm := 12000, numSegments := 0 } }

/-- Degenerate zero-margin eye spec (`minEyeHeightMv = 0`, `txLaunchSwingMv = 58`) where vertical eye
height is completely closed (`evalEyeHeightMv = 0 mV`). -/
def zeroHeightClosedEyeSpec : EyeDiagramSpec :=
  { goldenSerdesEyeSpec with
    channelName     := "SERDES_10G_ZERO_EYE_HEIGHT"
    txLaunchSwingMv := 58
    minEyeHeightMv  := 0 }

/-- Theorem (`eyeOpeningSignoff_poles`):
`checkEyeOpeningSignoff` accepts `goldenSerdesEyeSpec` and refuses `highLossFr4EyeSpec`
(excessive FR-4 dielectric insertion loss), `unmatchedSkewEyeSpec` (horizontal eye closure due to skew),
and `zeroHeightClosedEyeSpec` (`0 mV` closed vertical eye)! -/
example :
    checkEyeOpeningSignoff goldenSerdesEyeSpec = true ∧
    checkEyeOpeningSignoff highLossFr4EyeSpec = false ∧
    checkEyeOpeningSignoff unmatchedSkewEyeSpec = false ∧
    checkEyeOpeningSignoff zeroHeightClosedEyeSpec = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Obend.Hardware.PCB
end
