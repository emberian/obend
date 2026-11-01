module
/-
# Obend.Hardware.RF — Ham Radio & RF Transceiver Chain: Transmission-Line VSWR, Conjugate Impedance Matching, Tayloe Quadrature ($I/Q$) SDR Mixer, Friis Noise Figure & FCC Part 97 Harmonics

Formalizes **RF engineering, amateur (ham) radio transceiver architecture, and software-defined radio
(SDR) signal chains** within `Obend.Hardware`:

1. **Transmission Lines, Reflection Coefficient $|\Gamma|^2$, VSWR & Conjugate Matching (`Impedance`, `gammaMagSqNum`, `gammaMagSqDen`)**:
   - Models complex load impedance $Z_L = R_L + j X_L$ terminated on a characteristic impedance
     $Z_0 = 50\,\Omega$, with squared voltage reflection magnitude
     $|\Gamma|^2 = \frac{(R_L - Z_0)^2 + X_L^2}{(R_L + Z_0)^2 + X_L^2}$,
   - Proves **`conjugate_match_zero_reflection`**: when $R_L = Z_0$ and $X_L = 0$,
     `gammaMagSqNum z0 zL = 0` ($\Gamma = 0, \text{VSWR} = 1.0 : 1$, zero reflected power; targeted by `#tooth`),
   - Proves **`conjugate_match_maximizes_power`** (Maximum Power Transfer Theorem): for a generator
     with internal impedance $Z_S = R_S + j X_S$ and load $Z_L = R_L + j X_L$, the scaled power
     transfer numerator $4 R_S R_L$ never exceeds $(R_S + R_L)^2 + (X_S + X_L)^2$, achieving exact
     equality when $R_L = R_S$ and $X_L = -X_S$ ($Z_L = Z_S^*$),
   - Proves `vswr_mismatch_300ohm_on_50ohm_refused` ($\text{VSWR} = 6:1$ twin-lead mismatch rejected).
2. **ITU / FCC Amateur Radio Bands & L-Network Antenna Tuner (`HamBand`, `checkHamBandFreqKhz`, `LMatchNetwork`)**:
   - Covers `160m`, `80m`, `40m` (`7000..7300 kHz`, `7074 kHz` FT8), `20m` (`14000..14350 kHz`,
     `14074 kHz` FT8), `2m` (`144000..148000 kHz`), and `70cm` (`420000..450000 kHz`),
   - Verifies L-section reactive impedance transformation $R_{\text{high}} = R_{\text{low}} \cdot (1 + Q^2)$.
3. **Tayloe Quadrature ($I/Q$) Switching SDR Detector & Image Rejection (`evalQuadratureImagePhaseCancel`)**:
   - Models the 4-phase ($0^\circ, 90^\circ, 180^\circ, 270^\circ$) Tayloe commutator mixer + $90^\circ$
     Hilbert phasing network,
   - Proves **`tayloe_iq_cancels_image_sideband`**: when $I$ and $Q$ conversion gains are matched
     (`gainI = gainQ`) and quadrature phase error is zero (`phaseErr = 0`), the unwanted image
     sideband cancels identically to `0` while the desired USB/LSB sideband coherently doubles to
     `2 * gainI * sigAmp`! (Targeted by `#tooth`.)
4. **Cascaded Friis Noise Figure & FCC Part 97.307(d) Harmonic Suppression (`evalFriisTwoStageMilliNf`, `checkFccPart97Harmonics`)**:
   - Proves `lna_gain_reduces_cascaded_noise_figure` and verifies that a Class-E HF Power Amplifier
     followed by a 7-element Chebyshev Low-Pass Filter suppresses 2nd and 3rd harmonics below the
     FCC Part 97.307(d) $-43.0\,\text{dBc}$ limit (`fcc_part97_chebyshev7_pa_accepted` vs
     `unfiltered_class_e_pa_refused`).
5. **Complete 40m FT8 Ham Radio Transceiver Signoff Certificate (`RfTransceiverCert`, `checkRfTransceiverSignoff`)**.
-/
public import Obend.Hardware.Thermal
@[expose] public section

namespace Obend.Hardware.RF
open Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. Complex Impedance, Reflection Coefficient $|\Gamma|^2$, VSWR & Conjugate Match -/

/-- Complex impedance $Z = R + j X$ (in ohms $\Omega$ or milliohms $\text{m}\Omega$):
* `rOhm`: resistive real part $R$,
* `xOhm`: reactive imaginary part $X = \omega L - \frac{1}{\omega C}$ ($X > 0$ inductive, $X < 0$ capacitive). -/
structure Impedance where
  rOhm : Int
  xOhm : Int
  deriving DecidableEq, Repr

/-- Numerator of the squared voltage reflection coefficient $|\Gamma|^2 = \left|\frac{Z_L - Z_0}{Z_L + Z_0}\right|^2$:
$$\text{gammaMagSqNum}(Z_0, Z_L) = (R_L - Z_0)^2 + X_L^2.$$ -/
def gammaMagSqNum (z0 : Int) (zL : Impedance) : Int :=
  (zL.rOhm - z0) * (zL.rOhm - z0) + zL.xOhm * zL.xOhm

/-- Denominator of the squared voltage reflection coefficient $|\Gamma|^2$:
$$\text{gammaMagSqDen}(Z_0, Z_L) = (R_L + Z_0)^2 + X_L^2.$$ -/
def gammaMagSqDen (z0 : Int) (zL : Impedance) : Int :=
  (zL.rOhm + z0) * (zL.rOhm + z0) + zL.xOhm * zL.xOhm

/-- Exact rational VSWR $\le 2.0 : 1$ checker (no floating-point square roots required):
$$\text{VSWR} = \frac{1 + |\Gamma|}{1 - |\Gamma|} \le 2 \iff |\Gamma| \le \frac{1}{3} \iff 9 \cdot |\Gamma|^2 \le 1 \iff 9 \cdot \text{gammaMagSqNum} \le \text{gammaMagSqDen}.$$ -/
def checkVswrUnder2To1 (z0 : Int) (zL : Impedance) : Bool :=
  decide (0 < z0) &&
  decide (0 < zL.rOhm) &&
  decide (9 * gammaMagSqNum z0 zL ≤ gammaMagSqDen z0 zL)

/-- Exact rational VSWR $\le 1.5 : 1$ checker:
$$\text{VSWR} \le 1.5 \iff |\Gamma| \le \frac{1}{5} \iff 25 \cdot |\Gamma|^2 \le 1 \iff 25 \cdot \text{gammaMagSqNum} \le \text{gammaMagSqDen}.$$ -/
def checkVswrUnder3To2 (z0 : Int) (zL : Impedance) : Bool :=
  decide (0 < z0) &&
  decide (0 < zL.rOhm) &&
  decide (25 * gammaMagSqNum z0 zL ≤ gammaMagSqDen z0 zL)

/-- Theorem (`conjugate_match_zero_reflection`):
When a load impedance `zL` is matched to the characteristic transmission-line impedance `z0`
(`zL.rOhm = z0` and `zL.xOhm = 0`), the reflected power numerator `gammaMagSqNum z0 zL` is
identically `0` ($\Gamma = 0, \text{VSWR} = 1.0 : 1$)!
Written via `dsimp only` + `rw` (zero `simp` aux defs) so `#tooth` can mutate `gammaMagSqNum`. -/
theorem conjugate_match_zero_reflection
    (z0 : Int) (zL : Impedance)
    (hR : zL.rOhm = z0) (hX : zL.xOhm = 0) :
    gammaMagSqNum z0 zL = 0 := by
  dsimp only [gammaMagSqNum]
  rw [hR, hX, Int.sub_self, Int.mul_zero, Int.add_zero]

/-- Scaled delivered power numerator $4 R_S R_L$ in the Maximum Power Transfer ratio
$\frac{P_{\text{load}}}{P_{\text{avail,max}}} = \frac{4 R_S R_L}{(R_S + R_L)^2 + (X_S + X_L)^2}$. -/
def powerTransferNumScaled (zS zL : Impedance) : Int :=
  4 * zS.rOhm * zL.rOhm

/-- Scaled available power denominator $(R_S + R_L)^2 + (X_S + X_L)^2$ written in canonical
sum-of-squares form $4 R_S R_L + (R_S - R_L)^2 + (X_S + X_L)^2$. -/
def powerTransferDenomScaled (zS zL : Impedance) : Int :=
  4 * zS.rOhm * zL.rOhm +
  (zS.rOhm - zL.rOhm) * (zS.rOhm - zL.rOhm) +
  (zS.xOhm + zL.xOhm) * (zS.xOhm + zL.xOhm)

/-- Theorem (`conjugate_match_maximizes_power` — Maximum Power Transfer Theorem):
For ANY generator impedance $Z_S = R_S + j X_S$ and ANY load impedance $Z_L = R_L + j X_L$:
1. The delivered power numerator never exceeds the available power denominator
   (`powerTransferNumScaled zS zL ≤ powerTransferDenomScaled zS zL`), and
2. Under exact complex conjugate matching (`zL.rOhm = zS.rOhm` and `zL.xOhm = -zS.xOhm`, i.e. $Z_L = Z_S^*$),
   the mismatch squares vanish and $100\%$ of available power is transferred to the load! -/
theorem conjugate_match_maximizes_power (zS zL : Impedance) :
    powerTransferNumScaled zS zL ≤ powerTransferDenomScaled zS zL ∧
    (zL.rOhm = zS.rOhm → zL.xOhm = -zS.xOhm →
      powerTransferDenomScaled zS zL = powerTransferNumScaled zS zL) := by
  dsimp only [powerTransferNumScaled, powerTransferDenomScaled]
  have hR := int_sq_nonneg (zS.rOhm - zL.rOhm)
  have hX := int_sq_nonneg (zS.xOhm + zL.xOhm)
  refine ⟨by omega, ?_⟩
  intro hEqR hEqX
  have hSubR : zS.rOhm - zL.rOhm = 0 := by omega
  have hAddX : zS.xOhm + zL.xOhm = 0 := by omega
  rw [hSubR, hAddX, Int.mul_zero, Int.add_zero, Int.add_zero]

/-- Theorem (`vswr_mismatch_300ohm_on_50ohm_refused`):
A matched $50\,\Omega$ dummy load/antenna passes both `checkVswrUnder3To2` ($\le 1.5:1$) and
`checkVswrUnder2To1` ($\le 2.0:1$), whereas connecting an unmatched $300\,\Omega$ folded-dipole
twin-lead directly to a $50\,\Omega$ transmitter ($\text{VSWR} = 6.0 : 1$) is refused! -/
theorem vswr_mismatch_300ohm_on_50ohm_refused :
    checkVswrUnder3To2 50 ⟨50, 0⟩ = true ∧
    checkVswrUnder2To1 50 ⟨300, 0⟩ = false ∧
    checkVswrUnder3To2 50 ⟨300, 0⟩ = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## 2. Amateur Radio Bands (`HamBand`) & L-Network Impedance Matching Tuner -/

/-- ITU Region 2 / FCC Part 97 amateur radio frequency bands. -/
inductive HamBand where
  | band160m -- 1.800 .. 2.000 MHz (MF Top Band)
  | band80m  -- 3.500 .. 4.000 MHz (HF 80m)
  | band40m  -- 7.000 .. 7.300 MHz (HF 40m, 7074 kHz FT8)
  | band20m  -- 14.000 .. 14.350 MHz (HF 20m, 14074 kHz FT8)
  | band2m   -- 144.000 .. 148.000 MHz (VHF 2m)
  | band70cm -- 420.000 .. 450.000 MHz (UHF 70cm)
  deriving DecidableEq, Repr

/-- Lower and upper band-edge frequencies `(fMinKhz, fMaxKhz)` in kilohertz ($\text{kHz}$). -/
def hamBandLimitsKhz : HamBand → Nat × Nat
  | .band160m => (1800, 2000)
  | .band80m  => (3500, 4000)
  | .band40m  => (7000, 7300)
  | .band20m  => (14000, 14350)
  | .band2m   => (144000, 148000)
  | .band70cm => (420000, 450000)

/-- Verify that a carrier frequency `freqKhz` ($\text{kHz}$) lies strictly within the allocated amateur band `band`. -/
def checkHamBandFreqKhz (band : HamBand) (freqKhz : Nat) : Bool :=
  let (fMin, fMax) := hamBandLimitsKhz band
  decide (fMin ≤ freqKhz) && decide (freqKhz ≤ fMax)

/-- Theorem (`ft8_40m_and_20m_in_ham_bands`):
Standard WSJT-X FT8 calling frequencies (`7074 kHz` on 40m, `14074 kHz` on 20m) and `144200 kHz`
(2m SSB calling) are accepted by `checkHamBandFreqKhz`, while an out-of-band `6950 kHz` pirate
transmission is refused! -/
theorem ft8_40m_and_20m_in_ham_bands :
    checkHamBandFreqKhz .band40m 7074 = true ∧
    checkHamBandFreqKhz .band20m 14074 = true ∧
    checkHamBandFreqKhz .band2m 144200 = true ∧
    checkHamBandFreqKhz .band40m 6950 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- L-Section reactive impedance-matching network transforming a low antenna resistance `rLowOhm`
up to transceiver line impedance `rHighOhm` ($50\,\Omega$) with circuit quality factor $Q$:
$$R_{\text{high}} = R_{\text{low}} \cdot (1 + Q^2), \qquad X_{\text{series}} = Q \cdot R_{\text{low}}, \qquad X_{\text{shunt}} = \frac{R_{\text{high}}}{Q}.$$ -/
structure LMatchNetwork where
  rLowOhm     : Int
  rHighOhm    : Int
  qFactor     : Int
  xSeriesOhm  : Int
  xShuntOhm   : Int
  deriving DecidableEq, Repr

/-- Verify that an `LMatchNetwork` satisfies the exact series-to-parallel L-network transformation
equations $R_{\text{high}} = R_{\text{low}} (1 + Q^2)$, $X_{\text{series}} = Q R_{\text{low}}$, and
$Q X_{\text{shunt}} = R_{\text{high}}$. -/
def checkLMatchTransform (net : LMatchNetwork) : Bool :=
  decide (0 < net.rLowOhm) &&
  decide (0 < net.qFactor) &&
  decide (net.rHighOhm = net.rLowOhm * (1 + net.qFactor * net.qFactor)) &&
  decide (net.xSeriesOhm = net.qFactor * net.rLowOhm) &&
  decide (net.qFactor * net.xShuntOhm = net.rHighOhm)

/-- Canonical L-network matching a short 40m mobile whip antenna ($R_L = 10\,\Omega$) to $Z_0 = 50\,\Omega$
with quality factor $Q = 2$ ($X_{\text{series}} = 20\,\Omega$, $X_{\text{shunt}} = 25\,\Omega$). -/
def whip10To50LMatch : LMatchNetwork where
  rLowOhm    := 10
  rHighOhm   := 50
  qFactor    := 2
  xSeriesOhm := 20
  xShuntOhm  := 25

/-- Theorem (`lMatch_10ohm_to_50ohm_verified`):
`whip10To50LMatch` satisfies the L-network impedance transformation equations (`checkLMatchTransform = true`). -/
theorem lMatch_10ohm_to_50ohm_verified :
    checkLMatchTransform whip10To50LMatch = true :=
  rfl

/-! ## 3. Tayloe Quadrature ($I/Q$) Switching SDR Detector & Image Sideband Cancellation -/

/-- Residual unwanted image-sideband amplitude at the output of a 4-phase Tayloe quadrature ($I/Q$)
SDR mixer + $90^\circ$ Hilbert combiner:
$$\text{image} \propto (G_I \cos\Delta\omega t - G_Q \cos(\Delta\omega t + \Delta\phi)) \approx (G_I - G_Q) \cdot A_{\text{sig}} + \Delta\phi \cdot A_{\text{sig}}.$$ -/
def evalQuadratureImagePhaseCancel (gainI gainQ phaseErr sigAmp : Int) : Int :=
  (gainI - gainQ) * sigAmp + phaseErr * sigAmp

/-- Desired Single-Sideband (USB/LSB) coherent sum amplitude at the output of the Tayloe $I/Q$ combiner:
$$\text{desired} = (G_I + G_Q) \cdot A_{\text{sig}}.$$ -/
def evalQuadratureDesiredSideband (gainI gainQ sigAmp : Int) : Int :=
  (gainI + gainQ) * sigAmp

/-- Theorem (`tayloe_iq_cancels_image_sideband`):
When the Tayloe quadrature mixer's $I$ and $Q$ baseband channels have matched conversion gain
(`gainI = gainQ`) and zero quadrature phase skew (`phaseErr = 0`), the opposite-sideband image
cancels identically to `0`, while the desired sideband coherently doubles to `2 * gainI * sigAmp`!
Written via `dsimp only` + `rw` + `omega` (zero `simp` aux defs) so `#tooth` can mutate
`evalQuadratureImagePhaseCancel`. -/
theorem tayloe_iq_cancels_image_sideband
    (gainI gainQ phaseErr sigAmp : Int)
    (hGain  : gainI = gainQ)
    (hPhase : phaseErr = 0) :
    evalQuadratureImagePhaseCancel gainI gainQ phaseErr sigAmp = 0 ∧
    evalQuadratureDesiredSideband gainI gainQ sigAmp = 2 * gainI * sigAmp := by
  dsimp only [evalQuadratureImagePhaseCancel, evalQuadratureDesiredSideband]
  rw [← hGain, hPhase, Int.sub_self, Int.zero_mul, Int.add_zero]
  refine ⟨rfl, ?_⟩
  have hTwo : gainI + gainI = 2 * gainI := by omega
  rw [hTwo]

/-! ## 4. Cascaded Friis Noise Figure & FCC Part 97.307(d) Harmonic Suppression -/

/-- Friis two-stage cascaded noise factor $F_{\text{total}} = F_1 + \frac{F_2 - 1000}{G_1}$
in milli-linear units (where $1000 = 1.0 = 0.0\,\text{dB}$ noise factor, `f1Milli` is LNA noise
factor, `f2Milli` is mixer/ADC second-stage noise factor, and `gain1Linear` is LNA linear power gain $G_1$). -/
def evalFriisTwoStageMilliNf (f1Milli f2Milli gain1Linear : Nat) : Nat :=
  f1Milli + (f2Milli - 1000) / gain1Linear

/-- Theorem (`lna_gain_reduces_cascaded_noise_figure`):
1. Adding a $20\,\text{dB}$ ($G_1 = 100$) Low-Noise Amplifier (`f1Milli = 1350`, $1.3\,\text{dB}$ NF)
   in front of a noisy SDR mixer/ADC (`f2Milli = 10000`, $10.0\,\text{dB}$ NF) reduces the cascaded
   receiver noise factor from $10350$ ($G_1 = 1$) to $1440$ ($1.58\,\text{dB}$),
2. For any `f1Milli, gain1Linear` and second-stage noise factors `f2a ≤ f2b`,
   `evalFriisTwoStageMilliNf f1Milli f2a gain1Linear ≤ evalFriisTwoStageMilliNf f1Milli f2b gain1Linear`, and
3. For any `g1 ≤ g2`, the cross-multiplied second-stage noise term satisfies
   `g1 * (f2Milli - 1000) ≤ g2 * (f2Milli - 1000)`. -/
theorem lna_gain_reduces_cascaded_noise_figure
    (f1Milli f2a f2b g1 g2 : Nat)
    (hF2 : f2a ≤ f2b)
    (hGain : g1 ≤ g2) :
    evalFriisTwoStageMilliNf 1350 10000 100 = 1440 ∧
    evalFriisTwoStageMilliNf 1350 10000 1 = 10350 ∧
    evalFriisTwoStageMilliNf f1Milli f2a g1 ≤ evalFriisTwoStageMilliNf f1Milli f2b g1 ∧
    g1 * (f2a - 1000) ≤ g2 * (f2a - 1000) := by
  dsimp only [evalFriisTwoStageMilliNf]
  have hSub : f2a - 1000 ≤ f2b - 1000 := by omega
  have hDiv : (f2a - 1000) / g1 ≤ (f2b - 1000) / g1 := Nat.div_le_div_right hSub
  have hMul : g1 * (f2a - 1000) ≤ g2 * (f2a - 1000) := Nat.mul_le_mul_right (f2a - 1000) hGain
  refine ⟨rfl, rfl, by omega, hMul⟩

/-- Harmonic & spurious emission profile of an HF Amateur Radio Power Amplifier (PA) + Low-Pass Filter (LPF),
with attenuations in tenths of a decibel ($0.1\,\text{dBc}$, so $430 = 43.0\,\text{dBc}$):
Per **FCC Part 97.307(d)**, for transmitters operating below $30\,\text{MHz}$, the mean power of any
spurious emission must be at least $43\,\text{dB}$ below the mean power of the fundamental emission ($\ge 430$ tenths dBc). -/
structure PaHarmonicSpec where
  paName                : String
  band                  : HamBand
  carrierFreqKhz        : Nat
  raw2ndHarmonicTenthDb : Nat
  raw3rdHarmonicTenthDb : Nat
  lpfElementCount       : Nat
  lpf2ndAttenTenthDb    : Nat
  lpf3rdAttenTenthDb    : Nat
  deriving DecidableEq, Repr

/-- Total 2nd-harmonic ($2 f_0$) suppression in $0.1\,\text{dBc}$ at the antenna port. -/
def total2ndHarmonicSuppressionTenthDbc (spec : PaHarmonicSpec) : Nat :=
  spec.raw2ndHarmonicTenthDb + spec.lpf2ndAttenTenthDb

/-- Total 3rd-harmonic ($3 f_0$) suppression in $0.1\,\text{dBc}$ at the antenna port. -/
def total3rdHarmonicSuppressionTenthDbc (spec : PaHarmonicSpec) : Nat :=
  spec.raw3rdHarmonicTenthDb + spec.lpf3rdAttenTenthDb

/-- Check FCC Part 97.307(d) compliance for an HF Power Amplifier + Chebyshev Low-Pass Filter:
1. Carrier frequency lies inside the allocated `HamBand` (`checkHamBandFreqKhz`),
2. Output Low-Pass Filter has at least 5 reactive elements (`5 ≤ lpfElementCount`),
3. Total 2nd harmonic suppression $\ge 43.0\,\text{dBc}$ (`430 ≤ total2ndHarmonicSuppressionTenthDbc`),
4. Total 3rd harmonic suppression $\ge 43.0\,\text{dBc}$ (`430 ≤ total3rdHarmonicSuppressionTenthDbc`). -/
def checkFccPart97Harmonics (spec : PaHarmonicSpec) : Bool :=
  checkHamBandFreqKhz spec.band spec.carrierFreqKhz &&
  decide (5 ≤ spec.lpfElementCount) &&
  decide (430 ≤ total2ndHarmonicSuppressionTenthDbc spec) &&
  decide (430 ≤ total3rdHarmonicSuppressionTenthDbc spec)

/-- Golden 40m (`7074 kHz` FT8) Class-E HF Power Amplifier followed by a 7-element Chebyshev LPF:
achieves $18.0 + 40.6 = 58.6\,\text{dBc} \ge 43.0\,\text{dBc}$ 2nd-harmonic suppression and
$24.0 + 62.0 = 86.0\,\text{dBc}$ 3rd-harmonic suppression! -/
def golden40mClassEPaSpec : PaHarmonicSpec where
  paName                := "pa_40m_class_e_chebyshev7"
  band                  := .band40m
  carrierFreqKhz        := 7074
  raw2ndHarmonicTenthDb := 180
  raw3rdHarmonicTenthDb := 240
  lpfElementCount       := 7
  lpf2ndAttenTenthDb    := 406
  lpf3rdAttenTenthDb    := 620

/-- Unfiltered Class-E PA connected directly to the antenna without the 7-element Chebyshev LPF:
2nd harmonic is only $-18.0\,\text{dBc}$ (violating FCC Part 97.307 by $25\,\text{dB}$!). -/
def unfilteredClassEPaSpec : PaHarmonicSpec :=
  { golden40mClassEPaSpec with
    paName             := "pa_40m_unfiltered_illegal"
    lpfElementCount    := 0
    lpf2ndAttenTenthDb := 0
    lpf3rdAttenTenthDb := 0 }

/-- Theorem (`fcc_part97_chebyshev7_pa_accepted_and_unfiltered_refused`):
`golden40mClassEPaSpec` achieves $586$ ($58.6\,\text{dBc} \ge 43.0\,\text{dBc}$) 2nd-harmonic
suppression and passes `checkFccPart97Harmonics`, whereas `unfilteredClassEPaSpec` is refused! -/
theorem fcc_part97_chebyshev7_pa_accepted_and_unfiltered_refused :
    total2ndHarmonicSuppressionTenthDbc golden40mClassEPaSpec = 586 ∧
    checkFccPart97Harmonics golden40mClassEPaSpec = true ∧
    checkFccPart97Harmonics unfilteredClassEPaSpec = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## 5. Complete 40m FT8 Ham Radio Transceiver Signoff Certificate (`RfTransceiverCert`) -/

/-- Complete verification certificate for an amateur radio SDR transceiver (`rf-transceiver-signoff@1`):
* `rigName`: transceiver design identifier,
* `band`, `carrierFreqKhz`: operating amateur band and dial frequency ($\text{kHz}$),
* `z0Ohm`, `matchedLoad`: transmission line characteristic impedance and L-network matched load,
* `iqGainI`, `iqGainQ`, `iqPhaseErr`, `iqRejectionTenthDb`: Tayloe $I/Q$ quadrature balance & image rejection,
* `rxCascadedMilliNf`: Friis two-stage receiver noise factor ($\le 2000 \approx 3.0\,\text{dB}$),
* `paSpec`: Class-E Power Amplifier + Chebyshev LPF harmonic suppression spec,
* `paThermal`: PA transistor emitter-ballasted electro-thermal stability spec,
* `paSteadyTjMk`: steady-state PA junction temperature in millidegrees C ($\le 125000 = 125.0^\circ\text{C}$). -/
structure RfTransceiverCert where
  rigName            : String
  band               : HamBand
  carrierFreqKhz     : Nat
  z0Ohm              : Int
  matchedLoad        : Impedance
  iqGainI            : Int
  iqGainQ            : Int
  iqPhaseErr         : Int
  iqRejectionTenthDb : Nat
  rxCascadedMilliNf  : Nat
  paSpec             : PaHarmonicSpec
  paThermal          : ElectroThermalBjtSpec
  paSteadyTjMk       : Int
  deriving DecidableEq, Repr

/-- Complete kernel signoff checker for an `RfTransceiverCert`. -/
def checkRfTransceiverSignoff (cert : RfTransceiverCert) : Bool :=
  checkHamBandFreqKhz cert.band cert.carrierFreqKhz &&
  (cert.paSpec.band == cert.band) &&
  (cert.paSpec.carrierFreqKhz == cert.carrierFreqKhz) &&
  checkVswrUnder3To2 cert.z0Ohm cert.matchedLoad &&
  decide (evalQuadratureImagePhaseCancel cert.iqGainI cert.iqGainQ cert.iqPhaseErr 100 = 0) &&
  decide (400 ≤ cert.iqRejectionTenthDb) &&
  decide (cert.rxCascadedMilliNf ≤ 2000) &&
  checkFccPart97Harmonics cert.paSpec &&
  checkThermalLoopStable cert.paThermal &&
  decide (cert.paSteadyTjMk ≤ 125000)

/-- Golden 40m (`7074 kHz` FT8) Tayloe Quadrature SDR + Class-E PA transceiver signoff certificate. -/
def golden40mFt8TransceiverCert : RfTransceiverCert where
  rigName            := "obend_qcx_sdr_40m_ft8"
  band               := .band40m
  carrierFreqKhz     := 7074
  z0Ohm              := 50
  matchedLoad        := ⟨50, 0⟩
  iqGainI            := 1000
  iqGainQ            := 1000
  iqPhaseErr         := 0
  iqRejectionTenthDb := 524
  rxCascadedMilliNf  := 1528
  paSpec             := golden40mClassEPaSpec
  paThermal          := emitterBallastedPowerBjt
  paSteadyTjMk       := 84200

/-- Bad transceiver certificate with bypassed Chebyshev LPF (`unfilteredClassEPaSpec`, $-18\,\text{dBc}$ 2nd harmonic). -/
def unfilteredPaTransceiverCert : RfTransceiverCert :=
  { golden40mFt8TransceiverCert with
    rigName := "obend_qcx_unfiltered_pa"
    paSpec  := unfilteredClassEPaSpec }

/-- Bad transceiver certificate with severe antenna impedance mismatch ($300\,\Omega$ load on $50\,\Omega$ coax, $\text{VSWR} = 6:1$). -/
def highVswrTransceiverCert : RfTransceiverCert :=
  { golden40mFt8TransceiverCert with
    rigName     := "obend_qcx_high_vswr"
    matchedLoad := ⟨300, 0⟩ }

/-- Theorem (`rf_transceiver_signoff_poles`):
`checkRfTransceiverSignoff` accepts `golden40mFt8TransceiverCert` and refuses both
`unfilteredPaTransceiverCert` (FCC Part 97 harmonic violation) and `highVswrTransceiverCert`
($6:1$ VSWR mismatch)! -/
theorem rf_transceiver_signoff_poles :
    checkRfTransceiverSignoff golden40mFt8TransceiverCert = true ∧
    checkRfTransceiverSignoff unfilteredPaTransceiverCert = false ∧
    checkRfTransceiverSignoff highVswrTransceiverCert = false :=
  ⟨rfl, rfl, rfl⟩

end Obend.Hardware.RF
