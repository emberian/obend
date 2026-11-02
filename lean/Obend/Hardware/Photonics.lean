module
/-
# Obend.Hardware.Photonics — Open-Foundry Silicon Photonics (`SiEPIC 220nm SOI`, `IHP SG13G2 EPIC`, `SiN`), Coupled-Mode Theory, MZI Modulators & Microring Resonators

Formalizes **Silicon Photonics (SiPh) and Photonic Integrated Circuits (PICs)** across open-foundry
platforms (`SiEPIC 220nm SOI` at $\lambda = 1550\,\text{nm}$ / $1310\,\text{nm}$, `IHP SG13G2 EPIC`
monolithic BiCMOS+Silicon Photonics, and low-loss $400\,\text{nm}$ $\text{Si}_3\text{N}_4$):

1. **Waveguide Modes, Effective Index $n_{\text{eff}}(\lambda, T)$ & Thermo-Optic Phase Shift**:
   - Models `PhotonicPlatform` (`soi220nm`, `ihpSg13g2Epic`, `sin400nm`), `WaveguideSpec`
     ($500\,\text{nm} \times 220\,\text{nm}$ single-mode $\text{TE}_{00}$ strip waveguide with
     $n_{\text{eff}} \approx 2.400$, group index $n_g \approx 4.200$, and silicon thermo-optic
     coefficient $\frac{dn}{dT} = +1.86 \times 10^{-4}\,\text{K}^{-1} = 186\,\text{ppm/K}$),
   - Proves **`thermoOptic_phase_monotone_temp`**: increasing temperature excursion $\Delta T$ or
     active heater length $L$ monotonically increases the effective index and accumulated optical path length.
2. **Coupled-Mode Theory (CMT) $2 \times 2$ Directional Coupler & Unitary Power Conservation**:
   - Models an evanescent $2 \times 2$ `DirectionalCoupler` with power transmission factor $t^2$ and
     cross-coupling factor $\kappa^2$ obeying lossless unitarity $t^2 + \kappa^2 = 1000^2$,
   - Proves **`directionalCoupler_conserves_optical_power`** ($P_{\text{out},1} + P_{\text{out},2} = (t^2 + \kappa^2)(P_{\text{in},1} + P_{\text{in},2})$)
     and **`coupler_3db_equal_split`** (a 50:50 3-dB coupler with $t^2 = \kappa^2 = 500000$ splits
     any single-input beam into two identical output beams).
3. **Mach-Zehnder Interferometer (MZI) & Thermo-Optic Phase Shifter**:
   - Models a balanced $2 \times 2$ `MachZehnderModulator` with TiN micro-heater phase shifter,
   - Proves **`mzi_constructive_at_zero_phase`** (at $\Delta\phi = 0$, $100\%$ of optical power exits
     the bar port and $0\%$ exits the cross port) and **`mzi_destructive_at_pi_phase`** (at
     $\Delta\phi = \pi$, the bar port experiences complete destructive extinction to $0$).
4. **Microring Resonator (MRR) WDM Filter, Critical Coupling & Free Spectral Range ($\text{FSR}$)**:
   - Models an all-pass / add-drop `MicroringResonator` with bus self-coupling $r \in [0, 1000]$ and
     round-trip field attenuation $a \in [0, 1000]$,
   - Proves **`mrr_thru_numerator_nonneg`** ($(r - a)^2 \ge 0$) and **`mrr_critical_coupling_zero_through`**
     (resonant through-port transmission $(r - a)^2$ vanishes to zero **if and only if** the critical
     coupling condition $r = a$ holds!),
   - Formalizes Free Spectral Range $\text{FSR}_{\text{pm}} = \frac{\lambda_{\text{nm}}^2 \cdot 1000}{n_g \cdot L_{\mu\text{m}}}$
     and photonic layout DRC (`checkPhotonicDrc`, `photonicDrc_sound`, refusing tight SOI bends
     $< 5000\,\text{nm}$ that suffer radiative mode leakage).
-/
public import Obend.Hardware.Thermal
public import Obend.Analysis.Equitable
@[expose] public section

namespace Obend.Hardware.Photonics
open Obend.Hardware.Thermal
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. Photonic Foundry Platforms, Waveguide Dispersion & Thermo-Optic Effect -/

/-- Open-source and MPW photonic integrated circuit (PIC) foundry platforms:
* `soi220nm`: $220\,\text{nm}$ Silicon-on-Insulator (`SiEPIC` / `ANT NanoSOI` / `Cornerstone`),
* `ihpSg13g2Epic`: `IHP SG13G2 EPIC` $130\,\text{nm}$ SiGe BiCMOS + monolithic $220\,\text{nm}$ SOI photonics,
* `sin400nm`: $400\,\text{nm}$ low-loss Silicon Nitride ($\text{Si}_3\text{N}_4$ on $\text{SiO}_2$ cladding). -/
inductive PhotonicPlatform where
  | soi220nm
  | ihpSg13g2Epic
  | sin400nm
  deriving DecidableEq, Repr

/-- Single-mode optical strip/rib waveguide specification:
* `platform`: target photonic foundry process,
* `widthNm`: waveguide core width in nanometers ($500\,\text{nm}$ for C-band $1550\,\text{nm}$ $\text{TE}_{00}$ SOI),
* `heightNm`: silicon or $\text{Si}_3\text{N}_4$ core thickness in nanometers ($220\,\text{nm}$ SOI, $400\,\text{nm}$ SiN),
* `wavelengthNm`: operating telecommunications wavelength (`1550` C-band or `1310` O-band),
* `neffPermille`: baseline effective phase index $n_{\text{eff}}(T_0) \times 1000$ (`2400` for $n_{\text{eff}} = 2.400$),
* `ngPermille`: group index $n_g = n_{\text{eff}} - \lambda \frac{dn_{\text{eff}}}{d\lambda} \times 1000$ (`4200` for $n_g = 4.200$ in SOI),
* `dnDtPpmPerC`: thermo-optic coefficient $\frac{dn_{\text{eff}}}{dT}$ in $\text{ppm/K}$ (`186` for Si $= 1.86 \times 10^{-4}\,\text{K}^{-1}$, `24` for $\text{Si}_3\text{N}_4$),
* `propLossMdBPerCm`: linear waveguide propagation loss in milli-dB per cm (`1500` $= 1.5\,\text{dB/cm}$). -/
structure WaveguideSpec where
  platform         : PhotonicPlatform
  widthNm          : Nat
  heightNm         : Nat
  wavelengthNm     : Nat
  neffPermille     : Int
  ngPermille       : Nat
  dnDtPpmPerC      : Int
  propLossMdBPerCm : Nat
  deriving DecidableEq, Repr

/-- Canonical C-band ($1550\,\text{nm}$) single-mode $\text{TE}_{00}$ strip waveguide on $220\,\text{nm}$ SOI. -/
def soi220StripWaveguide1550 : WaveguideSpec where
  platform         := .soi220nm
  widthNm          := 500
  heightNm         := 220
  wavelengthNm     := 1550
  neffPermille     := 2400
  ngPermille       := 4200
  dnDtPpmPerC      := 186
  propLossMdBPerCm := 1500

/-- Canonical C-band ($1550\,\text{nm}$) low-loss $\text{Si}_3\text{N}_4$ waveguide ($n_{\text{eff}} = 1.720$,
$n_g = 2.050$, $7.5\times$ lower thermo-optic drift $\frac{dn}{dT} = 24\,\text{ppm/K}$). -/
def sin400Waveguide1550 : WaveguideSpec where
  platform         := .sin400nm
  widthNm          := 1000
  heightNm         := 400
  wavelengthNm     := 1550
  neffPermille     := 1720
  ngPermille       := 2050
  dnDtPpmPerC      := 24
  propLossMdBPerCm := 300

/-- Evaluate the temperature-dependent effective index $n_{\text{eff}}(T)$ in parts-per-million ($\text{ppm}$):
$$n_{\text{eff,ppm}}(\Delta T) = 1000 \cdot n_{\text{eff,permille}}(T_0) + \frac{dn_{\text{eff}}}{dT} \cdot \Delta T.$$ -/
def evalNeffPpm (wg : WaveguideSpec) (deltaTC : Int) : Int :=
  1000 * wg.neffPermille + wg.dnDtPpmPerC * deltaTC

/-- Evaluate the thermo-optic optical path-length modulation $\Delta(\text{OPL}) = L_{\mu\text{m}} \cdot \frac{dn_{\text{eff}}}{dT} \cdot \Delta T$
(in $\text{pm}$ of optical path shift, proportional to the accumulated phase shift $\Delta\phi = \frac{2\pi}{\lambda} \Delta(\text{OPL})$). -/
def evalThermoOpticOplShiftPm (wg : WaveguideSpec) (lengthUm deltaTC : Int) : Int :=
  lengthUm * (wg.dnDtPpmPerC * deltaTC)

/-- Theorem (`thermoOptic_phase_monotone_temp`):
For any waveguide with positive thermo-optic coefficient `0 ≤ wg.dnDtPpmPerC` and non-negative
active heater length `0 ≤ lengthUm`, increasing the temperature excursion `dt1 ≤ dt2` monotonically
increases both the effective mode index `evalNeffPpm` and the accumulated thermo-optic phase/path shift
`evalThermoOpticOplShiftPm`. -/
theorem thermoOptic_phase_monotone_temp
    (wg : WaveguideSpec) (lengthUm dt1 dt2 : Int)
    (hDnDt : 0 ≤ wg.dnDtPpmPerC)
    (hLen  : 0 ≤ lengthUm)
    (hTemp : dt1 ≤ dt2) :
    evalNeffPpm wg dt1 ≤ evalNeffPpm wg dt2 ∧
    evalThermoOpticOplShiftPm wg lengthUm dt1 ≤ evalThermoOpticOplShiftPm wg lengthUm dt2 := by
  dsimp only [evalNeffPpm, evalThermoOpticOplShiftPm]
  have hIndex : wg.dnDtPpmPerC * dt1 ≤ wg.dnDtPpmPerC * dt2 :=
    int_mul_le_mul_of_nonneg_left dt1 dt2 wg.dnDtPpmPerC hTemp hDnDt
  have hOpl : lengthUm * (wg.dnDtPpmPerC * dt1) ≤ lengthUm * (wg.dnDtPpmPerC * dt2) :=
    int_mul_le_mul_of_nonneg_left (wg.dnDtPpmPerC * dt1) (wg.dnDtPpmPerC * dt2) lengthUm hIndex hLen
  refine ⟨by omega, hOpl⟩

/-! ## 2. Coupled-Mode Theory (CMT) $2 \times 2$ Directional Coupler & Unitary Power Conservation -/

/-- Evanescent $2 \times 2$ optical directional coupler modeled via Coupled-Mode Theory (CMT):
The unitary transfer matrix of a symmetric lossless coupler is
$$U = \begin{pmatrix} t & j \kappa \\ j \kappa & t \end{pmatrix}, \qquad t^2 + \kappa^2 = 1,$$
where `tSqPpm` ($t^2 \times 10^6$) is the straight-through (bar) power transmission coefficient and
`kappaSqPpm` ($\kappa^2 \times 10^6$) is the evanescent cross-coupling power coefficient. -/
structure DirectionalCoupler where
  couplerName     : String
  gapNm           : Nat
  couplingLenUm   : Nat
  tFieldPermille  : Int
  kFieldPermille  : Int
  tSqPpm          : Int
  kappaSqPpm      : Int
  deriving DecidableEq, Repr

/-- Alias for `DirectionalCoupler`. -/
abbrev DirectionalCouplerSpec := DirectionalCoupler

/-- Scaled cross-coupling power coefficient $\kappa^2 \times 10^6$ (`kappaSqPpm`). -/
def DirectionalCoupler.kappaSqScaled (dc : DirectionalCoupler) : Int :=
  dc.kappaSqPpm

/-- Scaled bar-transmission power coefficient $t^2 \times 10^6$ (`tSqPpm`). -/
def DirectionalCoupler.tSqScaled (dc : DirectionalCoupler) : Int :=
  dc.tSqPpm

/-- Check that a `DirectionalCoupler` satisfies lossless unitary power conservation
$t^2 + \kappa^2 = 10^6\,\text{ppm}$ (`1000000`). -/
def isLosslessCoupler (dc : DirectionalCoupler) : Bool :=
  decide (0 ≤ dc.tSqPpm) &&
  decide (0 ≤ dc.kappaSqPpm) &&
  decide (dc.tSqPpm + dc.kappaSqPpm = 1000000)

/-- Canonical 50:50 ($3\,\text{dB}$) directional coupler ($t^2 = \kappa^2 = 500000\,\text{ppm}$). -/
def coupler3dB : DirectionalCoupler where
  couplerName    := "dc_3dB_1550nm_gap200nm"
  gapNm          := 200
  couplingLenUm  := 14
  tFieldPermille := 707
  kFieldPermille := 707
  tSqPpm         := 500000
  kappaSqPpm     := 500000

/-- Canonical 62.5 : 37.5 ($5 : 3$) Krawtchouk boundary directional coupler
($t^2 = 625000\,\text{ppm}, \kappa^2 = 375000\,\text{ppm} \implies t^2 + \kappa^2 = 1000000\,\text{ppm}$,
realizing exact $3 : 4 : 3$ coupling-squared ratio against `coupler3dB`'s $500000\,\text{ppm}$). -/
def couplerKrawtchouk375 : DirectionalCoupler where
  couplerName    := "dc_625_375_krawtchouk"
  gapNm          := 225
  couplingLenUm  := 11
  tFieldPermille := 791
  kFieldPermille := 612
  tSqPpm         := 625000
  kappaSqPpm     := 375000

/-- Canonical 64:36 ($800 : 600$ Pythagorean field amplitude) lossless directional coupler
($t = 0.800, \kappa = 0.600 \implies t^2 + \kappa^2 = 640000 + 360000 = 1000000$). -/
def couplerPythagorean80_60 : DirectionalCoupler where
  couplerName    := "dc_64_36_pythagorean"
  gapNm          := 220
  couplingLenUm  := 11
  tFieldPermille := 800
  kFieldPermille := 600
  tSqPpm         := 640000
  kappaSqPpm     := 360000

/-- Output optical power at Port 1 (bar/through port) for incoherent/quadrature input powers $(P_1, P_2)$:
$$P_{\text{out},1} = t^2 P_1 + \kappa^2 P_2.$$ -/
def evalCouplerOut1Power (dc : DirectionalCoupler) (pIn1Uw pIn2Uw : Int) : Int :=
  dc.tSqPpm * pIn1Uw + dc.kappaSqPpm * pIn2Uw

/-- Output optical power at Port 2 (cross port) for input powers $(P_1, P_2)$:
$$P_{\text{out},2} = \kappa^2 P_1 + t^2 P_2.$$ -/
def evalCouplerOut2Power (dc : DirectionalCoupler) (pIn1Uw pIn2Uw : Int) : Int :=
  dc.kappaSqPpm * pIn1Uw + dc.tSqPpm * pIn2Uw

/-- Theorem (`directionalCoupler_conserves_optical_power`):
For ANY `DirectionalCoupler` and ANY input optical powers `pIn1Uw, pIn2Uw : Int`:
1. Total output power equals `(dc.tSqPpm + dc.kappaSqPpm) * (pIn1Uw + pIn2Uw)`, and
2. Whenever `dc` is lossless (`dc.tSqPpm + dc.kappaSqPpm = 1000000`), total output optical power
   is strictly conserved (`1000000 * (pIn1Uw + pIn2Uw)`) with zero insertion loss! -/
theorem directionalCoupler_conserves_optical_power
    (dc : DirectionalCoupler) (pIn1Uw pIn2Uw : Int) :
    evalCouplerOut1Power dc pIn1Uw pIn2Uw + evalCouplerOut2Power dc pIn1Uw pIn2Uw =
      (dc.tSqPpm + dc.kappaSqPpm) * (pIn1Uw + pIn2Uw) ∧
    (dc.tSqPpm + dc.kappaSqPpm = 1000000 →
      evalCouplerOut1Power dc pIn1Uw pIn2Uw + evalCouplerOut2Power dc pIn1Uw pIn2Uw =
        1000000 * (pIn1Uw + pIn2Uw)) := by
  dsimp only [evalCouplerOut1Power, evalCouplerOut2Power]
  have hDist : (dc.tSqPpm + dc.kappaSqPpm) * (pIn1Uw + pIn2Uw) =
      (dc.tSqPpm + dc.kappaSqPpm) * pIn1Uw + (dc.tSqPpm + dc.kappaSqPpm) * pIn2Uw :=
    Int.mul_add (dc.tSqPpm + dc.kappaSqPpm) pIn1Uw pIn2Uw
  have h1 : (dc.tSqPpm + dc.kappaSqPpm) * pIn1Uw = dc.tSqPpm * pIn1Uw + dc.kappaSqPpm * pIn1Uw :=
    Int.add_mul dc.tSqPpm dc.kappaSqPpm pIn1Uw
  have h2 : (dc.tSqPpm + dc.kappaSqPpm) * pIn2Uw = dc.tSqPpm * pIn2Uw + dc.kappaSqPpm * pIn2Uw :=
    Int.add_mul dc.tSqPpm dc.kappaSqPpm pIn2Uw
  have hSum :
      (dc.tSqPpm * pIn1Uw + dc.kappaSqPpm * pIn2Uw) + (dc.kappaSqPpm * pIn1Uw + dc.tSqPpm * pIn2Uw) =
      (dc.tSqPpm + dc.kappaSqPpm) * (pIn1Uw + pIn2Uw) := by
    omega
  refine ⟨hSum, ?_⟩
  intro hUnit
  rw [hSum, hUnit]

/-- Theorem (`coupler_3db_equal_split`):
When a single optical beam `(pInUw, 0)` enters Port 1 of the 50:50 3-dB coupler `coupler3dB`,
the bar and cross output ports receive identical optical power `500000 * pInUw`, and their sum
equals `1000000 * pInUw`. -/
theorem coupler_3db_equal_split (pInUw : Int) :
    evalCouplerOut1Power coupler3dB pInUw 0 = evalCouplerOut2Power coupler3dB pInUw 0 ∧
    evalCouplerOut1Power coupler3dB pInUw 0 = 500000 * pInUw ∧
    evalCouplerOut1Power coupler3dB pInUw 0 + evalCouplerOut2Power coupler3dB pInUw 0 = 1000000 * pInUw := by
  dsimp only [evalCouplerOut1Power, evalCouplerOut2Power, coupler3dB]
  refine ⟨by omega, by omega, by omega⟩

/-! ## 3. Mach-Zehnder Interferometer (MZI) & Thermo-Optic Phase Shifter -/

/-- Balanced $2 \times 2$ Mach-Zehnder Interferometer (MZI) modulator specification:
* `mziName`: device instance name,
* `armLengthUm`: active phase-shifter arm length in micrometers ($\mu\text{m}$),
* `pPiMw`: electrical TiN micro-heater power $P_\pi$ (in milliwatts $\text{mW}$, typically $\approx 20\,\text{mW}$)
  required to induce a $\Delta\phi = \pi$ optical phase shift between the upper and lower arms,
* `insertionLossPermille`: passive excess loss factor. -/
structure MachZehnderModulator where
  mziName               : String
  armLengthUm           : Nat
  pPiMw                 : Int
  insertionLossPermille : Int
  deriving DecidableEq, Repr

/-- Normalized MZI bar-port (through-port) output intensity as a function of input optical power
`pInUw` and normalized heater power $P_{\text{heater}} \in [0, P_\pi]$:
$$P_{\text{bar}} = (P_\pi - P_{\text{heater}}) \cdot P_{\text{in}}.$$
At $P_{\text{heater}} = 0$ ($\Delta\phi = 0$), constructive interference routes all power to the bar
port; at $P_{\text{heater}} = P_\pi$ ($\Delta\phi = \pi$), destructive interference completely
extinguishes the bar port! -/
def evalMziBarOutput (mzi : MachZehnderModulator) (pInUw heaterPowerMw : Int) : Int :=
  (mzi.pPiMw - heaterPowerMw) * pInUw

/-- Normalized MZI cross-port output intensity:
$$P_{\text{cross}} = P_{\text{heater}} \cdot P_{\text{in}}.$$ -/
def evalMziCrossOutput (_mzi : MachZehnderModulator) (pInUw heaterPowerMw : Int) : Int :=
  heaterPowerMw * pInUw

/-- Theorem (`mzi_constructive_at_zero_phase`):
At zero heater bias (`heaterPowerMw = 0`, so $\Delta\phi = 0$), the MZI exhibits constructive
interference at the bar port (`evalMziBarOutput mzi pInUw 0 = mzi.pPiMw * pInUw`) and complete
nulling at the cross port (`evalMziCrossOutput mzi pInUw 0 = 0`). -/
theorem mzi_constructive_at_zero_phase
    (mzi : MachZehnderModulator) (pInUw : Int) :
    evalMziBarOutput mzi pInUw 0 = mzi.pPiMw * pInUw ∧
    evalMziCrossOutput mzi pInUw 0 = 0 := by
  dsimp only [evalMziBarOutput, evalMziCrossOutput]
  rw [Int.sub_zero, Int.zero_mul]
  exact ⟨rfl, rfl⟩

/-- Theorem (`mzi_destructive_at_pi_phase`):
When the TiN micro-heater is driven at the half-wave switching power `heaterPowerMw = mzi.pPiMw`
($\Delta\phi = \pi$), the MZI bar port undergoes complete destructive interference
(`evalMziBarOutput mzi pInUw mzi.pPiMw = 0`) and $100\%$ of the optical carrier switches to the
cross port (`evalMziCrossOutput mzi pInUw mzi.pPiMw = mzi.pPiMw * pInUw`)! -/
theorem mzi_destructive_at_pi_phase
    (mzi : MachZehnderModulator) (pInUw : Int) :
    evalMziBarOutput mzi pInUw mzi.pPiMw = 0 ∧
    evalMziCrossOutput mzi pInUw mzi.pPiMw = mzi.pPiMw * pInUw := by
  dsimp only [evalMziBarOutput, evalMziCrossOutput]
  have hZero : mzi.pPiMw - mzi.pPiMw = 0 := by omega
  rw [hZero, Int.zero_mul]
  exact ⟨rfl, rfl⟩

/-- Theorem (`mzi_complementary_ports_conserve_power`):
For any heater drive `heaterPowerMw : Int`, the sum of the MZI bar-port and cross-port outputs
is invariant and equals `mzi.pPiMw * pInUw`. -/
theorem mzi_complementary_ports_conserve_power
    (mzi : MachZehnderModulator) (pInUw heaterPowerMw : Int) :
    evalMziBarOutput mzi pInUw heaterPowerMw + evalMziCrossOutput mzi pInUw heaterPowerMw =
      mzi.pPiMw * pInUw := by
  dsimp only [evalMziBarOutput, evalMziCrossOutput]
  have hSub : (mzi.pPiMw - heaterPowerMw) + heaterPowerMw = mzi.pPiMw := by omega
  have hAdd : ((mzi.pPiMw - heaterPowerMw) + heaterPowerMw) * pInUw =
      (mzi.pPiMw - heaterPowerMw) * pInUw + heaterPowerMw * pInUw :=
    Int.add_mul (mzi.pPiMw - heaterPowerMw) heaterPowerMw pInUw
  rw [hSub] at hAdd
  omega

/-! ## 4. Microring Resonator (MRR) WDM Filter, Critical Coupling & Free Spectral Range ($\text{FSR}$) -/

/-- All-pass / add-drop Microring Resonator (MRR) WDM filter specification:
* `ringName`: resonator identifier,
* `bendRadiusNm`: ring waveguide bend radius $R$ in nanometers ($\ge 5000\,\text{nm}$ on $220\,\text{nm}$ SOI),
* `circumferenceUm`: round-trip optical cavity length $L = 2\pi R$ in micrometers ($\mu\text{m}$),
* `rSelfPermille`: bus-to-ring coupler self-coupling field coefficient $r \in [0, 1000]$,
* `aRoundTripPermille`: single-pass cavity field attenuation factor $a = e^{-\alpha L / 2} \in [0, 1000]$.
At resonance ($\phi = 2\pi m$), the through-port intensity transmission is
$$T_{\text{thru}}(\phi = 2\pi m) = \left(\frac{r - a}{1 - r a}\right)^2.$$ -/
structure MicroringResonator where
  ringName           : String
  bendRadiusNm       : Nat
  circumferenceUm    : Nat
  rSelfPermille      : Int
  aRoundTripPermille : Int
  deriving DecidableEq, Repr

/-- Numerator $(r - a)^2$ of the resonant through-port power transmission of a `MicroringResonator`. -/
def evalMrrResonantThruNum (mrr : MicroringResonator) : Int :=
  (mrr.rSelfPermille - mrr.aRoundTripPermille) * (mrr.rSelfPermille - mrr.aRoundTripPermille)

/-- Denominator $(1000000 - r \cdot a)^2$ of the resonant through-port power transmission. -/
def evalMrrResonantThruDen (mrr : MicroringResonator) : Int :=
  (1000000 - mrr.rSelfPermille * mrr.aRoundTripPermille) *
  (1000000 - mrr.rSelfPermille * mrr.aRoundTripPermille)

/-- Helper lemma: for any integer `d : Int`, if `d * d = 0`, then `d = 0`.
Proved by case analysis on `Int` and `Nat` with zero external algebra tactics. -/
theorem int_sq_eq_zero (d : Int) (h : d * d = 0) : d = 0 := by
  cases d with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ k => cases h
  | negSucc n =>
    cases h

/-- Theorem (`mrr_thru_numerator_nonneg`):
For any microring resonator parameters `r, a : Int`, the resonant through-port transmission
numerator `(r - a)^2` is always non-negative (`0 ≤ evalMrrResonantThruNum mrr`). -/
theorem mrr_thru_numerator_nonneg (mrr : MicroringResonator) :
    0 ≤ evalMrrResonantThruNum mrr := by
  dsimp only [evalMrrResonantThruNum]
  exact int_sq_nonneg (mrr.rSelfPermille - mrr.aRoundTripPermille)

/-- Theorem (`mrr_critical_coupling_zero_through`):
**Critical Coupling Theorem for Optical Microring Resonators**:
At resonance ($\phi = 2\pi m$), the through-port optical power numerator `evalMrrResonantThruNum mrr`
vanishes to `0` (infinite extinction ratio, 100% power transfer into the resonant cavity)
**if and only if** the bus self-coupling coefficient $r$ equals the round-trip cavity field
transmission factor $a$ (`mrr.rSelfPermille = mrr.aRoundTripPermille`)! -/
theorem mrr_critical_coupling_zero_through (mrr : MicroringResonator) :
    evalMrrResonantThruNum mrr = 0 ↔ mrr.rSelfPermille = mrr.aRoundTripPermille := by
  dsimp only [evalMrrResonantThruNum]
  constructor
  · intro hZero
    have hDiffZero := int_sq_eq_zero (mrr.rSelfPermille - mrr.aRoundTripPermille) hZero
    omega
  · intro hEq
    have hSub : mrr.rSelfPermille - mrr.aRoundTripPermille = 0 := by omega
    rw [hSub]
    rfl

/-- Free Spectral Range ($\text{FSR}$, in picometers $\text{pm}$) of an optical microring or MZI delay
interferometer with wavelength $\lambda_{\text{nm}}$, group index $n_g \times 1000$, and cavity
round-trip length $L_{\mu\text{m}}$:
$$\text{FSR}_{\text{pm}} = \frac{\lambda_{\text{nm}}^2 \cdot 1000000}{n_{g,\text{permille}} \cdot L_{\mu\text{m}}}.$$ -/
def evalFsrPm (wavelengthNm ngPermille cavityLengthUm : Nat) : Nat :=
  (wavelengthNm * wavelengthNm * 1000000) / (ngPermille * cavityLengthUm)

/-- Minimum allowable waveguide bend radius (in nanometers) to prevent radiative whisper-gallery
mode leakage on each `PhotonicPlatform`:
* `soi220nm` / `ihpSg13g2Epic`: high index contrast ($\Delta n \approx 2.0$) permits $5000\,\text{nm}$ ($5\,\mu\text{m}$) bends,
* `sin400nm`: moderate index contrast ($\Delta n \approx 0.55$) requires $\ge 25000\,\text{nm}$ ($25\,\mu\text{m}$) bends. -/
def minPhotonicBendRadiusNm : PhotonicPlatform → Nat
  | .soi220nm      => 5000
  | .ihpSg13g2Epic => 5000
  | .sin400nm      => 25000

/-- Complete Silicon Photonics layout & WDM filter Design Rule Check (`checkPhotonicDrc`):
1. Waveguide width lies in the single-mode $\text{TE}_{00}$ window $[400\,\text{nm}, 1200\,\text{nm}]$,
2. Microring bend radius meets the platform minimum radiative bend limit (`minPhotonicBendRadiusNm`),
3. Directional coupler gap $\ge 150\,\text{nm}$ (DUV lithography trench resolution limit) and lossless unitarity holds,
4. Critically coupled WDM microring achieves zero resonant through-port transmission (`r = a`),
5. Free Spectral Range meets the WDM channel grid target (`minFsrPm ≤ evalFsrPm`). -/
def checkPhotonicDrc
    (wg : WaveguideSpec)
    (dc : DirectionalCoupler)
    (mrr : MicroringResonator)
    (minFsrPm : Nat) : Bool :=
  let minBend := minPhotonicBendRadiusNm wg.platform
  let fsrPm := evalFsrPm wg.wavelengthNm wg.ngPermille mrr.circumferenceUm
  decide (400 ≤ wg.widthNm) &&
  decide (wg.widthNm ≤ 1200) &&
  decide (minBend ≤ mrr.bendRadiusNm) &&
  decide (150 ≤ dc.gapNm) &&
  isLosslessCoupler dc &&
  decide (mrr.rSelfPermille = mrr.aRoundTripPermille) &&
  decide (minFsrPm ≤ fsrPm)

/-- Theorem (`photonicDrc_sound`):
If `checkPhotonicDrc wg dc mrr minFsrPm = true`, then:
1. The microring bend radius satisfies `minPhotonicBendRadiusNm wg.platform ≤ mrr.bendRadiusNm`,
2. The directional coupler is unitary (`dc.tSqPpm + dc.kappaSqPpm = 1000000`),
3. The microring is critically coupled with zero resonant through-port transmission (`evalMrrResonantThruNum mrr = 0`), and
4. The Free Spectral Range satisfies `minFsrPm ≤ evalFsrPm wg.wavelengthNm wg.ngPermille mrr.circumferenceUm`. -/
theorem photonicDrc_sound
    (wg : WaveguideSpec) (dc : DirectionalCoupler) (mrr : MicroringResonator) (minFsrPm : Nat)
    (hOk : checkPhotonicDrc wg dc mrr minFsrPm = true) :
    minPhotonicBendRadiusNm wg.platform ≤ mrr.bendRadiusNm ∧
    dc.tSqPpm + dc.kappaSqPpm = 1000000 ∧
    evalMrrResonantThruNum mrr = 0 ∧
    minFsrPm ≤ evalFsrPm wg.wavelengthNm wg.ngPermille mrr.circumferenceUm := by
  unfold checkPhotonicDrc isLosslessCoupler at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hCrit : evalMrrResonantThruNum mrr = 0 :=
    (mrr_critical_coupling_zero_through mrr).mpr hOk.1.2
  exact ⟨hOk.1.1.1.1.2, hOk.1.1.2.2, hCrit, hOk.2⟩

/-- Golden `SiEPIC 220nm SOI` C-band ($1550\,\text{nm}$) WDM microring resonator ($R = 5\,\mu\text{m}$,
$L = 31\,\mu\text{m}$, critically coupled $r = a = 985$, $\text{FSR} \approx 18452\,\text{pm} = 18.45\,\text{nm}$). -/
def goldenSoi220Microring : MicroringResonator where
  ringName           := "mrr_wdm_soi220_r5um"
  bendRadiusNm       := 5000
  circumferenceUm    := 31
  rSelfPermille      := 985
  aRoundTripPermille := 985

/-- Sub-minimum $2\,\mu\text{m}$ ($2000\,\text{nm} < 5000\,\text{nm}$) SOI microring that suffers severe
radiative bending loss and must be refused by `checkPhotonicDrc`. -/
def leakyTightBendMicroring : MicroringResonator where
  ringName           := "mrr_leaky_r2um"
  bendRadiusNm       := 2000
  circumferenceUm    := 12
  rSelfPermille      := 985
  aRoundTripPermille := 985

/-- Theorem (`goldenSoi220Pic_accepted_and_tight_bend_refused`):
The golden `SiEPIC 220nm SOI` photonic circuit passes `checkPhotonicDrc` with $\text{FSR} \ge 15000\,\text{pm}$
($15\,\text{nm}$), while a radiative $2\,\mu\text{m}$ tight-bend ring is rejected (`= false`). -/
theorem goldenSoi220Pic_accepted_and_tight_bend_refused :
    checkPhotonicDrc soi220StripWaveguide1550 coupler3dB goldenSoi220Microring 15000 = true ∧
    checkPhotonicDrc soi220StripWaveguide1550 coupler3dB leakyTightBendMicroring 15000 = false :=
  ⟨rfl, rfl⟩

/-! ## 5. Complex Gaussian-Integer ($\mathbb{Z}[i]$) Optical Field Phasors & $2 \times 2$ Unitary Directional Coupler -/

/-- Exact Gaussian-integer ($\mathbb{Z}[i]$) complex optical electric field phasor $E = E_{\text{re}} + i E_{\text{im}}$:
* `re`: in-phase ($I$) optical field amplitude component,
* `im`: quadrature ($Q$) optical field amplitude component. -/
structure ComplexField where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace ComplexField

/-- Zero optical electric field phasor $0 + 0i$. -/
def zero : ComplexField := ⟨0, 0⟩

/-- Coherent superposition (complex addition) of two optical field phasors. -/
def add (z w : ComplexField) : ComplexField :=
  ⟨z.re + w.re, z.im + w.im⟩

/-- Coherent subtraction of two optical field phasors. -/
def sub (z w : ComplexField) : ComplexField :=
  ⟨z.re - w.re, z.im - w.im⟩

/-- Complex multiplication $(a + ib)(c + id) = (ac - bd) + i(ad + bc)$ of two optical phasors. -/
def mul (z w : ComplexField) : ComplexField :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- Real scalar field attenuation or gain $c \cdot (E_{\text{re}} + i E_{\text{im}})$. -/
def scale (c : Int) (z : ComplexField) : ComplexField :=
  ⟨c * z.re, c * z.im⟩

/-- Quarter-wave ($+\pi/2$ radian, factor of $i$) optical phase rotation $i \cdot (E_{\text{re}} + i E_{\text{im}}) = -E_{\text{im}} + i E_{\text{re}}$. -/
def mulI (z : ComplexField) : ComplexField :=
  ⟨-z.im, z.re⟩

/-- Optical intensity / power $|E|^2 = E_{\text{re}}^2 + E_{\text{im}}^2$ of a complex field phasor. -/
def normSq (z : ComplexField) : Int :=
  z.re * z.re + z.im * z.im

end ComplexField

/-- Theorem (`complexField_normSq_nonneg`):
Optical power $|E|^2 = \text{re}^2 + \text{im}^2$ is universally non-negative for all `z : ComplexField`. -/
theorem complexField_normSq_nonneg (z : ComplexField) :
    0 ≤ z.normSq := by
  dsimp only [ComplexField.normSq]
  have hRe : 0 ≤ z.re * z.re := int_sq_nonneg z.re
  have hIm : 0 ≤ z.im * z.im := int_sq_nonneg z.im
  omega

/-- Helper algebraic identities on `Int` for ring normalization without external algebra tactics. -/
theorem int_one_mul (a : Int) : 1 * a = a := by omega

theorem int_neg_one_mul (a : Int) : (-1) * a = -a := by omega

theorem int_neg_neg (a : Int) : -(-a) = a := by omega

theorem int_add_neg_self (a : Int) : a + (-a) = 0 := by omega

theorem int_neg_add_self (a : Int) : (-a) + a = 0 := by omega

theorem int_neg_mul_left (a b : Int) : (-a) * b = -(a * b) := by
  have hDist : (a + (-a)) * b = a * b + (-a) * b := Int.add_mul a (-a) b
  rw [int_add_neg_self a, Int.zero_mul] at hDist
  omega

theorem int_mul_neg_right (a b : Int) : a * (-b) = -(a * b) := by
  rw [Int.mul_comm a (-b), Int.mul_comm a b]
  exact int_neg_mul_left b a

/-- Four-factor integer multiplication swap $(p q)(r s) = (p r)(q s)$. -/
theorem int_mul_four_swap (p q r s : Int) :
    (p * q) * (r * s) = (p * r) * (q * s) := by
  rw [Int.mul_assoc p q (r * s)]
  rw [← Int.mul_assoc q r s]
  rw [Int.mul_comm q r]
  rw [Int.mul_assoc r q s]
  rw [← Int.mul_assoc p r (q * s)]

/-- **Brahmagupta-Fibonacci Two-Square Identity** (`brahmagupta_cancel`):
$$(t a - k b)^2 + (k a + t b)^2 = (t^2 + k^2)(a^2 + b^2),$$
where the opposite-sign evanescent cross-interference terms $-2 t k a b$ and $+2 t k a b$
cancel identically across all `t, k, a, b : Int`. -/
theorem brahmagupta_cancel (t k a b : Int) :
    (t * a - k * b) * (t * a - k * b) + (k * a + t * b) * (k * a + t * b) =
      (t * t + k * k) * (a * a + b * b) := by
  have hSubSq : (t * a - k * b) * (t * a - k * b) =
      (t * a) * (t * a) - (t * a) * (k * b) - (k * b) * (t * a) + (k * b) * (k * b) := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]
    omega
  have hAddSq : (k * a + t * b) * (k * a + t * b) =
      (k * a) * (k * a) + (k * a) * (t * b) + (t * b) * (k * a) + (t * b) * (t * b) := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have hRhs : (t * t + k * k) * (a * a + b * b) =
      (t * t) * (a * a) + (k * k) * (a * a) + (t * t) * (b * b) + (k * k) * (b * b) := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have hTA : (t * a) * (t * a) = (t * t) * (a * a) := int_mul_four_swap t a t a
  have hKB : (k * b) * (k * b) = (k * k) * (b * b) := int_mul_four_swap k b k b
  have hKA : (k * a) * (k * a) = (k * k) * (a * a) := int_mul_four_swap k a k a
  have hTB : (t * b) * (t * b) = (t * t) * (b * b) := int_mul_four_swap t b t b
  have hCross1 : (t * a) * (k * b) = (k * a) * (t * b) := by
    rw [int_mul_four_swap t a k b, int_mul_four_swap k a t b, Int.mul_comm t k]
  have hCross2 : (k * b) * (t * a) = (t * b) * (k * a) := by
    rw [Int.mul_comm (k * b) (t * a), Int.mul_comm (t * b) (k * a), hCross1]
  omega

/-- Coherent $2 \times 2$ evanescent directional coupler transfer matrix over $\mathbb{Z}[i]$:
$$\begin{pmatrix} E_{\text{out},1} \\ E_{\text{out},2} \end{pmatrix}
  = \begin{pmatrix} t & i \kappa \\ i \kappa & t \end{pmatrix}
    \begin{pmatrix} E_1 \\ E_2 \end{pmatrix}
  = \begin{pmatrix} t E_1 + i \kappa E_2 \\ i \kappa E_1 + t E_2 \end{pmatrix}.$$ -/
def evalDirectionalCoupler2x2
    (t kappa : Int) (e1 e2 : ComplexField) : ComplexField × ComplexField :=
  let out1 : ComplexField := ⟨t * e1.re - kappa * e2.im, t * e1.im + kappa * e2.re⟩
  let out2 : ComplexField := ⟨-kappa * e1.im + t * e2.re, kappa * e1.re + t * e2.im⟩
  (out1, out2)

/-- Theorem (`directional_coupler_2x2_power_conservation`):
For ALL straight-through and cross-coupling field coefficients `t, kappa : Int` and ALL complex
input optical field phasors `e1, e2 : ComplexField` (arbitrary relative phase and amplitude), the
$2 \times 2$ directional coupler transfer matrix $\begin{pmatrix} t & i\kappa \\ i\kappa & t \end{pmatrix}$
strictly conserves total optical power up to the unitary scale factor $t^2 + \kappa^2$:
$$|E_{\text{out},1}|^2 + |E_{\text{out},2}|^2 = (t^2 + \kappa^2)\left(|E_1|^2 + |E_2|^2\right).$$ -/
theorem directional_coupler_2x2_power_conservation
    (t kappa : Int) (e1 e2 : ComplexField) :
    let (out1, out2) := evalDirectionalCoupler2x2 t kappa e1 e2
    out1.normSq + out2.normSq = (t * t + kappa * kappa) * (e1.normSq + e2.normSq) := by
  dsimp only [evalDirectionalCoupler2x2, ComplexField.normSq]
  have hSwapSub : -kappa * e1.im + t * e2.re = t * e2.re - kappa * e1.im := by
    rw [int_neg_mul_left kappa e1.im]
    omega
  have hSwapAdd : t * e1.im + kappa * e2.re = kappa * e2.re + t * e1.im := by omega
  rw [hSwapSub, hSwapAdd]
  have hB1 :
      (t * e1.re - kappa * e2.im) * (t * e1.re - kappa * e2.im) +
        (kappa * e1.re + t * e2.im) * (kappa * e1.re + t * e2.im) =
      (t * t + kappa * kappa) * (e1.re * e1.re + e2.im * e2.im) :=
    brahmagupta_cancel t kappa e1.re e2.im
  have hB2 :
      (t * e2.re - kappa * e1.im) * (t * e2.re - kappa * e1.im) +
        (kappa * e2.re + t * e1.im) * (kappa * e2.re + t * e1.im) =
      (t * t + kappa * kappa) * (e2.re * e2.re + e1.im * e1.im) :=
    brahmagupta_cancel t kappa e2.re e1.im
  have hDist1 :
      (t * t + kappa * kappa) * (e1.re * e1.re + e2.im * e2.im) =
      (t * t + kappa * kappa) * (e1.re * e1.re) + (t * t + kappa * kappa) * (e2.im * e2.im) :=
    Int.mul_add (t * t + kappa * kappa) (e1.re * e1.re) (e2.im * e2.im)
  have hDist2 :
      (t * t + kappa * kappa) * (e2.re * e2.re + e1.im * e1.im) =
      (t * t + kappa * kappa) * (e2.re * e2.re) + (t * t + kappa * kappa) * (e1.im * e1.im) :=
    Int.mul_add (t * t + kappa * kappa) (e2.re * e2.re) (e1.im * e1.im)
  have hDistGoal :
      (t * t + kappa * kappa) * ((e1.re * e1.re + e1.im * e1.im) + (e2.re * e2.re + e2.im * e2.im)) =
      (t * t + kappa * kappa) * (e1.re * e1.re) +
        (t * t + kappa * kappa) * (e1.im * e1.im) +
        (t * t + kappa * kappa) * (e2.re * e2.re) +
        (t * t + kappa * kappa) * (e2.im * e2.im) := by
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    omega
  omega

/-! ## 6. Cascaded $2 \times 2$ Complex MZI Transfer Matrix -/

/-- Upper-arm optical phase shifter transfer matrix $\begin{pmatrix} e^{i\Delta\phi} & 0 \\ 0 & 1 \end{pmatrix}$
represented by a complex phase phasor `phasePhasor : ComplexField` ($1 + 0i$ for $\Delta\phi = 0$,
$-1 + 0i$ for $\Delta\phi = \pi$, $0 + 1i$ for $\Delta\phi = \pi/2$). -/
def evalPhaseShifter2x2
    (phasePhasor : ComplexField) (e1 e2 : ComplexField) : ComplexField × ComplexField :=
  (ComplexField.mul phasePhasor e1, e2)

/-- Complete cascaded $2 \times 2$ Mach-Zehnder Interferometer (MZI) complex field transfer matrix
$$T_{\text{MZI}} = U_{\text{DC}}(t, \kappa) \cdot \Phi(\Delta\phi) \cdot U_{\text{DC}}(t, \kappa)$$
formed by composing the input $2 \times 2$ directional coupler, the upper-arm thermo-optic phase
shifter `phasePhasor`, and the output $2 \times 2$ directional coupler. -/
def evalCascadedMzi2x2
    (t kappa : Int) (phasePhasor : ComplexField) (eIn1 eIn2 : ComplexField) :
    ComplexField × ComplexField :=
  let (m1, m2) := evalDirectionalCoupler2x2 t kappa eIn1 eIn2
  let (p1, p2) := evalPhaseShifter2x2 phasePhasor m1 m2
  evalDirectionalCoupler2x2 t kappa p1 p2

/-- Theorem (`cascaded_mzi_zero_phase_pure_cross`):
For ANY symmetric 50:50 directional coupler (`t = kappa`) and ANY complex input optical field
`eIn : ComplexField` injected into Port 1 (`eIn2 = ⟨0, 0⟩`), when the phase shifter is unshifted
($\Delta\phi = 0$, `phasePhasor = ⟨1, 0⟩`), the two cascaded $i\kappa$ cross-couplings interfere
destructively at the bar port (`out1 = ⟨0, 0⟩`), routing 100% of the optical field to the cross port! -/
theorem cascaded_mzi_zero_phase_pure_cross
    (t : Int) (eIn : ComplexField) :
    (evalCascadedMzi2x2 t t ⟨1, 0⟩ eIn ⟨0, 0⟩).1 = ⟨0, 0⟩ := by
  simp only [evalCascadedMzi2x2, evalDirectionalCoupler2x2, evalPhaseShifter2x2, ComplexField.mul,
    Int.mul_zero, Int.zero_mul, Int.sub_zero, Int.add_zero, Int.sub_self,
    int_one_mul, int_neg_mul_left, int_mul_neg_right, int_add_neg_self]

/-- Theorem (`cascaded_mzi_pi_phase_pure_bar`):
For ANY symmetric 50:50 directional coupler (`t = kappa`) and ANY complex input optical field
`eIn : ComplexField` injected into Port 1 (`eIn2 = ⟨0, 0⟩`), when the upper-arm phase shifter induces
a half-wave shift ($\Delta\phi = \pi$, `phasePhasor = ⟨-1, 0⟩`), destructive interference completely
extinguishes the cross port (`out2 = ⟨0, 0⟩`), routing 100% of the optical field to the bar port! -/
theorem cascaded_mzi_pi_phase_pure_bar
    (t : Int) (eIn : ComplexField) :
    (evalCascadedMzi2x2 t t ⟨-1, 0⟩ eIn ⟨0, 0⟩).2 = ⟨0, 0⟩ := by
  simp only [evalCascadedMzi2x2, evalDirectionalCoupler2x2, evalPhaseShifter2x2, ComplexField.mul,
    Int.mul_zero, Int.zero_mul, Int.sub_zero, Int.add_zero,
    int_one_mul, int_neg_mul_left, int_mul_neg_right,
    int_neg_neg, int_add_neg_self, int_neg_add_self]

/-! ## 7. Thermo-Optic Crosstalk Pre-Distortion & 2-Boson Hong–Ou–Mandel Photonics Exports -/

export Obend.Analysis (
  faddeevAdjugateAndDet
  ThermoOpticPhaseShifter
  compensateThermalCrosstalk
  goldenThermalCrosstalk4x4
  faddeevAdjugate_cancels_crosstalk_4x4
  compensateThermalCrosstalk_exact_4x4
  twoBosonPermanent
  beamSplitter5050
  hong_ou_mandel_bunching_exact
  twoBosonPermanent_bose_symmetry
  twoBosonHamiltonian
  twoBosonPart
  twoBosonQuotient
  twoBoson_equitable_intertwining_poly
)

end Obend.Hardware.Photonics
end
