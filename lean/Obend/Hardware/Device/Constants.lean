module
/-
# Obend.Hardware.Device.Constants — the material and process numbers, each with its source

Every number here is a *parameter*: the theorems and checkers of `Device/` take the structures below as
arguments, and the values in this file are one instantiation (silicon at 300 K, the SkyWater sky130
process where it is public, the literature where it is not). Nothing in `Device/` is proved *about*
these values; what is proved is quantified over the structures.

Units are cm, s, V, A, K, eV throughout `Device/` (devsim's). Literature values quoted in µm and hours
are converted where they are defined, and the conversion is written out.

Sources (all in `~/paperbin/`, fetched 2026-11-04):
* Caughey, D. M., Thomas, R. E., "Carrier mobilities in silicon empirically related to doping and
  field", Proc. IEEE 55 (1967) 2192, as tabulated in Selberherr, *Analysis and Simulation of
  Semiconductor Devices* (Springer 1984), Tab. 4.1-1 (lattice mobility, row `[4.21]`), Tab. 4.1-2
  (electrons, row `[4.21]`) and Tab. 4.1-3 (holes, row `[4.21]`). The paper itself is paywalled
  (IEEE); the numbers are Selberherr's transcription.
* Plummer, Deal, Griffin, *Silicon VLSI Technology* (Prentice Hall 2000): ch. 7 Table 7-5 (intrinsic
  dopant diffusivities `D₀`, `E_A`), ch. 6 Table 6-? (Deal–Grove rate-constant Arrhenius fits), ch. 8
  table "Ranges and standard deviation ΔRp of dopants in randomly oriented silicon" (10–200 keV, µm).
  Read from the publisher's lecture slides of those chapters (`plummer-deal-griffin-silicon-vlsi-ch0{6,7,8}-*.pdf`).
* Deal, B. E., Grove, A. S., "General relationship for the thermal oxidation of silicon", J. Appl.
  Phys. 36 (1965) 3770: Table I (wet O₂) and Table II (dry O₂) measured rate constants; `0.44` for the
  silicon consumed per unit oxide grown (p. 3770).
* Green, M. A., "Intrinsic concentration, effective densities of states, and effective mass in
  silicon", J. Appl. Phys. 67 (1990) 2944: `N_c`, `N_v`, `E_g` at 300 K.
* Sze, S. M., Ng, K. K., *Physics of Semiconductor Devices* (3rd ed., Wiley 2007), Appendix G: `ε_Si`.
* CODATA 2018 / SI 2019: `q`, `k_B`, `ε₀`.
* SkyWater sky130 (`~/src/skywater-pdk`, `~/src/skywater-pdk-libs-sky130_fd_pr`, cloned 2026-11-04):
  `docs/rules/assumptions.rst` Tables 3a, 3b; `cells/nfet_01v8/sky130_fd_pr__nfet_01v8__tt.pm3.spice`
  (BSIM4 `toxe`, `xj`, `ndep`, `nsd`); `cells/diode_pw2nd_05v5/sky130_fd_pr__diode_pw2nd_05v5.model.spice`.
  **Implant energies and doses are not published by SkyWater**; the recipe in `Device/Sky130Diode.lean`
  derives them from the public well profile and junction depth and says so there.
-/
public import Obend.Hardware.Device.Enclosure
public section

namespace Obend.Hardware.Device
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. Silicon -/

/-- The semiconductor's constants at the operating temperature. `nc`, `nv` in cm⁻³, `egEv` in eV,
`eps0` in F/cm, `q` in C, `kB` in J/K. -/
structure SiliconConstants where
  tempK : CanonicalRat
  epsR : CanonicalRat
  eps0 : CanonicalRat
  q : CanonicalRat
  kB : CanonicalRat
  nc : CanonicalRat
  nv : CanonicalRat
  egEv : CanonicalRat
  deriving @[expose] DecidableEq, Repr

namespace SiliconConstants

/-- The thermal voltage `kT/q` in V (numerically also `kT` in eV). -/
@[expose] def vt (c : SiliconConstants) : CanonicalRat := c.kB * c.tempK / c.q

/-- The permittivity `ε_r ε₀` in F/cm. -/
@[expose] def eps (c : SiliconConstants) : CanonicalRat := c.epsR * c.eps0

/-- `n_i` is accepted when `n_i² ∈ N_c N_v · exp(−E_g/kT)`: the intrinsic density is derived from
`N_c`, `N_v`, `E_g`, not typed. -/
@[expose] def niOk (c : SiliconConstants) (ni : CanonicalRat) : Bool :=
  decide (0 < ni) &&
  decide (ni * ni ∈ Interval.scale (c.nc * c.nv) (expEnclosure (-c.egEv / c.vt)))

end SiliconConstants

/-- Silicon at 300 K. `ε_r = 11.9` (Sze–Ng App. G); `N_c = 2.86·10¹⁹`, `N_v = 3.10·10¹⁹`,
`E_g = 1.1242 eV` (Green 1990), which give `n_i ≈ 1.0·10¹⁰ cm⁻³`; `q`, `k_B`, `ε₀` exact SI 2019 /
CODATA 2018 (`ε₀ = 8.8541878128·10⁻¹² F/m = 8.8541878128·10⁻¹⁴ F/cm`). -/
def silicon300K : SiliconConstants where
  tempK := 300
  epsR := 11.9
  eps0 := 8.8541878128e-14
  q := 1.602176634e-19
  kB := 1.380649e-23
  nc := 2.86e19
  nv := 3.10e19
  egEv := 1.1242

/-! ## 2. Caughey–Thomas mobility -/

/-- `µ(N) = µ_min + (µ_max − µ_min)/(1 + (N/N_ref)^α)`, with `α = alphaNum/alphaDen`. `µ` in cm²/(V s),
`N_ref` in cm⁻³. -/
structure CaugheyThomas where
  muMin : CanonicalRat
  muMax : CanonicalRat
  nRef : CanonicalRat
  alphaNum : Nat
  alphaDen : Nat
  deriving @[expose] DecidableEq, Repr

namespace CaugheyThomas

/-- The mobility from the bracketed ratio `r = (N/N_ref)^α`. -/
@[expose] def muOf (ct : CaugheyThomas) (r : CanonicalRat) : CanonicalRat :=
  ct.muMin + (ct.muMax - ct.muMin) / (1 + r)

/-- `r` stands for `(N/N_ref)^α` to within relative `δ` (`powBracket`); `N ≥ 0`, `N_ref > 0`. -/
@[expose] def ratioOk (ct : CaugheyThomas) (nTot r δ : CanonicalRat) : Bool :=
  decide (0 < ct.nRef) && decide (0 ≤ nTot) && powBracket r (nTot / ct.nRef) ct.alphaNum ct.alphaDen δ

/-- More doping, less mobility: `µ_of` is antitone in `r ≥ 0` when `µ_min ≤ µ_max`. -/
theorem muOf_antitone (ct : CaugheyThomas) (h : ct.muMin ≤ ct.muMax) {r r' : CanonicalRat}
    (hr : 0 ≤ r) (hrr : r ≤ r') : ct.muOf r' ≤ ct.muOf r := by
  unfold muOf
  have h1 : (0 : CanonicalRat) < 1 + r := by grind
  have hinv : (1 + r')⁻¹ ≤ (1 + r)⁻¹ := Interval.inv_le_inv_of_le h1 (by grind)
  have hd : 0 ≤ ct.muMax - ct.muMin := by grind
  have := Rat.mul_le_mul_of_nonneg_left hinv hd
  rw [Rat.div_def, Rat.div_def]
  grind

/-- The mobility stays between `µ_min` and `µ_max` for `r ≥ 0`. -/
theorem muOf_bounds (ct : CaugheyThomas) (h : ct.muMin ≤ ct.muMax) {r : CanonicalRat} (hr : 0 ≤ r) :
    ct.muMin ≤ ct.muOf r ∧ ct.muOf r ≤ ct.muMax := by
  unfold muOf
  have h1 : (0 : CanonicalRat) < 1 + r := by grind
  have hinvpos : 0 < (1 + r)⁻¹ := Rat.inv_pos.2 h1
  have hinvle : (1 + r)⁻¹ ≤ 1 := by
    have h2 := Rat.mul_le_mul_of_nonneg_left (show (1 : CanonicalRat) ≤ 1 + r by grind) (Rat.le_of_lt hinvpos)
    rw [Rat.mul_one, Rat.mul_comm, Rat.mul_inv_cancel _ (Rat.ne_of_gt h1)] at h2
    exact h2
  have hd : 0 ≤ ct.muMax - ct.muMin := by grind
  rw [Rat.div_def]
  constructor
  · have := Rat.mul_nonneg hd (Rat.le_of_lt hinvpos)
    grind
  · have := Rat.mul_le_mul_of_nonneg_left hinvle hd
    grind

end CaugheyThomas

/-- Electrons in silicon at 300 K, Caughey–Thomas 1967 (Selberherr Tab. 4.1-1/4.1-2, row `[4.21]`):
`µ_min = 65`, `µ_max = 1330`, `N_ref = 8.5·10¹⁶`, `α = 0.72 = 18/25`. -/
def caugheyThomasElectrons1967 : CaugheyThomas where
  muMin := 65
  muMax := 1330
  nRef := 8.5e16
  alphaNum := 18
  alphaDen := 25

/-- Holes in silicon at 300 K, Caughey–Thomas 1967 (Selberherr Tab. 4.1-1/4.1-3, row `[4.21]`):
`µ_min = 47.7`, `µ_max = 495`, `N_ref = 6.3·10¹⁶`, `α = 0.76 = 19/25`. -/
def caugheyThomasHoles1967 : CaugheyThomas where
  muMin := 47.7
  muMax := 495
  nRef := 6.3e16
  alphaNum := 19
  alphaDen := 25

/-! ## 3. Shockley–Read–Hall -/

/-- SRH lifetimes (s) and the trap-level densities `n₁`, `p₁` (cm⁻³; `n_i` for a mid-gap trap). -/
structure SrhParams where
  tauN : CanonicalRat
  tauP : CanonicalRat
  n1 : CanonicalRat
  p1 : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- `U = (np − n_i²)/(τ_p (n + n₁) + τ_n (p + p₁))`, exact over `ℚ`. -/
@[expose] def SrhParams.rate (s : SrhParams) (ni n p : CanonicalRat) : CanonicalRat :=
  (n * p - ni * ni) / (s.tauP * (n + s.n1) + s.tauN * (p + s.p1))

/-- Mid-gap trap, `τ_n = τ_p = 10 µs` (devsim's default for lightly damaged bulk silicon; a lifetime
is a process-dependent parameter, not a constant, and the recipe may override it). -/
def srhMidgap10us (ni : CanonicalRat) : SrhParams where
  tauN := 1.0e-5
  tauP := 1.0e-5
  n1 := ni
  p1 := ni

/-! ## 4. Arrhenius rates: diffusivities and Deal–Grove constants -/

/-- `D(T) = D₀ exp(−E_A/kT)`. `d0` in the rate's own unit, `eaEv` in eV. -/
structure Arrhenius where
  d0 : CanonicalRat
  eaEv : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- `k_B/q` in eV/K from the constants (`8.617333262·10⁻⁵`). -/
@[expose] def SiliconConstants.kBEv (c : SiliconConstants) : CanonicalRat := c.kB / c.q

/-- A value `d` is accepted as `D(T)` when `d ∈ D₀ · exp(−E_A/(k_B T))`. -/
@[expose] def Arrhenius.ok (a : Arrhenius) (kBEv tempK d : CanonicalRat) : Bool :=
  decide (0 < tempK) && decide (d ∈ Interval.scale a.d0 (expEnclosure (-a.eaEv / (kBEv * tempK))))

/-- Dopant species. -/
inductive Species where
  | boron
  | phosphorus
  | arsenic
  | antimony
  deriving @[expose] DecidableEq, Repr

/-- Boron is the acceptor; the three group-V species are donors. -/
@[expose] def Species.isDonor : Species → Bool
  | .boron => false
  | _ => true

/-- Intrinsic diffusivities in silicon, Plummer–Deal–Griffin Table 7-5 (`D₀` in cm²/s, `E_A` in eV):
B `1.0, 3.5`; P `4.70, 3.68`; As `9.17, 3.99`; Sb `4.58, 3.88`. Intrinsic means `n < n_i(T)`: the
concentration-dependent (charged-defect) terms of Table 7-? are not modelled, which under-estimates the
diffusion of the `10²⁰ cm⁻³` n⁺ layer; stated in `Device/Wafer.lean`. -/
@[expose] def intrinsicDiffusivity : Species → Arrhenius
  | .boron => ⟨1.0, 3.5⟩
  | .phosphorus => ⟨4.70, 3.68⟩
  | .arsenic => ⟨9.17, 3.99⟩
  | .antimony => ⟨4.58, 3.88⟩

/-- Oxidation ambient. -/
inductive OxidationAmbient where
  | dryO2
  | wetO2
  deriving @[expose] DecidableEq, Repr

/-- Deal–Grove rate constants as Arrhenius fits: `B = C₁ exp(−E₁/kT)`, `B/A = C₂ exp(−E₂/kT)`.
Stored in cm²/s and cm/s. -/
structure DealGroveRates where
  parabolic : Arrhenius
  linear : Arrhenius
  deriving @[expose] DecidableEq, Repr

/-- `1 µm²/h = 10⁻⁸ cm² / 3600 s`; `1 µm/h = 10⁻⁴ cm / 3600 s`. -/
@[expose] def um2PerHour : CanonicalRat := 1.0e-8 / 3600
@[expose] def umPerHour : CanonicalRat := 1.0e-4 / 3600

/-- Plummer Table 6-? (the Deal–Grove fits, for (100) silicon: the (111) `C₂` divided by 1.68):
dry O₂ `C₁ = 7.72·10² µm²/h, E₁ = 1.23 eV; C₂ = 6.23·10⁶/1.68 µm/h, E₂ = 2.0 eV`;
wet O₂ (H₂O) `C₁ = 3.86·10² µm²/h, E₁ = 0.78 eV; C₂ = 1.63·10⁸/1.68 µm/h, E₂ = 2.05 eV`. -/
@[expose] def dealGrove100 : OxidationAmbient → DealGroveRates
  | .dryO2 => ⟨⟨772 * um2PerHour, 1.23⟩, ⟨6.23e6 / 1.68 * umPerHour, 2.0⟩⟩
  | .wetO2 => ⟨⟨386 * um2PerHour, 0.78⟩, ⟨1.63e8 / 1.68 * umPerHour, 2.05⟩⟩

/-- Deal–Grove 1965 Table II, dry O₂ at 1000 °C, measured (not fitted): `B = 0.0117 µm²/h`,
`B/A = 0.071 µm/h`, `A = 0.165 µm`, `τ = 0.37 h`; Table I, wet O₂ (95 °C H₂O) at 1000 °C:
`B = 0.287 µm²/h`, `B/A = 1.27 µm/h`, `A = 0.226 µm`. Kept as the measurement the fit is checked
against in tier 2. -/
structure DealGroveMeasured where
  bUm2PerH : CanonicalRat
  bOverAUmPerH : CanonicalRat
  deriving @[expose] DecidableEq, Repr

def dealGrove1965Dry1000C : DealGroveMeasured := ⟨0.0117, 0.071⟩
def dealGrove1965Wet1000C : DealGroveMeasured := ⟨0.287, 1.27⟩

/-- Silicon consumed per unit of oxide grown (Deal–Grove 1965 p. 3770: the oxide's silicon is drawn
from the substrate at the ratio of the molecular densities, `0.44`). -/
@[expose] def siliconPerOxide : CanonicalRat := 0.44

/-! ## 5. Implant range statistics -/

/-- One row of a range table: energy (keV), projected range `R_p` and straggle `ΔR_p` (both nm). -/
structure RangeRow where
  keV : Nat
  rpNm : CanonicalRat
  drpNm : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- Plummer–Deal–Griffin ch. 8, "Ranges and standard deviation ΔRp of dopants in randomly oriented
silicon" (µm, here nm), 10–200 keV, columns P, As, Sb, B. -/
@[expose] def rangeTable : Species → List RangeRow
  | .phosphorus =>
    [⟨10, 19.9, 6.4⟩, ⟨20, 34.2, 12.5⟩, ⟨30, 47.3, 17.9⟩, ⟨40, 59.8, 22.9⟩, ⟨50, 71.7, 27.5⟩,
     ⟨60, 83.3, 31.7⟩, ⟨70, 94.7, 35.6⟩, ⟨80, 105, 39.3⟩, ⟨90, 116, 42.8⟩, ⟨100, 127, 46.1⟩,
     ⟨120, 148, 52.2⟩, ⟨140, 169, 57.9⟩, ⟨160, 189, 63.0⟩, ⟨180, 210, 67.8⟩, ⟨200, 229, 72.3⟩]
  | .arsenic =>
    [⟨10, 8.4, 4.3⟩, ⟨20, 15.6, 7.5⟩, ⟨30, 22.6, 10.2⟩, ⟨40, 29.4, 12.8⟩, ⟨50, 36.2, 15.2⟩,
     ⟨60, 42.9, 17.6⟩, ⟨70, 49.5, 19.8⟩, ⟨80, 56.1, 22.0⟩, ⟨90, 62.6, 24.1⟩, ⟨100, 69.2, 26.1⟩,
     ⟨120, 82.1, 30.1⟩, ⟨140, 95.0, 33.9⟩, ⟨160, 107, 37.5⟩, ⟨180, 120, 41.1⟩, ⟨200, 133, 44.6⟩]
  | .antimony =>
    [⟨10, 12.1, 5.8⟩, ⟨20, 21.9, 10.0⟩, ⟨30, 30.6, 13.3⟩, ⟨40, 38.5, 16.2⟩, ⟨50, 45.9, 18.7⟩,
     ⟨60, 52.8, 20.9⟩, ⟨70, 59.4, 22.9⟩, ⟨80, 65.6, 24.8⟩, ⟨90, 71.6, 26.5⟩, ⟨100, 77.3, 28.0⟩,
     ⟨120, 88.3, 30.9⟩, ⟨140, 98.5, 33.4⟩, ⟨160, 108, 35.7⟩, ⟨180, 117, 37.8⟩, ⟨200, 126, 39.7⟩]
  | .boron =>
    [⟨10, 47.3, 24.9⟩, ⟨20, 82.6, 38.4⟩, ⟨30, 114, 48.3⟩, ⟨40, 143, 56.2⟩, ⟨50, 171, 62.8⟩,
     ⟨60, 198, 68.5⟩, ⟨70, 223, 73.6⟩, ⟨80, 248, 78.0⟩, ⟨90, 272, 82.1⟩, ⟨100, 296, 85.7⟩,
     ⟨120, 341, 92.2⟩, ⟨140, 385, 97.8⟩, ⟨160, 428, 102⟩, ⟨180, 469, 107⟩, ⟨200, 509, 110⟩]

/-- `R_p`, `ΔR_p` (cm) at an energy, by linear interpolation between tabulated rows; `none` outside
the table (10–200 keV). -/
@[expose] def rangeAt (sp : Species) (keV : CanonicalRat) : Option (CanonicalRat × CanonicalRat) :=
  go (rangeTable sp)
where
  nm : CanonicalRat := 1.0e-7
  go : List RangeRow → Option (CanonicalRat × CanonicalRat)
    | r₁ :: r₂ :: rest =>
      if (r₁.keV : CanonicalRat) ≤ keV ∧ keV ≤ (r₂.keV : CanonicalRat) then
        let f := (keV - r₁.keV) / ((r₂.keV : CanonicalRat) - r₁.keV)
        some ((r₁.rpNm + f * (r₂.rpNm - r₁.rpNm)) * nm, (r₁.drpNm + f * (r₂.drpNm - r₁.drpNm)) * nm)
      else go (r₂ :: rest)
    | _ => none

/-- A range table is well formed when energies, ranges and straggles all increase down the rows. -/
@[expose] def rangeTableSorted : List RangeRow → Bool
  | r₁ :: r₂ :: rest =>
    decide (r₁.keV < r₂.keV) && decide (r₁.rpNm < r₂.rpNm) && decide (r₁.drpNm < r₂.drpNm) &&
    rangeTableSorted (r₂ :: rest)
  | _ => true

/-! ## 6. SkyWater sky130, what is public -/

namespace Sky130

/-- `docs/rules/assumptions.rst` Table 3a: p-well peak concentration `4·10¹⁷ cm⁻³` at depth
`0.42 µm`, characteristic length `y.char = 0.13 µm`; background `8·10¹⁴ cm⁻³`. -/
def pWellPeakCm3 : CanonicalRat := 4.0e17
def pWellPeakDepthCm : CanonicalRat := 0.42e-4
def pWellYCharCm : CanonicalRat := 0.13e-4
def backgroundCm3 : CanonicalRat := 8.0e14

/-- Table 3b: p-well vertical dimension `0.75 µm`; n⁺/p⁺ S/D junction depth `0.1 µm` (the BSIM card
says `xj = 1.5·10⁻⁷ m`). -/
def pWellDepthCm : CanonicalRat := 0.75e-4
def sdJunctionDepthDocsCm : CanonicalRat := 0.1e-4
def sdJunctionDepthBsimCm : CanonicalRat := 1.5e-5

/-- `sky130_fd_pr__nfet_01v8__tt.pm3.spice`: `toxe = 4.148 nm`, `ndep = 1.7·10¹⁷`, `nsd = 10²⁰`
(cm⁻³). -/
def toxeCm : CanonicalRat := 4.148e-7
def ndepCm3 : CanonicalRat := 1.7e17
def nsdCm3 : CanonicalRat := 1.0e20

/-- `sky130_fd_pr__diode_pw2nd_05v5.model.spice`: `js = 2.75·10⁻¹⁵ A/µm²` (`2.75·10⁻⁷ A/cm²`),
ideality `n = 1.2928`, `pb = 0.729 V`, `cj = 1.3459·10⁻¹⁵ F/µm²` (`1.3459·10⁻⁷ F/cm²`), `mj = 0.44`.
The compact model of the device the recipe is meant to reproduce; the drift-diffusion result is
compared with it in the report, not fitted to it. -/
def diodeJsAPerCm2 : CanonicalRat := 2.75e-7
def diodeIdeality : CanonicalRat := 1.2928
def diodeBuiltInV : CanonicalRat := 0.729
def diodeCj0FPerCm2 : CanonicalRat := 1.3459e-7

end Sky130

end Obend.Hardware.Device
end
