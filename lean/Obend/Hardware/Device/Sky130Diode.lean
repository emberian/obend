module
/-
# Obend.Hardware.Device.Sky130Diode — the recipe of a p-well/n⁺ diode in the terms of the sky130 process

One device end to end: the recipe below, run through `Device/Wafer.lean`, gives the doping profile
that `Device/DriftDiffusion.lean` solves (by devsim) and checks (by the kernel). The fixtures in
`Obend/Teeth/Hardware/DeviceFixtures.lean` check the devsim certificates for this recipe at two
p-well doses and refuse the certificate of one dose against the device of the other.

**What SkyWater publishes and what is derived.** The sky130 documentation gives the p-well as a
peak of `4·10¹⁷ cm⁻³` at `0.42 µm` with characteristic length `0.13 µm`, the substrate background
`8·10¹⁴ cm⁻³`, the n⁺ junction depth `0.1 µm`, and the n⁺ concentration `10²⁰ cm⁻³` (BSIM `nsd`); see
`Constants.Sky130`. **It does not publish implant energies, doses or thermal budgets.** Each step
below is therefore derived from the public numbers through the process model of `Wafer.lean` and
the literature tables of `Constants.lean`, and the derivation is in its docstring. The recipe is a
literature reconstruction consistent with the public profile, not SkyWater's flow.

1. **p-well implant, B 160 keV, `1.3·10¹³ cm⁻²`.** Plummer's table gives `R_p = 0.428 µm` at
   160 keV, the public peak depth is `0.42 µm`. The dose makes the peak `Q/√(2πσ²)` equal to the
   public `4·10¹⁷` at the post-drive `σ ≈ 0.13 µm`: `4·10¹⁷ · √(2π) · 1.3·10⁻⁵ cm = 1.3·10¹³`.
2. **Well drive, 1000 °C, 30 min.** With `D_B(1000 °C) = 1.0·exp(−3.5/(k·1273 K)) = 1.4·10⁻¹⁴ cm²/s`
   (Plummer Table 7-5), `σ² = ΔR_p² + 2Dt = (0.102 µm)² + 5.0·10⁻¹¹ cm²`, `σ = 0.124 µm`, against the
   public `y.char = 0.13 µm`. (A 1050 °C, 60 min drive would give `0.21 µm`; the public number selects
   the lighter drive.)
3. **Screen oxide, dry O₂, 900 °C, 60 min.** Deal–Grove with the Plummer fits for (100) silicon:
   `B = 1.1·10⁻¹⁴ cm²/s`, `B/A = 2.6·10⁻¹⁰ cm/s`, `A = 0.42 µm`; the linear regime gives
   `x ≈ B t/A = 9.3 nm`, consuming `0.44 · 9.3 = 4.1 nm` of silicon. The step also anneals the
   boron at 900 °C (negligible: `2Dt = 2·10⁻¹³ cm²`).
4. **n⁺ implant, As 50 keV, `10¹⁵ cm⁻²`, through the screen oxide.** `R_p = 36.2 nm`, `ΔR_p = 15.2 nm`;
   behind 9.3 nm of oxide the peak sits at 27 nm with `2.6·10²⁰ cm⁻³` (the `10²⁰` of BSIM `nsd`,
   before the clustering and solubility limits this model does not have). The junction with the
   p-well falls at 97 nm (device A) against the public `0.1 µm`.
5. **Activation anneal, 900 °C, 30 min.** `D_As(900 °C) = 6.6·10⁻¹⁷ cm²/s`; in the intrinsic model
   this moves nothing (`2Dt = 2.4·10⁻¹³ cm²` against `ΔR_p² = 2.3·10⁻¹² cm²`). The real n⁺ layer
   diffuses by concentration-enhanced mechanisms the intrinsic table omits; the junction depth is set
   here by the implant, which is why the recipe lands at 97 nm without them.
6. **Strip the oxide** (contact opening) and **deposit 0.5 µm of metal**: geometry steps; the 1D
   device model places the top contact at the silicon surface.

**Device B** is the same recipe with the p-well dose doubled (`2.6·10¹³`): the junction moves to
95 nm and the forward current at −0.5 V drops from 4.19 to 1.54 mA/cm² (devsim, `apps/sky130-diode/
certs/iv_{a,b}.json`), and a certificate of A is refused against B at the first node whose doping is
not B's (`DeviceFixtures.lean`).

**The device object.** The bottom contact is at a depth of 1.0 µm inside the p-well (a 1D stand-in
for the well tap), the area `10⁻⁶ cm²` (10 µm × 10 µm), the top (n⁺) contact biased, forward bias
negative. Tolerances: residuals `10⁻¹²` of their term scale (measured floor `3·10⁻¹⁴`), mobility
brackets `10⁻⁹`, Deal–Grove residual `10⁻¹²`.
-/
public import Obend.Hardware.Device.DriftDiffusion
import all Obend.Hardware.Device.Wafer
import all Obend.Hardware.Device.Constants
import all Obend.Hardware.Device.Enclosure
import all Obend.Analysis.RealAnalysis
public section

namespace Obend.Hardware.Device
open Obend.Analysis
set_option autoImplicit false

/-- Substrate: p-type, the public background concentration. -/
def sky130Background : CanonicalRat := -Sky130.backgroundCm3

/-- The recipe (temperatures in K, times in s, energies in keV, doses in cm⁻², thicknesses in cm). -/
def sky130DiodeRecipe (pWellDose : CanonicalRat := 1.3e13) (nPlusDose : CanonicalRat := 1.0e15) : List ProcessStep :=
  [ .implant .boron 160 pWellDose
  , .anneal 1273.15 1800
  , .oxidize .dryO2 1173.15 3600
  , .implant .arsenic 50 nPlusDose
  , .anneal 1173.15 1800
  , .strip .oxide
  , .deposit .metal 5.0e-5 ]

/-- The device object for a bias, given the mesh the producer solved on. -/
def sky130DiodeSpec (pWellDose biasV : CanonicalRat) (xCm : List CanonicalRat) : DdSpec where
  si := silicon300K
  ctN := caugheyThomasElectrons1967
  ctP := caugheyThomasHoles1967
  tauN := 1.0e-5
  tauP := 1.0e-5
  background := sky130Background
  recipe := sky130DiodeRecipe pWellDose
  xCm := xCm
  areaCm2 := 1.0e-6
  biasV := biasV
  tolRel := 1.0e-12
  mobDelta := 1.0e-9
  dealGroveTol := 1.0e-12

/-- Every physical quantity supplied to the reconstructed process has its required sign. -/
def sky130ProcessStepValid : ProcessStep → Prop
  | .implant _ energy dose => 0 < energy ∧ 0 < dose
  | .anneal temp time | .oxidize _ temp time => 0 < temp ∧ 0 ≤ time
  | .deposit _ thickness | .etch _ thickness | .etchSilicon thickness => 0 ≤ thickness
  | .strip _ => True

theorem sky130DiodeRecipe_wellFormed :
    (∀ step ∈ sky130DiodeRecipe 1.3e13, sky130ProcessStepValid step) ∧
    (∀ step ∈ sky130DiodeRecipe 2.6e13, sky130ProcessStepValid step) := by
  simp [sky130DiodeRecipe, sky130ProcessStepValid] <;> decide +kernel

/-- The first process step really implants different total boron doses in the wafer model. -/
theorem sky130Diode_implant_doses_distinct :
    ∃ a b : WaferState,
      (WaferState.bare sky130Background).implant .boron 160 1.3e13 = some a ∧
      (WaferState.bare sky130Background).implant .boron 160 2.6e13 = some b ∧
      a.dose .boron ≠ b.dose .boron := by
  let a := ((WaferState.bare sky130Background).implant .boron 160 1.3e13).getD
    (WaferState.bare sky130Background)
  let b := ((WaferState.bare sky130Background).implant .boron 160 2.6e13).getD
    (WaferState.bare sky130Background)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide +kernel

/-- Executing the first step of the actual two recipes preserves their distinct boron doses. -/
theorem sky130Diode_recipe_implant_inhabited :
    ∃ a b : WaferState,
      runRecipe silicon300K.kBEv 1.0e-12 (WaferState.bare sky130Background)
        ((sky130DiodeRecipe 1.3e13).take 1) [] = some a ∧
      runRecipe silicon300K.kBEv 1.0e-12 (WaferState.bare sky130Background)
        ((sky130DiodeRecipe 2.6e13).take 1) [] = some b ∧
      a.dose .boron ≠ b.dose .boron := by
  obtain ⟨a, b, ha, hb, hne⟩ := sky130Diode_implant_doses_distinct
  refine ⟨a, b, ?_, ?_, hne⟩
  · simp [sky130DiodeRecipe, runRecipe, ha]
  · simp [sky130DiodeRecipe, runRecipe, hb]

/-- Both validated process variants exist, rather than a conditional theorem with empty premises. -/
theorem sky130DiodeRecipe_inhabited : ∃ recipe : List ProcessStep,
    recipe ≠ [] ∧ ∀ step ∈ recipe, sky130ProcessStepValid step :=
  ⟨sky130DiodeRecipe 1.3e13, by decide +kernel, sky130DiodeRecipe_wellFormed.1⟩

/-- Thermal certificates for every anneal and oxidation of the complete recipe.
These rational enclosures are checked by `runRecipe`, including the oxide thickness. -/
def sky130DiodeRecipeCert : List StepCert := [.none, .anneal ⟨(139704938757218601236302167221 / 10000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (127285124165727245985789941611 / 10000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (73600496760766682802736643049 / 50000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (200374792411516841735175946103 / 100000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat)⟩, .oxidize ⟨(5575484527671213387676064621 / 500000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (131817414959506352512546157943 / 500000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (116086813682635911112065876419 / 125000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), ⟨(460459479144644233432335136009 / 500000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (36477130156731821541168838789 / 50000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (132620830368882962238209899491 / 2000000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (491587617609310379103390940267 / 5000000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat)⟩⟩, .none, .anneal ⟨(460459479144644233432335136009 / 500000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (36477130156731821541168838789 / 50000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (132620830368882962238209899491 / 2000000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat), (491587617609310379103390940267 / 5000000000000000000000000000000000000000000000 : Obend.Analysis.CanonicalRat)⟩, .none, .none]

/-- The complete seven-step process produces both acceptor and donor implants with
positive variance and dose, and the final metal contact. -/
theorem sky130Diode_full_recipe_inhabited :
    ∃ prof : WaferState,
      runRecipe silicon300K.kBEv 1.0e-12 (WaferState.bare sky130Background)
        (sky130DiodeRecipe 1.3e13) sky130DiodeRecipeCert = some prof ∧
      0 < prof.dose .boron ∧ 0 < prof.dose .arsenic ∧
      (∀ g ∈ prof.dopants, 0 < g.doseCm2 ∧ 0 < g.varCm2) ∧
      prof.films = [⟨.metal, 5.0e-5⟩] := by
  let result := runRecipe silicon300K.kBEv 1.0e-12 (WaferState.bare sky130Background)
    (sky130DiodeRecipe 1.3e13) sky130DiodeRecipeCert
  have hr : result.isSome = true := by decide +kernel
  refine ⟨result.getD (WaferState.bare sky130Background), ?_, ?_⟩
  · change result = _
    cases h : result <;> simp_all
  · decide +kernel

end Obend.Hardware.Device
end
