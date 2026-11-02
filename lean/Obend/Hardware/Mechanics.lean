module
/-
# Obend.Hardware.Mechanics — High-Speed Electric Machine Rotordynamics, Hot Air-Gap Clearance Stackups & Von Neumann Reflexive Manufacturing Closure

Formalizes **high-speed electric machine mechanical engineering, thermal-centrifugal rotor-stator
air-gap clearance stackups, and the Von Neumann Reflexive Manufacturing Fixed-Point** (self-reproducing
robotic motor/inverter/semiconductor factory closure) in the Lean 4 kernel:

1. **High-Speed Rotor Centrifugal Hoop Stress & Retention Sleeve Preload (`RotorStressSpec`, `evalCentrifugalHoopStressScaled`)**:
   - Models centrifugal hoop stress scaling $\sigma_\theta \propto \rho \cdot \omega^2 \cdot r^2$ in a
     high-speed permanent-magnet rotor and carbon-fiber / Inconel retention sleeve,
   - Proves **`centrifugal_hoop_stress_nonneg`** ($\rho \ge 0 \implies 0 \le \rho \omega^2 r^2$ for all
     $\omega, r \in \mathbb{Z}$) and **`centrifugal_hoop_stress_mono_speed`** ($0 \le \omega_1 \le \omega_2 \implies
     \sigma_\theta(\omega_1) \le \sigma_\theta(\omega_2)$).
2. **Hot Rotor-Stator Air-Gap Clearance Stackup (`evalHotAirGapUm`, `hot_air_gap_no_rub_sound`)**:
   - Models the radial air-gap budget of a liquid-cooled traction/industrial motor during high-power
     dynamometer operation as the cold assembly clearance minus differential rotor thermal growth,
     centrifugal radial expansion, and shaft/bearing TIR runout:
     $$g_{\text{hot}} = g_{\text{cold}} - (\Delta r_{\text{thermal}} + \Delta r_{\text{centrifugal}} + \Delta r_{\text{runout}}),$$
   - Proves **`hot_air_gap_no_rub_sound`**: whenever the hot air gap meets `minSafeAirGapUm > 0` under
     non-negative expansion components, the operating air gap is strictly positive (`0 < g_hot`,
     guaranteeing zero rotor-stator mechanical rub!) and bounded above by `coldAirGapUm`.
3. **The Von Neumann Reflexive Manufacturing Closure (`PartKind`, `FactoryCell`, `checkReflexiveSelfClosure`)**:
   - Models an autonomous 5-cell robotic fabrication facility manufacturing SiC wafers, stamped
     silicon-steel stator laminations, liquid-cooled housings, hairpin copper coils, sintered NdFeB
     magnets, precision bearings, `MS350`-class power inverter boards, high-torque electric motors,
     robotic assembly actuators, and lithography/stamping cells,
   - Proves **`von_neumann_reflexive_closure_sound`**: if `checkReflexiveSelfClosure cells = true`, then
     every required part in the Bill-of-Materials of every machine cell in the factory is producible
     by the factory itself (`∀ c ∈ cells, ∀ p ∈ c.requiredParts, isPartproducible cells p = true`)
     with non-negative net power balance (`0 ≤ evalNetFactoryPowerKw cells`),
   - Certifies the 5-cell autonomous factory `goldenVonNeumannFactory` (`golden_von_neumann_factory_self_closed`)
     and the combined mechanical + reflexive manufacturing signoff (`golden_mechanics_and_von_neumann_verified`).
-/
public import Obend.Hardware.Thermal
@[expose] public section

namespace Obend.Hardware.Mechanics
open Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. High-Speed Rotor Centrifugal Hoop Stress & Retention Sleeve Preload -/

/-- Scaled centrifugal hoop stress $\sigma_\theta \propto \rho \cdot \omega^2 \cdot r^2$ in a spinning
rotor or retention sleeve of mass density `rhoKgM3` ($\text{kg/m}^3$), angular velocity `omegaRadPerSec`
($\text{rad/s}$), and outer radius `radiusMm` ($\text{mm}$). -/
def evalCentrifugalHoopStressScaled (rhoKgM3 omegaRadPerSec radiusMm : Int) : Int :=
  rhoKgM3 * omegaRadPerSec * omegaRadPerSec * radiusMm * radiusMm

/-- Helper factorization identity rewriting left-associated `rho * omega * omega * r * r` into
`(rho * (omega * omega)) * (r * r)`. -/
theorem hoop_stress_factor_form (rho omega r : Int) :
    evalCentrifugalHoopStressScaled rho omega r =
      (rho * (omega * omega)) * (r * r) := by
  dsimp only [evalCentrifugalHoopStressScaled]
  rw [Int.mul_assoc (rho * omega * omega) r r,
      Int.mul_assoc rho omega omega]

/-- Theorem (`centrifugal_hoop_stress_nonneg`):
Universally for any non-negative material density `0 ≤ rho` and any angular velocity `omega : Int`
and radius `r : Int`, the centrifugal hoop stress `evalCentrifugalHoopStressScaled rho omega r`
is non-negative (`0 ≤ evalCentrifugalHoopStressScaled rho omega r`). -/
theorem centrifugal_hoop_stress_nonneg (rho omega r : Int) (hRho : 0 ≤ rho) :
    0 ≤ evalCentrifugalHoopStressScaled rho omega r := by
  rw [hoop_stress_factor_form]
  have hW2 : 0 ≤ omega * omega := int_sq_nonneg omega
  have hR2 : 0 ≤ r * r := int_sq_nonneg r
  have hRhoW2 : 0 ≤ rho * (omega * omega) := int_mul_nonneg rho (omega * omega) hRho hW2
  exact int_mul_nonneg (rho * (omega * omega)) (r * r) hRhoW2 hR2

/-- Theorem (`centrifugal_hoop_stress_mono_speed`):
Universally for any non-negative material density `0 ≤ rho`, non-negative angular speed `0 ≤ omega1`,
and increased rotor speed `omega1 ≤ omega2`, the centrifugal hoop stress increases monotonically:
`evalCentrifugalHoopStressScaled rho omega1 r ≤ evalCentrifugalHoopStressScaled rho omega2 r`. -/
theorem centrifugal_hoop_stress_mono_speed
    (rho omega1 omega2 r : Int)
    (hRho : 0 ≤ rho)
    (hW1  : 0 ≤ omega1)
    (hW   : omega1 ≤ omega2) :
    evalCentrifugalHoopStressScaled rho omega1 r ≤
    evalCentrifugalHoopStressScaled rho omega2 r := by
  rw [hoop_stress_factor_form rho omega1 r, hoop_stress_factor_form rho omega2 r]
  have hStep1 : omega1 * omega1 ≤ omega2 * omega1 :=
    int_mul_le_mul_of_nonneg_right omega1 omega2 omega1 hW hW1
  have hW2Nonneg : 0 ≤ omega2 := by omega
  have hStep2 : omega2 * omega1 ≤ omega2 * omega2 :=
    int_mul_le_mul_of_nonneg_left omega1 omega2 omega2 hW hW2Nonneg
  have hWsq : omega1 * omega1 ≤ omega2 * omega2 := by omega
  have hRhoW : rho * (omega1 * omega1) ≤ rho * (omega2 * omega2) :=
    int_mul_le_mul_of_nonneg_left (omega1 * omega1) (omega2 * omega2) rho hWsq hRho
  have hR2 : 0 ≤ r * r := int_sq_nonneg r
  exact int_mul_le_mul_of_nonneg_right
    (rho * (omega1 * omega1)) (rho * (omega2 * omega2)) (r * r) hRhoW hR2

/-! ## 2. Hot Rotor-Stator Air-Gap Clearance Stackup (Thermal + Centrifugal + Bearing Runout) -/

/-- Operating hot radial air gap $g_{\text{hot}}$ (in micrometers $\mu\text{m}$) between a spinning
rotor and its liquid-cooled stator bore:
$$g_{\text{hot}} = g_{\text{cold}} - (\Delta r_{\text{thermal}} + \Delta r_{\text{centrifugal}} + \Delta r_{\text{runout}}).$$ -/
def evalHotAirGapUm
    (coldAirGapUm thermalGrowthUm centrifugalGrowthUm bearingRunoutUm : Int) : Int :=
  coldAirGapUm - (thermalGrowthUm + centrifugalGrowthUm + bearingRunoutUm)

/-- Theorem (`hot_air_gap_no_rub_sound`):
If the thermal radial expansion `0 ≤ thermalGrowthUm`, centrifugal radial growth `0 ≤ centrifugalGrowthUm`,
and shaft/bearing TIR runout `0 ≤ bearingRunoutUm` are non-negative, and the hot air gap satisfies
`minSafeAirGapUm ≤ evalHotAirGapUm coldAirGapUm thermalGrowthUm centrifugalGrowthUm bearingRunoutUm`
for a positive minimum clearance `0 < minSafeAirGapUm`, then:
1. The hot operating air gap is strictly positive (`0 < evalHotAirGapUm ...`), preventing catastrophic
   high-speed rotor-stator mechanical rub, and
2. The hot operating air gap never exceeds the cold assembly air gap (`evalHotAirGapUm ... ≤ coldAirGapUm`). -/
theorem hot_air_gap_no_rub_sound
    (coldAirGapUm thermalGrowthUm centrifugalGrowthUm bearingRunoutUm minSafeAirGapUm : Int)
    (hTherm : 0 ≤ thermalGrowthUm)
    (hCent  : 0 ≤ centrifugalGrowthUm)
    (hRun   : 0 ≤ bearingRunoutUm)
    (hMin   : 0 < minSafeAirGapUm)
    (hSafe  : minSafeAirGapUm ≤
      evalHotAirGapUm coldAirGapUm thermalGrowthUm centrifugalGrowthUm bearingRunoutUm) :
    0 < evalHotAirGapUm coldAirGapUm thermalGrowthUm centrifugalGrowthUm bearingRunoutUm ∧
    evalHotAirGapUm coldAirGapUm thermalGrowthUm centrifugalGrowthUm bearingRunoutUm ≤ coldAirGapUm := by
  dsimp only [evalHotAirGapUm] at hSafe ⊢
  refine ⟨by omega, by omega⟩

/-! ## 3. The Von Neumann Reflexive Manufacturing Closure (`PartKind`, `FactoryCell`, `checkReflexiveSelfClosure`) -/

/-- Canonical taxonomy of physical sub-assemblies in an autonomous self-reproducing electric-machine,
power-electronics, and semiconductor factory. -/
inductive PartKind where
  | siliconSicWafer
  | stampedSteelLamination
  | liquidCooledStatorJacket
  | woundCopperHairpinCoil
  | sinteredNdFeBMagnet
  | precisionShaftBearing
  | ms350PowerInverterBoard
  | highTorqueElectricMotor
  | roboticAssemblyActuator
  | lithographyAndStampingCell
  deriving DecidableEq, Repr

/-- An automated manufacturing cell in a Von Neumann universal constructor / robotic factory:
* `cellId`: unique cell identifier,
* `name`: human-readable station description,
* `requiredParts`: Bill-of-Materials (`List PartKind`) needed to construct and maintain this cell,
* `producedParts`: parts (`List PartKind`) this cell manufactures or assembles,
* `powerProducedKw`: electrical power generated or recovered by this cell ($\text{kW}$, e.g. solar/dyno),
* `powerConsumedKw`: electrical power consumed by this cell during operation ($\text{kW}$). -/
structure FactoryCell where
  cellId          : Nat
  name            : String
  requiredParts   : List PartKind
  producedParts   : List PartKind
  powerProducedKw : Int
  powerConsumedKw : Int
  deriving DecidableEq, Repr

/-- Union of all `PartKind`s produced across all cells in the factory (`cells`). -/
def allProducedParts (cells : List FactoryCell) : List PartKind :=
  cells.foldr (fun c acc => c.producedParts ++ acc) []

/-- Check whether part `p` can be manufactured internally by at least one cell in `cells`. -/
def isPartproducible (cells : List FactoryCell) (p : PartKind) : Bool :=
  (allProducedParts cells).contains p

abbrev isPartProducible := isPartproducible

/-- Check whether every constituent BOM part required to build/maintain cell `c` is producible
by `allCells`. -/
def checkCellSelfCovered (allCells : List FactoryCell) (c : FactoryCell) : Bool :=
  c.requiredParts.all (isPartproducible allCells)

/-- Net electrical power balance $\sum_i (P_{\text{prod},i} - P_{\text{cons},i})$ (in $\text{kW}$)
across all cells in the factory. -/
def evalNetFactoryPowerKw (cells : List FactoryCell) : Int :=
  cells.foldr (fun c acc => (c.powerProducedKw - c.powerConsumedKw) + acc) 0

/-- **Von Neumann Reflexive Self-Closure Checker (`checkReflexiveSelfClosure`)**:
verifies that a factory `cells` is non-empty, closes its own Bill-of-Materials fixed point
(`∀ c ∈ cells, checkCellSelfCovered cells c`), and is energy self-sustaining (`0 ≤ evalNetFactoryPowerKw cells`). -/
def checkReflexiveSelfClosure (cells : List FactoryCell) : Bool :=
  !cells.isEmpty &&
  cells.all (checkCellSelfCovered cells) &&
  decide (0 ≤ evalNetFactoryPowerKw cells)

/-- Theorem (`von_neumann_reflexive_closure_sound`):
Whenever `checkReflexiveSelfClosure cells = true`, every machine cell `c ∈ cells` has 100% of its
required constituent BOM parts `p ∈ c.requiredParts` producible by the factory itself
(`isPartproducible cells p = true`), and the factory maintains a non-negative net power balance
(`0 ≤ evalNetFactoryPowerKw cells`). -/
theorem von_neumann_reflexive_closure_sound (cells : List FactoryCell)
    (hClosed : checkReflexiveSelfClosure cells = true) :
    (∀ c ∈ cells, ∀ p ∈ c.requiredParts, isPartproducible cells p = true) ∧
    0 ≤ evalNetFactoryPowerKw cells := by
  dsimp only [checkReflexiveSelfClosure] at hClosed
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hClosed
  refine ⟨?_, hClosed.2⟩
  intro c hc p hp
  have hCell : checkCellSelfCovered cells c = true := List.all_eq_true.1 hClosed.1.2 c hc
  dsimp only [checkCellSelfCovered] at hCell
  exact List.all_eq_true.1 hCell p hp

/-- Golden 5-cell Von Neumann self-reproducing electric-motor, `MS350` power-inverter, and SiC
semiconductor factory:
1. `cell0`: SiC wafer lithography & silicon-steel lamination stamping press,
2. `cell1`: 5-axis CNC liquid-cooled stator housing & precision bearing cell,
3. `cell2`: Robotic copper hairpin coil winder & NdFeB magnet sintering furnace,
4. `cell3`: `MS350` Variable-Frequency Drive (VFD) / power-inverter SMT assembly cell,
5. `cell4`: Robotic motor-stator insertion, regenerative dyno test stand & solar power array. -/
def goldenVonNeumannFactory : List FactoryCell :=
  [ { cellId          := 0
      name            := "cell0_sic_litho_and_lamination_press"
      requiredParts   := [.highTorqueElectricMotor, .ms350PowerInverterBoard, .roboticAssemblyActuator, .lithographyAndStampingCell]
      producedParts   := [.siliconSicWafer, .stampedSteelLamination, .lithographyAndStampingCell]
      powerProducedKw := 0
      powerConsumedKw := 85 }
  , { cellId          := 1
      name            := "cell1_cnc_stator_jacket_and_bearing_grinder"
      requiredParts   := [.highTorqueElectricMotor, .ms350PowerInverterBoard, .precisionShaftBearing, .roboticAssemblyActuator]
      producedParts   := [.liquidCooledStatorJacket, .precisionShaftBearing]
      powerProducedKw := 0
      powerConsumedKw := 60 }
  , { cellId          := 2
      name            := "cell2_hairpin_coil_winder_and_magnet_sinter"
      requiredParts   := [.highTorqueElectricMotor, .ms350PowerInverterBoard, .roboticAssemblyActuator]
      producedParts   := [.woundCopperHairpinCoil, .sinteredNdFeBMagnet]
      powerProducedKw := 0
      powerConsumedKw := 70 }
  , { cellId          := 3
      name            := "cell3_ms350_inverter_smt_and_wirebond"
      requiredParts   := [.siliconSicWafer, .roboticAssemblyActuator, .lithographyAndStampingCell]
      producedParts   := [.ms350PowerInverterBoard]
      powerProducedKw := 0
      powerConsumedKw := 40 }
  , { cellId          := 4
      name            := "cell4_robotic_rotor_stator_assembly_and_solar_dyno"
      requiredParts   := [ .stampedSteelLamination, .liquidCooledStatorJacket, .woundCopperHairpinCoil
                         , .sinteredNdFeBMagnet, .precisionShaftBearing, .ms350PowerInverterBoard ]
      producedParts   := [.highTorqueElectricMotor, .roboticAssemblyActuator]
      powerProducedKw := 450
      powerConsumedKw := 55 } ]

/-- Incomplete open-loop factory missing Cell 0 (cannot produce `.siliconSicWafer` or `.stampedSteelLamination`). -/
def incompleteOpenLoopFactory : List FactoryCell :=
  goldenVonNeumannFactory.drop 1

/-- Theorem (`golden_von_neumann_factory_self_closed`):
`goldenVonNeumannFactory` closes the reflexive Von Neumann BOM fixed point with $+140\,\text{kW}$
net surplus power (`checkReflexiveSelfClosure = true`), whereas `incompleteOpenLoopFactory` fails
reflexive closure (`false`)! -/
theorem golden_von_neumann_factory_self_closed :
    checkReflexiveSelfClosure goldenVonNeumannFactory = true ∧
    evalNetFactoryPowerKw goldenVonNeumannFactory = 140 ∧
    checkReflexiveSelfClosure incompleteOpenLoopFactory = false := by
  decide +kernel

/-! ## 4. Combined Mechanical Rotordynamics + Von Neumann Signoff (`RotorStressSpec`, `checkMechanicsSignoff`) -/

/-- Complete mechanical rotordynamics & air-gap clearance specification for a high-torque liquid-cooled
electric motor:
* `rotorName`: machine design identifier,
* `rhoKgM3`: rotor / sleeve effective density ($\text{kg/m}^3$),
* `omegaRadPerSec`: maximum rated mechanical angular velocity ($\text{rad/s}$),
* `radiusMm`: rotor outer radius ($\text{mm}$),
* `maxAllowableStressScaled`: maximum safe retention sleeve hoop stress (in scaled units),
* `coldAirGapUm`: cold assembly radial air-gap clearance ($\mu\text{m}$),
* `thermalGrowthUm`: differential rotor thermal expansion at rated coolant/winding temperature ($\mu\text{m}$),
* `centrifugalGrowthUm`: centrifugal radial growth at `omegaRadPerSec` ($\mu\text{m}$),
* `bearingRunoutUm`: worst-case shaft deflection and bearing TIR runout ($\mu\text{m}$),
* `minSafeAirGapUm`: minimum allowable hot radial air gap ($\mu\text{m}$) to guarantee zero rub. -/
structure RotorStressSpec where
  rotorName                : String
  rhoKgM3                  : Int
  omegaRadPerSec           : Int
  radiusMm                 : Int
  maxAllowableStressScaled : Int
  coldAirGapUm             : Int
  thermalGrowthUm          : Int
  centrifugalGrowthUm      : Int
  bearingRunoutUm          : Int
  minSafeAirGapUm          : Int
  deriving DecidableEq, Repr

/-- Combined mechanical rotordynamics, hot air-gap non-rubbing clearance, and Von Neumann reflexive
manufacturing signoff checker. -/
def checkMechanicsSignoff (spec : RotorStressSpec) (cells : List FactoryCell) : Bool :=
  let hoopStress := evalCentrifugalHoopStressScaled spec.rhoKgM3 spec.omegaRadPerSec spec.radiusMm
  let hotGap := evalHotAirGapUm spec.coldAirGapUm spec.thermalGrowthUm spec.centrifugalGrowthUm spec.bearingRunoutUm
  decide (0 ≤ spec.rhoKgM3) &&
  decide (0 ≤ spec.omegaRadPerSec) &&
  decide (0 < spec.radiusMm) &&
  decide (hoopStress ≤ spec.maxAllowableStressScaled) &&
  decide (0 ≤ spec.thermalGrowthUm) &&
  decide (0 ≤ spec.centrifugalGrowthUm) &&
  decide (0 ≤ spec.bearingRunoutUm) &&
  decide (0 < spec.minSafeAirGapUm) &&
  decide (spec.minSafeAirGapUm ≤ hotGap) &&
  checkReflexiveSelfClosure cells

/-- Theorem (`checkMechanicsSignoff_sound`):
Whenever `checkMechanicsSignoff spec cells = true`:
1. The rotor centrifugal hoop stress is non-negative and within `spec.maxAllowableStressScaled`,
2. The hot operating air gap is strictly positive (`0 < hotGap`, no rotor-stator rub) and bounded above by `coldAirGapUm`,
3. Every cell in `cells` has 100% of its required BOM parts producible by `cells` with non-negative net power! -/
theorem checkMechanicsSignoff_sound
    (spec : RotorStressSpec) (cells : List FactoryCell)
    (hOk : checkMechanicsSignoff spec cells = true) :
    0 ≤ evalCentrifugalHoopStressScaled spec.rhoKgM3 spec.omegaRadPerSec spec.radiusMm ∧
    evalCentrifugalHoopStressScaled spec.rhoKgM3 spec.omegaRadPerSec spec.radiusMm ≤
      spec.maxAllowableStressScaled ∧
    0 < evalHotAirGapUm spec.coldAirGapUm spec.thermalGrowthUm spec.centrifugalGrowthUm spec.bearingRunoutUm ∧
    evalHotAirGapUm spec.coldAirGapUm spec.thermalGrowthUm spec.centrifugalGrowthUm spec.bearingRunoutUm ≤
      spec.coldAirGapUm ∧
    (∀ c ∈ cells, ∀ p ∈ c.requiredParts, isPartproducible cells p = true) ∧
    0 ≤ evalNetFactoryPowerKw cells := by
  dsimp only [checkMechanicsSignoff] at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hRho : 0 ≤ spec.rhoKgM3 := hOk.1.1.1.1.1.1.1.1.1
  have hStressMax := hOk.1.1.1.1.1.1.2
  have hTherm : 0 ≤ spec.thermalGrowthUm := hOk.1.1.1.1.1.2
  have hCent : 0 ≤ spec.centrifugalGrowthUm := hOk.1.1.1.1.2
  have hRun : 0 ≤ spec.bearingRunoutUm := hOk.1.1.1.2
  have hMin : 0 < spec.minSafeAirGapUm := hOk.1.1.2
  have hGapSafe := hOk.1.2
  have hVn := von_neumann_reflexive_closure_sound cells hOk.2
  have hGap := hot_air_gap_no_rub_sound
    spec.coldAirGapUm spec.thermalGrowthUm spec.centrifugalGrowthUm spec.bearingRunoutUm spec.minSafeAirGapUm
    hTherm hCent hRun hMin hGapSafe
  exact ⟨centrifugal_hoop_stress_nonneg spec.rhoKgM3 spec.omegaRadPerSec spec.radiusMm hRho,
    hStressMax, hGap.1, hGap.2, hVn.1, hVn.2⟩

/-- Golden liquid-cooled PM rotor specification (`7800 kg/m^3` electrical steel core, `600 rad/s`,
`120 mm` radius, `1200 um` cold air gap, `220 um` thermal growth, `95 um` centrifugal growth,
`35 um` bearing runout $\implies 850\,\mu\text{m} \ge 500\,\mu\text{m}$ hot air gap). -/
def goldenLiquidCooledRotorSpec : RotorStressSpec where
  rotorName                := "liquid_cooled_ipm_dyno_rotor"
  rhoKgM3                  := 7800
  omegaRadPerSec           := 600
  radiusMm                 := 120
  maxAllowableStressScaled := 60000000000000
  coldAirGapUm             := 1200
  thermalGrowthUm          := 220
  centrifugalGrowthUm      := 95
  bearingRunoutUm          := 35
  minSafeAirGapUm          := 500

/-- Overspeed / thermally rubbing rotor specification (`omegaRadPerSec = 1200` exceeding sleeve limit,
and `thermalGrowthUm = 800` shrinking hot air gap to `270 um < 500 um`). -/
def rubbingOverspeedRotorSpec : RotorStressSpec :=
  { goldenLiquidCooledRotorSpec with
    rotorName       := "rubbing_overspeed_rotor"
    omegaRadPerSec  := 1200
    thermalGrowthUm := 800 }

/-- Theorem (`golden_mechanics_and_von_neumann_verified`):
`checkMechanicsSignoff` accepts `goldenLiquidCooledRotorSpec` with `goldenVonNeumannFactory`
(`hotAirGap = 850 um >= 500 um`), and refuses both `rubbingOverspeedRotorSpec` and
`incompleteOpenLoopFactory`! -/
theorem golden_mechanics_and_von_neumann_verified :
    evalHotAirGapUm
      goldenLiquidCooledRotorSpec.coldAirGapUm
      goldenLiquidCooledRotorSpec.thermalGrowthUm
      goldenLiquidCooledRotorSpec.centrifugalGrowthUm
      goldenLiquidCooledRotorSpec.bearingRunoutUm = 850 ∧
    checkMechanicsSignoff goldenLiquidCooledRotorSpec goldenVonNeumannFactory = true ∧
    checkMechanicsSignoff rubbingOverspeedRotorSpec goldenVonNeumannFactory = false ∧
    checkMechanicsSignoff goldenLiquidCooledRotorSpec incompleteOpenLoopFactory = false := by
  decide +kernel

/-! ## 5. Combined Bending + Torsion Shaft Von Mises Stress & Strain-Energy Positive-Definiteness -/

/-- Evaluates the squared Von Mises equivalent stress $\sigma_{\text{vM}}^2 = \sigma_b^2 + 3 \tau_t^2$
for a drive-train rotor shaft or machine spindle subjected to combined axial/bending normal
stress `sigmaBending` ($\sigma_b$) and torsional shear stress `tauTorsion` ($\tau_t$). -/
def evalCombinedBendingTorsionVonMisesSq (sigmaBending tauTorsion : Int) : Int :=
  sigmaBending * sigmaBending + 3 * (tauTorsion * tauTorsion)

/-- Helper lemma: for any non-zero integer `x ≠ 0`, its square is strictly positive (`0 < x * x`). -/
theorem int_sq_pos_of_ne_zero (x : Int) (hne : x ≠ 0) : 0 < x * x := by
  have hNonneg := int_sq_nonneg x
  have hPos : 0 < x ∨ x < 0 := by omega
  rcases hPos with h | h
  · exact Int.mul_pos h h
  · have hNeg : 0 < (-x) * (-x) := Int.mul_pos (by omega) (by omega)
    have hEq : (-x) * (-x) = x * x := by grind
    omega

/-- **Universal Non-Negativity, Component Dominance & Positive-Definiteness of Combined Bending + Torsion
Von Mises Stress Squared (`combinedBendingTorsionVonMisesSq_nonneg`)**:
For all signed bending stresses `sigmaBending : Int` and torsional shear stresses `tauTorsion : Int`,
the squared Von Mises equivalent stress $\sigma_{\text{vM}}^2 = \sigma_b^2 + 3 \tau_t^2$ is
non-negative, dominates both pure bending stress squared and $3\times$ pure torsional shear stress
squared, and is strictly positive whenever `sigmaBending ≠ 0 ∨ tauTorsion ≠ 0`. -/
theorem combinedBendingTorsionVonMisesSq_nonneg (sigmaBending tauTorsion : Int) :
    0 ≤ evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion ∧
    sigmaBending * sigmaBending ≤ evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion ∧
    3 * (tauTorsion * tauTorsion) ≤ evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion ∧
    (sigmaBending ≠ 0 ∨ tauTorsion ≠ 0 →
      0 < evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion) := by
  unfold evalCombinedBendingTorsionVonMisesSq
  have hB : 0 ≤ sigmaBending * sigmaBending := int_sq_nonneg sigmaBending
  have hT : 0 ≤ tauTorsion * tauTorsion := int_sq_nonneg tauTorsion
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro hNz
  rcases hNz with hBNz | hTNz
  · have hBPos : 0 < sigmaBending * sigmaBending := int_sq_pos_of_ne_zero sigmaBending hBNz
    omega
  · have hTPos : 0 < tauTorsion * tauTorsion := int_sq_pos_of_ne_zero tauTorsion hTNz
    omega

/-- Evaluates the scaled elastic strain energy $U_{\text{strain}} = k_{\text{bend}} M_b^2 + k_{\text{tors}} T_t^2$
of a rotor shaft or kinematic link under bending moment `mBend` and torsional torque `tTorsion`
with flexural compliance/stiffness factor `kBend` and torsional factor `kTors`. -/
def evalCombinedBendingTorsionStrainEnergy
    (kBend kTors mBend tTorsion : Int) : Int :=
  kBend * (mBend * mBend) + kTors * (tTorsion * tTorsion)

/-- **Strain-Energy Positive-Definiteness Under Combined Bending + Torsion
(`combinedBendingTorsionStrainEnergy_pos_def`)**:
For any positive flexural and torsional stiffness coefficients (`0 < kBend`, `0 < kTors`), the
elastic strain energy is non-negative for all `(mBend, tTorsion)` and strictly positive whenever
either the bending moment or torsional torque is non-zero (`mBend ≠ 0 ∨ tTorsion ≠ 0`). -/
theorem combinedBendingTorsionStrainEnergy_pos_def
    (kBend kTors mBend tTorsion : Int)
    (hKBend : 0 < kBend) (hKTors : 0 < kTors) :
    0 ≤ evalCombinedBendingTorsionStrainEnergy kBend kTors mBend tTorsion ∧
    (mBend ≠ 0 ∨ tTorsion ≠ 0 →
      0 < evalCombinedBendingTorsionStrainEnergy kBend kTors mBend tTorsion) := by
  unfold evalCombinedBendingTorsionStrainEnergy
  have hB2 : 0 ≤ mBend * mBend := int_sq_nonneg mBend
  have hT2 : 0 ≤ tTorsion * tTorsion := int_sq_nonneg tTorsion
  have hTermB : 0 ≤ kBend * (mBend * mBend) :=
    int_mul_nonneg kBend (mBend * mBend) (by omega) hB2
  have hTermT : 0 ≤ kTors * (tTorsion * tTorsion) :=
    int_mul_nonneg kTors (tTorsion * tTorsion) (by omega) hT2
  refine ⟨by omega, ?_⟩
  intro hNz
  rcases hNz with hBM | hTT
  · have hBPos : 0 < mBend * mBend := int_sq_pos_of_ne_zero mBend hBM
    have hKBPos : 0 < kBend * (mBend * mBend) := Int.mul_pos hKBend hBPos
    omega
  · have hTPos : 0 < tTorsion * tTorsion := int_sq_pos_of_ne_zero tTorsion hTT
    have hKTPos : 0 < kTors * (tTorsion * tTorsion) := Int.mul_pos hKTors hTPos
    omega

end Obend.Hardware.Mechanics
end
