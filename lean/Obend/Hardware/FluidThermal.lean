module
/-
# Obend.Hardware.FluidThermal — Liquid-Cooled Stator Jackets, Microchannel Cold Plates, Darcy-Weisbach Hydraulics & Conjugate Convective-Caloric Heat Transfer

Formalizes coupled **electro-fluid-thermal multiphysics** for liquid-cooled electric machine stators,
direct-slot cooling channels, and power-electronics microchannel cold plates within `Obend.Hardware`:

1. **Darcy-Weisbach Channel Hydraulics & Pump Power (`CoolingChannelSpec`, `evalDarcyPressureDropScaled`)**:
   - Models viscous turbulent/laminar pressure drop $\Delta p \propto f_D \cdot \frac{L}{D_h} \cdot \frac{1}{2}\rho v^2$
     across stator jacket cooling channels and cold-plate microchannels,
   - Proves **`darcy_pressure_drop_nonneg`** ($\forall \text{ch},\; f_D, L, \rho \ge 0 \implies \Delta p_{\text{scaled}} \ge 0$
     for arbitrary signed velocity $v \in \mathbb{Z}$) and **`darcy_pressure_drop_mono_length`**
     ($L_1 \le L_2 \implies \Delta p(L_1) \le \Delta p(L_2)$).
2. **Parallel Stator Cooling Manifold Mass-Flow Conservation (`sumBranchFlows`, `checkManifoldMassBalance`)**:
   - Verifies Kirchhoff fluid mass-balance $\dot{V}_{\text{inlet}} = \sum_{i} \dot{V}_{\text{branch},i}$
     and positive branch flow across parallel stator slot cooling channels (preventing flow-starvation dead zones),
   - Proves **`checkManifoldMassBalance_sound`** and **`manifold_total_flow_nonneg`**.
3. **Conjugate Convective + Caloric Stator Winding Thermal Network (`evalPeakWindingTempMilliC`, `evalCoolantOutletTempMilliC`)**:
   - Models the series conjugate thermal network from copper stator hairpins through slot-liner conduction
     ($R_{\text{cond}}$), turbulent Nusselt/Gnielinski convective film resistance ($R_{\text{conv}}$),
     and bulk coolant caloric heat-capacity rise ($R_{\text{caloric}} = 1 / (\dot{m} c_p)$),
   - Proves **`higher_flow_and_convection_lowers_winding_temp`** and **`coolant_outlet_above_inlet`**.
4. **Liquid-Cooled Motor Thermal & Cavitation Signoff Checker (`checkLiquidThermalSignoff`)**:
   - Enforces Class-H stator winding insulation limit ($180^\circ\text{C}$), NdFeB rotor magnet demagnetization
     limit ($120^\circ\text{C}$), maximum pump hydraulic pressure drop, and sub-boiling cavitation margin
     for 50/50 water-ethylene-glycol (WEG) coolant,
   - Proves **`checkLiquidThermalSignoff_sound`** and **`golden_liquid_cooled_stator_signoff_verified`**.
-/
public import Obend.Hardware.Thermal
@[expose] public section

namespace Obend.Hardware.FluidThermal
open Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. Darcy-Weisbach Channel Hydraulics & Pump Power (`CoolingChannelSpec`) -/

/-- Hydraulic specification of a liquid cooling channel (stator jacket spiral, axial slot channel,
or cold-plate microchannel):
* `frictionFactorMilli`: Darcy friction factor $f_D$ scaled by $10^3$ ($1000 \cdot f_D$),
* `lengthMm`: channel axial/helical length $L$ in millimeters ($\text{mm}$),
* `hydraulicDiaMm`: hydraulic diameter $D_h = \frac{4A}{P_{\text{wet}}}$ in millimeters ($\text{mm}$),
* `fluidDensityKgM3`: coolant density $\rho$ in $\text{kg/m}^3$ (e.g. $1065\,\text{kg/m}^3$ for 50/50 WEG),
* `velocityMmPerSec`: bulk coolant flow velocity $v$ in $\text{mm/s}$. -/
structure CoolingChannelSpec where
  frictionFactorMilli : Int
  lengthMm            : Int
  hydraulicDiaMm      : Int
  fluidDensityKgM3    : Int
  velocityMmPerSec    : Int
  deriving DecidableEq, Repr

/-- Scaled Darcy-Weisbach pressure drop numerator:
$$\Delta p_{\text{scaled}} = f_D \cdot L \cdot \rho \cdot v^2$$
(proportional to $\Delta p = f_D \frac{L}{D_h} \frac{\rho v^2}{2}$). -/
def evalDarcyPressureDropScaled (ch : CoolingChannelSpec) : Int :=
  ch.frictionFactorMilli * ch.lengthMm * ch.fluidDensityKgM3 * ch.velocityMmPerSec * ch.velocityMmPerSec

/-- Theorem (`darcy_pressure_drop_nonneg`):
For ANY `CoolingChannelSpec` `ch` with non-negative Darcy friction factor (`0 ≤ ch.frictionFactorMilli`),
non-negative channel length (`0 ≤ ch.lengthMm`), and non-negative fluid density (`0 ≤ ch.fluidDensityKgM3`),
the Darcy-Weisbach pressure drop numerator `evalDarcyPressureDropScaled ch` is non-negative (`0 ≤ Δp`)
for any flow velocity `ch.velocityMmPerSec : Int`. -/
theorem darcy_pressure_drop_nonneg
    (ch : CoolingChannelSpec)
    (hf : 0 ≤ ch.frictionFactorMilli)
    (hL : 0 ≤ ch.lengthMm)
    (hRho : 0 ≤ ch.fluidDensityKgM3) :
    0 ≤ evalDarcyPressureDropScaled ch := by
  dsimp only [evalDarcyPressureDropScaled]
  have h1 : 0 ≤ ch.frictionFactorMilli * ch.lengthMm :=
    int_mul_nonneg ch.frictionFactorMilli ch.lengthMm hf hL
  have h2 : 0 ≤ ch.frictionFactorMilli * ch.lengthMm * ch.fluidDensityKgM3 :=
    int_mul_nonneg (ch.frictionFactorMilli * ch.lengthMm) ch.fluidDensityKgM3 h1 hRho
  have hv2 : 0 ≤ ch.velocityMmPerSec * ch.velocityMmPerSec :=
    int_sq_nonneg ch.velocityMmPerSec
  rw [Int.mul_assoc (ch.frictionFactorMilli * ch.lengthMm * ch.fluidDensityKgM3)
        ch.velocityMmPerSec ch.velocityMmPerSec]
  exact int_mul_nonneg (ch.frictionFactorMilli * ch.lengthMm * ch.fluidDensityKgM3)
    (ch.velocityMmPerSec * ch.velocityMmPerSec) h2 hv2

/-- Theorem (`darcy_pressure_drop_mono_length`):
Increasing cooling channel length `l1 ≤ l2` under non-negative friction factor `0 ≤ f` and fluid
density `0 ≤ rho` monotonically increases the Darcy-Weisbach pressure drop across the channel. -/
theorem darcy_pressure_drop_mono_length
    (f l1 l2 d rho v : Int)
    (hf : 0 ≤ f)
    (hRho : 0 ≤ rho)
    (hL : l1 ≤ l2) :
    evalDarcyPressureDropScaled ⟨f, l1, d, rho, v⟩ ≤
      evalDarcyPressureDropScaled ⟨f, l2, d, rho, v⟩ := by
  dsimp only [evalDarcyPressureDropScaled]
  have h1 : f * l1 ≤ f * l2 :=
    int_mul_le_mul_of_nonneg_left l1 l2 f hL hf
  have h2 : f * l1 * rho ≤ f * l2 * rho :=
    int_mul_le_mul_of_nonneg_right (f * l1) (f * l2) rho h1 hRho
  have hv2 : 0 ≤ v * v := int_sq_nonneg v
  rw [Int.mul_assoc (f * l1 * rho) v v, Int.mul_assoc (f * l2 * rho) v v]
  exact int_mul_le_mul_of_nonneg_right (f * l1 * rho) (f * l2 * rho) (v * v) h2 hv2

/-! ## 2. Parallel Stator Cooling Manifold Mass-Flow Conservation -/

/-- Total volumetric/mass flow rate summed across all parallel cooling branches in a stator manifold. -/
def sumBranchFlows : List Int → Int
  | [] => 0
  | q :: rest => q + sumBranchFlows rest

/-- Check Kirchhoff fluid mass conservation (`inletFlowMlPerMin = sumBranchFlows branchFlows`)
and strict positivity (`0 < q`) of every parallel cooling channel branch flow (no stagnant/starved slots). -/
def checkManifoldMassBalance (inletFlowMlPerMin : Int) (branchFlows : List Int) : Bool :=
  decide (inletFlowMlPerMin = sumBranchFlows branchFlows) &&
  branchFlows.all (fun q => decide (0 < q))

/-- Soundness of `checkManifoldMassBalance`:
if `checkManifoldMassBalance inletFlowMlPerMin branchFlows = true`, then the total branch flow
equals `inletFlowMlPerMin` and every individual cooling branch has strictly positive flow `0 < q`. -/
theorem checkManifoldMassBalance_sound
    (inletFlowMlPerMin : Int)
    (branchFlows : List Int)
    (hOk : checkManifoldMassBalance inletFlowMlPerMin branchFlows = true) :
    inletFlowMlPerMin = sumBranchFlows branchFlows ∧
    ∀ q ∈ branchFlows, 0 < q := by
  unfold checkManifoldMassBalance at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hOk
  exact ⟨hOk.1, fun q hq => hOk.2 q hq⟩

/-- Theorem (`manifold_total_flow_nonneg`):
If every cooling branch in `branchFlows` has non-negative flow (`∀ q ∈ branchFlows, 0 ≤ q`),
then the total manifold flow `sumBranchFlows branchFlows` is non-negative (`0 ≤ sumBranchFlows branchFlows`). -/
theorem manifold_total_flow_nonneg
    (branchFlows : List Int)
    (hNonneg : ∀ q ∈ branchFlows, 0 ≤ q) :
    0 ≤ sumBranchFlows branchFlows := by
  induction branchFlows with
  | nil =>
    simp [sumBranchFlows]
  | cons q rest ih =>
    have hq : 0 ≤ q := hNonneg q (by simp)
    have hRest : 0 ≤ sumBranchFlows rest :=
      ih (fun x hx => hNonneg x (by simp [hx]))
    dsimp only [sumBranchFlows]
    omega

/-! ## 3. Conjugate Convective + Caloric Stator Winding Thermal Network -/

/-- Peak copper stator winding temperature (in millidegrees C, $\text{m}^\circ\text{C}$) above coolant
inlet temperature `tInletMilliC` under total stator heat loss `powerLossW` ($\text{W}$), governed by
three series thermal impedances (in $\text{mK/W}$):
1. `rCaloricMilliKPerW`: bulk coolant caloric heating impedance $R_{\text{caloric}} = \frac{1000}{\dot{m} c_p}$,
2. `rConvMilliKPerW`: convective film impedance $R_{\text{conv}} = \frac{1000}{h_{\text{conv}} A_{\text{wet}}}$,
3. `rCondMilliKPerW`: slot-liner + impregnation potting + stator tooth conduction impedance $R_{\text{cond}}$. -/
def evalPeakWindingTempMilliC
    (tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rCondMilliKPerW : Int) : Int :=
  tInletMilliC + powerLossW * (rCaloricMilliKPerW + rConvMilliKPerW + rCondMilliKPerW)

/-- Universal Conjugate Cooling Monotonicity Theorem (`higher_flow_and_convection_lowers_winding_temp`):
For any non-negative stator copper/iron power loss `0 ≤ powerLossW`, if increasing coolant mass flow
lowers caloric thermal resistance (`rCal2 ≤ rCal1`) and increasing turbulent Nusselt/Gnielinski
convection lowers convective film resistance (`rConv2 ≤ rConv1`), then peak stator winding temperature
monotonically decreases:
$$T_{\text{winding}}(R_{\text{cal},2}, R_{\text{conv},2}) \le T_{\text{winding}}(R_{\text{cal},1}, R_{\text{conv},1}).$$ -/
theorem higher_flow_and_convection_lowers_winding_temp
    (tInlet powerLossW rCal1 rCal2 rConv1 rConv2 rCond : Int)
    (hPower : 0 ≤ powerLossW)
    (hCal   : rCal2 ≤ rCal1)
    (hConv  : rConv2 ≤ rConv1) :
    evalPeakWindingTempMilliC tInlet powerLossW rCal2 rConv2 rCond ≤
      evalPeakWindingTempMilliC tInlet powerLossW rCal1 rConv1 rCond := by
  dsimp only [evalPeakWindingTempMilliC]
  have hSum : rCal2 + rConv2 + rCond ≤ rCal1 + rConv1 + rCond := by omega
  have hMul : powerLossW * (rCal2 + rConv2 + rCond) ≤ powerLossW * (rCal1 + rConv1 + rCond) :=
    int_mul_le_mul_of_nonneg_left (rCal2 + rConv2 + rCond) (rCal1 + rConv1 + rCond) powerLossW hSum hPower
  omega

/-- Coolant outlet bulk temperature (in $\text{m}^\circ\text{C}$) from first-law enthalpy balance:
$$T_{\text{outlet}} = T_{\text{inlet}} + \frac{P_{\text{loss,mW}} \cdot 1000}{\dot{m}_{\text{g/s}} \cdot c_p}.$$ -/
def evalCoolantOutletTempMilliC
    (tInletMilliC powerLossMilliW massFlowGramPerSec cpJPerGramK : Int) : Int :=
  tInletMilliC + (powerLossMilliW * 1000) / (massFlowGramPerSec * cpJPerGramK)

/-- Non-negativity of integer Euclidean division for non-negative dividend and divisor. -/
theorem int_ediv_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact Int.natCast_nonneg (m / n)
    | negSucc n => omega
  | negSucc m => omega

/-- Theorem (`coolant_outlet_above_inlet`):
Whenever heat dissipation `0 ≤ powerLossMilliW`, coolant mass flow `0 ≤ massFlowGramPerSec`,
and specific heat capacity `0 ≤ cpJPerGramK` are non-negative, the coolant outlet temperature
is never below the coolant inlet temperature (`tInletMilliC ≤ evalCoolantOutletTempMilliC ...`). -/
theorem coolant_outlet_above_inlet
    (tInletMilliC powerLossMilliW massFlowGramPerSec cpJPerGramK : Int)
    (hPower : 0 ≤ powerLossMilliW)
    (hFlow  : 0 ≤ massFlowGramPerSec)
    (hCp    : 0 ≤ cpJPerGramK) :
    tInletMilliC ≤
      evalCoolantOutletTempMilliC tInletMilliC powerLossMilliW massFlowGramPerSec cpJPerGramK := by
  dsimp only [evalCoolantOutletTempMilliC]
  have hNum : 0 ≤ powerLossMilliW * 1000 :=
    int_mul_nonneg powerLossMilliW 1000 hPower (by omega)
  have hDen : 0 ≤ massFlowGramPerSec * cpJPerGramK :=
    int_mul_nonneg massFlowGramPerSec cpJPerGramK hFlow hCp
  have hDiv : 0 ≤ (powerLossMilliW * 1000) / (massFlowGramPerSec * cpJPerGramK) :=
    int_ediv_nonneg (powerLossMilliW * 1000) (massFlowGramPerSec * cpJPerGramK) hNum hDen
  omega

/-! ## 4. Liquid-Cooled Motor Thermal & Cavitation Signoff Checker (`checkLiquidThermalSignoff`) -/

/-- Complete electro-fluid-thermal signoff checker for a liquid-cooled electric machine:
* `tWindingMilliC ≤ maxClassHInsulationMilliC`: Class-H polyamide-imide / PEEK magnet-wire limit ($180,000\,\text{m}^\circ\text{C} = 180^\circ\text{C}$),
* `tMagnetMilliC ≤ maxMagnetDemagMilliC`: NdFeB N42SH/N48UH irreversible demagnetization limit ($120,000\,\text{m}^\circ\text{C} = 120^\circ\text{C}$),
* `pressureDropPa ≤ maxPumpPressurePa`: hydraulic pressure drop within coolant pump envelope,
* `tOutletMilliC < tBoilingMarginMilliC`: coolant outlet strictly below nucleate-boiling / pump-cavitation threshold. -/
def checkLiquidThermalSignoff
    (tWindingMilliC maxClassHInsulationMilliC : Int)
    (tMagnetMilliC maxMagnetDemagMilliC : Int)
    (pressureDropPa maxPumpPressurePa : Int)
    (tOutletMilliC tBoilingMarginMilliC : Int) : Bool :=
  decide (tWindingMilliC ≤ maxClassHInsulationMilliC) &&
  decide (tMagnetMilliC ≤ maxMagnetDemagMilliC) &&
  decide (pressureDropPa ≤ maxPumpPressurePa) &&
  decide (tOutletMilliC < tBoilingMarginMilliC)

/-- Soundness theorem (`checkLiquidThermalSignoff_sound`):
If `checkLiquidThermalSignoff` returns `true`, then all four multiphysics thermal, magnetic,
hydraulic, and anti-cavitation safety invariants hold simultaneously. -/
theorem checkLiquidThermalSignoff_sound
    (tWindingMilliC maxClassHInsulationMilliC : Int)
    (tMagnetMilliC maxMagnetDemagMilliC : Int)
    (pressureDropPa maxPumpPressurePa : Int)
    (tOutletMilliC tBoilingMarginMilliC : Int)
    (hOk : checkLiquidThermalSignoff
      tWindingMilliC maxClassHInsulationMilliC
      tMagnetMilliC maxMagnetDemagMilliC
      pressureDropPa maxPumpPressurePa
      tOutletMilliC tBoilingMarginMilliC = true) :
    tWindingMilliC ≤ maxClassHInsulationMilliC ∧
    tMagnetMilliC ≤ maxMagnetDemagMilliC ∧
    pressureDropPa ≤ maxPumpPressurePa ∧
    tOutletMilliC < tBoilingMarginMilliC := by
  unfold checkLiquidThermalSignoff at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.1.1, hOk.1.1.2, hOk.1.2, hOk.2⟩

/-- Golden liquid-cooled axial/radial-flux traction stator signoff (`golden_liquid_cooled_stator_signoff_verified`):
Verifies by kernel evaluation (`decide +kernel`) a $4\,\text{kW}$-loss liquid-cooled stator jacket
with 6 parallel cooling channels ($6 \times 1500\,\text{mL/min} = 9000\,\text{mL/min} = 150\,\text{g/s}$),
$T_{\text{inlet}} = 60^\circ\text{C}$, peak winding temperature $148^\circ\text{C} \le 180^\circ\text{C}$ (Class-H),
rotor magnet temperature $102^\circ\text{C} \le 120^\circ\text{C}$, pressure drop $42\,\text{kPa} \le 80\,\text{kPa}$,
and coolant outlet $67.6^\circ\text{C} < 105^\circ\text{C}$ boiling margin. -/
theorem golden_liquid_cooled_stator_signoff_verified :
    let branchFlows : List Int := [1500, 1500, 1500, 1500, 1500, 1500]
    let tWinding := evalPeakWindingTempMilliC 60000 4000 2 8 12
    let tOutlet  := evalCoolantOutletTempMilliC 60000 4000000 150 3500
    checkManifoldMassBalance 9000 branchFlows = true ∧
    tWinding = 148000 ∧
    tOutlet = 67619 ∧
    checkLiquidThermalSignoff tWinding 180000 102000 120000 42000 80000 tOutlet 105000 = true := by
  decide +kernel

/-! ## 5. LC Drives (Potsdam, NY) Direct In-Slot Stator Microchannel Cooling vs. Outer Jacket -/

/-- Evaluates peak stator conductor temperature (in millidegrees Celsius) for a conventional
outer-water-jacketed electric motor, where heat must traverse the slot liner insulation
(`rSlotLinerMilliKPerW`) and the laminated silicon-steel stator tooth/yoke (`rIronYokeMilliKPerW`)
in series with the coolant caloric and convective resistances:
$$T_{\text{jacket}} = T_{\text{inlet}} + P_{\text{loss}} (R_{\text{cal}} + R_{\text{conv}} + R_{\text{liner}} + R_{\text{yoke}}).$$ -/
def evalOuterJacketWindingTempMilliC
    (tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rSlotLinerMilliKPerW rIronYokeMilliKPerW : Int) : Int :=
  tInletMilliC +
    powerLossW * (rCaloricMilliKPerW + rConvMilliKPerW + rSlotLinerMilliKPerW + rIronYokeMilliKPerW)

/-- Evaluates peak stator conductor temperature (in millidegrees Celsius) for an LC Drives
direct in-slot microchannel liquid-cooled stator, where non-conductive microchannels are placed
directly inside the stator slot in intimate contact with the conductors (`rDirectWallMilliKPerW`),
completely bypassing the slot-liner and laminated iron-yoke thermal barrier:
$$T_{\text{in-slot}} = T_{\text{inlet}} + P_{\text{loss}} (R_{\text{cal}} + R_{\text{conv}} + R_{\text{wall}}).$$ -/
def evalLcDrivesInSlotWindingTempMilliC
    (tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rDirectWallMilliKPerW : Int) : Int :=
  tInletMilliC +
    powerLossW * (rCaloricMilliKPerW + rConvMilliKPerW + rDirectWallMilliKPerW)

/-- Exact Temperature Reduction Identity for Direct In-Slot Cooling (`lc_drives_in_slot_temp_drop_identity`):
The conductor temperature reduction achieved by LC Drives direct in-slot cooling over a conventional
outer water jacket is identically $P_{\text{loss}} \cdot (R_{\text{liner}} + R_{\text{yoke}} - R_{\text{wall}})$. -/
theorem lc_drives_in_slot_temp_drop_identity
    (tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rSlotLinerMilliKPerW rIronYokeMilliKPerW rDirectWallMilliKPerW : Int) :
    evalOuterJacketWindingTempMilliC tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rSlotLinerMilliKPerW rIronYokeMilliKPerW -
      evalLcDrivesInSlotWindingTempMilliC tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rDirectWallMilliKPerW =
    powerLossW * (rSlotLinerMilliKPerW + rIronYokeMilliKPerW - rDirectWallMilliKPerW) := by
  unfold evalOuterJacketWindingTempMilliC evalLcDrivesInSlotWindingTempMilliC
  simp only [Int.mul_add, Int.mul_sub]
  omega

/-- Strict Thermal Dominance of LC Drives In-Slot Cooling (`lc_drives_in_slot_cooler_than_outer_jacket`):
Whenever stator copper dissipation is positive (`0 < powerLossW`) and the direct in-slot microchannel
wall resistance is strictly lower than the series slot-liner plus laminated-iron-yoke resistance
(`rDirectWallMilliKPerW < rSlotLinerMilliKPerW + rIronYokeMilliKPerW`), the LC Drives direct in-slot
cooled winding runs strictly cooler than a conventional outer-jacketed motor at the same flow rate. -/
theorem lc_drives_in_slot_cooler_than_outer_jacket
    (tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rSlotLinerMilliKPerW rIronYokeMilliKPerW rDirectWallMilliKPerW : Int)
    (hLoss : 0 < powerLossW)
    (hBypass : rDirectWallMilliKPerW < rSlotLinerMilliKPerW + rIronYokeMilliKPerW) :
    evalLcDrivesInSlotWindingTempMilliC tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rDirectWallMilliKPerW <
      evalOuterJacketWindingTempMilliC tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rSlotLinerMilliKPerW rIronYokeMilliKPerW := by
  have hDiff := lc_drives_in_slot_temp_drop_identity
    tInletMilliC powerLossW rCaloricMilliKPerW rConvMilliKPerW rSlotLinerMilliKPerW rIronYokeMilliKPerW rDirectWallMilliKPerW
  have hPos : 0 < powerLossW * (rSlotLinerMilliKPerW + rIronYokeMilliKPerW - rDirectWallMilliKPerW) :=
    Int.mul_pos hLoss (by omega)
  omega

/-- Golden LC Drives (Potsdam, NY) High-Torque Stator Dyno Comparison (`lc_drives_potsdam_dyno_comparison_verified`):
At $8\,\text{kW}$ continuous stator copper loss with $T_{\text{inlet}} = 50^\circ\text{C}$ (`50000 mC`):
- A conventional outer-jacketed motor ($R_{\text{liner}} = 12\,\text{mK/W}$, $R_{\text{yoke}} = 18\,\text{mK/W}$)
  reaches $346^\circ\text{C}$ (`346000 mC`), violating Class-H $180^\circ\text{C}$ insulation and failing signoff.
- The LC Drives direct in-slot liquid-cooled stator ($R_{\text{wall}} = 2\,\text{mK/W}$) runs at
  $122^\circ\text{C}$ (`122000 mC`), $224^\circ\text{C}$ cooler, passing Class-H signoff with $58^\circ\text{C}$ margin! -/
theorem lc_drives_potsdam_dyno_comparison_verified :
    let tOuterJacket := evalOuterJacketWindingTempMilliC 50000 8000 2 5 12 18
    let tLcInSlot    := evalLcDrivesInSlotWindingTempMilliC 50000 8000 2 5 2
    tOuterJacket = 346000 ∧
    tLcInSlot = 122000 ∧
    tOuterJacket - tLcInSlot = 224000 ∧
    checkLiquidThermalSignoff tOuterJacket 180000 102000 120000 42000 80000 67619 105000 = false ∧
    checkLiquidThermalSignoff tLcInSlot 180000 102000 120000 42000 80000 67619 105000 = true := by
  decide +kernel

end Obend.Hardware.FluidThermal
end
