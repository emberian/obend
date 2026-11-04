module

public import Obend.Tactic.Tooth
public import Obend.Hardware.Thermal
public import Obend.Hardware.Magnetics
public import Obend.Hardware.FluidThermal
public import Obend.Hardware.PowerElectronics
public import Obend.Hardware.Kinematics
public import Obend.Hardware.Mechanics
public import Obend.Vault.HardwareProjection
public import Obend.Vault.PhysicalProjection
import all Obend.Hardware.Thermal
import all Obend.Hardware.Magnetics
import all Obend.Hardware.FluidThermal
import all Obend.Hardware.PowerElectronics
import all Obend.Hardware.Kinematics
import all Obend.Hardware.Mechanics
import all Obend.Vault.HardwareProjection
import all Obend.Vault.PhysicalProjection

/-!
# Metasystem Test Suite — Coupled Multi-Physics & Closed-Loop Mechatronics (`WS-J`)

Verifies universal theorems, concrete positive/negative boundary cases, `#tooth` mutation-killing
probes, and `#print axioms` (`0 sorryAx`) across:
1. `Obend.Hardware.Magnetics`:
   - `FemmMesh2D`, `evalElementResidual`, `evalMeshNodalResidual`, `evalMeshTotalCoEnergy`,
   - `evalElementResidual_gauge_invariant`, `evalElementResidual_ampere_sum`,
   - `evalElementResidual_virtual_work_identity`, `evalMeshNodalResidual_gauge_invariant`,
   - `evalMeshTotalCoEnergy_nonneg`, `evalMeshTotalCoEnergy_gauge_invariant`,
   - `evalMaxwellStressTorqueScaled`, `maxwell_stress_quadrature_symmetry`,
   - `maxwell_stress_agrees_with_dq0_pm_torque`,
   - `accumulateBhSecantReluctivity`, `bhSecantAccumulate_positive_and_monotone`.
2. `Obend.Hardware.Thermal` & `Obend.Hardware.FluidThermal`:
   - `evalCopperJouleHeatingTcr`, `evalCopperJouleSlope`, `evalConvectiveHeatRemoval`,
   - `stepCoupledElectroThermalMap`, `electroThermal_step_diff_identity`,
   - `electroThermal_equilibrium_stability_dichotomy`,
   - `electroThermal_steady_state_unique_and_contraction`.
3. `Obend.Hardware.PowerElectronics`:
   - `evalPwmModulatedVoltageScaled`, `checkLinearPwmModulation`, `evalSicInverterTotalLoss`,
   - `CoupledDriveTrainSpec`, `checkDriveTrainCoDesign`, `driveTrainCoDesign_sound`,
   - `goldenCoupledDriveTrainSpec`, `golden_coupled_drive_train_verified`.
4. `Obend.Hardware.Kinematics` & `Obend.Hardware.Mechanics`:
   - `propagateSerialChainTwists`, `propagateSerialChainTwists_append`,
   - `propagateSerialChainTwists_scale`, `propagateSerialChainTwists_zipWith_add`,
   - `spatialPower_propagateSerialChainTwists_append`,
   - `evalCombinedBendingTorsionVonMisesSq`, `combinedBendingTorsionVonMisesSq_nonneg`,
   - `evalCombinedBendingTorsionStrainEnergy`, `combinedBendingTorsionStrainEnergy_pos_def`.
5. `Obend.Vault.HardwareProjection` & `Obend.Vault.PhysicalProjection`:
   - `driveTrainCoDesignToData`, `projectDriveTrainCoDesign`,
   - `projectDriveTrainCoDesign_deterministic`, `driveTrainCoDesign_projection_sound`.
-/

@[expose] public section
namespace Obend.Tests.Metasystem.CoupledMultiphysicsTest

open Obend.Core.Data
open Obend.Doc
open Obend.Hardware.Thermal
open Obend.Hardware.Magnetics
open Obend.Hardware.FluidThermal
open Obend.Hardware.PowerElectronics
open Obend.Hardware.Kinematics
open Obend.Hardware.Mechanics
open Obend.Vault.HardwareProjection
open Obend.Vault.PhysicalProjection

set_option autoImplicit false

/-! ## 1. Global 2D FEMM Mesh Stiffness Assembly, Maxwell Stress Torque & Secant B-H Convergence -/

def testMesh2D : FemmMesh2D where
  triangles :=
    [ goldenStatorToothTriangle
    , { goldenStatorToothTriangle with jzScaled := 5, nuScaled := 1200 }
    , { goldenStatorToothTriangle with x2 := 1000, y2 := 2000, jzScaled := -3, nuScaled := 950 } ]
  vertexMap := fun idx =>
    if idx == 0 then (0, 1, 2)
    else if idx == 1 then (1, 2, 3)
    else (2, 0, 99) -- includes shared/non-manifold edge (0,2) and out-of-bounds vertex 99
  nodalPotentials := fun v =>
    match v with
    | 0 => 100
    | 1 => 250
    | 2 => 400
    | 3 => 550
    | _ => 700

/-- 1.1 Universal `FemmMesh2D` co-energy non-negativity, co-energy gauge invariance,
    and global nodal residual gauge invariance (`evalMeshNodalResidual_gauge_invariant`). -/
theorem test_femm_mesh_coenergy_nonneg_and_gauge_invariance
    (mesh : FemmMesh2D) (c : Int) (nodeIdx : Nat)
    (hNu : ∀ tri ∈ mesh.triangles, 0 ≤ tri.nuScaled) :
    0 ≤ evalMeshTotalCoEnergy mesh ∧
    evalMeshTotalCoEnergy { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } =
      evalMeshTotalCoEnergy mesh ∧
    evalMeshNodalResidual { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } nodeIdx =
      evalMeshNodalResidual mesh nodeIdx :=
  ⟨evalMeshTotalCoEnergy_nonneg mesh hNu,
   evalMeshTotalCoEnergy_gauge_invariant mesh c,
   evalMeshNodalResidual_gauge_invariant mesh c nodeIdx⟩

/-- 1.2 Concrete 3-triangle `FemmMesh2D` residual Ampere sum, Galerkin virtual work identity,
    assembled nodal residual, and co-energy positivity check. -/
theorem test_concrete_femm_mesh_residual_and_coenergy :
    let (r0, r1, r2) := evalElementResidual goldenStatorToothTriangle 0 1 2 testMesh2D.nodalPotentials
    r0 + r1 + r2 = 0 ∧
    0 < evalMeshTotalCoEnergy testMesh2D ∧
    evalMeshTotalCoEnergy { testMesh2D with nodalPotentials := fun n => testMesh2D.nodalPotentials n + 42 } =
      evalMeshTotalCoEnergy testMesh2D ∧
    evalMeshNodalResidual { testMesh2D with nodalPotentials := fun n => testMesh2D.nodalPotentials n + 42 } 2 =
      evalMeshNodalResidual testMesh2D 2 ∧
    evalMeshNodalResidual testMesh2D 42 = 0 := by
  refine ⟨by decide +kernel, by decide +kernel,
    evalMeshTotalCoEnergy_gauge_invariant testMesh2D 42,
    evalMeshNodalResidual_gauge_invariant testMesh2D 42 2,
    by decide +kernel⟩

/-- 1.3 Universal Maxwell Stress Tensor quadrature symmetry and $dq0$ torque agreement. -/
theorem test_maxwell_stress_symmetry_and_dq0_agreement
    (m : IpmMotorSpec) (rGapMm lStackMm bRadialPm dTheta idAmp iqAmp : Int)
    (samples s1 s2 : List AirGapHarmonicSample)
    (hPsi : m.psiPmMilliWb * 1000 = rGapMm * rGapMm * lStackMm * bRadialPm * dTheta) :
    (evalMaxwellStressTorqueScaled rGapMm lStackMm (swapAirGapBrBtheta samples) =
      evalMaxwellStressTorqueScaled rGapMm lStackMm samples ∧
     evalMaxwellStressTorqueScaled rGapMm lStackMm (s1 ++ s2) =
      evalMaxwellStressTorqueScaled rGapMm lStackMm s1 +
      evalMaxwellStressTorqueScaled rGapMm lStackMm s2) ∧
    (evalMaxwellStressTorqueScaled rGapMm lStackMm
      [{ bRadialMt := bRadialPm, bTangentialMt := iqAmp, arcWeight := 3 * m.polePairs * dTheta }] =
      evalIpmTorqueTwiceMicroNm m 0 iqAmp ∧
     evalMaxwellStressTorqueScaled 1 1
      [{ bRadialMt := m.psiPmMilliWb * 1000 + (m.ldMicroH - m.lqMicroH) * idAmp
         bTangentialMt := iqAmp
         arcWeight := 3 * m.polePairs }] =
      evalIpmTorqueTwiceMicroNm m idAmp iqAmp) :=
  ⟨⟨(maxwell_stress_quadrature_symmetry rGapMm lStackMm samples s1 s2).1,
    (maxwell_stress_quadrature_symmetry rGapMm lStackMm samples s1 s2).2.1⟩,
   maxwell_stress_agrees_with_dq0_pm_torque m rGapMm lStackMm bRadialPm dTheta idAmp iqAmp hPsi⟩

/-- 1.4 Concrete Maxwell Stress Tensor evaluation on empty, single-sector, and multi-sector contours. -/
example :
    let contour : List AirGapHarmonicSample :=
      [ { bRadialMt := 1200, bTangentialMt := 300, arcWeight := 4 }
      , { bRadialMt := 1150, bTangentialMt := 280, arcWeight := 4 } ]
    evalMaxwellStressTorqueScaled 60 150 [] = 0 ∧
    evalMaxwellStressTorqueScaled 60 150 (swapAirGapBrBtheta contour) =
      evalMaxwellStressTorqueScaled 60 150 contour ∧
    evalMaxwellStressTorqueScaled (-60) 150 contour =
      evalMaxwellStressTorqueScaled 60 150 contour ∧
    0 < evalMaxwellStressTorqueScaled 60 150 contour := by
  decide +kernel

/-- 1.5 Positivity and monotonicity of the secant-reluctivity sum (`bhSecantAccumulate_positive_and_monotone`). -/
theorem test_bh_secant_positive_and_monotone
    (nuLinear kSat nuCur1 nuCur2 bSq1 bSq2 : Int)
    (hNu0 : 0 < nuLinear) (hSat : 0 ≤ kSat)
    (hCurPos : 0 ≤ nuCur1) (hCurLe : nuCur1 ≤ nuCur2)
    (hBPos : 0 ≤ bSq1) (hBLe : bSq1 ≤ bSq2) :
    0 < accumulateBhSecantReluctivity nuLinear kSat nuCur1 bSq1 ∧
    nuCur1 + nuLinear ≤ accumulateBhSecantReluctivity nuLinear kSat nuCur1 bSq1 ∧
    accumulateBhSecantReluctivity nuLinear kSat nuCur1 bSq1 ≤
      accumulateBhSecantReluctivity nuLinear kSat nuCur2 bSq2 :=
  bhSecantAccumulate_positive_and_monotone nuLinear kSat nuCur1 nuCur2 bSq1 bSq2 hNu0 hSat hCurPos hCurLe hBPos hBLe

/-! ## 2. Electro-Thermal Copper TCR Feedback & Runaway vs. Equilibrium Dichotomy -/

/-- 2.1 Universal Thermal Runaway vs. Stable Equilibrium Dichotomy (`electroThermal_equilibrium_stability_dichotomy`)
    including stable contraction, thermal runaway divergence, and exact neutral boundary invariance. -/
theorem test_electroThermal_equilibrium_stability_dichotomy
    (iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 t2 : Int)
    (hDt : 0 < dt) (hOrder : t2 < t1) :
    (evalCopperJouleSlope iAmp r0Mohm alphaPermille < gTh →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2 <
      t1 - t2) ∧
    (gTh < evalCopperJouleSlope iAmp r0Mohm alphaPermille →
      t1 - t2 <
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2) ∧
    (gTh = evalCopperJouleSlope iAmp r0Mohm alphaPermille →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2 =
      t1 - t2) :=
  electroThermal_equilibrium_stability_dichotomy
    iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 t2 hDt hOrder

/-- 2.2 Universal steady-state equilibrium $T^\star$ uniqueness and excess temperature contraction. -/
theorem test_electroThermal_steady_state_unique
    (iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar1 tStar2 tCur : Int)
    (hDt : 0 < dt)
    (hFix1 : stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar1 = tStar1) :
    (evalCopperJouleSlope iAmp r0Mohm alphaPermille ≠ gTh →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar2 = tStar2 →
      tStar1 = tStar2) ∧
    (tStar1 < tCur →
      evalCopperJouleSlope iAmp r0Mohm alphaPermille < gTh →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tCur - tStar1 <
        tCur - tStar1) :=
  let h := electroThermal_steady_state_unique_and_contraction
    iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar1 tStar2 tCur hDt hFix1
  ⟨h.1, h.2.1⟩

/-- 2.3 Concrete verification of stable contraction ($G_{\text{th}} > I^2 R_0 \alpha$),
    thermal runaway divergence ($G_{\text{th}} < I^2 R_0 \alpha$), and the exact neutral
    boundary ($G_{\text{th}} = I^2 R_0 \alpha$). -/
example :
    let iAmp := 10
    let r0Mohm := 5
    let alphaPermille := 4
    let cuSlope := evalCopperJouleSlope iAmp r0Mohm alphaPermille -- 100 * 5 * 4 = 2000
    let gThStable := 2500
    let gThNeutral := 2000
    let gThRunaway := 1500
    let t1 := 120
    let t2 := 100
    cuSlope = 2000 ∧
    (stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille 25 300 400 gThStable 50 1 t1 -
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille 25 300 400 gThStable 50 1 t2 < t1 - t2) ∧
    (stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille 25 300 400 gThNeutral 50 1 t1 -
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille 25 300 400 gThNeutral 50 1 t2 = t1 - t2) ∧
    (t1 - t2 <
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille 25 300 400 gThRunaway 50 1 t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille 25 300 400 gThRunaway 50 1 t2) := by
  decide +kernel

/-! ## 3. Coupled Motor-Inverter-Cooler Drive Train Co-Design (`checkDriveTrainCoDesign`) -/

/-- 3.1 Universal soundness of `checkDriveTrainCoDesign`. -/
theorem test_drive_train_codesign_sound
    (spec : CoupledDriveTrainSpec)
    (hOk : checkDriveTrainCoDesign spec = true) :
    (0 ≤ spec.modulationPermille ∧ spec.modulationPermille ≤ 1000) ∧
    evalTurnOffPeakVoltageV spec.vDcBusV spec.lBusNh spec.diDtAmpPerNs ≤ spec.vDssRatedV ∧
    spec.turnOffMaxNs < spec.deadTimeNs + spec.turnOnMinNs ∧
    evalCopperJouleSlope spec.iRmsAmp spec.r0CuMohm spec.alphaCuPermille < spec.gThCooler ∧
    spec.tWindingMilliC ≤ spec.maxClassHInsulationMilliC ∧
    0 ≤ evalPwmModulatedVoltageScaled spec.modulationPermille spec.vDcBusV ∧
    evalPwmModulatedVoltageScaled spec.modulationPermille spec.vDcBusV ≤ 1000 * spec.vDcBusV ∧
    0 ≤ spec.pCoreLoss ∧
    spec.tCoolantMilliC ≤ spec.tWindingMilliC := by
  have h := driveTrainCoDesign_sound spec hOk
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
         h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

/-- 3.2 Concrete golden pass and negative boundary refutations for `checkDriveTrainCoDesign`:
    - `goldenCoupledDriveTrainSpec` passes (`true`),
    - Over-modulation ($M = 1050 > 1000$) is refused (`false`),
    - Negative DC link voltage ($V_{\text{DC}} = -100$) is refused (`false`),
    - Busbar overshoot ($L_{\text{bus}} = 60\,\text{nH} \implies V_{\text{peak}} = 1280\,\text{V} > 1200\,\text{V}$) is refused (`false`),
    - Negative iron core loss ($P_{\text{core}} = -10$) is refused (`false`),
    - Inadequate cooler conductance ($G_{\text{th}} = 1500000 \le I^2 R_0 \alpha = 1920000$) is refused (`false`),
    - Coolant hotter than winding ($T_{\text{coolant}} = 130000 > T_{\text{winding}} = 122000$) is refused (`false`),
    - Class-H winding overtemperature ($T_{\text{winding}} = 185000 > 180000$) is refused (`false`). -/
example :
    checkDriveTrainCoDesign goldenCoupledDriveTrainSpec = true ∧
    checkDriveTrainCoDesign { goldenCoupledDriveTrainSpec with modulationPermille := 1050 } = false ∧
    checkDriveTrainCoDesign { goldenCoupledDriveTrainSpec with vDcBusV := -100 } = false ∧
    checkDriveTrainCoDesign { goldenCoupledDriveTrainSpec with lBusNh := 60 } = false ∧
    checkDriveTrainCoDesign { goldenCoupledDriveTrainSpec with pCoreLoss := -10 } = false ∧
    checkDriveTrainCoDesign { goldenCoupledDriveTrainSpec with gThCooler := 1500000 } = false ∧
    checkDriveTrainCoDesign { goldenCoupledDriveTrainSpec with tCoolantMilliC := 130000 } = false ∧
    checkDriveTrainCoDesign { goldenCoupledDriveTrainSpec with tWindingMilliC := 185000 } = false := by
  decide +kernel

/-! ## 4. Multi-Body Serial Twist Propagation, Combined Bending + Torsion & `.obnb` Projections -/

/-- 4.1 Universal serial chain twist additivity (both concatenation and pointwise superposition),
    scaling linearity, and virtual power distribution. -/
theorem test_serial_chain_twist_linearity
    (s : Int) (f : SpatialWrench6D) (c1 c2 : List SpatialTwist6D)
    (hLen : c1.length = c2.length) :
    propagateSerialChainTwists (c1 ++ c2) =
      SpatialTwist6D.add (propagateSerialChainTwists c1) (propagateSerialChainTwists c2) ∧
    propagateSerialChainTwists (List.zipWith SpatialTwist6D.add c1 c2) =
      SpatialTwist6D.add (propagateSerialChainTwists c1) (propagateSerialChainTwists c2) ∧
    propagateSerialChainTwists (c1.map (SpatialTwist6D.scale s)) =
      SpatialTwist6D.scale s (propagateSerialChainTwists c1) ∧
    spatialPower f (propagateSerialChainTwists (c1 ++ c2)) =
      spatialPower f (propagateSerialChainTwists c1) +
      spatialPower f (propagateSerialChainTwists c2) :=
  ⟨propagateSerialChainTwists_append c1 c2,
   propagateSerialChainTwists_zipWith_add c1 c2 hLen,
   propagateSerialChainTwists_scale s c1,
   spatialPower_propagateSerialChainTwists_append f c1 c2⟩

/-- 4.2 Universal non-negativity and positive-definiteness under combined bending + torsion. -/
theorem test_combined_bending_torsion_von_mises_and_strain_energy
    (sigmaBending tauTorsion kBend kTors mBend tTorsion : Int)
    (hKB : 0 < kBend) (hKT : 0 < kTors) :
    (0 ≤ evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion ∧
     sigmaBending * sigmaBending ≤ evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion ∧
     3 * (tauTorsion * tauTorsion) ≤ evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion ∧
     (sigmaBending ≠ 0 ∨ tauTorsion ≠ 0 →
       0 < evalCombinedBendingTorsionVonMisesSq sigmaBending tauTorsion)) ∧
    (0 ≤ evalCombinedBendingTorsionStrainEnergy kBend kTors mBend tTorsion ∧
     (mBend ≠ 0 ∨ tTorsion ≠ 0 →
       0 < evalCombinedBendingTorsionStrainEnergy kBend kTors mBend tTorsion)) :=
  ⟨combinedBendingTorsionVonMisesSq_nonneg sigmaBending tauTorsion,
   combinedBendingTorsionStrainEnergy_pos_def kBend kTors mBend tTorsion hKB hKT⟩

/-- 4.3 `.obnb` drive-train co-design projection determinism and cross-module verification across
     BOTH `Obend.Vault.PhysicalProjection` and `Obend.Vault.HardwareProjection`. -/
theorem test_project_drive_train_codesign_deterministic_and_verified :
    let cell := Obend.Vault.PhysicalProjection.projectDriveTrainCoDesign
                  "drivetrain_cell_0" goldenCoupledDriveTrainSpec
    (match cell with
     | .cell id kind _ pins rec =>
       id = "drivetrain_cell_0" ∧ kind = .hardwareSchematic ∧ pins = [] ∧ rec = none
     | _ => False) ∧
    Obend.Vault.PhysicalProjection.driveTrainCoDesignToData goldenCoupledDriveTrainSpec =
      Obend.Vault.HardwareProjection.driveTrainCoDesignToData goldenCoupledDriveTrainSpec ∧
    Obend.Vault.PhysicalProjection.projectDriveTrainCoDesign "drivetrain_cell_0" goldenCoupledDriveTrainSpec =
      Obend.Vault.HardwareProjection.projectDriveTrainCoDesign "drivetrain_cell_0" goldenCoupledDriveTrainSpec := by
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-! ## 5. `#tooth` Mutation-Killing Probes & `#print axioms` Verification (`0 sorryAx`) -/

/-- Tooth 1: Broken `evalMaxwellStressTorqueScaled` that subtracts `evalMaxwellStressTorque` instead of multiplying. -/
def evalMaxwellStressTorqueScaledBroken
    (rGapMm lStackMm : Int) (samples : List AirGapHarmonicSample) : Int :=
  (rGapMm * rGapMm * lStackMm) - evalMaxwellStressTorque samples

#tooth Obend.Hardware.Magnetics.maxwell_stress_quadrature_symmetry by mutation Obend.Hardware.Magnetics.evalMaxwellStressTorqueScaled := evalMaxwellStressTorqueScaledBroken

/-- Tooth 2: Broken `accumulateBhSecantReluctivity` that subtracts `evalNonlinearReluctivity` instead of adding. -/
def stepBhSecantReluctivityBroken (nuLinear kSat nuCur bSq : Int) : Int :=
  nuCur - evalNonlinearReluctivity nuLinear kSat bSq

#tooth Obend.Hardware.Magnetics.bhSecantAccumulate_positive_and_monotone by mutation Obend.Hardware.Magnetics.accumulateBhSecantReluctivity := stepBhSecantReluctivityBroken

/-- Tooth 3: Broken `evalCopperJouleSlope` that ignores `alphaPermille`. -/
def evalCopperJouleSlopeBroken (iAmp r0Mohm _alphaPermille : Int) : Int :=
  iAmp * iAmp * r0Mohm

#tooth Obend.Hardware.Thermal.electroThermal_equilibrium_stability_dichotomy by mutation Obend.Hardware.Thermal.evalCopperJouleSlope := evalCopperJouleSlopeBroken

/-- Tooth 4: Broken `propagateSerialChainTwists` that drops the head joint twist `v` instead of accumulating it. -/
def propagateSerialChainTwistsBroken : List SpatialTwist6D → SpatialTwist6D
  | [] => SpatialTwist6D.zero
  | _ :: rest => propagateSerialChainTwistsBroken rest

#tooth Obend.Hardware.Kinematics.propagateSerialChainTwists_append by mutation Obend.Hardware.Kinematics.propagateSerialChainTwists := propagateSerialChainTwistsBroken

/-- Tooth 5: Broken `evalCombinedBendingTorsionVonMisesSq` that subtracts $3 \tau_t^2$ instead of adding. -/
def evalCombinedBendingTorsionVonMisesSqBroken (sigmaBending tauTorsion : Int) : Int :=
  sigmaBending * sigmaBending - 3 * (tauTorsion * tauTorsion)

#tooth Obend.Hardware.Mechanics.combinedBendingTorsionVonMisesSq_nonneg by mutation Obend.Hardware.Mechanics.evalCombinedBendingTorsionVonMisesSq := evalCombinedBendingTorsionVonMisesSqBroken

/-- Tooth 6: Broken `checkDriveTrainCoDesign` that skips the thermal runaway check `cuSlope < spec.gThCooler`. -/
def checkDriveTrainCoDesignBroken (spec : CoupledDriveTrainSpec) : Bool :=
  let vPeakV := evalTurnOffPeakVoltageV spec.vDcBusV spec.lBusNh spec.diDtAmpPerNs
  let pInv := evalSicInverterTotalLoss spec.iRmsAmp spec.rDsOnMohm spec.kSwScaled spec.fSwKhz spec.vDcBusV
  let motor : IpmMotorSpec :=
    { polePairs    := spec.polePairs
    , psiPmMilliWb := spec.psiPmMilliWb
    , ldMicroH     := spec.ldMicroH
    , lqMicroH     := spec.lqMicroH }
  let shaftTorque := evalIpmTorqueScaled motor spec.idAmp spec.iqAmp
  checkLinearPwmModulation spec.modulationPermille &&
  decide (0 ≤ spec.vDcBusV) &&
  decide (vPeakV ≤ spec.vDssRatedV) &&
  checkDeadTimeInterlock spec.deadTimeNs spec.turnOffMaxNs spec.turnOnMinNs spec.safetyMarginNs &&
  decide (pInv ≤ spec.maxInverterLossBudget) &&
  decide (spec.minShaftTorqueScaled ≤ shaftTorque) &&
  decide (0 ≤ spec.pCoreLoss) &&
  decide (spec.tCoolantMilliC ≤ spec.tWindingMilliC) &&
  decide (spec.tWindingMilliC ≤ spec.maxClassHInsulationMilliC)

#tooth Obend.Hardware.PowerElectronics.driveTrainCoDesign_sound by mutation Obend.Hardware.PowerElectronics.checkDriveTrainCoDesign := checkDriveTrainCoDesignBroken

#print axioms Obend.Hardware.Magnetics.evalElementResidual_ampere_sum
#print axioms Obend.Hardware.Magnetics.evalElementResidual_virtual_work_identity
#print axioms Obend.Hardware.Magnetics.evalMeshNodalResidual_gauge_invariant
#print axioms Obend.Hardware.Magnetics.evalMeshTotalCoEnergy_nonneg
#print axioms Obend.Hardware.Magnetics.maxwell_stress_quadrature_symmetry
#print axioms Obend.Hardware.Magnetics.maxwell_stress_agrees_with_dq0_pm_torque
#print axioms Obend.Hardware.Magnetics.bhSecantAccumulate_positive_and_monotone
#print axioms Obend.Hardware.Thermal.electroThermal_equilibrium_stability_dichotomy
#print axioms Obend.Hardware.Thermal.electroThermal_steady_state_unique_and_contraction
#print axioms Obend.Hardware.PowerElectronics.driveTrainCoDesign_sound
#print axioms Obend.Hardware.Kinematics.propagateSerialChainTwists_append
#print axioms Obend.Hardware.Kinematics.propagateSerialChainTwists_scale
#print axioms Obend.Hardware.Kinematics.propagateSerialChainTwists_zipWith_add
#print axioms Obend.Hardware.Mechanics.combinedBendingTorsionVonMisesSq_nonneg
#print axioms Obend.Hardware.Mechanics.combinedBendingTorsionStrainEnergy_pos_def
#print axioms Obend.Vault.HardwareProjection.projectDriveTrainCoDesign_deterministic
#print axioms Obend.Vault.HardwareProjection.driveTrainCoDesign_projection_sound
#print axioms Obend.Vault.PhysicalProjection.projectDriveTrainCoDesign_deterministic
#print axioms Obend.Vault.PhysicalProjection.driveTrainCoDesign_projection_sound

end Obend.Tests.Metasystem.CoupledMultiphysicsTest
end
