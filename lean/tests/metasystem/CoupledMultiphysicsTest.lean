module

public import Obend.Tactic.Tooth
public import Obend.Hardware.Magnetics
public import Obend.Hardware.ThermalPassivity
public import Obend.Hardware.Kinematics
public import Obend.Vault.HardwareProjection
public import Obend.Vault.PhysicalProjection
import all Obend.Hardware.Magnetics
import all Obend.Hardware.ThermalPassivity
import all Obend.Hardware.Kinematics
import all Obend.Vault.HardwareProjection
import all Obend.Vault.PhysicalProjection

/-!
# Metasystem Test Suite — Coupled Multi-Physics, $1/\Delta_e$ Courant $P_1$ FEMM, PRIMA Thermal Passivity & Featherstone Twist Chains (`WS-J`)

Verifies universal theorems, concrete positive/negative boundary cases, `#tooth` mutation-killing
probes, and `#print axioms` (`0 sorryAx`) across:
1. `Obend.Hardware.Magnetics`:
   - Exact `/ \Delta_e`-normalized rational (`Rat`) Courant $P_1$ FEMM assembly (`FemmMesh2D`,
     `evalElementResidualQ_ampere_sum`, `evalElementResidualQ_virtual_work_identity`,
     `evalMeshNodalResidualQ_gauge_invariant`, `evalMeshTotalCoEnergyQ_nonneg`),
   - Scaled integer mesh assembly (`evalMeshNodalResidual_gauge_invariant`,
     `evalMeshTotalCoEnergy_nonneg`, `evalMeshTotalCoEnergy_gauge_invariant`),
   - Damped Picard nonlinear $B$-$H$ fixed-point iteration (`stepBhPicardReluctivity`,
     `stepBhPicardReluctivity_fixed_point`, `stepBhPicardReluctivity_monotone`).
2. `Obend.Hardware.ThermalPassivity`:
   - Discretized Fourier heat operator & PRIMA congruence projection (`prima_preserves_passivity`),
   - $N$-node Graph-Laplacian thermal network passivity (`laplacian_quadratic_passive_universal`),
   - Multi-column ($N \times 2$) PRIMA Krylov congruence passivity (`prima_2col_congruence_preserves_passivity`).
3. `Obend.Hardware.Kinematics`:
   - `propagateSerialChainTwists`, `propagateSerialChainTwists_append`,
     `propagateSerialChainTwists_scale`, `propagateSerialChainTwists_zipWith_add`,
     `spatialPower_propagateSerialChainTwists_append`.
4. `Obend.Vault.PhysicalProjection`:
   - `physical_projection_deterministic`, `physical_cnc_abbe_projection_sound`,
     `physical_openusd_lifecycle_projection_sound`, `physical_projection_doc_noninterference`.
-/

@[expose] public section
namespace Obend.Tests.Metasystem.CoupledMultiphysicsTest

open Obend.Core.Data
open Obend.Doc
open Obend.Hardware.Magnetics
open Obend.Hardware.ThermalPassivity
open Obend.Hardware.Kinematics
open Obend.Vault.HardwareProjection
open Obend.Vault.PhysicalProjection

set_option autoImplicit false

/-! ## 1. Global 2D `/ \Delta_e`-Normalized Courant $P_1$ FEMM Stiffness Assembly & Damped Picard B-H Fixed-Point -/

def testMesh2D : FemmMesh2D where
  triangles :=
    [ goldenStatorToothTriangle
    , { goldenStatorToothTriangle with jzScaled := 5, nuScaled := 1200 }
    , { goldenStatorToothTriangle with x2 := 1000, y2 := 2000, jzScaled := -3, nuScaled := 950 } ]
  vertexMap := fun idx =>
    if idx == 0 then (0, 1, 2)
    else if idx == 1 then (1, 2, 3)
    else (2, 0, 99)
  nodalPotentials := fun v =>
    match v with
    | 0 => 100
    | 1 => 250
    | 2 => 400
    | 3 => 550
    | _ => 700

theorem test_femm_mesh_coenergy_nonneg_and_gauge_invariance
    (mesh : FemmMesh2D) (c : Int) (nodeIdx : Nat)
    (hNu : ∀ tri ∈ mesh.triangles, 0 ≤ tri.nuScaled) :
    (0 : Rat) ≤ evalMeshTotalCoEnergyQ mesh ∧
    evalMeshNodalResidualQ { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } nodeIdx =
      evalMeshNodalResidualQ mesh nodeIdx ∧
    0 ≤ evalMeshTotalCoEnergy mesh ∧
    evalMeshTotalCoEnergy { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } =
      evalMeshTotalCoEnergy mesh ∧
    evalMeshNodalResidual { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } nodeIdx =
      evalMeshNodalResidual mesh nodeIdx :=
  ⟨evalMeshTotalCoEnergyQ_nonneg mesh hNu,
   evalMeshNodalResidualQ_gauge_invariant mesh c nodeIdx,
   evalMeshTotalCoEnergy_nonneg mesh hNu,
   evalMeshTotalCoEnergy_gauge_invariant mesh c,
   evalMeshNodalResidual_gauge_invariant mesh c nodeIdx⟩

theorem test_femm_q_ampere_and_virtual_work
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) :
    (let (r0, r1, r2) := evalElementResidualQ tri v0 v1 v2 nodalPotentials
     r0 + r1 + r2 = -3 * (((tri.jzScaled : Rat) * (tri.absTwiceArea : Rat)) / 6)) ∧
    (let a0 : Rat := (nodalPotentials v0 : Rat)
     let a1 : Rat := (nodalPotentials v1 : Rat)
     let a2 : Rat := (nodalPotentials v2 : Rat)
     let (r0, r1, r2) := evalElementResidualQ tri v0 v1 v2 nodalPotentials
     a0 * r0 + a1 * r1 + a2 * r2 =
       ((evalElementMagneticEnergyScaled tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2) : Rat) /
         (2 * (tri.absTwiceArea : Rat))) -
       (a0 + a1 + a2) * (((tri.jzScaled : Rat) * (tri.absTwiceArea : Rat)) / 6)) :=
  ⟨evalElementResidualQ_ampere_sum tri v0 v1 v2 nodalPotentials,
   evalElementResidualQ_virtual_work_identity tri v0 v1 v2 nodalPotentials⟩

theorem test_bh_picard_fixed_point_and_monotone
    (nuLinear kSat omegaPermille nuCur1 nuCur2 bSq1 bSq2 : Int)
    (hOmegaLo : 0 ≤ omegaPermille)
    (hOmegaHi : omegaPermille ≤ 1000)
    (hSat : 0 ≤ kSat)
    (hCurLe : nuCur1 ≤ nuCur2)
    (hBLe : bSq1 ≤ bSq2) :
    stepBhPicardReluctivity nuLinear kSat omegaPermille
      (evalNonlinearReluctivity nuLinear kSat bSq1) bSq1 =
      evalNonlinearReluctivity nuLinear kSat bSq1 ∧
    stepBhPicardReluctivity nuLinear kSat omegaPermille nuCur1 bSq1 ≤
      stepBhPicardReluctivity nuLinear kSat omegaPermille nuCur2 bSq2 :=
  ⟨stepBhPicardReluctivity_fixed_point nuLinear kSat omegaPermille _ bSq1 rfl,
   (stepBhPicardReluctivity_monotone nuLinear kSat omegaPermille nuCur1 nuCur2 bSq1 bSq2
      hOmegaLo hOmegaHi hSat hCurLe hBLe).1⟩

#guard evalMeshTotalCoEnergy testMesh2D > 0
#guard evalMeshNodalResidual testMesh2D 42 == 0
#guard stepBhPicardReluctivity 800 5 500 1300 100 == 1300

/-! ## 2. PRIMA Thermal Model-Order Reduction & Graph-Laplacian Passivity (`ThermalPassivity`) -/

theorem test_thermal_laplacian_and_prima_passivity
    (op : FineThermalOperator) (v1 v2 z : Int)
    (hg1 : 0 ≤ op.g1) (hg2 : 0 ≤ op.g2) (hg12 : 0 ≤ op.g12)
    (col0 col1 tempsMk : List Int) (edges : List ThermalEdge) (alpha0 alpha1 : Int)
    (hPassive : ∀ e ∈ edges, 0 ≤ e.conductanceMwPerK) :
    0 ≤ primaProject1D op v1 v2 ∧
    0 ≤ evalReducedThermalEnergy op v1 v2 z ∧
    0 ≤ evalLaplacianQuadratic tempsMk edges ∧
    0 ≤ evalPrima2ColReducedQuadratic col0 col1 edges alpha0 alpha1 :=
  ⟨(prima_preserves_passivity op v1 v2 z hg1 hg2 hg12).1,
   (prima_preserves_passivity op v1 v2 z hg1 hg2 hg12).2.1,
   laplacian_quadratic_passive_universal tempsMk edges hPassive,
   prima_2col_congruence_preserves_passivity col0 col1 edges alpha0 alpha1 hPassive⟩

/-! ## 3. Multi-Body Serial Twist Propagation & `.obnb` Physical Projections -/

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

theorem test_physical_projections_verified (spec : CncToolpathViewportSpec) :
    (evalUncompensatedTipPos3D
      (evalAbbeCompensatedCmd3D spec.pTarget spec.linErr spec.angErr spec.abbeArm)
      spec.linErr spec.angErr spec.abbeArm = spec.pTarget ∧
     spatialPower (spatialCrossForce spec.twist spec.momentum) spec.twist = 0 ∧
     (Obend.Leaf.emit Obend.Hardware.UserspacePhysical.cnc5AxisMillComp).closedB = true) ∧
    (let usd := goldenOpenUsdViewportSpec
     let stator := goldenStatorMultiphysicsSpec
     Obend.Hardware.OpenUSD.applyUsdRelocate usd.relocateDst usd.relocateSrc
       (Obend.Hardware.OpenUSD.applyUsdRelocate usd.relocateSrc usd.relocateDst usd.primPath) = usd.primPath ∧
     (Obend.Hardware.OpenUSD.AffineForm1D.sub usd.sdfWallForm usd.sdfWallForm).toInterval = { lo := 0, hi := 0 } ∧
     Obend.Hardware.OpenUSD.checkPartLifecycleInvariant usd.minWallUm usd.maxTempMilliC
       (Obend.Hardware.OpenUSD.finalUsdState usd.initSample usd.timeSamples) = true ∧
     Obend.Analysis.verifyTrajectorySafety stator.ode stator.initBox stator.steps stator.safeBounds = true ∧
     (Obend.Leaf.emit Obend.Hardware.UserspacePhysical.lcDrivesStatorUsdComp).closedB = true) :=
  ⟨physical_cnc_abbe_projection_sound spec, physical_openusd_lifecycle_projection_sound⟩

/-! ## 4. `#tooth` Mutation-Killing Probes & `#print axioms` Verification (`0 sorryAx`) -/

def stepBhPicardBrokenUnscaled (nuLinear kSat omegaPermille nuCur bSq : Int) : Int :=
  (1000 - omegaPermille) * nuCur + omegaPermille * evalNonlinearReluctivity nuLinear kSat bSq

#tooth Obend.Hardware.Magnetics.stepBhPicardReluctivity_fixed_point by mutation
  Obend.Hardware.Magnetics.stepBhPicardReluctivity := stepBhPicardBrokenUnscaled

def evalEdgeQuadraticBrokenLinear (tempsMk : List Int) (e : ThermalEdge) : Int :=
  e.conductanceMwPerK * (tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0)

#tooth Obend.Hardware.ThermalPassivity.laplacian_quadratic_passive_universal by mutation
  Obend.Hardware.ThermalPassivity.evalEdgeQuadratic := evalEdgeQuadraticBrokenLinear

def propagateSerialChainTwistsBroken : List SpatialTwist6D → SpatialTwist6D
  | [] => SpatialTwist6D.zero
  | _ :: rest => propagateSerialChainTwistsBroken rest

#tooth Obend.Hardware.Kinematics.propagateSerialChainTwists_append by mutation
  Obend.Hardware.Kinematics.propagateSerialChainTwists := propagateSerialChainTwistsBroken

#print axioms Obend.Hardware.Magnetics.evalElementResidualQ_ampere_sum
#print axioms Obend.Hardware.Magnetics.evalElementResidualQ_virtual_work_identity
#print axioms Obend.Hardware.Magnetics.evalMeshNodalResidualQ_gauge_invariant
#print axioms Obend.Hardware.Magnetics.evalMeshTotalCoEnergyQ_nonneg
#print axioms Obend.Hardware.Magnetics.stepBhPicardReluctivity_fixed_point
#print axioms Obend.Hardware.Magnetics.stepBhPicardReluctivity_monotone
#print axioms Obend.Hardware.ThermalPassivity.prima_preserves_passivity
#print axioms Obend.Hardware.ThermalPassivity.laplacian_quadratic_passive_universal
#print axioms Obend.Hardware.ThermalPassivity.prima_2col_congruence_preserves_passivity
#print axioms Obend.Hardware.Kinematics.propagateSerialChainTwists_append
#print axioms Obend.Hardware.Kinematics.propagateSerialChainTwists_scale
#print axioms Obend.Hardware.Kinematics.propagateSerialChainTwists_zipWith_add
#print axioms Obend.Vault.PhysicalProjection.physical_projection_deterministic
#print axioms Obend.Vault.PhysicalProjection.physical_cnc_abbe_projection_sound
#print axioms Obend.Vault.PhysicalProjection.physical_openusd_lifecycle_projection_sound

end Obend.Tests.Metasystem.CoupledMultiphysicsTest
end
