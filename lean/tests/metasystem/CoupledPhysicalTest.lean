/-
# `tests/CoupledPhysicalTest.lean` — End-to-End Verification of WS-R:
# 1. The canonical OpenUSD model (audit fix 6)
# 2. Multi-Limb ($K$-Limb) Ozaki Base-13 `FP4` integer identities (`Obend.Hardware.Accelerators`)
# 3. Octree pruning regimes (`GeometryCAM.ivMinChoice`)
# 4. Coupled Sampled-Data Cyber-Physical Powertrain `DigitalTwin` (`Obend.Hardware.DigitalTwin`)
# 5. `stdlib/physical/*.obend` Elaborated via `#import_obend` in `Obend.Hardware.UserspacePhysical`
# The VOP64 GPU interpreter and the six-stage self-acceleration tests went 2026-11-05 with the module that
# held them; the GPU path is `Obend.Hardware.Gpu`.
-/
import Lean
import Obend.Hardware.Accelerators
import Obend.Hardware.GeometryCAM
import Obend.Hardware.OpenUSD
import Obend.Hardware.Magnetics
import Obend.Hardware.OpenHypergraph
import Obend.Hardware.DigitalTwin
import Obend.Hardware.UserspacePhysical
import Obend.Tactic.Tooth

namespace Obend.Tests.CoupledPhysicalTest

open Obend.Core.Term (Primitive Term Step Steps Evaluates)
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.GeometryCAM
open Obend.Hardware.OpenUSD
open Obend.Hardware.Magnetics
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.PowerElectronics
open Obend.Hardware.FluidThermal
open Obend.Hardware.Mechanics
open Obend.Hardware.Analog
open Obend.Hardware.DSP
open Obend.Hardware.DigitalTwin
open Obend.Hardware.UserspacePhysical

set_option autoImplicit false
set_option maxHeartbeats 800000

-- ============================================================================
-- 1. Audit Fix 6 Verification
-- ============================================================================

/-- Audit Fix 6: `OpenUSD.lean` is the single canonical OpenUSD model, consuming `UsdArcKind`
and `UsdArcKind.strength` from `GeometryCAM.lean`. -/
theorem test_audit_fix6_canonical_openusd_liverps :
    UsdArcKind.specializesArc.strength < UsdArcKind.payloadArc.strength ∧
    UsdArcKind.payloadArc.strength < UsdArcKind.referencesArc.strength ∧
    UsdArcKind.referencesArc.strength < UsdArcKind.relocatesArc.strength ∧
    UsdArcKind.relocatesArc.strength < UsdArcKind.variantArc.strength ∧
    UsdArcKind.variantArc.strength < UsdArcKind.inheritsArc.strength ∧
    UsdArcKind.inheritsArc.strength < UsdArcKind.localArc.strength := by
  decide +kernel

-- ============================================================================
-- 2. Multi-Limb ($K$-Limb) Ozaki Base-13 `FP4` Tensor-Core Arithmetic (Pillar 2C)
-- ============================================================================

/-- Universal exactness of $K$-limb Base-13 evaluation (`evalBase13Limbs`), addition
(`addBase13Limbs`), scalar scaling (`scaleBase13Limbs`), Cauchy convolution (`mulBase13Limbs`),
and $K$-limb Tensor-Core inner product (`evalOzakiBase13KLimbDot` = `kulischDot`). -/
theorem test_ozaki_base13_klimb_universal
    (xs ys : List Int) (c : Int) (vecsA vecsB : List (List Int)) :
    evalBase13Limbs (addBase13Limbs xs ys) = evalBase13Limbs xs + evalBase13Limbs ys ∧
    evalBase13Limbs (scaleBase13Limbs c xs) = c * evalBase13Limbs xs ∧
    evalBase13Limbs (mulBase13Limbs xs ys) = evalBase13Limbs xs * evalBase13Limbs ys ∧
    evalOzakiBase13KLimbDot vecsA vecsB =
      kulischDot (vecsA.map evalBase13Limbs) (vecsB.map evalBase13Limbs) :=
  ⟨evalBase13Limbs_add_exact xs ys,
   evalBase13Limbs_scale_exact c xs,
   ozaki_base13_klimb_mul_exact xs ys,
   ozaki_base13_klimb_dot_exact vecsA vecsB⟩

/-- Concrete 4-limb and 5-limb Ozaki Base-13 `FP4` inner product verification with
`allLimbsDoubledFp4 = true` (every limb lies in the exact doubled `FP4` (`E2M1`) grid `[-12, 12]`). -/
theorem test_ozaki_klimb_fp4_concrete_4_and_5_limbs :
    let a4 : List Int := [12, -8, 6, -4]
    let b4 : List Int := [-6, 12, -3, 8]
    let a5 : List Int := [8, -12, 4, 6, -2]
    let b5 : List Int := [3, 6, -8, 12, -4]
    allLimbsDoubledFp4 a4 = true ∧
    allLimbsDoubledFp4 b4 = true ∧
    allLimbsDoubledFp4 a5 = true ∧
    allLimbsDoubledFp4 b5 = true ∧
    evalBase13Limbs (mulBase13Limbs a4 b4) = evalBase13Limbs a4 * evalBase13Limbs b4 ∧
    evalBase13Limbs (mulBase13Limbs a5 b5) = evalBase13Limbs a5 * evalBase13Limbs b5 ∧
    evalOzakiBase13KLimbDot [a4, a5] [b4, b5] =
      evalBase13Limbs a4 * evalBase13Limbs b4 + evalBase13Limbs a5 * evalBase13Limbs b5 := by
  decide +kernel

-- ============================================================================
-- 3. Octree pruning regimes
-- ============================================================================

/-- Concrete verification of all 3 octree pruning regimes (`.left` = 1, `.right` = 2, `.both` = 3)
of `GeometryCAM.ivMinChoice`. -/
theorem test_fidget_octree_all_three_regimes :
    (Obend.Hardware.GeometryCAM.ivMinChoice { lo := 4, hi := 8 } { lo := 10, hi := 20 } = FidgetChoice.left) ∧
    (Obend.Hardware.GeometryCAM.ivMinChoice { lo := 26, hi := 30 } { lo := 10, hi := 20 } = FidgetChoice.right) ∧
    (Obend.Hardware.GeometryCAM.ivMinChoice { lo := 11, hi := 15 } { lo := 10, hi := 20 } = FidgetChoice.both) := by
  decide +kernel

-- ============================================================================
-- 4. Coupled Sampled-Data Cyber-Physical Powertrain `DigitalTwin` (Pillar 2B)
-- ============================================================================

/-- Sampled-data current loop ISS contraction, closed-loop multi-domain safety invariant,
and golden `MS350` + LC Drives IPM digital twin trajectory verification. -/
theorem test_digital_twin_iss_and_golden_trajectory
    (spec : PowertrainPlantSpec) (st : PowertrainTwinState)
    (iqRefAmp iq1 iq2 kpPermille qDistAmp : Int)
    (bits vInMv vLsbMv : Nat)
    (hKpPos : 0 < kpPermille)
    (hKpSub : kpPermille < 1000)
    (hOrder : iq2 < iq1)
    (hLsbPos : 0 < vLsbMv) :
    (stepQuantizedCurrentLoop iqRefAmp iq1 kpPermille qDistAmp -
       stepQuantizedCurrentLoop iqRefAmp iq2 kpPermille qDistAmp =
       (1000 - kpPermille) * (iq1 - iq2) ∧
     0 < (1000 - kpPermille) * (iq1 - iq2) ∧
     (1000 - kpPermille) * (iq1 - iq2) < 1000 * (iq1 - iq2) ∧
     (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
     runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits ∧
     (vInMv < 2 ^ bits * vLsbMv →
       vInMv < (runSarAdcN bits 0 vInMv vLsbMv + 1) * vLsbMv)) ∧
    (checkPowertrainTwinSafety spec st = true →
      spec.minShaftTorqueScaled ≤ evalIpmTorqueScaled spec.motor st.idAmp st.iqAmp ∧
      st.tWindingMilliC ≤ spec.maxClassHInsulationMilliC ∧
      st.tMagnetMilliC ≤ spec.maxMagnetDemagMilliC ∧
      0 < st.hotAirGapUm ∧
      spec.minSafeAirGapUm ≤ st.hotAirGapUm ∧
      st.hotAirGapUm ≤ spec.coldAirGapUm ∧
      (evalActiveBalancingStep st.fcmlCapErrMv spec.activeBalGainPermille) *
        (evalActiveBalancingStep st.fcmlCapErrMv spec.activeBalGainPermille) ≤
        st.fcmlCapErrMv * st.fcmlCapErrMv ∧
      checkPartLifecycleInvariant spec.minSafeAirGapUm spec.maxClassHInsulationMilliC
        (toUsdPhysicalState st) = true) :=
  ⟨sampled_data_current_loop_iss_contraction iqRefAmp iq1 iq2 kpPermille qDistAmp
     bits vInMv vLsbMv hKpPos hKpSub hOrder hLsbPos,
   sampled_data_closed_loop_powertrain_safety_invariant spec st⟩

theorem test_golden_ms350_ipm_digital_twin :
    let s0 := goldenTwinState0
    let s1 := stepSampledDataDigitalTwin goldenMs350IpmPlantSpec s0
    let s2 := stepSampledDataDigitalTwin goldenMs350IpmPlantSpec s1
    evalFcmlHarmonicSteinmetzLossW 2 1 50 7 2 = 360 ∧
    runSarAdcN 4 0 950 100 = 9 ∧
    s1.iqAmp = 242 ∧
    s2.iqAmp = 254 ∧
    s1.rotorAngleMrad = 0 ∧
    s1.fcmlCapErrMv = 80 ∧
    s2.fcmlCapErrMv = 64 ∧
    s1.tWindingMilliC = 123737 ∧
    s2.tWindingMilliC = 123953 ∧
    s1.hotAirGapUm = 777 ∧
    s2.hotAirGapUm = 777 ∧
    checkPowertrainTwinSafety goldenMs350IpmPlantSpec s0 = true ∧
    checkPowertrainTwinSafety goldenMs350IpmPlantSpec s1 = true ∧
    checkPowertrainTwinSafety goldenMs350IpmPlantSpec s2 = true ∧
    checkUsdTimeSampleChain 500 180000
      (toUsdPhysicalState s0) [toUsdPhysicalState s1, toUsdPhysicalState s2] = true :=
  golden_ms350_ipm_digital_twin_trajectory_verified

-- ============================================================================
-- 5. `stdlib/physical/*.obend` Elaborated via `#import_obend` in `UserspacePhysical`
-- ============================================================================

/-- All 4 `stdlib/physical/*.obend` packages elaborate at compile time via `#import_obend`,
pass `FrontEnd.accept`, discharge all 5 open-recursion claims, and match the compositions
in `Obend.Hardware.UserspacePhysical` by `rfl`. -/
theorem test_stdlib_physical_obend_packages_and_compositions :
    lcDrivesStatorUsdComp = StdLcDrivesStator.lcDrivesProductionStator_comp ∧
    statorInSlotComp = StdLcDrivesStator.statorInSlot_comp ∧
    ms350PhaseLegComp = StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp ∧
    q3PhotonicComp = StdCleanroomTcadStack.q3KrawtchoukArray_comp ∧
    cleanroomTcadStackComp = StdCleanroomTcadStack.cleanroomTcadStack_comp ∧
    cnc5AxisMillComp = StdCnc5AxisMill.compensated5AxisMill_comp :=
  ⟨lcDrivesStatorUsdComp_eq_imported,
   statorInSlotComp_eq_imported,
   ms350PhaseLegComp_eq_imported,
   q3PhotonicComp_eq_imported,
   cleanroomTcadStackComp_eq_imported,
   cnc5AxisMillComp_eq_imported⟩

/-- Universal parametric evaluation across all 4 `#import_obend`-elaborated open-recursive
physical domain hierarchies (`LcDrivesStator`, `Ms350FcmlPhaseLeg`, `Q3PhotonicCouplerArray`,
`CleanroomTcadStack`). -/
theorem test_four_stdlib_physical_domain_objects_universal
    (loss r currentA diDt margin pIn modeIdx vov fanout : Nat) :
    -- 1. LC Drives In-Slot Stator (`stdlib/physical/LcDrivesStator.obend`)
    Evaluates (.app (.get statorInSlotCore4Object "peakWindingTemp") (.nat loss)) (.nat (50 + loss * 9)) ∧
    Evaluates (.app (.get statorInSlotCore4Object "sdfMargin") (.nat r)) (.nat ((r + 10) + 6)) ∧
    -- 2. MS350 FCML SiC Phase Leg (`stdlib/physical/Ms350FcmlPhaseLeg.obend`)
    Evaluates (.app (.get ms350PhaseLegCore4Object "switchingLossUj") (.nat currentA)) (.nat (currentA * 3 + 120)) ∧
    Evaluates (.app (.get ms350PhaseLegCore4Object "shootThroughSafe") (.nat diDt)) (.boolean (decide (diDt ≤ 80))) ∧
    Evaluates (.app (.get ms350PhaseLegCore4Object "effectiveGateDelayNs") (.nat margin)) (.nat ((margin + 12) + 25)) ∧
    -- 3. Q3 Photonic Coupler Array (`stdlib/physical/CleanroomTcadStack.obend`)
    Evaluates (.app (.get q3PhotonicCore4Object "transferredPowerMw") (.nat pIn)) (.nat (pIn * 7 + 3)) ∧
    Evaluates (.app (.get q3PhotonicCore4Object "krawtchoukPhaseShiftMrad") (.nat modeIdx)) (.nat (modeIdx * 15 + 45)) ∧
    -- 4. Cleanroom-to-TCAD FinFET Stack (`stdlib/physical/CleanroomTcadStack.obend`)
    Evaluates (.app (.get cleanroomTcadCore4Object "drainCurrentUa") (.nat vov)) (.nat (vov * 5 + 250)) ∧
    Evaluates (.app (.get cleanroomTcadCore4Object "gateDelayPs") (.nat fanout)) (.nat ((fanout * 8 + 20) + 4)) :=
  ⟨stator_in_slot_peak_temp_forall loss,
   stator_in_slot_sdf_margin_forall r,
   ms350_switching_loss_forall currentA,
   ms350_shoot_through_safe_forall diDt,
   ms350_gate_delay_forall margin,
   q3_photonic_transferred_power_forall pIn,
   q3_photonic_phase_shift_forall modeIdx,
   cleanroom_tcad_drain_current_forall vov,
   cleanroom_tcad_gate_delay_forall fanout⟩

-- ============================================================================
-- 6. `#tooth` Mutation Proofs
-- ============================================================================

#tooth test_ozaki_klimb_fp4_concrete_4_and_5_limbs by
  mutation mulBase13Limbs := fun xs _ => xs

#tooth test_fidget_octree_all_three_regimes by
  mutation ivMinChoice := fun _ _ => FidgetChoice.both

#tooth test_golden_ms350_ipm_digital_twin by
  mutation evalFcmlHarmonicSteinmetzLossW := fun _ _ _ _ _ => 0

-- ============================================================================
-- 7. Compile-Time Axiom Audit (`0 sorryAx`, `0 custom axioms`, `0 Classical.choice`)
-- ============================================================================

open Lean Elab Command in
elab "#verify_coupled_physical_axioms" : command => do
  let choiceFreeTargets : List Name := [
    ``Obend.Hardware.Accelerators.evalBase13Limbs_add_exact,
    ``Obend.Hardware.Accelerators.evalBase13Limbs_scale_exact,
    ``Obend.Hardware.Accelerators.ozaki_base13_klimb_mul_exact,
    ``Obend.Hardware.Accelerators.ozaki_base13_klimb_dot_exact,
    ``Obend.Hardware.UserspacePhysical.stator_in_slot_peak_temp_forall,
    ``Obend.Hardware.UserspacePhysical.stator_in_slot_sdf_margin_forall,
    ``Obend.Hardware.UserspacePhysical.ms350_switching_loss_forall,
    ``Obend.Hardware.UserspacePhysical.ms350_shoot_through_safe_forall,
    ``Obend.Hardware.UserspacePhysical.ms350_gate_delay_forall,
    ``Obend.Hardware.UserspacePhysical.q3_photonic_transferred_power_forall,
    ``Obend.Hardware.UserspacePhysical.q3_photonic_phase_shift_forall,
    ``Obend.Hardware.UserspacePhysical.cleanroom_tcad_drain_current_forall,
    ``Obend.Hardware.UserspacePhysical.cleanroom_tcad_gate_delay_forall,
    ``test_four_stdlib_physical_domain_objects_universal
  ]
  let standardTargets : List Name := [
    ``Obend.Hardware.DigitalTwin.sampled_data_current_loop_iss_contraction,
    ``Obend.Hardware.DigitalTwin.sampled_data_closed_loop_powertrain_safety_invariant,
    ``Obend.Hardware.DigitalTwin.golden_ms350_ipm_digital_twin_trajectory_verified
  ]
  for t in choiceFreeTargets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    if axs.contains ``Classical.choice then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on Classical.choice"
  let allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for t in standardTargets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    for a in axs do
      if !allowedStandard.contains a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on non-standard axiom {a}"
  logInfo m!"[PASS] CoupledPhysicalTest axiom audit verified: {choiceFreeTargets.length} constructive targets (0 sorryAx, 0 Classical.choice) and {standardTargets.length} standard targets (0 sorryAx, 0 custom axioms)"

#verify_coupled_physical_axioms

end Obend.Tests.CoupledPhysicalTest
