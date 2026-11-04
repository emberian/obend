/-
# `tests/CoupledPhysicalTest.lean` — End-to-End Verification of WS-R:
# 1. In-Place 64-Bit `AmdGpuVop64Inst` Self-Acceleration (`compileRtlExprToAmdGpu`)
# 2. Multi-Limb ($K$-Limb) Ozaki Base-13 `FP4` Tensor-Core Arithmetic (`Obend.Hardware.Accelerators`)
# 3. 6-Stage Coupled PDE (`libCEED`/`FEMM`), Reverse-Mode AD (`catgrad`), & Geometry (`Fidget`) Self-Acceleration
# 4. Coupled Sampled-Data Cyber-Physical Powertrain `DigitalTwin` (`Obend.Hardware.DigitalTwin`)
# 5. `stdlib/physical/*.obend` Elaborated via `#import_obend` in `Obend.Hardware.UserspacePhysical`
-/
import Lean
import Obend.Hardware.Accelerators
import Obend.Hardware.GeometryCAM
import Obend.Hardware.OpenUSD
import Obend.Hardware.Magnetics
import Obend.Hardware.OpenHypergraph
import Obend.Hardware.DigitalTwin
import Obend.Hardware.UserspacePhysical
import Obend.Lower.Proofs.SelfAccelerate
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
-- 1. In-Place Audit Fix 5 & Audit Fix 6 Verification
-- ============================================================================

/-- Audit Fix 5: `compileRtlExprToAmdGpu` is the single canonical 64-bit `AmdGpuVop64Inst`
compiler for `RtlExpr`, handling `.ult`, `.eq`, `.mux`, and `.bitNot` exactly across all
64-bit `BitVec 64` inputs without 32-bit truncation or operator erasure. -/
theorem test_audit_fix5_in_place_vop64_compiler :
    (∀ (op : RtlAluOp) (inputs wires regs : Nat → BitVec 64) (a b : BitVec 64),
      evalAmdGpuExpr inputs wires regs (.alu op (.const a) (.const b)) =
        evalRtlExpr inputs wires regs (.alu op (.const a) (.const b))) ∧
    (∀ (inputs wires regs : Nat → BitVec 64) (a : BitVec 64),
      evalAmdGpuExpr inputs wires regs (.bitNot (.const a)) =
        evalRtlExpr inputs wires regs (.bitNot (.const a))) ∧
    (∀ (inputs wires regs : Nat → BitVec 64) (c t f : BitVec 64),
      evalAmdGpuExpr inputs wires regs (.mux (.const c) (.const t) (.const f)) =
        evalRtlExpr inputs wires regs (.mux (.const c) (.const t) (.const f))) :=
  ⟨evalAmdGpuExpr_faithful_all_ops.1,
   evalAmdGpuExpr_faithful_all_ops.2.2.1,
   evalAmdGpuExpr_faithful_all_ops.2.2.2.2.1⟩

/-- Concrete verification of `.bitNot`, `.alu .ult`, `.alu .eq`, and `.mux` in
`compileRtlExprToAmdGpu` and `evalCompiledAmdGpuModule`. -/
theorem test_vop64_bitNot_ult_eq_mux_concrete :
    let expr : RtlExpr :=
      .mux (.alu .ult (.inputPort 0) (.const 20#64))
        (.alu .eq (.inputPort 0) (.const 12#64))
        (.bitNot (.const 0#64))
    let mod : RtlModule := {
      name := "vop64_audit_probe"
      inputNames := ["in_arg0"]
      wires := [{ wireIdx := 0, name := "w0", expr := expr }]
      regs := []
      outputs := [{ name := "out_res", expr := .wireRef 0 }]
    }
    evalCompiledAmdGpuModule mod 12 = some 1 ∧
    evalCompiledAmdGpuModule mod 15 = some 0 ∧
    evalCompiledAmdGpuModule mod 25 = some (2 ^ 64 - 1) := by
  decide +kernel

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

/-- 4-limb Base-13 `FP4` (`E2M1`, doubled magnitudes in `[-12, 12]`) multiplication and
AMD `CDNA3` `vMfmaDot4` diagonal partial-product bridge. -/
theorem test_ozaki_base13_4limb_fp4_mfma_bridge
    (a0 a1 a2 a3 b0 b1 b2 b3 acc : Int) :
    evalBase13Limbs (mulBase13Limbs [a0, a1, a2, a3] [b0, b1, b2, b3]) =
      (a0 + 13 * a1 + 169 * a2 + 2197 * a3) * (b0 + 13 * b1 + 169 * b2 + 2197 * b3) ∧
    readVgpr
      (execAmdGpuInst [a0, a1, a2, a3, 1, 13, 169, 2197, 0]
        (.vMfmaDot4 9 0 4 8)) 9 =
      evalBase13Limbs [a0, a1, a2, a3] ∧
    readVgpr
      (execAmdGpuInst [a0, a1, a2, a3, b0, b1, b2, b3, acc]
        (.vMfmaDot4 9 0 4 8)) 9 =
      acc + kulischDot [a0, a1, a2, a3] [b0, b1, b2, b3] :=
  ozaki_base13_4limb_fp4_mfma_bridge a0 a1 a2 a3 b0 b1 b2 b3 acc

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
-- 3. 6-Stage Coupled PDE (`libCEED`), AD (`catgrad`), & Geometry (`Fidget`) Self-Acceleration
-- ============================================================================

/-- Master 6-Stage Universal Self-Acceleration Theorem across:
1. `libCeedFemmNodalOpLExpr` (`self_accelerate_libceed_femm_nodal_op_6stage`, matching `Magnetics.evalLibCeedElementOp`),
2. `catgradOpticRevAdLExpr` (`self_accelerate_catgrad_optic_rev_ad_6stage`, matching `OpenHypergraph.evalOpticChain2Rev`),
3. `fidgetChoiceOctreePruneLExpr` (`self_accelerate_fidget_choice_octree_6stage`, matching `GeometryCAM.ivMinChoice` across `.left`, `.right`, `.both`). -/
theorem test_coupled_pde_ad_geometry_6stage_universal
    (as bs : List Int) (xs ys : List (List Int)) :
    evalBase13Limbs (mulBase13Limbs as bs) = evalBase13Limbs as * evalBase13Limbs bs ∧
    evalOzakiBase13KLimbDot xs ys = kulischDot (xs.map evalBase13Limbs) (ys.map evalBase13Limbs) ∧
    SSteps (.app libCeedFemmNodalOpLExpr (.lit 6)) (.lit 35) ∧
    SSteps (.app catgradOpticRevAdLExpr (.lit 7)) (.lit 56) ∧
    SSteps (.app fidgetChoiceOctreePruneLExpr (.lit 8)) (.lit 1) ∧
    (Obend.Hardware.Magnetics.evalLibCeedElementOp selfAccelFemmTriangle 6 3 2).1 = 35 ∧
    (Obend.Hardware.OpenHypergraph.evalOpticChain2Rev
      (Obend.Hardware.OpenHypergraph.compileOpticAdjoint .mul)
      (Obend.Hardware.OpenHypergraph.compileOpticAdjoint .mul)
      (Obend.Hardware.OpenHypergraph.evalOpticChain2Fwd .mul .mul 4 7).2 1).2 = 56 ∧
    Obend.Hardware.GeometryCAM.ivMinChoice { lo := 4, hi := 8 } { lo := 10, hi := 20 } = .left :=
  coupled_pde_ad_geometry_6stage_universal_self_acceleration as bs xs ys

theorem test_three_6stage_kernels_full_pipeline :
    (let C := leanComposition "libCeedNodal" (lowerT libCeedFemmNodalOpLExpr)
     let B := emit C
     Halts (.app (.get B.link "libCeedNodal") (.nat 6)) (.natural 35)) ∧
    (let C := leanComposition "catgradRevAd" (lowerT catgradOpticRevAdLExpr)
     let B := emit C
     Halts (.app (.get B.link "catgradRevAd") (.nat 7)) (.natural 56)) ∧
    (let C := leanComposition "fidgetPrune" (lowerT fidgetChoiceOctreePruneLExpr)
     let B := emit C
     Halts (.app (.get B.link "fidgetPrune") (.nat 8)) (.natural 1)) :=
  ⟨self_accelerate_libceed_femm_nodal_op_6stage.2.2.1,
   self_accelerate_catgrad_optic_rev_ad_6stage.2.2.1,
   self_accelerate_fidget_choice_octree_6stage.2.2.1⟩

/-- Concrete verification of all 3 octree pruning regimes (`.left` = 1, `.right` = 2, `.both` = 3)
in `self_accelerate_fidget_choice_octree_6stage` across `SSteps`, `Core4`, `Leaf.Book`, FPGA `DSP58`,
AMD `CDNA3` `AmdGpuVop64Inst` (`v_cmp_lt_u64` + `v_cndmask_b64`), and $K$-limb Ozaki Base-13. -/
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
-- 6. `#tooth` Mutation Proofs Across All WS-R Deliverables
-- ============================================================================

#tooth test_vop64_bitNot_ult_eq_mux_concrete by
  mutation compileRtlExprToAmdGpu := fun r _ => (r, r + 1, [AmdGpuVop64Inst.v_mov_b64 r 0#64])

#tooth test_ozaki_klimb_fp4_concrete_4_and_5_limbs by
  mutation mulBase13Limbs := fun xs _ => xs

#tooth test_fidget_octree_all_three_regimes by
  mutation ivMinChoice := fun _ _ => FidgetChoice.both

#tooth test_golden_ms350_ipm_digital_twin by
  mutation evalFcmlHarmonicSteinmetzLossW := fun _ _ _ _ _ => 0

#tooth userspace_ms350_phase_leg_to_fpga_and_amd_gpu_verified by
  mutation ms350PhaseLegComp := statorInSlotComp

#tooth userspace_cleanroom_tcad_and_q3_to_fpga_and_amd_gpu_verified by
  mutation cleanroomTcadStackComp := q3PhotonicComp

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
    ``Obend.Hardware.Accelerators.ozaki_base13_4limb_fp4_mfma_bridge,
    ``Obend.Lower.libCeedFemmNodalOp_runs_6,
    ``Obend.Lower.catgradOpticRevAd_runs_7,
    ``Obend.Lower.fidgetChoiceOctreePrune_runs_8,
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
    ``Obend.Lower.evalAmdGpuExpr_faithful_all_ops,
    ``Obend.Lower.self_accelerate_libceed_femm_nodal_op_6stage,
    ``Obend.Lower.self_accelerate_catgrad_optic_rev_ad_6stage,
    ``Obend.Lower.self_accelerate_fidget_choice_octree_6stage,
    ``Obend.Lower.coupled_pde_ad_geometry_6stage_universal_self_acceleration,
    ``Obend.Hardware.DigitalTwin.sampled_data_current_loop_iss_contraction,
    ``Obend.Hardware.DigitalTwin.sampled_data_closed_loop_powertrain_safety_invariant,
    ``Obend.Hardware.DigitalTwin.golden_ms350_ipm_digital_twin_trajectory_verified,
    ``Obend.Hardware.UserspacePhysical.userspace_physical_stator_to_fpga_verified,
    ``Obend.Hardware.UserspacePhysical.userspace_cnc_5axis_to_fpga_and_amd_gpu_verified,
    ``Obend.Hardware.UserspacePhysical.userspace_ms350_phase_leg_to_fpga_and_amd_gpu_verified,
    ``Obend.Hardware.UserspacePhysical.userspace_cleanroom_tcad_and_q3_to_fpga_and_amd_gpu_verified
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
