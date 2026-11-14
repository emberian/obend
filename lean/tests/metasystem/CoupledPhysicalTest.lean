/-
# `tests/metasystem/CoupledPhysicalTest.lean` — End-to-End Verification of WS-R:
# 1. The canonical OpenUSD model (audit fix 6)
# 2. Multi-Limb ($K$-Limb) Ozaki Base-13 `FP4` integer identities (`Obend.Hardware.Accelerators`)
# 3. Octree pruning regimes (`GeometryCAM.ivMinChoice`)
# 4. Grounded Sampled-Data ZOH Current-Loop ISS Ball (`Obend.Hardware.CurrentLoop`)
-/
import Lean
import Obend.Hardware.Accelerators
import Obend.Hardware.GeometryCAM
import Obend.Hardware.OpenUSD
import Obend.Hardware.Magnetics
import Obend.Hardware.OpenHypergraph
import Obend.Hardware.CurrentLoop
import Obend.Hardware.Analog
import Obend.Hardware.DSP
import Obend.Tactic.Tooth

namespace Obend.Tests.CoupledPhysicalTest

open Obend.Core.Term (Primitive Term Step Steps Evaluates)
open Obend.Analysis (CanonicalRat)
open Obend.Hardware.HDL
open Obend.Hardware.Accelerators
open Obend.Hardware.GeometryCAM
open Obend.Hardware.OpenUSD
open Obend.Hardware.Magnetics
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.CurrentLoop
open Obend.Hardware.Analog
open Obend.Hardware.DSP

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

theorem test_fidget_octree_all_three_regimes :
    (Obend.Hardware.GeometryCAM.ivMinChoice { lo := 4, hi := 8 } { lo := 10, hi := 20 } = FidgetChoice.left) ∧
    (Obend.Hardware.GeometryCAM.ivMinChoice { lo := 26, hi := 30 } { lo := 10, hi := 20 } = FidgetChoice.right) ∧
    (Obend.Hardware.GeometryCAM.ivMinChoice { lo := 11, hi := 15 } { lo := 10, hi := 20 } = FidgetChoice.both) := by
  decide +kernel

-- ============================================================================
-- 4. Grounded Sampled-Data ZOH Current-Loop ISS Ball (`Obend.Hardware.CurrentLoop`)
-- ============================================================================

theorem test_quantized_current_loop_lsb_and_iss_ball
    (kpMilli kiMilli kpQ32 kiQ32 errMa intMv : Int)
    (d : ZohRl)
    (ha : d.a ∈ (⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩ : Obend.Analysis.Interval))
    (hb : d.b ∈ (⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩ : Obend.Analysis.Interval))
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (rMa vffMv : Int) (qs0 : QuantizedLoopState) :
    (let (int', v) := rtlPiStep kpMilli kiMilli errMa intMv
     1000 * (int' - intMv) ≤ errMa * kiMilli ∧
     errMa * kiMilli < 1000 * (int' - intMv) + 1000 ∧
     1000 * (v - int') ≤ errMa * kpMilli ∧
     errMa * kpMilli < 1000 * (v - int') + 1000) ∧
    (let (intQ, vQ) := rtlPiStepQ32 kpQ32 kiQ32 errMa intMv
     4294967296 * (intQ - intMv) ≤ errMa * kiQ32 ∧
     errMa * kiQ32 < 4294967296 * (intQ - intMv) + 4294967296 ∧
     4294967296 * (vQ - intQ) ≤ errMa * kpQ32 ∧
     errMa * kpQ32 < 4294967296 * (vQ - intQ) + 4294967296) ∧
    (let r := ratMilli rMa
     let vff := ratMilli vffMv
     let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
       let s := (iterateQuantizedRtlLoop d 400 50 rMa vffMv k qs0).toLoopState
       (errX r s, errZ d r vff s)
     (quadForm lcP11 lcP12 lcP22 (traj 0).1 (traj 0).2 ≤ lcIssBallRadius →
       ∀ k, quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 ≤ lcIssBallRadius) ∧
     (∀ k, lcM * ((traj k).1 * (traj k).1) ≤
       ratPow lcRhoIss k * (lcC * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + lcIssBallRadius)) :=
  let hIss := lc_drives_quantized_current_loop_iss_ball d ha hb hbR rMa vffMv qs0
  ⟨rtlPiStep_within_lsb kpMilli kiMilli errMa intMv,
   rtlPiStepQ32_within_lsb kpQ32 kiQ32 errMa intMv,
   hIss.2.2.1, hIss.2.2.2⟩

-- ============================================================================
-- 5. `#tooth` Mutation Proofs
-- ============================================================================

#tooth Obend.Hardware.Accelerators.ozaki_base13_klimb_mul_exact by
  mutation Obend.Hardware.Accelerators.mulBase13Limbs := fun xs _ => xs

#tooth Obend.Hardware.CurrentLoop.rtlPiStep_within_lsb by
  mutation Obend.Hardware.CurrentLoop.rtlPiStep := fun _ _ _ intMv => (intMv + 2, intMv + 2)

-- ============================================================================
-- 6. Compile-Time Axiom Audit (`0 sorryAx`, `0 custom axioms`, `0 Classical.choice`)
-- ============================================================================

open Lean Elab Command in
elab "#verify_coupled_physical_axioms" : command => do
  let choiceFreeTargets : List Name := [
    ``Obend.Hardware.Accelerators.evalBase13Limbs_add_exact,
    ``Obend.Hardware.Accelerators.evalBase13Limbs_scale_exact,
    ``Obend.Hardware.Accelerators.ozaki_base13_klimb_mul_exact,
    ``Obend.Hardware.Accelerators.ozaki_base13_klimb_dot_exact
  ]
  let standardTargets : List Name := [
    ``Obend.Hardware.CurrentLoop.rtlPiStep_within_lsb,
    ``Obend.Hardware.CurrentLoop.rtlPiStepQ32_within_lsb,
    ``Obend.Hardware.CurrentLoop.discrete_lyapunov_iss_ball,
    ``Obend.Hardware.CurrentLoop.quantized_current_loop_iss_ball,
    ``Obend.Hardware.CurrentLoop.lc_drives_quantized_current_loop_iss_ball
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
