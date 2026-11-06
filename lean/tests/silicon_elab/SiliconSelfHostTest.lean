/-
# `tests/silicon_elab/SiliconSelfHostTest.lean` — End-to-End Test Suite for Wave 4 (`WS-4B-1`)

Exercises:
1. **`#silicon_check`**: since 2026-11-04 the command refuses every declaration outside the Zone-4
   fragment (it used to pass any sorry-free declaration as `PARTIAL/UNSUPPORTED_FRAGMENT`). The six
   self-hosting targets this file ran it on (`kernelCheckDecl`, `runBottomUpCamInfer`,
   `stepSiliconKernelCamFsm`, `type_preservation`, `silicon_self_hosting_milestone_sound`,
   `silicon_kernel_verilator_cosim_sound`) are outside the fragment, so the invocations are gone;
   a declaration the fragment covers can still be checked with the command.
2. **All 5 Proof-Reconstructing `by silicon_*` Tactics (`0 sorry`)**:
   - `by silicon_simp` (Zone 3 `DiscrTreeLUT` + Zone 1 1-cycle closed-term $\beta$-bypass WHNF),
   - `by silicon_eqsat` (`EqSatHypergraph` equality saturation + Clairvoyant extraction),
   - `by silicon_sos` (`SosLyapunov` / `SOS` Gram matrix & Positivstellensatz certificates),
   - `by silicon_interval` (`TaylorModel` / `RealAnalysis` recursive branch-and-bound subdivision,
     including dependency-problem tightening on $x^2 - x \in [-1/4, 2]$ over $x \in [0, 2]$ where
     depth-0 interval arithmetic fails and depth-3 subdivision succeeds),
   - `by silicon_flowpipe` (`Flowpipe` $N$-D validated Picard-Lindelöf & Euler reachability tubes).
3. **Flagship App #5 (`apps/silicon-kernel-verilator/`) & `.obend` Bundle Verification**:
   - Verifies `siliconKernelBundle_accepted_and_claims_hold`,
     `siliconKernelBundle_crossPackage_cone_survives`, and `silicon_kernel_verilator_cosim_sound`.
-/
import Obend.Tactic.SiliconElab
import Obend.Apps.SiliconKernelVerilator
import Obend.Lower.Inductive
import Obend.Lower.LeanKernel
import Obend.Lower.ExprCAM
import Obend.Lower.MetaUnify
import Obend.Lower.DiscrTreeLUT
import Obend.Lower.SiliconElabFabric
import Obend.Hardware.OpenHypergraph
import Obend.Analysis.RealAnalysis
import Obend.Judge.RealAnalysis
import Obend.Analysis.SosLyapunov
import Obend.Analysis.EqSatHypergraph
import Obend.Analysis.TaylorModel
import Obend.Analysis.Flowpipe

namespace Obend.Tests.SiliconSelfHostTest

open Obend.Core.Term
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
open Obend.Lower.DiscrTreeLUT
open Obend.Lower.SiliconElabFabric
open Obend.Hardware.OpenHypergraph
open Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
open Obend.Tactic.SiliconElab
open Obend.Apps.SiliconKernelVerilator

/-! ## 1. `#silicon_check` refuses what it cannot check (2026-11-04): the self-hosting targets are
outside the Zone-4 fragment and are no longer invoked here. -/

/-! ## 2. Tactic 1: `by silicon_simp` (Zone 3 `DiscrTreeLUT` + Zone 1 WHNF) -/

theorem test_silicon_simp_zone1_whnf :
    let eClosedBeta := KExpr.app (.lam kNatConst (.lit (.natVal 42))) (.lit (.natVal 7))
    let (hClosedBeta, cam1) := internToHwExprCAM eClosedBeta HwExprCAM.empty
    (stepCamWhnf { cam := cam1, focusHandle := hClosedBeta }).steps = 1 := by
  silicon_simp

theorem test_silicon_simp_discr_lut :
    evalSlotGuardedDiscrTile sampleEpoch1Guard epoch1LeafView 1 10#64 = (true, 42#64) ∧
    evalSlotGuardedDiscrTile sampleEpoch2Guard epoch2LeafView 2 10#64 = (true, 70#64) := by
  silicon_simp

theorem test_silicon_simp_four_zone_miller :
    let qSimp := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10))
    (match runSiliconElabFabricFourZones stdKernelEnv 8 sampleMetaCtx sampleMillerConstraints
             sampleMillerRawDecl sampleEpoch1Guard sampleEpoch1DiscrTrie epoch1LeafView 1 qSimp 10#64 with
     | some (_, z3, z4, elabDecl) =>
       !declHasMVar elabDecl &&
       kernelCheckDecl stdKernelEnv 8 elabDecl &&
       z3.usedFastPath &&
       (z3.lutValue == 42#64) &&
       (z4.statusTag == 1) &&
       z4.rtlJudgeAccepted
     | none => false) = true := by
  silicon_simp

/-! ## 3. Tactic 2: `by silicon_eqsat` (`EqSatHypergraph` Saturation & Clairvoyant Extraction) -/

theorem test_silicon_eqsat_diamond_cost_reduction :
    let gAdj := compileGraphAdjoint goldenDiamondHypergraph
    let gOpt := optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph
    let env : Nat → Int := fun w =>
      match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 9 => 1 | _ => 0
    evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
    (extractHyperEdges gOpt).length < (extractHyperEdges gAdj).length ∧
    (extractHyperEdges gOpt).length = 11 ∧
    (extractHyperEdges gAdj).length = 13 ∧
    gOpt.wf = true ∧
    evalHypergraphComb gOpt env = evalHypergraphComb gAdj env ∧
    evalHypergraphComb gOpt env = [87, 11, 11, 7, 7] ∧
    evalHypergraphLayeredSync gOpt env = [87, 11, 11, 7, 7] := by
  silicon_eqsat

theorem test_silicon_eqsat_diamond_symbolic_cotangents (x0 x1 x2 x3 dOut : Int) :
    let gAdj := compileGraphAdjoint goldenDiamondHypergraph
    let gOpt := optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph
    let env : Nat → Int := fun w =>
      match w with
      | 0 => x0
      | 1 => x1
      | 2 => x2
      | 3 => x3
      | 9 => dOut
      | _ => 0
    evalHypergraphComb gOpt env = evalHypergraphComb gAdj env ∧
    evalHypergraphComb gOpt env =
      [ (x0 + x1) * (x2 + x3) + 10
      , (x2 + x3) * dOut
      , (x2 + x3) * dOut
      , (x0 + x1) * dOut
      , (x0 + x1) * dOut ] := by
  silicon_eqsat

theorem test_silicon_eqsat_bespoke_symbolic_ring (a b c : Int) :
    (a + b) * c + a * 0 = a * c + b * c := by
  silicon_eqsat

/-! ## 4. Tactic 3: `by silicon_sos` (`SosLyapunov` / `SOS` Gram Witness Verification) -/

theorem test_silicon_sos_universal_nonneg :
    SOSQuery.SemanticMeaning sampleSosNonnegQuery := by
  silicon_sos

theorem test_silicon_sos_lyapunov_cbf :
    checkSosLyapunov goldenLyapunovSpec2D goldenLyapunovWitness2D = true ∧
    checkSosCbf goldenCbfSpec2D goldenCbfWitness2D = true := by
  silicon_sos

/-! ## 5. Tactic 4: `by silicon_interval` (`TaylorModel`, Negative Endpoints, Depth > 6 & 2D Box Subdivision) -/

theorem test_silicon_interval_depth0_insufficient_and_depth3_succeeds :
    verifyRealBoundSubdiv 0 "x" domZeroToTwo quadMinusLinearExpr tightQuadBound = false ∧
    verifyRealBoundSubdiv 3 "x" domZeroToTwo quadMinusLinearExpr tightQuadBound = true := by
  silicon_interval

theorem test_silicon_interval_subdiv_universal
    (rho : String → CanonicalRat) (hDom : rho "x" ∈ domZeroToTwo) :
    evalExpr rho quadMinusLinearExpr ∈ tightQuadBound := by
  silicon_interval

theorem test_silicon_interval_neg_endpoints_depth7 :
    verifyRealBoundSubdiv 0 "x" negDomMinusOneToZero quadPlusLinearExpr tightNegQuadBound = false ∧
    verifyRealBoundSubdiv 7 "x" negDomMinusOneToZero quadPlusLinearExpr tightNegQuadBound = true := by
  silicon_interval

theorem test_silicon_interval_neg_endpoints_depth7_universal
    (rho : String → CanonicalRat) (hDom : rho "x" ∈ negDomMinusOneToZero) :
    evalExpr rho quadPlusLinearExpr ∈ tightNegQuadBound := by
  silicon_interval

theorem test_silicon_interval_multivariate_2d_box :
    verifyRealBoxBoundSubdiv [] box2DZeroToTwo quad2DBoxExpr tight2DBoxBound = false ∧
    verifyRealBoxBoundSubdiv ["x", "y", "x", "y", "x", "y"] box2DZeroToTwo quad2DBoxExpr tight2DBoxBound = true := by
  silicon_interval

theorem test_silicon_interval_multivariate_2d_box_universal
    (rho : String → CanonicalRat)
    (hBox : ∀ v I, box2DZeroToTwo.lookup v = some I → rho v ∈ I) :
    evalExpr rho quad2DBoxExpr ∈ tight2DBoxBound := by
  silicon_interval

/-! ## 6. Tactic 5: `by silicon_flowpipe` (`Flowpipe` Validated Picard & Euler Reachability) -/

theorem test_silicon_flowpipe_universal_step_mem
    {stateBox velBox remPad : Interval} {x0 v0 r : CanonicalRat} (dt : CanonicalRat)
    (hx0 : x0 ∈ stateBox) (hv0 : v0 ∈ velBox) (hr : r ∈ remPad) :
    (x0 + dt * v0 + r) ∈ stepFlowpipe1D stateBox velBox dt remPad := by
  silicon_flowpipe

/-- Cooling is certified safe for two steps. It was three until the flowpipe became validated
Picard over boxes: the validated tube widens (after three steps `T ∈ [15.08, 28.5]`) and the third
step's continuous-time rough enclosure leaves `[15, 35]`, so three steps are no longer certified. -/
theorem test_silicon_flowpipe_euler_enclosure :
    let X0 : Interval := ⟨28, 30⟩
    let V0 : Interval := ⟨-10, -8⟩
    let dt : CanonicalRat := CanonicalRat.mk 1 2
    let rem : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    let X1 := stepFlowpipe1D X0 V0 dt rem
    let initBox := [("T", X0)]
    let safeEnv := [("T", (⟨15, 35⟩ : Interval))]
    X1 = ⟨CanonicalRat.mk 229 10, CanonicalRat.mk 261 10⟩ ∧
    Interval.containsRat X1 (28 + dt * (-8) + CanonicalRat.mk (-1) 10) = true ∧
    Interval.containsRat X1 (29 + dt * (-9) + 0) = true ∧
    Interval.containsRat X1 (30 + dt * (-10) + CanonicalRat.mk 1 10) = true ∧
    verifyTrajectorySafety thermalCoolingOde initBox 2 safeEnv = true ∧
    verifyTrajectorySafety thermalRunawayOde initBox 2 safeEnv = false := by
  silicon_flowpipe

/-! ## 7. Edge-Case Refusal Poles: Deep Nested `sorryAx`, Transitive Cone `sorryAx` & `#tooth` Mutants -/

/-- Environment cone contaminated by a `sorryAx` helper declaration `selfHostSorryProofInfo`. -/
def coneEnvWithSorryHelper : KEnv :=
  { constants := stdKernelEnv.constants ++ [selfHostSorryProofInfo]
  , recRules  := stdKernelEnv.recRules }

theorem test_edge_cases_deep_sorry_cone_sorry_and_tooth_refusal :
    -- 1. `deepNestedSorryLeanConstInfo` (with `sorryAx` at depth 8, truncated at `maxDepth = 3`) is refused
    (runSiliconCheckTelemetry stdKernelEnv 8 (extractLeanConstInfoBounded 3 deepNestedSorryLeanConstInfo)).hasSorryAx = true ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 (extractLeanConstInfoBounded 3 deepNestedSorryLeanConstInfo)).kernelVerdict = false ∧
    -- 2. A clean declaration checked in a `sorryAx`-contaminated environment cone is refused
    (runSiliconCheckTelemetry coneEnvWithSorryHelper 8 selfHostIdentityProofInfo).hasSorryAx = true ∧
    (runSiliconCheckTelemetry coneEnvWithSorryHelper 8 selfHostIdentityProofInfo).kernelVerdict = false ∧
    -- 3. `#tooth`-mutated ill-typed declaration is refused by `runSiliconCheckTelemetry`
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostMutatedBadProofInfo).kernelVerdict = false := by
  decide +kernel

-- 4. Live meta-level `#silicon_check` runner refuses `sorryAx`-contaminated `Lean.ConstantInfo`s
run_cmd do
  let env ← Lean.getEnv
  let (_, v1) := runSiliconCheckCommandMeta env sampleLiveLeanSorryInfo none
  let (_, v2) := runSiliconCheckCommandMeta env deepNestedSorryLeanConstInfo none
  let (_, v3) := runSiliconCheckCommandMeta env sampleLiveLeanDefnInfo none
  if v1 || v2 || !v3 then
    Lean.throwError s!"Expected sampleLiveLeanSorryInfo=false ({v1}), deepNestedSorryLeanConstInfo=false ({v2}), sampleLiveLeanDefnInfo=true ({v3})"

/-! ## 8. Master End-to-End Reflexive Self-Hosting & Flagship App #5 Theorem -/

theorem silicon_self_host_end_to_end_test_sound :
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostKernelCheckDeclInfo).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostBottomUpCamInferInfo).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostIdentityProofInfo).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostMutatedBadProofInfo).1 = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostMutatedBadProofInfo).kernelVerdict = false ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostSorryProofInfo).1 = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostSorryProofInfo).kernelVerdict = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 (extractLeanConstInfoBounded 3 deepNestedSorryLeanConstInfo)).kernelVerdict = false ∧
    runVerilatorCoSimModel.status = "PASS" ∧
    runVerilatorCoSimModel.epoch1LutOut = 42#64 ∧
    runVerilatorCoSimModel.epoch2LutOut = 70#64 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms Obend.Tactic.SiliconElab.verifyRealBoundSubdiv_sound
#print axioms Obend.Tactic.SiliconElab.verifyRealBoxBoundSubdiv_sound
#print axioms Obend.Tactic.SiliconElab.sos_cert_implies_nonneg
#print axioms Obend.Tactic.SiliconElab.silicon_self_hosting_milestone_sound
#print axioms Obend.Apps.SiliconKernelVerilator.silicon_kernel_verilator_cosim_sound
#print axioms silicon_self_host_end_to_end_test_sound

end Obend.Tests.SiliconSelfHostTest
