/-
# `tests/silicon_elab/SiliconSelfHostTest.lean` — De Bruijn Proof-Producing `by silicon_simp`, Certified Interval/SOS Bridges & Flagship App #5

Exercises (`0 sorryAx`):
1. **Genuine De Bruijn-Criterion `by silicon_simp` & `by silicon_simp [lem1, ← lem2, ...]`**:
   - Multi-step chained custom equational rewrites (`lem1` -> `lem2` -> `lem3`) indexed in
     `DiscrTrieNode` via arity-tagged Polish paths (`exprToDiscrPath`) and matched via
     `MetaUnify.metaUnifyFuel`,
   - Deep congruence proof reconstruction (`mkCongrArg` / `mkCongrFun` / `mkCongr`) under nested
     applications `wrap (step1 (step0 x))`,
   - Reverse `←` directional rewrites (`by silicon_simp [← h]`),
   - Zone-1 `HwExprCAM` closed & open $\beta$-reduction combined with equational simplification,
   - Core polymorphic `List`, `Option`, `Nat`, and `Bool` rewrites + conjunctions & `↔` goals,
   - Meta-level axiom hygiene assertion verifying **zero `sorryAx`** in reconstructed proof terms!
2. **Certified Interval Subdivision & SOS Soundness Theorems (`Obend.Tactic.SiliconElab`)**:
   - `verifyRealBoundSubdiv_sound`, `verifyRealBoxBoundSubdiv_sound`, and `sos_cert_implies_nonneg`.
3. **Live `#silicon_check` Telemetry & Refusal Poles + `SiliconKernelVerilator`**:
   - Verifies `#silicon_check` acceptance of clean supported declarations and refusal of `sorryAx`,
     ill-typed `#tooth` mutants, and truncated cones, plus `silicon_kernel_verilator_cosim_verified`.
-/
import Lean
import Obend.Tactic.SiliconElab
import Obend.Apps.SiliconKernelVerilator
import Obend.Lower.Inductive
import Obend.Lower.LeanKernel
import Obend.Lower.ExprCAM
import Obend.Lower.MetaUnify
import Obend.Lower.DiscrTreeLUT
import Obend.Lower.SiliconElabFabric
import Obend.Analysis.RealAnalysis
import Obend.Judge.RealAnalysis
import Obend.Analysis.SosLyapunov

namespace Obend.Tests.SiliconSelfHostTest

open Obend.Core.Term
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
open Obend.Lower.DiscrTreeLUT
open Obend.Lower.SiliconElabFabric
open Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
open Obend.Tactic.SiliconElab
open Obend.Apps.SiliconKernelVerilator

/-! ## 1. Genuine Proof-Producing `by silicon_simp` & `by silicon_simp [lem1, ← lem2, ...]` -/

opaque pipeStage0 : Nat → Nat
opaque pipeStage1 : Nat → Nat
opaque pipeStage2 : Nat → Nat
opaque pipeWrap   : Nat → Nat → Nat

/-- Default Zone-3 `DiscrTrieNode` + Zone-1 WHNF equational simplification over symbolic `Nat`s
(zero `omega`/`simp`/`grind` fallback — `pipeWrap` is `opaque`!). -/
theorem test_silicon_simp_nat_and_beta (a b : Nat) :
    pipeWrap ((fun x : Nat => x + 0) (a * 1)) (0 + (b - b)) = pipeWrap a 0 := by
  silicon_simp

/-- Polymorphic `List`, `Option`, and `Bool` equational rewrites with `mkCongr` / `mkCongrArg`. -/
theorem test_silicon_simp_poly_list_option_bool (α β : Type) (f : α → β) (x : α) (xs : List α) (b : Bool) :
    (([x] ++ ([] ++ xs)).length = Nat.succ xs.length) ∧
    (Option.map f (some x) = some (f x)) ∧
    ((!(!b && true) || false) = b) := by
  silicon_simp

/-- Chained 3-step user lemma rewrites (`h0`, `h1`, `h2`) under deep nested congruence! -/
theorem test_silicon_simp_chained_user_lemmas
    (x y : Nat)
    (h0 : ∀ n, pipeStage0 n = pipeStage1 (n + 0))
    (h1 : ∀ n, pipeStage1 n = pipeStage2 (1 * n))
    (h2 : pipeStage2 x = y) :
    pipeWrap (pipeStage0 x) (y + 0) = pipeWrap y y := by
  silicon_simp [h0, h1, h2]

/-- Reverse `←` directional rewrite (`by silicon_simp [← hRev]`) on an `opaque` function! -/
theorem test_silicon_simp_reverse_arrow
    (x z : Nat)
    (hRev : pipeStage2 z = pipeStage0 x) :
    pipeWrap (pipeStage0 (x + 0)) 0 = pipeWrap (pipeStage2 z) 0 := by
  silicon_simp [← hRev]

/-- Propositional `↔` goal closed via `propext` + `iff_of_eq` inside `silicon_simp`. -/
theorem test_silicon_simp_iff_goal (P Q : Prop) (h : P ↔ Q) :
    P ↔ Q := by
  silicon_simp [h]

/-- Hardware Zone-1 WHNF & Zone-3 `DiscrTreeLUT` universally quantified equational checks via `by silicon_simp`. -/
theorem test_silicon_simp_zone1_and_zone3 (n : Nat) :
    (let eClosedBeta := KExpr.app (.lam kNatConst (.lit (.natVal 42))) (.lit (.natVal 7))
     let (hClosedBeta, cam1) := internToHwExprCAM eClosedBeta HwExprCAM.empty
     (stepCamWhnf { cam := cam1, focusHandle := hClosedBeta }).steps = 1) ∧
    ((queryDiscrTrieNode epoch1DiscrTrie
        (exprToDiscrPath 8 (.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal n))))).map
        (·.lutTag) = [101]) ∧
    ((compileDiscrTrieToRtl "tcam_z3" [(101, 4, 2)]).outputs.length = 1) := by
  silicon_simp

-- Compile-time audit: verify via `Lean.collectAxioms` that none of the `by silicon_simp` theorems depend on `sorryAx`!
run_cmd do
  let env ← Lean.getEnv
  let targets :=
    [ ``test_silicon_simp_nat_and_beta
    , ``test_silicon_simp_poly_list_option_bool
    , ``test_silicon_simp_chained_user_lemmas
    , ``test_silicon_simp_reverse_arrow
    , ``test_silicon_simp_iff_goal
    , ``test_silicon_simp_zone1_and_zone3 ]
  for nm in targets do
    if (env.find? nm).isNone then
      Lean.throwError s!"Missing theorem `{nm}`"
    let axs ← Lean.collectAxioms nm
    if axs.contains ``sorryAx then
      Lean.throwError s!"`{nm}` contains sorryAx!"

/-! ## 2. Certified Interval Subdivision & SOS Non-Negativity Theorems (`Obend.Tactic.SiliconElab`) -/

theorem test_interval_subdiv_universal
    (rho : String → CanonicalRat) (hDom : rho "x" ∈ domZeroToTwo) :
    evalExpr rho quadMinusLinearExpr ∈ tightQuadBound :=
  verifyRealBoundSubdiv_sound 3 "x" domZeroToTwo quadMinusLinearExpr tightQuadBound
    (by decide +kernel) rho hDom

theorem test_box_subdiv_universal
    (rho : String → CanonicalRat)
    (hBox : ∀ v I, box2DZeroToTwo.lookup v = some I → rho v ∈ I) :
    evalExpr rho quad2DBoxExpr ∈ tight2DBoxBound :=
  quad2DBox_subdiv_encloses rho hBox

theorem test_sos_universal_nonneg :
    SOSQuery.SemanticMeaning sampleSosNonnegQuery :=
  sampleSosNonneg_holds

/-! ## 3. `#silicon_check` Telemetry, Deep `sorryAx` Refusal Poles & `SiliconKernelVerilator` -/

/-- Host `Lean.ConstantInfo` containing `sorryAx` nested 6 lambdas deep (beyond `maxDepth = 3`). -/
def deepNestedSorryLeanConstInfo : Lean.ConstantInfo :=
  let natC := Lean.mkConst ``Nat
  let sorryLeaf := Lean.mkApp2 (Lean.mkConst ``sorryAx [.succ .zero]) natC (Lean.mkConst ``Bool.false)
  let deepBody :=
    Lean.Expr.lam `x1 natC
      (Lean.Expr.lam `x2 natC
        (Lean.Expr.lam `x3 natC
          (Lean.Expr.lam `x4 natC
            (Lean.Expr.lam `x5 natC
              (Lean.Expr.lam `x6 natC sorryLeaf .default) .default) .default) .default) .default) .default
  let arrow6 :=
    Lean.Expr.forallE `x1 natC
      (Lean.Expr.forallE `x2 natC
        (Lean.Expr.forallE `x3 natC
          (Lean.Expr.forallE `x4 natC
            (Lean.Expr.forallE `x5 natC
              (Lean.Expr.forallE `x6 natC natC .default) .default) .default) .default) .default) .default
  .defnInfo
    { name        := `deepNestedSorryFn
    , levelParams := []
    , type        := arrow6
    , value       := deepBody
    , hints       := .abbrev
    , safety      := .safe }

def cleanIdNatLeanConstInfo : Lean.ConstantInfo :=
  let natC := Lean.mkConst ``Nat
  .defnInfo
    { name        := `cleanIdNatFn
    , levelParams := []
    , type        := Lean.Expr.forallE `x natC natC .default
    , value       := Lean.Expr.lam `x natC (.bvar 0) .default
    , hints       := .abbrev
    , safety      := .safe }

def coneEnvWithSorryHelper : KEnv :=
  { constants   := stdKernelEnv.constants ++ [invalidSorryDecl]
  , recRules    := stdKernelEnv.recRules
  , inductDecls := stdKernelEnv.inductDecls }

run_cmd do
  let env ← Lean.getEnv
  let (_, vSorry) := runSiliconCheckCommandMeta env deepNestedSorryLeanConstInfo none
  let (_, vClean) := runSiliconCheckCommandMeta env cleanIdNatLeanConstInfo none
  if vSorry || !vClean then
    Lean.throwError s!"Expected deepNestedSorry=false ({vSorry}) and cleanIdNat=true ({vClean})"

theorem silicon_self_host_end_to_end_verified (m : String) :
    (.get SiliconKernelBundle.epoch2DprSiliconFabric_comp.flatten m ≈b
      .get SiliconKernelBundle.epoch2DprSiliconFabric_comp.object m) ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty validIdNatDecl).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty validPropIdDecl).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty invalidMismatchDecl).1 = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 invalidMismatchDecl).kernelVerdict = false ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty invalidSorryDecl).1 = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 invalidSorryDecl).kernelVerdict = false ∧
    (runSiliconCheckTelemetry coneEnvWithSorryHelper 8 validPropIdDecl).hasSorryAx = true ∧
    (runSiliconCheckTelemetry coneEnvWithSorryHelper 8 validPropIdDecl).kernelVerdict = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 (extractLeanConstInfoBounded 3 deepNestedSorryLeanConstInfo)).hasSorryAx = true ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 (extractLeanConstInfoBounded 3 deepNestedSorryLeanConstInfo)).kernelVerdict = false ∧
    runVerilatorCoSimModel.status = "PASS" ∧
    runVerilatorCoSimModel.epoch1LutOut = 42#64 ∧
    runVerilatorCoSimModel.epoch2LutOut = 70#64 := by
  have hCosim := silicon_kernel_verilator_cosim_verified m
  refine ⟨hCosim.1, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          hCosim.2.2.1, hCosim.2.2.2.1, hCosim.2.2.2.2.1⟩

#print axioms test_silicon_simp_nat_and_beta
#print axioms test_silicon_simp_poly_list_option_bool
#print axioms test_silicon_simp_chained_user_lemmas
#print axioms test_silicon_simp_reverse_arrow
#print axioms test_silicon_simp_iff_goal
#print axioms test_silicon_simp_zone1_and_zone3
#print axioms Obend.Tactic.SiliconElab.verifyRealBoundSubdiv_sound
#print axioms Obend.Tactic.SiliconElab.verifyRealBoxBoundSubdiv_sound
#print axioms Obend.Tactic.SiliconElab.sos_cert_implies_nonneg
#print axioms Obend.Apps.SiliconKernelVerilator.silicon_kernel_verilator_cosim_verified
#print axioms silicon_self_host_end_to_end_verified

end Obend.Tests.SiliconSelfHostTest
