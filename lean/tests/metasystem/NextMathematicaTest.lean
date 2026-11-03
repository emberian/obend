module
/-
# NextMathematicaTest — End-to-End Verification of WS-S Deliverables

Tests:
1. **Domain-Guarded `AnalyticModel` (`Obend.Analysis.TaylorModel`)**:
   - Canonical validity domains `expValidDomain`, `trigValidDomain`, `ln1pValidDomain`, `sqrt1pValidDomain`,
   - Domain-guarded `tmExpCertified_models`, `tmSinCertified_models`, `tmCosCertified_models`,
     `tmLn1pCertified_models`, `tmSqrt1pCertified_models`,
   - Out-of-domain rejection `analyticModel_domain_guard_rejects_out_of_domain` (e.g. $x = 10$ for `expValidDomain`).
2. **Single-Pass Reverse-Mode AD (`Obend.Analysis.Diff`)**:
   - Canonical single-pass linear-time `gradReverse` (`O(|e|)` on `.sqr` towers),
   - `gradReverse_agrees_with_dual`, `gradReverseAccumulatedIdx_sound`, `gradReverseAccumulated_agrees_with_dual`.
3. **$N$-Dimensional Validated Picard–Lindelöf Flowpipes (`Obend.Analysis.Flowpipe`)**:
   - Multi-variable `evalOdeField`, `evalOdeLieDerivComponent`, `evalOdeJacobian`, `verifyPicardAPriori`,
     `stepPicardValidated` over 1D `thermalCoolingOde` and 2D `coupledOscillatorOde`,
   - `evalOdeField_sound`, `evalOdeLieDerivComponent_sound`, `picard_step_encloses_trajectory`.
4. **Universal Whole-DAG `compileGraphAdjoint_dag_sound` (`Obend.Hardware.OpenHypergraph`)**:
   - `specEdgeLocalPullback`, `accumSpecCotangents`, `specGradEdges`, `CotStateInvariant`,
   - `emitAndAccum_preserves_invariant`, `pullbackHyperEdge_sound`, `compileGraphAdjoint_dag_sound`.
5. **Equality Saturation & Cost-Optimal Adjoint / RTL Extraction (`Obend.Analysis.EqSatHypergraph`)**:
   - `applyEqSatRule_preserves_consistency`, `saturateHyperEGraph_preserves_consistency`,
   - `extractMinCost_improves_cost`, `goldenDiamondAdjoint_eqSat_strict_cost_reduction`,
   - `optimizeAdjointHypergraph_preserves_cotangents`, `eqSat_preserves_eval_and_adjoint`,
   - `eqSat_pipelined_rtl_sound`, `pontryagin_flowpipe_adjoint_eqSat_sound`.
-/
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.EqSatHypergraph
@[expose] public section

namespace Obend.Tests.NextMathematicaTest
open Obend.Analysis
open Obend.Hardware.OpenHypergraph

/-! ## 1. Domain-Guarded `AnalyticModel` Verification -/

theorem test_analyticModel_domain_guards :
    let tenthDom : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    Interval.subset tenthDom expValidDomain = true ∧
    Interval.subset tenthDom trigValidDomain = true ∧
    Interval.subset tenthDom ln1pValidDomain = true ∧
    Interval.subset tenthDom sqrt1pValidDomain = true ∧
    Interval.subset (Interval.ofPoint 10) expValidDomain = false ∧
    Interval.subset (Interval.ofPoint 5) trigValidDomain = false ∧
    Interval.subset (Interval.ofPoint (-1)) ln1pValidDomain = false ∧
    Interval.subset (Interval.ofPoint (-1)) sqrt1pValidDomain = false :=
  analyticModel_domain_guard_rejects_out_of_domain

theorem test_tmCertified_models_tenthDom :
    let tenthDom : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    TaylorModel.Models (AnalyticModel.expFn (R := CanonicalRat)) (tmExpCertified tenthDom) ∧
    TaylorModel.Models (AnalyticModel.sinFn (R := CanonicalRat)) (tmSinCertified tenthDom) ∧
    TaylorModel.Models (AnalyticModel.cosFn (R := CanonicalRat)) (tmCosCertified tenthDom) ∧
    TaylorModel.Models (AnalyticModel.ln1pFn (R := CanonicalRat)) (tmLn1pCertified tenthDom) ∧
    TaylorModel.Models (AnalyticModel.sqrt1pFn (R := CanonicalRat)) (tmSqrt1pCertified tenthDom) := by
  have hDom := analyticModel_domain_guard_rejects_out_of_domain
  exact ⟨ tmExpCertified_models CanonicalRat _ hDom.1
        , tmSinCertified_models CanonicalRat _ hDom.2.1
        , tmCosCertified_models CanonicalRat _ hDom.2.1
        , tmLn1pCertified_models CanonicalRat _ hDom.2.2.1
        , tmSqrt1pCertified_models CanonicalRat _ hDom.2.2.2.1 ⟩

/-! ## 2. Single-Pass Reverse-Mode AD Verification -/

example := @gradReverse_agrees_with_dual
example := @gradReverseAccumulated_agrees_with_dual
example := @gradReverseAccumulatedIdx_sound

/-! ## 3. $N$-Dimensional Validated Picard–Lindelöf Flowpipe Verification -/

example := @evalOdeField_sound
example := @evalOdeLieDerivComponent_sound
example := @verifyPicardAPriori_encloses
example := picard_step_encloses_trajectory

/-! ## 4. Universal Whole-DAG `compileGraphAdjoint_dag_sound` Verification -/

example := @compileGraphAdjoint_dag_sound
example := @pullbackHyperEdge_sound
example := @emitAndAccum_preserves_invariant

/-! ## 5. Verified E-Graph Equality Saturation & Cost-Optimal Extraction Verification -/

example := @applyEqSatRule_preserves_consistency
example := @saturateHyperEGraph_preserves_consistency
example := @extractMinCost_improves_cost
example := goldenDiamondAdjoint_eqSat_strict_cost_reduction
example := @optimizeAdjointHypergraph_preserves_cotangents
example := @eqSat_preserves_eval_and_adjoint
example := eqSat_pipelined_rtl_sound
example := pontryagin_flowpipe_adjoint_eqSat_sound

#print axioms tmExpCertified_models
#print axioms gradReverse_agrees_with_dual
#print axioms picard_step_encloses_trajectory
#print axioms compileGraphAdjoint_dag_sound
#print axioms eqSat_preserves_eval_and_adjoint
#print axioms eqSat_pipelined_rtl_sound
#print axioms pontryagin_flowpipe_adjoint_eqSat_sound

end Obend.Tests.NextMathematicaTest
end
