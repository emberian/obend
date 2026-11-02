/-
# `tests/metasystem/ClairvoyantAndCostTest.lean` — Executable Clairvoyant Call-by-Need Oracle,
# Sands Improvement Algebra, Fold Collapse Cost Reduction & Quantitative Sharing Cost Judge

End-to-end verification of `WS-K`:
1. **`Obend.Equiv.Clairvoyant` & `Obend.Equiv.Ahead` — Executable Clairvoyant Minimum-Cost Evaluator**:
   - `evalClairvoyantMinCost : Nat → Term → Option (Term × Nat)` and `evalCBV : Nat → Term → Option (Term × Nat)`.
   - `evalClairvoyantMinCost_sound`, `evalClairvoyantMinCost_value_sound`, `evalClairvoyantMinCost_skip_app_sound`.
   - `evalClairvoyant_skip_unused_arg_saves_cost`: constant function `λ x => .nat 42` skips any expensive or
     divergent argument at cost `2` (`1` for `Skip` + `1` for β).
   - `ahead_sharing_saves_duplicate_cost` & `cv_dupAdd_shared`: call-by-need sharing on `λ x => x + x`.

2. **`Obend.Equiv.Improvement` & `Obend.Fold.Collapse` — Sands Improvement Algebra & Collapse Tick Reduction**:
   - `EvalImproves`, `SandsImproves`, `StrictEvalImproves` reflexivity and transitivity.
   - `beta_value_improves_cost`, `evalCBV_beta_value_improves_cost`, `beta_demanded_evalImproves`.
   - `collapse_reduces_ticks` and `collapse_extend_reduces_ticks`.

3. **`Obend.Judge.Cost` & `Obend.Judge.LayeredCost` — Clairvoyant Sharing Cost Certificate**:
   - `SharingCostCert`, `verifySharingCostCert`, `verifySharingCostCert_sound`, `sharingCostJudge`.
   - `LayeredSharingCostCert`, `verifyLayeredSharingCostCert`, `verifyLayeredSharingCostCert_sound`.
-/
import Obend.Equiv.Clairvoyant
import Obend.Equiv.Ahead
import Obend.Equiv.Improvement
import Obend.Equiv.Cost
import Obend.Fold.Collapse
import Obend.Judge.Cost
import Obend.Judge.LayeredCost

namespace Obend.Tests.ClairvoyantAndCostTest

open Obend.Core.Term
open Obend.Equiv
open Obend.Fold.Collapse
open Obend.Judge
open Obend.Judge.Cost
open Obend.Judge.LayeredCost

set_option autoImplicit false

-- ============================================================================
-- 1. Executable Clairvoyant Minimum-Cost Evaluator: Values, Skip vs. Let′, Project & Case
-- ============================================================================

/-- Closed values evaluate to themselves at cost 0 under `evalClairvoyantMinCost`. -/
theorem test_clairvoyant_values_zero_cost :
    evalClairvoyantMinCost 0 (.nat 42) = some (.nat 42, 0) ∧
    evalClairvoyantMinCost 0 (.boolean true) = some (.boolean true, 0) ∧
    evalClairvoyantMinCost 0 (.label "ok") = some (.label "ok", 0) ∧
    evalClairvoyantMinCost 0 (.lam (.bound 0)) = some (.lam (.bound 0), 0) ∧
    evalClairvoyantMinCost 0 (.record [("x", .nat 7), ("y", .boolean false)]) =
      some (.record [("x", .nat 7), ("y", .boolean false)], 0) ∧
    evalClairvoyantMinCost 0 (.inject "some" (.nat 9)) =
      some (.inject "some" (.nat 9), 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (evalClairvoyantMinCost_value_sound (.nat 42) 0).1
  · exact (evalClairvoyantMinCost_value_sound (.boolean true) 0).1
  · exact (evalClairvoyantMinCost_value_sound (.label "ok") 0).1
  · exact (evalClairvoyantMinCost_value_sound (.lam (.bound 0)) 0).1
  · have hrec : CValue (.record [("x", .nat 7), ("y", .boolean false)]) := by
      refine .record ?_
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact .value (.nat 7)
      · exact .value (.boolean false)
    exact (evalClairvoyantMinCost_value_sound hrec 0).1
  · exact (evalClairvoyantMinCost_value_sound (.inject "some" (.value (.nat 9))) 0).1

/-- An expensive arithmetic tree: `((10 + 20) + (30 + 40))` costs 3 ticks to evaluate in CBV. -/
def expensiveArith : Term :=
  .binary .add (.binary .add (.nat 10) (.nat 20)) (.binary .add (.nat 30) (.nat 40))

theorem expensiveArith_not_settled : ¬ Settled expensiveArith := by
  intro h
  cases h with
  | value hv => cases hv

/-- Unused-argument `Skip`: applying `λ x => .nat 42` to `expensiveArith` costs `2` in
`evalClairvoyantMinCost` (via `Skip`), whereas `evalCBV` pays `5` (`3` for `expensiveArith` + `2`),
and applying `λ x => .nat 42` to a stuck/divergent term `(.get skipped "missing")` still succeeds
at cost `2` in `evalClairvoyantMinCost` while failing (`none`) in `evalCBV`. -/
theorem test_skip_unused_arg_vs_cbv :
    evalClairvoyantMinCost 5 (.app (.lam (.nat 42)) expensiveArith) = some (.nat 42, 2) ∧
    CV (.app (.lam (.nat 42)) expensiveArith) (.nat 42) 2 ∧
    evalCBV 5 (.app (.lam (.nat 42)) expensiveArith) = some (.nat 42, 5) ∧
    evalClairvoyantMinCost 5 (.app (.lam (.nat 42)) (.get skipped "missing")) = some (.nat 42, 2) ∧
    evalCBV 5 (.app (.lam (.nat 42)) (.get skipped "missing")) = none := by
  have hskip := evalClairvoyant_skip_unused_arg_saves_cost expensiveArith expensiveArith_not_settled 4
  have hstuck_ns : ¬ Settled (.get skipped "missing") := by
    intro h; cases h with | value hv => cases hv
  have hskip_stuck := evalClairvoyant_skip_unused_arg_saves_cost (.get skipped "missing") hstuck_ns 4
  have hcbv_arith : evalCBV 4 expensiveArith = some (.nat 100, 3) :=
    optTermNatBeq_sound (by decide +kernel)
  have hvs := cv_skip_vs_cbv_unused_arg expensiveArith_not_settled hcbv_arith
  have hcbv_none : evalCBV 5 (.app (.lam (.nat 42)) (.get skipped "missing")) = none :=
    optTermNatBeq_sound (by decide +kernel)
  exact ⟨hskip.1, hskip.2, hvs.2.1, hskip_stuck.1, hcbv_none⟩

/-- Soundness on β-redexes via `evalClairvoyantMinCost_skip_app_sound`. -/
theorem test_skip_app_sound (a : Term) :
    ∃ v' k', evalClairvoyantMinCost 2 (.app (.lam (.nat 99)) a) = some (v', k') ∧
      k' ≤ 2 ∧ CV (.app (.lam (.nat 99)) a) v' k' := by
  have hinst : instantiate (.nat 99) skipped = .nat 99 := by
    simp [instantiate, Term.substitute]
  have hskip : evalClairvoyantMinCost 1 (instantiate (.nat 99) skipped) = some (.nat 99, 0) := by
    rw [hinst]
    exact (evalClairvoyantMinCost_value_sound (.nat 99) 1).1
  simpa using evalClairvoyantMinCost_skip_app_sound (.nat 99) a (.nat 99) 0 1 hskip

/-- Used-argument `Let′` on `dupAdd` (`λ x => x + x`): evaluates `expensiveArith` once (cost 3),
binds `.nat 100` (+1), and adds `100 + 100` (+1) plus β (+1) for total cost `6` (`3 + 3`). -/
theorem test_used_arg_let_prime_sharing :
    evalClairvoyantMinCost 6 (.app dupAdd expensiveArith) = some (.nat 200, 6) ∧
    CV (.app dupAdd expensiveArith) (.nat 200) 6 := by
  have heval : evalClairvoyantMinCost 6 (.app dupAdd expensiveArith) = some (.nat 200, 6) :=
    optTermNatBeq_sound (by decide +kernel)
  exact ⟨heval, evalClairvoyantMinCost_sound 6 _ _ _ heval⟩

/-- `.project` and `.case` (both with literal `.inject` and non-literal `.app` scrutinees,
with used payload and skipped payload) in `evalClairvoyantMinCost` vs `evalCBV`. -/
theorem test_project_and_case_clairvoyant :
    evalClairvoyantMinCost 4 (.project (.prototype (.label "spec") (.nat 77))) = some (.nat 77, 1) ∧
    evalClairvoyantMinCost 5
      (.case (.inject "val" expensiveArith) [("val", .nat 11), ("other", .bound 0)]) =
      some (.nat 11, 3) ∧
    evalClairvoyantMinCost 5
      (.case (.inject "val" expensiveArith) [("val", .bound 0), ("other", .nat 0)]) =
      some (.nat 100, 6) ∧
    evalClairvoyantMinCost 6
      (.case (.app (.lam (.inject "val" expensiveArith)) (.nat 0)) [("val", .nat 11), ("other", .bound 0)]) =
      some (.nat 11, 4) ∧
    evalCBV 6
      (.case (.app (.lam (.inject "val" expensiveArith)) (.nat 0)) [("val", .nat 11), ("other", .bound 0)]) =
      some (.nat 11, 7) :=
  ⟨optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel)⟩

/-- Selective skipping of unused fields/components in unsettled `.record`, `.prototype`, and `.specification`
in `evalClairvoyantMinCost` vs `evalCBV`. -/
theorem test_demand_hint_record_proto_spec :
    evalClairvoyantMinCost 6 (.get (.record [("a", expensiveArith), ("b", .nat 7)]) "b") = some (.nat 7, 5) ∧
    evalCBV 6 (.get (.record [("a", expensiveArith), ("b", .nat 7)]) "b") = some (.nat 7, 8) ∧
    evalClairvoyantMinCost 6 (.project (.prototype expensiveArith (.nat 77))) = some (.nat 77, 3) ∧
    evalCBV 6 (.project (.prototype expensiveArith (.nat 77))) = some (.nat 77, 6) ∧
    evalClairvoyantMinCost 6 (.reflect (.prototype (.nat 77) expensiveArith)) = some (.nat 77, 3) ∧
    evalCBV 6 (.reflect (.prototype (.nat 77) expensiveArith)) = some (.nat 77, 6) ∧
    evalClairvoyantMinCost 6 (.metadata (.specification (.nat 77) expensiveArith)) = some (.nat 77, 3) ∧
    evalCBV 6 (.metadata (.specification (.nat 77) expensiveArith)) = some (.nat 77, 6) :=
  ⟨optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel)⟩

/-- Two-stage `.fix` wave evaluation in `evalClairvoyantMinCost`:
1. `knot (.nat 42)` unfolds at cost `3` (`CostTests.knot_unfold`).
2. `{good = 7, bad = self.bad}.good` evaluates to `.nat 7` at cost `5` (`CostTests.good_cost`),
   skipping the self-looping field `bad`.
3. `{a = 7, b = self.a}.b` evaluates in two waves to `.nat 7` at cost `7` (`CostTests.self_field_cost`). -/
theorem test_fix_knot_waves_clairvoyant :
    evalClairvoyantMinCost 6 (knot (.nat 42)) = some (.nat 42, 3) ∧
    evalClairvoyantMinCost 6 (.get FareTests.object "good") = some (.nat 7, 5) ∧
    evalClairvoyantMinCost 6 (.get CostTests.selfField "b") = some (.nat 7, 7) :=
  ⟨optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel),
   optTermNatBeq_sound (by decide +kernel)⟩

-- ============================================================================
-- 2. Quantitative `Ahead` Sharing vs. Duplicated Evaluation on `λ x => x + x`
-- ============================================================================

/-- `expensiveArith` reduces to `.nat 100` in 3 reference steps (`StepsCount expensiveArith (.nat 100) 3`). -/
theorem expensiveArith_stepsCount : StepsCount expensiveArith (.nat 100) 3 := by
  have s1 : Step expensiveArith (.binary .add (.nat 30) (.binary .add (.nat 30) (.nat 40))) :=
    .binaryLeft .add _ (.primitive .add (.nat 10) (.nat 20) (.nat 30) (.natural 10) (.natural 20) rfl)
  have s2 : Step (.binary .add (.nat 30) (.binary .add (.nat 30) (.nat 40)))
      (.binary .add (.nat 30) (.nat 70)) :=
    .binaryRight .add (.nat 30) (.natural 30)
      (.primitive .add (.nat 30) (.nat 40) (.nat 70) (.natural 30) (.natural 40) rfl)
  have s3 : Step (.binary .add (.nat 30) (.nat 70)) (.nat 100) :=
    .primitive .add (.nat 30) (.nat 70) (.nat 100) (.natural 30) (.natural 70) rfl
  exact .next s1 (.next s2 (.next s3 (.refl _)))

/-- Sharing via `Ahead` on `dupAdd expensiveArith` costs `3 + 2 = 5` steps vs `2 * 3 + 2 = 8` steps
when `expensiveArith` is duplicated before evaluation (`5 < 8`). -/
theorem test_ahead_sharing_saves_duplicate_cost :
    StepsCount expensiveArith (.nat 100) 3 ∧
    StepsCount (.app dupAdd (.nat 100)) (.nat 200) 2 ∧
    StepsCount (.app dupAdd expensiveArith) (.nat 200) 8 ∧
    Ahead (.app dupAdd expensiveArith) (.app dupAdd (.nat 100)) ∧
    3 + 2 < 2 * 3 + 2 := by
  have h := ahead_sharing_saves_duplicate_cost expensiveArith_stepsCount
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2 (by omega)⟩

-- ============================================================================
-- 3. Sands Improvement Algebra & `beta_value_improves_cost`
-- ============================================================================

/-- Reflexivity and transitivity of `EvalImproves`, `SandsImproves`, and `StrictEvalImproves`,
plus `beta_value_improves_cost` on nested β-value redexes. -/
theorem test_beta_value_improves_cost :
    let body := Term.binary .add (.bound 0) (.nat 5)
    let v := Term.nat 10
    CV (instantiate body v) (.nat 15) 1 ∧
    CV (.app (.lam body) v) (.nat 15) 2 ∧
    1 < 1 + 1 ∧
    StrictEvalImproves 1 (.app (.lam body) v) (instantiate body v) ∧
    EvalImproves (.app (.lam body) v) (instantiate body v) ∧
    evalCBV 4 (.app (.lam body) v) = some (.nat 15, 2) ∧
    evalCBV 3 (instantiate body v) = some (.nat 15, 1) := by
  intro body v
  have hinst : instantiate body v = .binary .add (.nat 10) (.nat 5) := by
    simp [body, v, instantiate, Term.substitute]
  have hcv_inst : CV (instantiate body v) (.nat 15) 1 := by
    rw [hinst]
    have := Run.binary (op := .add) (Run.value (.nat 10)) (Run.value (.nat 5)) rfl
    simpa using this
  have hbeta := beta_value_improves_cost (.nat 10) hcv_inst
  have hdem : ∀ w j, ¬ CV (instantiate body skipped) w j := by
    intro w j h
    have hskip_inst : instantiate body skipped = .binary .add skipped (.nat 5) := by
      simp [body, instantiate, Term.substitute]
    rw [hskip_inst] at h
    cases h with
    | value hv => cases hv
    | binary hl _ _ => exact cv_skipped_false hl
  have heval_imp := (beta_demanded_evalImproves (.value (.nat 10)) hdem).2
  have hcbv_inst : evalCBV 3 (instantiate body v) = some (.nat 15, 1) :=
    optTermNatBeq_sound (by decide +kernel)
  have hcbv_beta := evalCBV_beta_value_improves_cost (.nat 10) hcbv_inst
  exact ⟨hbeta.2.1, hbeta.1, hbeta.2.2.1, hbeta.2.2.2, heval_imp, hcbv_beta.1, hcbv_inst⟩

/-- Transitivity of `StrictEvalImproves` and `EvalImproves` across β-value steps. -/
theorem test_sands_improvement_transitivity :
    let t0 := Term.app (.lam (.bound 0)) (.nat 12)
    let t1 := Term.nat 12
    StrictEvalImproves 1 t0 t1 ∧
    EvalImproves t0 t1 ∧
    SandsImproves t1 t1 := by
  intro t0 t1
  have hinst : instantiate (.bound 0) (.nat 12) = t1 := by
    simp [t1, instantiate]
  have hcv1 : CV (instantiate (.bound 0) (.nat 12)) (.nat 12) 0 := by
    rw [hinst]; exact .value (.nat 12)
  have hbeta := beta_value_improves_cost (body := .bound 0) (.nat 12) hcv1
  have hstrict : StrictEvalImproves 1 t0 t1 := by
    simpa [t0, hinst] using hbeta.2.2.2
  have hdem : ∀ w j, ¬ CV (instantiate (.bound 0) skipped) w j := by
    intro w j h
    have hskip : instantiate (.bound 0) skipped = skipped := by
      simp [instantiate]
    rw [hskip] at h
    exact cv_skipped_false h
  have heval0 := (beta_demanded_evalImproves (body := .bound 0) (.value (.nat 12)) hdem).2
  have heval : EvalImproves t0 t1 := by
    simpa [t0, hinst] using heval0
  exact ⟨StrictEvalImproves.trans hstrict (StrictEvalImproves.refl t1),
    EvalImproves.trans (EvalImproves.refl t0) heval,
    SandsImproves.trans (SandsImproves.refl t1) (SandsImproves.refl t1)⟩

-- ============================================================================
-- 4. Fold Collapse Cost Reduction (`collapse_reduces_ticks` & `collapse_extend_reduces_ticks`)
-- ============================================================================

/-- Collapsing a statically known record projection `.get (.record [("a", .nat 7), ("b", .nat 42)]) "b"`
reduces tick cost from `1` to `0` (`collapse_reduces_ticks`). -/
theorem test_collapse_reduces_ticks :
    let fs : List (String × Term) := [("a", .nat 7), ("b", .nat 42)]
    collapseProjection (.get (.record fs) "b") = .nat 42 ∧
    CV (collapseProjection (.get (.record fs) "b")) (.nat 42) 0 ∧
    CV (.get (.record fs) "b") (.nat 42) 1 ∧
    StrictEvalImproves 1 (.get (.record fs) "b") (collapseProjection (.get (.record fs) "b")) ∧
    EvalImproves (.get (.record fs) "b") (collapseProjection (.get (.record fs) "b")) := by
  intro fs
  have hrec : CValue (.record fs) := by
    refine .record ?_
    intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact .value (.nat 7)
    · exact .value (.nat 42)
  have hcol := collapse_reduces_ticks hrec (name := "b") (x := .nat 42) rfl (.value (.nat 42))
  exact ⟨hcol.1, hcol.2.1, hcol.2.2.1, hcol.2.2.2.2.1, hcol.2.2.2.2.2⟩

/-- Collapsing an extension projection `.get (.extend (.record [("a", .nat 7)]) [("b", .nat 42)]) "b"`
reduces tick cost from `3` to `0` (`collapse_extend_reduces_ticks`), and multi-layer
`termExtendTower` projections collapse in one pass (`collapseProjection_tower_eq`). -/
theorem test_collapse_extend_reduces_ticks :
    let inh : List (String × Term) := [("a", .nat 7)]
    let ext : List (String × Term) := [("b", .nat 42)]
    let ext2 : List (String × Term) := [("c", .nat 99)]
    collapseProjection (.get (.extend (.record inh) ext) "b") = .nat 42 ∧
    CV (collapseProjection (.get (.extend (.record inh) ext) "b")) (.nat 42) 0 ∧
    CV (.get (.extend (.record inh) ext) "b") (.nat 42) 3 ∧
    collapseProjection (.get (termExtendTower inh [ext, ext2]) "b") = .nat 42 ∧
    collapseProjection (.get (termExtendTower inh [ext, ext2]) "c") = .nat 99 := by
  intro inh ext ext2
  have hinh : CValue (.record inh) := by
    refine .record ?_
    intro f hf
    simp only [inh, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact .value (.nat 7)
  have hext : ∀ f ∈ ext, Settled f.2 := by
    intro f hf
    simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact .value (.nat 42)
  have hcol := collapse_extend_reduces_ticks hinh hext (name := "b") (x := .nat 42) rfl (.value (.nat 42))
  have htow_b : collapseProjection (.get (termExtendTower inh [ext, ext2]) "b") = .nat 42 :=
    collapseProjection_tower_eq (base := inh) (layers := [ext, ext2]) (name := "b") (x := .nat 42) rfl
  have htow_c : collapseProjection (.get (termExtendTower inh [ext, ext2]) "c") = .nat 99 :=
    collapseProjection_tower_eq (base := inh) (layers := [ext, ext2]) (name := "c") (x := .nat 99) rfl
  exact ⟨hcol.1, hcol.2.1, hcol.2.2.1, htow_b, htow_c⟩

-- ============================================================================
-- 5. `SharingCostCert` & `verifySharingCostCert` Judge Verification
-- ============================================================================

/-- Certificate 1: Unused expensive argument skipped at clairvoyant cost 2 vs CBV cost 5. -/
def skipSharingCert : SharingCostCert := {
  term := .app (.lam (.nat 42)) expensiveArith
  expectedValue := .nat 42
  fuel := 5
  clairvoyantBound := 2
  cbvBound := 5
}

/-- Certificate 2: Duplicated variable `dupAdd expensiveArith` shared at cost 6. -/
def dupSharingCert : SharingCostCert := {
  term := .app dupAdd expensiveArith
  expectedValue := .nat 200
  fuel := 6
  clairvoyantBound := 6
  cbvBound := 6
}

/-- Certificate 3: Rejected certificate with an overly tight `clairvoyantBound = 1` (actual cost is 2). -/
def overBudgetSharingCert : SharingCostCert := {
  term := .app (.lam (.nat 42)) expensiveArith
  expectedValue := .nat 42
  fuel := 5
  clairvoyantBound := 1
  cbvBound := 5
}

/-- Certificate 4: Rejected certificate where `fuel = 2` is sufficient for `evalClairvoyantMinCost`
(via `Skip`) but insufficient for `evalCBV` (preventing a bogus `cbvBound = 2` from passing). -/
def underFueledCbvSharingCert : SharingCostCert := {
  term := .app (.lam (.nat 42)) expensiveArith
  expectedValue := .nat 42
  fuel := 2
  clairvoyantBound := 2
  cbvBound := 2
}

/-- Certificate 5: Record projection `.get (.record [("a", expensiveArith), ("b", .nat 7)]) "b"`
evaluated at clairvoyant cost 5 (skipping field `"a"`) vs CBV cost 8. -/
def recordProjSharingCert : SharingCostCert := {
  term := .get (.record [("a", expensiveArith), ("b", .nat 7)]) "b"
  expectedValue := .nat 7
  fuel := 6
  clairvoyantBound := 5
  cbvBound := 8
}

theorem test_verifySharingCostCert :
    verifySharingCostCert skipSharingCert = true ∧
    verifySharingCostCert dupSharingCert = true ∧
    verifySharingCostCert recordProjSharingCert = true ∧
    verifySharingCostCert overBudgetSharingCert = false ∧
    verifySharingCostCert underFueledCbvSharingCert = false ∧
    sharingCostCheck 0 skipSharingCert () = .ok ∧
    sharingCostCheck 0 overBudgetSharingCert () = .refused .checkFailed [] := by
  decide +kernel

theorem test_verifySharingCostCert_sound :
    SharingCostMeaning skipSharingCert ∧
    SharingCostMeaning dupSharingCert ∧
    SharingCostMeaning recordProjSharingCert :=
  ⟨verifySharingCostCert_sound test_verifySharingCostCert.1,
   verifySharingCostCert_sound test_verifySharingCostCert.2.1,
   verifySharingCostCert_sound test_verifySharingCostCert.2.2.1⟩

/-- Combined `LayeredSharingCostCert` verifying both `LayeredCost.layered` ("b" within 7) and
`skipSharingCert` (clairvoyant cost 2 vs CBV cost 5). -/
def testLayeredSharingCert : LayeredSharingCostCert := {
  composition := layered
  member := "b"
  layeredBound := 7
  demandCert := ⟨layeredFields, "b"⟩
  sharingCert := skipSharingCert
}

theorem test_verifyLayeredSharingCostCert_ok :
    verifyLayeredSharingCostCert testLayeredSharingCert = true := by
  decide +kernel

theorem test_verifyLayeredSharingCostCert_sound :
    layered.closedB = true ∧
    layeredCheck 0 (layered, "b", 7) ⟨layeredFields, "b"⟩ = .ok ∧
    SharingCostMeaning skipSharingCert :=
  verifyLayeredSharingCostCert_sound test_verifyLayeredSharingCostCert_ok

-- ============================================================================
-- 6. Axiom Audit (`0 sorryAx`, `0 Classical.choice`)
-- ============================================================================

#print axioms evalClairvoyantWithHint_sound
#print axioms evalClairvoyantMinCost_sound
#print axioms evalClairvoyantMinCost_value_sound
#print axioms evalClairvoyantMinCost_skip_app_sound
#print axioms evalClairvoyant_skip_unused_arg_saves_cost
#print axioms ahead_sharing_saves_duplicate_cost
#print axioms beta_value_improves_cost
#print axioms collapse_reduces_ticks
#print axioms collapse_extend_reduces_ticks
#print axioms collapseProjection_tower_eq
#print axioms verifySharingCostCert_sound
#print axioms verifyLayeredSharingCostCert_sound
#print axioms test_skip_unused_arg_vs_cbv
#print axioms test_demand_hint_record_proto_spec
#print axioms test_fix_knot_waves_clairvoyant
#print axioms test_verifySharingCostCert_sound
#print axioms test_verifyLayeredSharingCostCert_sound

end Obend.Tests.ClairvoyantAndCostTest
