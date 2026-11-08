import Obend.Tactic.Tooth
import Obend.Analysis.RealAnalysis
import Obend.Analysis.TaylorModel
import Obend.Analysis.Flowpipe
import Obend.Analysis.Groebner
import Obend.Analysis.Diff
import Obend.Judge.RealAnalysis
import Obend.Hardware.OpenHypergraph

/-!
# `tests/metasystem/NextMathematicaSoundnessTest.lean` — WS-C ("Next Mathematica") End-to-End Soundness Suite

Comprehensive verification of the WS-C deliverables:
1. **`Obend.Analysis.RealAnalysis`** — Universal Rational Interval Arithmetic Spine (`Interval.Mem`,
   `Interval.Wf`, `Interval.add_mem`, `Interval.neg_mem`, `Interval.sub_mem`, `Interval.mul_mem`,
   `Interval.sqr_mem`, `evalInterval_sound`) + `#tooth` mutation probes.
2. **`Obend.Analysis.TaylorModel` & `Obend.Analysis.Flowpipe`** — Signed symmetric Lagrange remainders
   (`lagrangeRemExp4`, `lagrangeRemSin5`, `lagrangeRemCos4`, `lagrangeRemLn1p4`, `lagrangeRemSqrt3`),
   `TaylorModel.Models` (`add_models`, `sub_models`, `scale_models`), `AnalyticModel`
   (`tmSinCertified_models`, `tmExpCertified_models`, `tmCosCertified_models`), and Picard–Lindelöf
   a-priori flowpipe step validation (`verifyPicardAPriori`, `derivePicardRemainder`,
   `picard_step_encloses_trajectory`).
3. **`Obend.Judge.RealAnalysis` & `Obend.Analysis.Groebner`** — Multiplicative Graded-Lexicographic
   monomial order (`Monomial.grlexLt`, `grlex_mul_compatible`), independent polynomial ring evaluation
   (`SparsePoly.eval`, `eval_add`, `eval_sub`, `eval_mul`, `eval_neg`, `eval_sq_nonneg`), and
   semantic soundness of ideal membership & Stengle's Positivstellensatz
   (`checkIdealMembership_eval_sound`, `positivstellensatz_eval_infeasible`).
4. **`Obend.Analysis.Diff` & `Obend.Hardware.OpenHypergraph`** — Accumulated SSA/DAG reverse-mode AD
   (`accumulateGrad`, `gradReverseAccumulated`, `gradReverseAccumulated_agrees_with_dual`,
   `gradReverseAccumulated_nestedSqr_linear`), whole-graph functorial reverse-AD (`compileGraphAdjoint`,
   `compileGraphAdjoint_multiEdge_sound`), and pipelined wavefront RTL compilation
   (`compileHypergraphToRtlPipelined`, `compileHypergraphToRtlPipelined_sound`).
-/

namespace Obend.Tests.NextMathematicaSoundnessTest

open Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
open Obend.Hardware.HDL
open Obend.Hardware.OpenHypergraph

-- ============================================================================
-- 1. Universal Rational Interval Arithmetic Spine (`Obend.Analysis.RealAnalysis`)
-- ============================================================================

-- Universal interval enclosure theorems over `CanonicalRat` (`Rat`).
example {x y : CanonicalRat} {A B : Obend.Analysis.Interval}
    (hx : x ∈ A) (hy : y ∈ B) :
    (x + y) ∈ Obend.Analysis.Interval.add A B :=
  Obend.Analysis.Interval.add_mem hx hy

example {x : CanonicalRat} {A : Obend.Analysis.Interval}
    (hx : x ∈ A) :
    (-x) ∈ Obend.Analysis.Interval.neg A :=
  Obend.Analysis.Interval.neg_mem hx

example {x y : CanonicalRat} {A B : Obend.Analysis.Interval}
    (hx : x ∈ A) (hy : y ∈ B) :
    (x - y) ∈ Obend.Analysis.Interval.sub A B :=
  Obend.Analysis.Interval.sub_mem hx hy

example {x y : CanonicalRat} {A B : Obend.Analysis.Interval}
    (hx : x ∈ A) (hy : y ∈ B) :
    (x * y) ∈ Obend.Analysis.Interval.mul A B :=
  Obend.Analysis.Interval.mul_mem hx hy

example {x : CanonicalRat} {A : Obend.Analysis.Interval}
    (hx : x ∈ A) :
    (x * x) ∈ Obend.Analysis.Interval.sqr A :=
  Obend.Analysis.Interval.sqr_mem hx

example
    (env : List (String × Obend.Analysis.Interval))
    (rho : String → CanonicalRat)
    (hEnv : ∀ v I, env.lookup v = some I → rho v ∈ I)
    (e : RealExpr) (I : Obend.Analysis.Interval)
    (hEval : evalInterval env e = some I) :
    evalExpr rho e ∈ I :=
  evalInterval_sound env rho hEnv e I hEval

-- Edge-case checks: negative-negative multiplication, zero-straddling square, missing variable lookup.
#guard Obend.Analysis.Interval.mul ⟨-4, -2⟩ ⟨-5, -3⟩ == ⟨6, 20⟩
#guard Obend.Analysis.Interval.sqr ⟨-3, 2⟩ == ⟨0, 9⟩
#guard Obend.Analysis.Interval.sqr ⟨-5, -2⟩ == ⟨4, 25⟩
#guard evalInterval [] (.var "missing") == none

-- `#tooth` mutation probes on `Interval.add`, `Interval.mul`, and `evalInterval`.
theorem test_interval_add_sound_probe :
    ∀ (x y : CanonicalRat) (A B : Obend.Analysis.Interval),
      x ∈ A → y ∈ B → (x + y) ∈ Obend.Analysis.Interval.add A B :=
  fun _ _ _ _ hx hy => Obend.Analysis.Interval.add_mem hx hy

#tooth test_interval_add_sound_probe by mutation
  Obend.Analysis.Interval.add := fun a b => ⟨a.lo + b.hi, a.hi + b.lo⟩

theorem test_interval_mul_sound_probe :
    ∀ (x y : CanonicalRat) (A B : Obend.Analysis.Interval),
      x ∈ A → y ∈ B → (x * y) ∈ Obend.Analysis.Interval.mul A B :=
  fun _ _ _ _ hx hy => Obend.Analysis.Interval.mul_mem hx hy

#tooth test_interval_mul_sound_probe by mutation
  Obend.Analysis.Interval.mul := fun a b => ⟨a.lo * b.lo, a.hi * b.hi⟩

theorem test_evalInterval_sound_probe :
    ∀ (env : List (String × Obend.Analysis.Interval)) (rho : String → CanonicalRat),
      (∀ v I, env.lookup v = some I → rho v ∈ I) →
      ∀ (e : RealExpr) (I : Obend.Analysis.Interval),
        evalInterval env e = some I → evalExpr rho e ∈ I :=
  evalInterval_sound

#tooth test_evalInterval_sound_probe by mutation
  Obend.Analysis.evalInterval := fun _ _ => some ⟨0, 0⟩

-- ============================================================================
-- 2. Signed Lagrange Remainders, `AnalyticModel` & Picard Flowpipes
-- ============================================================================

-- Positive singleton domain X = [1/10, 1/10] where sin(1/10) - p_5(1/10) < 0:
-- The signed remainder `lagrangeRemSin5` produces `[-1/720000000, 1/720000000]`,
-- enclosing the negative residual `-1/720000000`.
def singletonTenth : Obend.Analysis.Interval :=
  Obend.Analysis.Interval.ofPoint (CanonicalRat.mk 1 10)

#guard lagrangeRemSin5 singletonTenth ==
  ⟨CanonicalRat.mk (-1) 720000000, CanonicalRat.mk 1 720000000⟩
#guard Obend.Analysis.Interval.containsRat (lagrangeRemSin5 singletonTenth)
  (CanonicalRat.mk (-1) 720000000) == true
#guard Obend.Analysis.Interval.containsRat (lagrangeRemExp4 singletonTenth)
  (CanonicalRat.mk (-1) 4000000) == true
#guard Obend.Analysis.Interval.containsRat (lagrangeRemCos4 singletonTenth)
  (CanonicalRat.mk (-1) 12000000) == true
#guard Obend.Analysis.Interval.containsRat (lagrangeRemLn1p4 singletonTenth)
  (CanonicalRat.mk (-32) 500000) == true
#guard Obend.Analysis.Interval.containsRat (lagrangeRemSqrt3 singletonTenth)
  (CanonicalRat.mk (-5) 80000) == true

-- Universal `TaylorModel.Models` preservation and `AnalyticModel` soundness theorems.
example {f g : CanonicalRat → CanonicalRat} {tmA tmB : TaylorModel}
    (hC : tmA.center = tmB.center) (hD : tmA.domain = tmB.domain)
    (hA : TaylorModel.Models f tmA) (hB : TaylorModel.Models g tmB) :
    TaylorModel.Models (fun x => f x + g x) (tmAdd tmA tmB) :=
  TaylorModel.add_models hC hD hA hB

example {f g : CanonicalRat → CanonicalRat} {tmA tmB : TaylorModel}
    (hC : tmA.center = tmB.center) (hD : tmA.domain = tmB.domain)
    (hA : TaylorModel.Models f tmA) (hB : TaylorModel.Models g tmB) :
    TaylorModel.Models (fun x => f x - g x) (tmSub tmA tmB) :=
  TaylorModel.sub_models hC hD hA hB

example (s : CanonicalRat) {f : CanonicalRat → CanonicalRat} {tm : TaylorModel}
    (h : TaylorModel.Models f tm) :
    TaylorModel.Models (fun x => s * f x) (tmScale s tm) :=
  TaylorModel.scale_models s h

example (order : Nat) {f g : CanonicalRat → CanonicalRat} {tmA tmB : TaylorModel}
    (hC : tmA.center = tmB.center) (hD : tmA.domain = tmB.domain)
    (hA : TaylorModel.Models f tmA) (hB : TaylorModel.Models g tmB) :
    TaylorModel.Models (fun x => f x * g x) (tmMul order tmA tmB) :=
  TaylorModel.mul_models order hC hD hA hB

example {f : CanonicalRat → CanonicalRat} {tm : TaylorModel}
    (h : TaylorModel.Models f tm) {x : CanonicalRat} (hx : x ∈ tm.domain) :
    f x ∈ evalTaylorModelRange tm :=
  evalTaylorModelRange_encloses h hx

-- The certified models hold on their valid domains (`trigValidDomain`, `expValidDomain`); since
-- the domain hypotheses were added, nothing is claimed outside them.
example (R : Type) [M : AnalyticModel R] (dom : Obend.Analysis.Interval)
    (hT : Obend.Analysis.Interval.subset dom trigValidDomain = true)
    (hE : Obend.Analysis.Interval.subset dom expValidDomain = true) :
    TaylorModel.Models M.sinFn (tmSinCertified dom) ∧
    TaylorModel.Models M.expFn (tmExpCertified dom) ∧
    TaylorModel.Models M.cosFn (tmCosCertified dom) :=
  ⟨tmSinCertified_models R dom hT, tmExpCertified_models R dom hE, tmCosCertified_models R dom hT⟩

-- Concrete instance check: `tmSinCertified singletonTenth` encloses `AnalyticModel.sinFn (1/10)` at `x = 1/10`.
set_option maxRecDepth 2000 in
example :
    (AnalyticModel.sinFn (R := CanonicalRat) (CanonicalRat.mk 1 10)) ∈
      evalTaylorModelPoint (tmSinCertified singletonTenth) (CanonicalRat.mk 1 10) :=
  evalTaylorModelPoint_encloses (tmSinCertified_models CanonicalRat singletonTenth)
    (Obend.Analysis.Interval.ofPoint_mem (CanonicalRat.mk 1 10))

-- `#tooth` probe on `lagrangeRemSin5`: mutating `lagrangeRemSin5` back to positive singleton `1/720`
-- fails to enclose the negative residual at `X = [1/10, 1/10]`.
theorem test_lagrangeRemSin5_encloses_neg_residual :
    Obend.Analysis.Interval.containsRat (lagrangeRemSin5 singletonTenth)
      (CanonicalRat.mk (-1) 720000000) = true := by
  decide +kernel

#tooth test_lagrangeRemSin5_encloses_neg_residual by mutation
  Obend.Analysis.lagrangeRemSin5 := fun dom =>
    Obend.Analysis.Interval.mul (Obend.Analysis.Interval.ofPoint (CanonicalRat.mk 1 720))
      (Obend.Analysis.intervalPow dom 6)

-- Picard-Lindelöf a-priori enclosure & derived remainder soundness (`Flowpipe.lean`), over boxes
-- (`List (String × Interval)`) since the flowpipe left its 1D interface.
#guard verifyPicardAPriori thermalCoolingOde [("T", ⟨30, 30⟩)] [("T", ⟨25, 30⟩)] (CanonicalRat.mk 1 2) == true
#guard verifyPicardAPriori thermalCoolingOde [("T", ⟨30, 30⟩)] [("T", ⟨28, 30⟩)] (CanonicalRat.mk 1 2) == false

-- The trajectory enclosure, for every field of every system, and its concrete poles (the
-- zero-pad cooling step `[205/8, 105/4]` contains the exact trajectory `26.0653`).
example := picard_step_encloses_trajectory.1
example := picard_step_encloses_trajectory.2

theorem test_picard_rejects_narrow_apriori :
    verifyPicardAPriori thermalCoolingOde [("T", ⟨30, 30⟩)] [("T", ⟨28, 30⟩)] (CanonicalRat.mk 1 2) = false := by
  decide +kernel

#tooth verifyPicardAPriori_encloses by mutation
  Obend.Analysis.verifyPicardAPriori := fun _ _ _ _ => true

-- ============================================================================
-- 3. Multiplicative Graded-Lex Monomial Order & Ring Denotation (`Judge/RealAnalysis`, `Groebner`)
-- ============================================================================

-- Verify that `Monomial.grlexLt` (`Monomial.lt`) fixes the non-multiplicative bug:
-- `1 < x_0` (`[] < [(0, 1)]`) AND multiplying both sides by `x_1` (`[(1, 1)]`) preserves
-- the strict inequality: `x_1 < x_0 * x_1` (`[(1, 1)] < [(0, 1), (1, 1)]`)!
#guard Monomial.grlexLt [] [(0, 1)] == true
#guard Monomial.grlexLt (Monomial.mul [] [(1, 1)]) (Monomial.mul [(0, 1)] [(1, 1)]) == true
#guard Monomial.grlexLt [(1, 1)] [(0, 1), (1, 1)] == true
#guard Monomial.grlexLt [(0, 2)] [(1, 1)] == false

example (m1 m2 m : Monomial) (h : Monomial.grlexLt m1 m2 = true) :
    Monomial.grlexLt (Monomial.mul m1 m) (Monomial.mul m2 m) = true :=
  grlex_mul_compatible m1 m2 m h

-- `#tooth` probe on `Monomial.grlexLt`: mutating `grlexLt` back to un-graded variable-index-first
-- ordering violates `[(1, 1)] < [(0, 1), (1, 1)]`.
theorem test_grlex_multiplicative_witness :
    Monomial.grlexLt [(1, 1)] [(0, 1), (1, 1)] = true := rfl

#tooth test_grlex_multiplicative_witness by mutation
  Obend.Judge.SOS.Monomial.grlexLt := fun m1 m2 =>
    match m1, m2 with
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | (v1, _) :: _, (v2, _) :: _ => decide (v1 < v2)

-- Ring evaluation homomorphism theorems for `SparsePoly.eval` (`Poly.eval`).
example (ρ : Nat → CanonicalRat) (p1 p2 : SparsePoly) :
    SparsePoly.eval ρ (Poly.add p1 p2) = SparsePoly.eval ρ p1 + SparsePoly.eval ρ p2 ∧
    SparsePoly.eval ρ (Poly.sub p1 p2) = SparsePoly.eval ρ p1 - SparsePoly.eval ρ p2 ∧
    SparsePoly.eval ρ (Poly.mul p1 p2) = SparsePoly.eval ρ p1 * SparsePoly.eval ρ p2 ∧
    SparsePoly.eval ρ (Poly.neg p1) = -(SparsePoly.eval ρ p1) ∧
    0 ≤ SparsePoly.eval ρ (Poly.sqr p1) :=
  ⟨SparsePoly.eval_add ρ p1 p2,
   SparsePoly.eval_sub ρ p1 p2,
   SparsePoly.eval_mul ρ p1 p2,
   SparsePoly.eval_neg ρ p1,
   SparsePoly.eval_sq_nonneg ρ p1⟩

-- True semantic soundness of `checkIdealMembership` and `positivstellensatzCheck`.
example (target : Poly) (gens : List Poly) (cert : IdealMembershipCert)
    (h : checkIdealMembership target gens cert = true)
    (ρ : Nat → CanonicalRat)
    (hGens : ∀ g ∈ gens, g.eval ρ = 0) :
    target.eval ρ = 0 :=
  checkIdealMembership_eval_sound target gens cert h ρ hGens

example (fuel : Nat) (q : PositivstellensatzQuery) (c : PositivstellensatzCert)
    (hOk : positivstellensatzCheck fuel q c = .ok)
    (hMonoidOne : c.monoidIndices = [])
    (ρ : Nat → CanonicalRat)
    (hNonneg : ∀ g ∈ q.nonneg, 0 ≤ g.eval ρ)
    (hEqs : ∀ h ∈ q.eqs, h.eval ρ = 0) :
    False :=
  positivstellensatz_eval_infeasible fuel q c hOk hMonoidOne ρ hNonneg hEqs

-- Concrete semantic refutation via `positivstellensatz_eval_infeasible`:
-- No rational point `ρ` can lie on the unit circle `x_0^2 + x_1^2 - 1 = 0` while satisfying `-x_0^2 - x_1^2 ≥ 0`.
theorem test_unit_circle_origin_infeasible
    (ρ : Nat → CanonicalRat)
    (hNonneg : 0 ≤ (Poly.neg (Poly.add (Poly.sqr (polyVarPow 0 1)) (Poly.sqr (polyVarPow 1 1)))).eval ρ)
    (hEq : (Poly.sub (Poly.add (Poly.sqr (polyVarPow 0 1)) (Poly.sqr (polyVarPow 1 1))) Poly.one).eval ρ = 0) :
    False := by
  let x0 := polyVarPow 0 1
  let x1 := polyVarPow 1 1
  let sumSq := Poly.add (Poly.sqr x0) (Poly.sqr x1)
  let h0 := Poly.sub sumSq Poly.one
  let g0 := Poly.neg sumSq
  let q : PositivstellensatzQuery := { strictPos := [], nonneg := [g0], eqs := [h0] }
  let c : PositivstellensatzCert :=
    { monoidIndices := [], sigma0 := ⟨[]⟩, coneTerms := [(⟨[(1, Poly.one)]⟩, 0)], idealTerms := [(Poly.one, 0)] }
  have hOk : positivstellensatzCheck 0 q c = .ok := by decide +kernel
  exact positivstellensatz_eval_infeasible 0 q c hOk rfl ρ
    (by intro g hg; simp [q] at hg; subst hg; exact hNonneg)
    (by intro h hh; simp [q] at hh; subst hh; exact hEq)

-- ============================================================================
-- 4. Accumulated Reverse-AD, Whole-Graph `compileGraphAdjoint` & Pipelined RTL
-- ============================================================================

-- `gradReverse` and `gradReverseAccumulated` both have linear size `1` on nested squares (the `2^n`
-- blowup is fixed in `gradReverse` itself) and agree with forward-mode `DualRat`.
#guard (gradReverse (fun _ => 2) 1 (nestedSqrChain 4 (.var "x"))).length == 1
#guard (gradReverseAccumulated (fun _ => 2) 1 (nestedSqrChain 4 (.var "x"))).length == 1
#guard accumulateGradStr (gradReverseAccumulated (fun _ => 2) 1 (nestedSqrChain 3 (.var "x"))) "x" == 1024
#guard (evalDualRat (fun _ => 2) "x" (nestedSqrChain 3 (.var "x"))).der == 1024

example (rho : String → CanonicalRat) (bar : CanonicalRat) (diffVar : String) (e : RealExpr) :
    accumulateGradStr (gradReverseAccumulated rho bar e) diffVar =
      bar * (evalDualRat rho diffVar e).der ∧
    accumulateGradStr (gradReverseAccumulated rho 1 e) diffVar =
      (evalDualRat rho diffVar e).der ∧
    (gradReverseAccumulated rho bar e).length ≤ (exprDistinctVars e).length :=
  gradReverseAccumulated_agrees_with_dual rho bar diffVar e

example (symTab : List String) (rho : String → CanonicalRat) (bar : CanonicalRat)
    (diffVar : String) (e : RealExpr)
    (hInj : ∀ v, (varIndexOf symTab v == varIndexOf symTab diffVar) = (v == diffVar)) :
    accumulateGrad (gradReverseAccumulatedIdx symTab rho bar e) (varIndexOf symTab diffVar) =
      bar * (evalDualRat rho diffVar e).der :=
  gradReverseAccumulatedIdx_agrees_with_dual symTab rho bar diffVar e hInj

example (rho : String → CanonicalRat) (name : String) (n : Nat) (bar : CanonicalRat) :
    (gradReverse rho bar (nestedSqrChain n (.var name))).length = 1 ∧
    (gradReverseAccumulated rho bar (nestedSqrChain n (.var name))).length = 1 :=
  gradReverseAccumulated_nestedSqr_linear rho name n bar

-- `#tooth` probe on `gradReverseAccumulated`: mutating `gradReverseAccumulated` to return `[]`
-- breaks derivative agreement on `samplePolyExpr`.
theorem test_gradReverseAccumulated_samplePoly :
    accumulateGradStr (gradReverseAccumulated (fun _ => 4) 1 samplePolyExpr) "x" = 11 := by
  decide +kernel

#tooth test_gradReverseAccumulated_samplePoly by mutation
  Obend.Analysis.gradReverseAccumulated := fun _ _ _ => []

-- Whole-Graph Functorial Reverse-AD (`compileGraphAdjoint`, `compileGraphAdjoint_multiEdge_sound`).
example (op1 op2 : OpticOp) (x y dOut : Int) :
    let gFwd := compileOpticChain2FwdHypergraph op1 op2
    let gAdj := compileGraphAdjoint gFwd
    let env  := opticChain2AdjointInitEnv x y dOut
    let (z, res) := evalOpticChain2Fwd op1 op2 x y
    let (dx, dy) := evalOpticChain2Rev (compileOpticAdjoint op1) (compileOpticAdjoint op2) res dOut
    gAdj.wf = true ∧
    evalHypergraphComb gAdj env = [z, dx, dy] ∧
    evalHypergraphLayered gAdj env = [z, dx, dy] ∧
    evalHypergraphLayeredSync gAdj env = [z, dx, dy] := by
  have h := compileGraphAdjoint_multiEdge_sound op1 op2 x y dOut
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

example (x0 x1 x2 x3 dOut : Int) :
    let gAdj := compileGraphAdjoint goldenDiamondHypergraph
    let env : Nat → Int := fun w =>
      match w with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 9 => dOut | _ => 0
    let expected :=
      [ (x0 + x1) * (x2 + x3) + 10
      , (x2 + x3) * dOut
      , (x2 + x3) * dOut
      , (x0 + x1) * dOut
      , (x0 + x1) * dOut ]
    evalHypergraphComb gAdj env = expected ∧
    evalHypergraphLayered gAdj env = expected ∧
    evalHypergraphLayeredSync gAdj env = expected :=
  compileGraphAdjoint_diamond_symbolic_sound x0 x1 x2 x3 dOut

-- `#tooth` probe on `compileGraphAdjoint`: mutating `compileGraphAdjoint` to return the un-differentiated
-- forward graph fails to produce the `[z, dx, dy]` gradient outputs.
theorem test_compileGraphAdjoint_diamond_eval :
    evalHypergraphComb (compileGraphAdjoint goldenDiamondHypergraph)
      (fun w => match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 9 => 1 | _ => 0) =
      [87, 11, 11, 7, 7] := by
  decide +kernel

#tooth test_compileGraphAdjoint_diamond_eval by mutation
  Obend.Hardware.OpenHypergraph.compileGraphAdjoint := fun g => g

-- Pipelined Wavefront RTL Compilation (`compileHypergraphToRtlPipelined`, `compileHypergraphToRtlPipelined_sound`).
#guard (compileHypergraphToRtlPipelined "diamond_pipe" goldenDiamondHypergraph).regs.length == 27

-- The whole-module theorem, instantiated: its two side conditions are decided on the diamond.
example (ins initRegs : Nat → BitVec 64) :
    (evalModuleOutputs (compileHypergraphToRtlPipelined "diamond_pipe" goldenDiamondHypergraph) ins
        (runModuleTrace (compileHypergraphToRtlPipelined "diamond_pipe" goldenDiamondHypergraph) initRegs
          (List.replicate (layerHypergraph goldenDiamondHypergraph).length (false, ins)))).map Prod.snd =
      goldenDiamondHypergraph.boundaryOut.table.map
        (evalLayeredStagesSyncBv ins (layerHypergraph goldenDiamondHypergraph)) :=
  compileHypergraphToRtlPipelined_sound "diamond_pipe" goldenDiamondHypergraph (by decide) (by decide) ins initRegs

-- A known answer: inputs 3, 4, 5, 6 give (3 + 4) * (5 + 6) + 10 = 87 after one edge per stage.
#guard
  let m := compileHypergraphToRtlPipelined "diamond_pipe" goldenDiamondHypergraph
  let ins : Nat → BitVec 64 := fun u => match u with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | _ => 0
  (evalModuleOutputs m ins (runModuleTrace m (fun _ => 0#64) (List.replicate 3 (false, ins)))).map Prod.snd
    == [87#64]

example
    (initEnv : Nat → Int) (stages : List (List HyperEdge))
    (hArith : stages.all (fun s => s.all (fun e => e.op.isArithmetic)) = true) :
    evalLayeredStagesSyncBv (fun u => BitVec.ofInt 64 (initEnv u)) stages =
      fun w => BitVec.ofInt 64 (evalLayeredStagesSync initEnv stages w) :=
  evalLayeredStagesSyncBv_ofInt initEnv stages hArith


-- `#tooth` probe on `compileHypergraphToRtlPipelined`: mutating `regs := []` breaks the 27-register
-- 3-stage pipeline check for `goldenDiamondHypergraph`.
theorem test_pipelined_rtl_has_stage_regs :
    (compileHypergraphToRtlPipelined "diamond_pipe" goldenDiamondHypergraph).regs.length = 27 := rfl

#tooth test_pipelined_rtl_has_stage_regs by mutation
  Obend.Hardware.OpenHypergraph.compileHypergraphToRtlPipelined :=
    fun name _ => { name := name, inputNames := [], wires := [], regs := [], outputs := [] }

-- ============================================================================
-- 5. Axiom Audit (`0 sorryAx`)
-- ============================================================================

#print axioms Obend.Analysis.Interval.add_mem
#print axioms Obend.Analysis.Interval.neg_mem
#print axioms Obend.Analysis.Interval.sub_mem
#print axioms Obend.Analysis.Interval.mul_mem
#print axioms Obend.Analysis.Interval.sqr_mem
#print axioms Obend.Analysis.evalInterval_sound
#print axioms Obend.Analysis.TaylorModel.add_models
#print axioms Obend.Analysis.TaylorModel.sub_models
#print axioms Obend.Analysis.TaylorModel.scale_models
#print axioms Obend.Analysis.TaylorModel.mul_models
#print axioms Obend.Analysis.evalTaylorModelRange_encloses
#print axioms Obend.Analysis.tmExpCertified_models
#print axioms Obend.Analysis.tmSinCertified_models
#print axioms Obend.Analysis.tmCosCertified_models
#print axioms Obend.Analysis.evalDualInterval_sound
#print axioms Obend.Analysis.meanValueEnclosure_sound
#print axioms Obend.Analysis.evalOdeField_sound
#print axioms Obend.Analysis.evalOdeJacobian_sound
#print axioms Obend.Analysis.picard_step_encloses_trajectory
#print axioms Obend.Judge.SOS.grlex_mul_compatible
#print axioms Obend.Judge.SOS.SparsePoly.eval_add
#print axioms Obend.Judge.SOS.SparsePoly.eval_sub
#print axioms Obend.Judge.SOS.SparsePoly.eval_mul
#print axioms Obend.Judge.SOS.SparsePoly.eval_neg
#print axioms Obend.Judge.SOS.SparsePoly.eval_sq_nonneg
#print axioms Obend.Analysis.checkIdealMembership_eval_sound
#print axioms Obend.Analysis.positivstellensatz_eval_infeasible
#print axioms Obend.Analysis.gradReverseAccumulated_agrees_with_dual
#print axioms Obend.Analysis.gradReverseAccumulatedIdx_agrees_with_dual
#print axioms Obend.Analysis.gradReverseAccumulated_nestedSqr_linear
#print axioms Obend.Hardware.OpenHypergraph.compileGraphAdjoint_multiEdge_sound
#print axioms Obend.Hardware.OpenHypergraph.compileGraphAdjoint_diamond_symbolic_sound
#print axioms Obend.Hardware.OpenHypergraph.compileHypergraphToRtlPipelined_sound

end Obend.Tests.NextMathematicaSoundnessTest

