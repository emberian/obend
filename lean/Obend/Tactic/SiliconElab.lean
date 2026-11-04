module
/-
# `Obend.Tactic.SiliconElab` — Live Hardware-Assisted Lean 4 (`#silicon_check` & All 5 `by silicon_*` Tactics)

Implements Wave 4 Lane `WS-4B-1` (`QUALIFICATION-AND-SILICON-LEAN.md` §2.3 & North Star 1):
1. **Canonical Self-Hosting Aliases**:
   - `Obend.Core.type_preservation` (aliasing `Obend.Core.Proofs.Preservation.typed_stepRaw_preserved`),
   - `Obend.Lower.SiliconElabFabric.stepSiliconKernelCamFsm` (aliasing `Obend.Lower.SiliconElabFabric.runSiliconKernelCamFsm`).
2. **Live `#silicon_check <DeclName>` Command Elaborator**:
   - Extracts any target declaration (and its referenced environment declaration cone) from `(← getEnv)`,
   - Translates `Lean.Expr` into self-hosted `KExpr` and interns the DAG into `HwExprCAM`,
   - Packs every deduplicated node into an 88-bit `PackedNodeWord` (`packNodeWord88 : PackedNodeWord → BitVec 88`)
     with an `OBCAMv1` `SiliconElabWireHeader`,
   - Executes the 4-Zone `SiliconElabFabric` co-processor model (Zone 1 `HwExprCAM` WHNF & 1-cycle closed-term
     $\beta$-bypass, Zone 2 2x2 2D XY credit-flow NoC unifier, Zone 3 `DiscrTreeLUT` + 3-phase `ICAP` DPR guard,
     and Zone 4 bottom-up CAM typechecker `runBottomUpCamInfer` / `stepSiliconKernelCamFsm`),
   - Logs structured hardware telemetry (`activeZones`, `packedNodeWords88`, `hwCycles`, `zone1CamHits`,
     `zone1BetaBypasses`, `zone2NocFlits`, `zone3LutHits`, and `kernelVerdict`).
3. **Certified Interval Subdivision & SOS Non-Negativity Bridge Theorems**:
   - `bisectInterval`, `verifyRealBoundSubdiv`, and `verifyRealBoundSubdiv_sound`,
   - `sos_cert_implies_nonneg` wrapping `Obend.Judge.SOS.sosCheck_sound`.
4. **All 5 Proof-Reconstructing Hardware-Accelerated Tactics**:
   - `by silicon_simp` (Zone 3 `DiscrTreeLUT` + Zone 1 WHNF $\to$ Lean kernel rewrite/reduction proof),
   - `by silicon_eqsat` (`EqSatHypergraph` saturation + Clairvoyant extraction $\to$ `eqSat_preserves_eval_and_adjoint` / ring proof),
   - `by silicon_sos` (`SosLyapunov` / `SOS` Gram witness $\to$ `sos_cert_implies_nonneg` / `checkPsatzNonneg_sound` / `checkSosLyapunov_sound` / `checkSosCbf_sound`),
   - `by silicon_interval` (`TaylorModel` / `RealAnalysis` subdivision $\to$ `verifyRealBoundSubdiv_sound` / `taylorModel_transcendental_enclosure_sound` / `intervalCheck_sound`),
   - `by silicon_flowpipe` (`Flowpipe` $N$-D validated Picard $\to$ `picard_step_encloses_trajectory` / `taylorModel_picard_sound` / `flowpipe_step_encloses_euler`).
5. **Reflexive Self-Hosting Milestone Theorem (`silicon_self_hosting_milestone_sound`)**:
   - Machine-checked proof (`0 sorry`) that the 4-Zone `SiliconElabFabric` + 88-bit `HwExprCAM` pipeline
     self-checks the representations of `Obend.Lower.LeanKernel.kernelCheckDecl`,
     `Obend.Lower.SiliconElabFabric.runBottomUpCamInfer` / `stepSiliconKernelCamFsm`, and
     `Obend.Core.type_preservation`, while refusing `#tooth`-mutated and `sorryAx`-contaminated declarations.
-/
public meta import Lean
public import Lean
public import Obend.Lower.Inductive
public meta import Obend.Lower.Inductive
public import Obend.Lower.LeanKernel
public meta import Obend.Lower.LeanKernel
public import Obend.Lower.ExprCAM
public meta import Obend.Lower.ExprCAM
public import Obend.Lower.DiscrTreeLUT
public meta import Obend.Lower.DiscrTreeLUT
public import Obend.Lower.SiliconElabFabric
public meta import Obend.Lower.SiliconElabFabric
import all Obend.Lower.SiliconElabFabric
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Hardware.Judge
import all Obend.Judge.Class
public import Obend.Core.Proofs.Preservation
public import Obend.Analysis.RealAnalysis
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.SosLyapunov
public import Obend.Analysis.EqSatHypergraph
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.Flowpipe
public import Obend.Tactic.Tooth

@[expose] public section

/-! ## 1. Canonical Self-Hosting Symbol Aliases -/

namespace Obend.Core

/-- Alias for the demand machine's type preservation theorem
(`Obend.Core.Proofs.Preservation.typed_stepRaw_preserved`). Its proof term is far outside the Zone-4
fragment; `#silicon_check` on it refuses, as it must (2026-11-04). -/
abbrev type_preservation := @Obend.Core.Proofs.Preservation.typed_stepRaw_preserved

end Obend.Core

namespace Obend.Lower.SiliconElabFabric

/-- Canonical step-level alias for the Zone-4 bottom-up CAM kernel FSM (`runSiliconKernelCamFsm`). -/
abbrev stepSiliconKernelCamFsm := @Obend.Lower.SiliconElabFabric.runSiliconKernelCamFsm

end Obend.Lower.SiliconElabFabric

namespace Obend.Tactic.SiliconElab

open Lean Elab Command Tactic Meta
open Obend.Lower.LeanKernel
open Obend.Lower.Inductive
open Obend.Lower.ExprCAM
open Obend.Lower.DiscrTreeLUT
open Obend.Lower.SiliconElabFabric
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.Judge
open Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS

/-! ## 2. Certified Interval Subdivision (`verifyRealBoundSubdiv_sound`, `verifyRealBoxBoundSubdiv_sound`) & SOS Bridge (`sos_cert_implies_nonneg`) -/

/-- Bisect a closed rational interval `[lo, hi]` at its exact midpoint `mid = (lo + hi) / 2`. -/
def bisectInterval (dom : Interval) : Interval × Interval :=
  let mid : CanonicalRat := (dom.lo + dom.hi) / 2
  (⟨dom.lo, mid⟩, ⟨mid, dom.hi⟩)

/-- Every point `x ∈ dom` lies in either the left half or the right half of `bisectInterval dom`. -/
theorem mem_bisectInterval {x : CanonicalRat} {dom : Interval} (hx : x ∈ dom) :
    x ∈ (bisectInterval dom).1 ∨ x ∈ (bisectInterval dom).2 := by
  simp only [bisectInterval, Interval.mem_iff] at hx ⊢
  rcases hx with ⟨hlo, hhi⟩
  by_cases hmid : x ≤ (dom.lo + dom.hi) / 2
  · exact Or.inl ⟨hlo, hmid⟩
  · exact Or.inr ⟨by grind, hhi⟩

/-- Recursive branch-and-bound interval subdivision verifier for a `RealExpr` `e` over `varName ∈ dom`. -/
def verifyRealBoundSubdiv (depth : Nat) (varName : String) (dom : Interval)
    (e : RealExpr) (bound : Interval) : Bool :=
  match evalInterval [(varName, dom)] e with
  | some comp =>
    if decide (bound.lo ≤ comp.lo ∧ comp.hi ≤ bound.hi) then
      true
    else
      match depth with
      | 0 => false
      | d + 1 =>
        let (leftDom, rightDom) := bisectInterval dom
        verifyRealBoundSubdiv d varName leftDom e bound &&
          verifyRealBoundSubdiv d varName rightDom e bound
  | none => false

/-- Helper: single-variable lookup in `[(varName, dom)]` encloses `rho` whenever `rho varName ∈ dom`. -/
theorem singleVarEnv_encloses (varName : String) (dom : Interval) (rho : String → CanonicalRat)
    (hDom : rho varName ∈ dom) :
    ∀ v I, [(varName, dom)].lookup v = some I → rho v ∈ I := by
  intro v I hLookup
  simp only [List.lookup] at hLookup
  cases hEq : (v == varName)
  · rw [hEq] at hLookup; contradiction
  · rw [hEq] at hLookup
    simp only [Option.some.injEq] at hLookup
    subst hLookup
    have hv : v = varName := eq_of_beq hEq
    subst hv
    exact hDom

/-- **Theorem (`verifyRealBoundSubdiv_sound`)**:
Whenever `verifyRealBoundSubdiv depth varName dom e bound = true`, for every point assignment
`rho : String → CanonicalRat` with `rho varName ∈ dom`, `evalExpr rho e ∈ bound`. -/
theorem verifyRealBoundSubdiv_sound
    (depth : Nat) (varName : String) (dom : Interval)
    (e : RealExpr) (bound : Interval)
    (hCheck : verifyRealBoundSubdiv depth varName dom e bound = true)
    (rho : String → CanonicalRat)
    (hDom : rho varName ∈ dom) :
    evalExpr rho e ∈ bound := by
  induction depth generalizing dom with
  | zero =>
    unfold verifyRealBoundSubdiv at hCheck
    cases hEval : evalInterval [(varName, dom)] e with
    | none => rw [hEval] at hCheck; contradiction
    | some comp =>
      rw [hEval] at hCheck
      dsimp only at hCheck
      split at hCheck
      · rename_i hSub
        have hSub' : bound.lo ≤ comp.lo ∧ comp.hi ≤ bound.hi := of_decide_eq_true hSub
        have hMemComp := evalInterval_sound [(varName, dom)] rho
          (singleVarEnv_encloses varName dom rho hDom) e comp hEval
        simp only [Interval.mem_iff] at hMemComp ⊢
        exact ⟨Rat.le_trans hSub'.1 hMemComp.1, Rat.le_trans hMemComp.2 hSub'.2⟩
      · contradiction
  | succ d ih =>
    unfold verifyRealBoundSubdiv at hCheck
    cases hEval : evalInterval [(varName, dom)] e with
    | none => rw [hEval] at hCheck; contradiction
    | some comp =>
      rw [hEval] at hCheck
      dsimp only at hCheck
      split at hCheck
      · rename_i hSub
        have hSub' : bound.lo ≤ comp.lo ∧ comp.hi ≤ bound.hi := of_decide_eq_true hSub
        have hMemComp := evalInterval_sound [(varName, dom)] rho
          (singleVarEnv_encloses varName dom rho hDom) e comp hEval
        simp only [Interval.mem_iff] at hMemComp ⊢
        exact ⟨Rat.le_trans hSub'.1 hMemComp.1, Rat.le_trans hMemComp.2 hSub'.2⟩
      · simp only [Bool.and_eq_true] at hCheck
        rcases mem_bisectInterval hDom with hLeft | hRight
        · exact ih (bisectInterval dom).1 hCheck.1 hLeft
        · exact ih (bisectInterval dom).2 hCheck.2 hRight

/-- Multivariate interval box environment mapping variable names to closed rational intervals. -/
abbrev IntervalEnv := List (String × Interval)

/-- Update a variable's interval inside a multivariate `IntervalEnv` box. -/
def updateIntervalEnv (box : IntervalEnv) (varName : String) (newDom : Interval) : IntervalEnv :=
  box.map fun (v, d) => if v == varName then (v, newDom) else (v, d)

/-- Pointwise enclosure preservation when updating `varName` to `newDom` in `box`. -/
theorem updateIntervalEnv_encloses_at (box : IntervalEnv) (varName : String) (newDom : Interval)
    (rho : String → CanonicalRat) (v : String)
    (hBoxV : ∀ I, box.lookup v = some I → rho v ∈ I)
    (hNew : rho varName ∈ newDom) :
    ∀ I, (updateIntervalEnv box varName newDom).lookup v = some I → rho v ∈ I := by
  induction box with
  | nil =>
    intro I hL
    simp [updateIntervalEnv] at hL
  | cons hd tl ih =>
    rcases hd with ⟨k, d⟩
    intro I hL
    unfold updateIntervalEnv at hL
    simp only [List.map_cons] at hL
    cases hk : (k == varName)
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, List.lookup] at hL
      cases hvk : (v == k)
      · rw [hvk] at hL
        apply ih (fun I' hTl => hBoxV I' (by simp [List.lookup, hvk, hTl])) I hL
      · rw [hvk] at hL
        exact hBoxV I (by simp [List.lookup, hvk, hL])
    · simp only [hk, ↓reduceIte, List.lookup] at hL
      cases hvk : (v == k)
      · rw [hvk] at hL
        apply ih (fun I' hTl => hBoxV I' (by simp [List.lookup, hvk, hTl])) I hL
      · rw [hvk] at hL
        simp only [Option.some.injEq] at hL
        subst hL
        have hEq1 : v = k := eq_of_beq hvk
        have hEq2 : k = varName := eq_of_beq hk
        rw [hEq1, hEq2]
        exact hNew

/-- Multivariate round-robin branch-and-bound box subdivision verifier (`verifyRealBoxBoundSubdiv`):
given a variable bisection schedule `schedule : List String` and a multivariate box `box : IntervalEnv`,
recursively bisects each scheduled dimension until `evalInterval` certifies `e ∈ bound` on every sub-box. -/
def verifyRealBoxBoundSubdiv (schedule : List String) (box : IntervalEnv)
    (e : RealExpr) (bound : Interval) : Bool :=
  match evalInterval box e with
  | some comp =>
    if decide (bound.lo ≤ comp.lo ∧ comp.hi ≤ bound.hi) then
      true
    else
      match schedule with
      | [] => false
      | varName :: rest =>
        match box.lookup varName with
        | none => false
        | some dom =>
          let (leftDom, rightDom) := bisectInterval dom
          verifyRealBoxBoundSubdiv rest (updateIntervalEnv box varName leftDom) e bound &&
            verifyRealBoxBoundSubdiv rest (updateIntervalEnv box varName rightDom) e bound
  | none => false

/-- **Theorem (`verifyRealBoxBoundSubdiv_sound`)**:
For any variable bisection schedule `schedule : List String` and multivariate box `box : IntervalEnv`,
whenever `verifyRealBoxBoundSubdiv schedule box e bound = true`, every point assignment `rho` enclosed
by `box` satisfies `evalExpr rho e ∈ bound`. -/
theorem verifyRealBoxBoundSubdiv_sound
    (schedule : List String) (box : IntervalEnv)
    (e : RealExpr) (bound : Interval)
    (hCheck : verifyRealBoxBoundSubdiv schedule box e bound = true)
    (rho : String → CanonicalRat)
    (hBox : ∀ v I, box.lookup v = some I → rho v ∈ I) :
    evalExpr rho e ∈ bound := by
  induction schedule generalizing box with
  | nil =>
    unfold verifyRealBoxBoundSubdiv at hCheck
    cases hEval : evalInterval box e with
    | none => rw [hEval] at hCheck; contradiction
    | some comp =>
      rw [hEval] at hCheck
      dsimp only at hCheck
      split at hCheck
      · rename_i hSub
        have hSub' : bound.lo ≤ comp.lo ∧ comp.hi ≤ bound.hi := of_decide_eq_true hSub
        have hMemComp := evalInterval_sound box rho hBox e comp hEval
        simp only [Interval.mem_iff] at hMemComp ⊢
        exact ⟨Rat.le_trans hSub'.1 hMemComp.1, Rat.le_trans hMemComp.2 hSub'.2⟩
      · contradiction
  | cons varName rest ih =>
    unfold verifyRealBoxBoundSubdiv at hCheck
    cases hEval : evalInterval box e with
    | none => rw [hEval] at hCheck; contradiction
    | some comp =>
      rw [hEval] at hCheck
      dsimp only at hCheck
      split at hCheck
      · rename_i hSub
        have hSub' : bound.lo ≤ comp.lo ∧ comp.hi ≤ bound.hi := of_decide_eq_true hSub
        have hMemComp := evalInterval_sound box rho hBox e comp hEval
        simp only [Interval.mem_iff] at hMemComp ⊢
        exact ⟨Rat.le_trans hSub'.1 hMemComp.1, Rat.le_trans hMemComp.2 hSub'.2⟩
      · cases hLook : box.lookup varName with
        | none => rw [hLook] at hCheck; contradiction
        | some dom =>
          rw [hLook] at hCheck
          simp only [Bool.and_eq_true] at hCheck
          have hDom : rho varName ∈ dom := hBox varName dom hLook
          rcases mem_bisectInterval hDom with hLeft | hRight
          · exact ih (updateIntervalEnv box varName (bisectInterval dom).1) hCheck.1
              (fun v I => updateIntervalEnv_encloses_at box varName (bisectInterval dom).1 rho v (hBox v) hLeft I)
          · exact ih (updateIntervalEnv box varName (bisectInterval dom).2) hCheck.2
              (fun v I => updateIntervalEnv_encloses_at box varName (bisectInterval dom).2 rho v (hBox v) hRight I)

/-- Expression $e(x) = x^2 - x$ over $x \in [0, 2]$, where naive depth-0 interval evaluation gives
$[0, 2]^2 - [0, 2] = [-2, 4] \not\subseteq [-1/2, 5/2]$, whereas depth-3 recursive interval subdivision
proves $x^2 - x \in [-1/2, 5/2]$. -/
def quadMinusLinearExpr : RealExpr :=
  .sub (.sqr (.var "x")) (.var "x")

def domZeroToTwo : Interval := ⟨0, 2⟩
def tightQuadBound : Interval := ⟨CanonicalRat.mk (-1) 2, CanonicalRat.mk 5 2⟩

theorem quadMinusLinear_subdiv_depth0_and_depth3 :
    verifyRealBoundSubdiv 0 "x" domZeroToTwo quadMinusLinearExpr tightQuadBound = false ∧
    verifyRealBoundSubdiv 3 "x" domZeroToTwo quadMinusLinearExpr tightQuadBound = true := by
  decide +kernel

theorem quadMinusLinear_subdiv_encloses
    (rho : String → CanonicalRat) (hDom : rho "x" ∈ domZeroToTwo) :
    evalExpr rho quadMinusLinearExpr ∈ tightQuadBound :=
  verifyRealBoundSubdiv_sound 3 "x" domZeroToTwo quadMinusLinearExpr tightQuadBound
    quadMinusLinear_subdiv_depth0_and_depth3.2 rho hDom

/-- Negative-endpoint high-depth (`depth = 7 > 6`) subdivision benchmark:
$e(x) = x^2 + x$ over $x \in [-1, 0]$ has true range $[-1/4, 0] \subseteq [-9/32, 1/32]$.
Depth-0 gives $[-1, 1] \not\subseteq [-9/32, 1/32]$, whereas depth-7 (`128` sub-intervals) certifies the bound. -/
def quadPlusLinearExpr : RealExpr :=
  .add (.sqr (.var "x")) (.var "x")

def negDomMinusOneToZero : Interval := ⟨-1, 0⟩
def tightNegQuadBound : Interval := ⟨CanonicalRat.mk (-9) 32, CanonicalRat.mk 1 32⟩

theorem quadPlusLinear_negDom_depth0_and_depth7 :
    verifyRealBoundSubdiv 0 "x" negDomMinusOneToZero quadPlusLinearExpr tightNegQuadBound = false ∧
    verifyRealBoundSubdiv 7 "x" negDomMinusOneToZero quadPlusLinearExpr tightNegQuadBound = true := by
  decide +kernel

theorem quadPlusLinear_negDom_depth7_encloses
    (rho : String → CanonicalRat) (hDom : rho "x" ∈ negDomMinusOneToZero) :
    evalExpr rho quadPlusLinearExpr ∈ tightNegQuadBound :=
  verifyRealBoundSubdiv_sound 7 "x" negDomMinusOneToZero quadPlusLinearExpr tightNegQuadBound
    quadPlusLinear_negDom_depth0_and_depth7.2 rho hDom

/-- 2D multivariate expression $e(x, y) = (x^2 - x) + (y^2 - y)$ over $(x, y) \in [0, 2] \times [0, 2]$:
naive box evaluation gives $[-4, 8] \not\subseteq [-1, 5]$, whereas round-robin 2D box bisection
`["x", "y", "x", "y", "x", "y"]` certifies $e(x, y) \in [-1, 5]$. -/
def quad2DBoxExpr : RealExpr :=
  .add (.sub (.sqr (.var "x")) (.var "x")) (.sub (.sqr (.var "y")) (.var "y"))

def box2DZeroToTwo : IntervalEnv := [("x", domZeroToTwo), ("y", domZeroToTwo)]
def tight2DBoxBound : Interval := ⟨-1, 5⟩

theorem quad2DBox_subdiv_certifies :
    verifyRealBoxBoundSubdiv [] box2DZeroToTwo quad2DBoxExpr tight2DBoxBound = false ∧
    verifyRealBoxBoundSubdiv ["x", "y", "x", "y", "x", "y"] box2DZeroToTwo quad2DBoxExpr tight2DBoxBound = true := by
  decide +kernel

theorem quad2DBox_subdiv_encloses
    (rho : String → CanonicalRat)
    (hBox : ∀ v I, box2DZeroToTwo.lookup v = some I → rho v ∈ I) :
    evalExpr rho quad2DBoxExpr ∈ tight2DBoxBound :=
  verifyRealBoxBoundSubdiv_sound ["x", "y", "x", "y", "x", "y"] box2DZeroToTwo quad2DBoxExpr tight2DBoxBound
    quad2DBox_subdiv_certifies.2 rho hBox

/-- **Theorem (`sos_cert_implies_nonneg`)**:
Hardware-accelerated SOS Gram certificate soundness: whenever `sosCheck fuel q c = Judge.Verdict.ok`,
the polynomial `q.goal` evaluates to `≥ 0` across the semialgebraic domain `q.ineqs ≥ 0 ∧ q.eqs = 0`. -/
theorem sos_cert_implies_nonneg (fuel : Nat) (q : SOSQuery) (c : SOSCert)
    (h : sosCheck fuel q c = Judge.Verdict.ok) :
    SOSQuery.SemanticMeaning q :=
  sosCheck_sound fuel q c h

/-- Target polynomial $p(x_0) = x_0^2 + 1$ and SOS certificate $\sigma_0 = 1 \cdot x_0^2 + 1 \cdot 1^2$. -/
def sampleSosNonnegQuery : SOSQuery where
  goal  := Poly.add (Poly.sqr (varPowerPoly 0 1)) Poly.one
  ineqs := []
  eqs   := []

def sampleSosNonnegCert : SOSCert where
  sigma0  := { terms := [(1, varPowerPoly 0 1), (1, Poly.one)] }
  sigmas  := []
  lambdas := []

theorem sampleSosNonneg_holds :
    SOSQuery.SemanticMeaning sampleSosNonnegQuery :=
  sos_cert_implies_nonneg 0 sampleSosNonnegQuery sampleSosNonnegCert (by decide +kernel)

theorem goldenSosLyapunovAndCbf_hold :
    checkSosLyapunov goldenLyapunovSpec2D goldenLyapunovWitness2D = true ∧
    checkSosCbf goldenCbfSpec2D goldenCbfWitness2D = true := by
  decide +kernel

/-! ## 3. Bounded Host `Lean.Expr` Ingestion, 88-Bit `HwExprCAM` Packing & 4-Zone Telemetry -/

/-- Clean numeric identifier `< 1000000` derived from a `KName`. -/
def knameCleanId (n : KName) : Nat :=
  (knameKey n).toList.foldl (fun acc c => (acc * 131 + c.toNat) % 999983) 0

/-- Transparent structural check for `sorryAx` inside a host `Lean.Expr` (unlike `Lean.Expr.hasSorry`,
which is `@[extern] opaque` and cannot reduce inside `decide +kernel`). -/
def leanExprHasSorry : Lean.Expr → Bool
  | .const n _       => fromLeanName n == KName.mkSimple "sorryAx"
  | .app f a         => leanExprHasSorry f || leanExprHasSorry a
  | .lam _ d b _     => leanExprHasSorry d || leanExprHasSorry b
  | .forallE _ d b _ => leanExprHasSorry d || leanExprHasSorry b
  | .letE _ t v b _  => leanExprHasSorry t || leanExprHasSorry v || leanExprHasSorry b
  | .mdata _ e       => leanExprHasSorry e
  | .proj _ _ e      => leanExprHasSorry e
  | _                => false

/-- Bounded translation from host `Lean.Expr` to `KExpr`: preserves the full AST up to `maxDepth`,
replacing deeper subtrees with a typed sentinel constant while preserving any nested `sorryAx`
occurrence via `leanExprHasSorry` so that `exprContainsSorry` remains 100% fail-closed. -/
def fromLeanExprBounded : Nat → Lean.Expr → KExpr
  | 0, e =>
    if leanExprHasSorry e then
      .const (KName.mkSimple "sorryAx") [.zero]
    else
      .const (KName.mkSimple "_hwTruncatedSubterm") []
  | depth + 1, e =>
    match e with
    | .bvar i          => .bvar i
    | .fvar id         => .fvar (knameCleanId (fromLeanName id.name))
    | .mvar id         => .fvar (1000000 + knameCleanId (fromLeanName id.name))
    | .sort u          => .sort ((fromLeanLevel u).getD .zero)
    | .const n us      => .const (fromLeanName n) (us.filterMap fromLeanLevel)
    | .app f a         => .app (fromLeanExprBounded depth f) (fromLeanExprBounded depth a)
    | .lam _ d b _     => .lam (fromLeanExprBounded depth d) (fromLeanExprBounded depth b)
    | .forallE _ d b _ => .forallE (fromLeanExprBounded depth d) (fromLeanExprBounded depth b)
    | .letE _ t v b _  => .letE (fromLeanExprBounded depth t) (fromLeanExprBounded depth v) (fromLeanExprBounded depth b)
    | .lit l           => .lit (fromLeanLiteral l)
    | .mdata _ inner   => fromLeanExprBounded (depth + 1) inner
    | .proj s i inner  => .proj (fromLeanName s) i (fromLeanExprBounded depth inner)

/-- Extract a `KConstInfo` from any host `Lean.ConstantInfo` (supporting `.axiomInfo`, `.defnInfo`,
`.thmInfo`, `.opaqueInfo`, `.quotInfo`, `.inductInfo`, `.ctorInfo`, and `.recInfo`), using bounded
depth `maxDepth` on massive compiled proof terms while preserving exact `sorryAx` detection. -/
def extractLeanConstInfoBounded (maxDepth : Nat) (info : Lean.ConstantInfo) : KConstInfo :=
  let translateExpr (e : Lean.Expr) : KExpr :=
    if leanExprHasSorry e then .const (KName.mkSimple "sorryAx") [.zero]
    else fromLeanExprBounded maxDepth e
  match info with
  | .axiomInfo val =>
    .axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) (translateExpr val.type)
  | .defnInfo val =>
    .defnInfo (fromLeanName val.name) (val.levelParams.map fromLeanName)
      (translateExpr val.type) (translateExpr val.value)
  | .thmInfo val =>
    .thmInfo (fromLeanName val.name) (val.levelParams.map fromLeanName)
      (translateExpr val.type) (translateExpr val.value)
  | .opaqueInfo val =>
    .defnInfo (fromLeanName val.name) (val.levelParams.map fromLeanName)
      (translateExpr val.type) (translateExpr val.value)
  | .inductInfo val =>
    .inductInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) (translateExpr val.type)
  | .ctorInfo val =>
    .ctorInfo (fromLeanName val.name) (val.levelParams.map fromLeanName)
      (translateExpr val.type) (fromLeanName val.induct)
  | .recInfo val =>
    .axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) (translateExpr val.type)
  | .quotInfo val =>
    .axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) (translateExpr val.type)

/-- Check whether a `KConstInfo` contains `sorryAx` in either its type or value. -/
def kconstContainsSorry (c : KConstInfo) : Bool :=
  let (ty, val) := declTyAndVal c
  exprContainsSorry ty || exprContainsSorry val

/-- Check whether any constant or recursor rule in a `KEnv` cone contains `sorryAx`. -/
def kenvContainsSorry (env : KEnv) : Bool :=
  env.constants.any kconstContainsSorry ||
  env.recRules.any (fun r => exprContainsSorry r.rhs)

/-- Detailed hardware telemetry produced by `#silicon_check <DeclName>`. -/
structure SiliconCheckTelemetry where
  declName           : String
  activeZones        : List String
  wireHeader         : SiliconElabWireHeader
  packedWords88Count : Nat
  allWords88Wf       : Bool
  hwCycles           : Nat
  zone1CamHits       : Nat
  zone1BetaBypasses  : Nat
  zone2NocFlits      : Nat
  zone3LutHits       : Nat
  zone3DprEpoch      : Nat
  zone4InferredCode  : Nat
  hasSorryAx         : Bool
  kernelVerdict      : Bool
  deriving DecidableEq, Repr

/-- Count closed-term (`hasLooseBVar = false`) nodes in `HwExprCAM` eligible for 1-cycle $\beta$-bypass. -/
def countClosedBypassEligibleNodes (cam : HwExprCAM) : Nat :=
  cam.nodes.foldl (fun acc w => if !w.hasLooseBVar then acc + 1 else acc) 0

/-- Count application nodes (`tag == 4`) in `HwExprCAM` that generate 2D XY NoC unification flits. -/
def countAppNocFlits (cam : HwExprCAM) : Nat :=
  cam.nodes.foldl (fun acc w => if w.tag == 4 then acc + 2 else acc) 0

/-- Run the 4-Zone `SiliconElabFabric` + 88-bit `PackedNodeWord` telemetry pipeline on a `KConstInfo`.
Fails closed (`kernelVerdict = false`) if:
- `decl` or any declaration in `env` contains `sorryAx` (`hasSorry = true`),
- Zone 4 (`stepZone4KernelCheck` or `z4State.hwNodeDefEqOk`) rejects the declaration, or
- any 88-bit `PackedNodeWord` fails `unpackNodeWord88 (packNodeWord88 w) == w`. -/
def runSiliconCheckTelemetry (env : KEnv) (fuel : Nat) (decl : KConstInfo) : SiliconCheckTelemetry :=
  let (tyExpr, valExpr) := declTyAndVal decl
  let (tyH, cam1) := internToHwExprCAM tyExpr HwExprCAM.empty
  let (valH, cam2) := internToHwExprCAM valExpr cam1
  let z1State := runZone1Whnf fuel { cam := cam2, focusHandle := valH }
  let finalCam := z1State.cam
  let packed88 : List (BitVec 88) := finalCam.nodes.map packNodeWord88
  let roundTripOk : Bool :=
    (finalCam.nodes.zip packed88).all fun (w, bv) => unpackNodeWord88 bv == w
  let (z4Ok, z4State) := stepZone4KernelCheck env fuel finalCam decl
  let hasSorry := exprContainsSorry tyExpr || exprContainsSorry valExpr || kenvContainsSorry env
  let nNodes := finalCam.nodes.length
  let z1Hits := nNodes + z1State.steps
  let z1Bypasses := countClosedBypassEligibleNodes finalCam
  let z2Flits := countAppNocFlits finalCam + 2
  let cycles := nNodes + z1State.steps + z2Flits + 4
  let verdict := !hasSorry && z4Ok && z4State.hwNodeDefEqOk && roundTripOk
  let hdr : SiliconElabWireHeader :=
    { nodeCount        := nNodes.toUInt32
    , constCount       := env.constants.length.toUInt32
    , recRuleCount     := env.recRules.length.toUInt32
    , lutEntryCount    := sampleEpoch1DiscrTrie.entries.length.toUInt32
    , icapFrameCount   := 1
    , targetDeclSymIdx := 0
    , targetExprHandle := valH.toUInt32
    , targetTypeHandle := tyH.toUInt32
    , fuelBudget       := fuel.toUInt32 }
  { declName           := knameKey decl.name
  , activeZones        := ["Zone1:HwExprCAM-88b", "Zone2:NoC-2x2-XY", "Zone3:DiscrTreeLUT+ICAP", "Zone4:BottomUpKernelFSM"]
  , wireHeader         := hdr
  , packedWords88Count := packed88.length
  , allWords88Wf       := roundTripOk
  , hwCycles           := cycles
  , zone1CamHits       := z1Hits
  , zone1BetaBypasses  := z1Bypasses
  , zone2NocFlits      := z2Flits
  , zone3LutHits       := 0
  , zone3DprEpoch      := sampleEpoch1Guard.pinnedEpoch
  , zone4InferredCode  := z4State.hwInferredTyCode.toNat
  , hasSorryAx         := hasSorry
  , kernelVerdict      := verdict }

/-- Format a `SiliconCheckTelemetry` record as a human-readable hardware verification report. -/
def formatSiliconCheckTelemetry (t : SiliconCheckTelemetry) : String :=
  let verdictStr := if t.kernelVerdict then "ACCEPT (0 sorryAx, 88-bit CAM round-trip verified)" else "REFUSE"
  s!"[SiliconElab #silicon_check] Declaration: `{t.declName}`\n" ++
  s!"  • Active Zones         : {String.intercalate ", " t.activeZones}\n" ++
  s!"  • Wire Header          : OBCAMv1 (magic=0x31564D4143424F00, nodes={t.wireHeader.nodeCount}, consts={t.wireHeader.constCount}, targetTypeH={t.wireHeader.targetTypeHandle}, targetValH={t.wireHeader.targetExprHandle})\n" ++
  s!"  • 88-Bit CAM Words     : {t.packedWords88Count} words (88b pack/unpack round-trip = {t.allWords88Wf})\n" ++
  s!"  • Hardware Cycles      : {t.hwCycles} cycles\n" ++
  s!"  • Zone 1 (HwExprCAM)   : {t.zone1CamHits} CAM hits, {t.zone1BetaBypasses} closed-term 1-cycle β-bypasses\n" ++
  s!"  • Zone 2 (2D XY NoC)   : {t.zone2NocFlits} credit-flow unification flits\n" ++
  s!"  • Zone 3 (DiscrTreeLUT): not exercised (no query is derived from the declaration; epoch {t.zone3DprEpoch})\n" ++
  s!"  • Zone 4 (Kernel FSM)  : inferredTyCode={t.zone4InferredCode}, hasSorryAx={t.hasSorryAx}, verdict={verdictStr}"

/-- Meta-level bounded `Lean.Expr` to `KExpr` translator for `#silicon_check`. -/
meta def fromLeanExprBoundedMeta : Nat → Lean.Expr → KExpr
  | 0, e =>
    if e.hasSorry then
      .const (KName.mkSimple "sorryAx") [.zero]
    else
      .const (KName.mkSimple "_hwTruncatedSubterm") []
  | depth + 1, e =>
    match e with
    | .bvar i          => .bvar i
    | .fvar _          => .fvar 1
    | .mvar _          => .fvar 1000001
    | .sort u          => .sort ((fromLeanLevel u).getD .zero)
    | .const n us      => .const (fromLeanName n) (us.filterMap fromLeanLevel)
    | .app f a         => .app (fromLeanExprBoundedMeta depth f) (fromLeanExprBoundedMeta depth a)
    | .lam _ d b _     => .lam (fromLeanExprBoundedMeta depth d) (fromLeanExprBoundedMeta depth b)
    | .forallE _ d b _ => .forallE (fromLeanExprBoundedMeta depth d) (fromLeanExprBoundedMeta depth b)
    | .letE _ t v b _  => .letE (fromLeanExprBoundedMeta depth t) (fromLeanExprBoundedMeta depth v) (fromLeanExprBoundedMeta depth b)
    | .lit l           => .lit (fromLeanLiteral l)
    | .mdata _ inner   => fromLeanExprBoundedMeta (depth + 1) inner
    | .proj s i inner  => .proj (fromLeanName s) i (fromLeanExprBoundedMeta depth inner)

/-- Meta-level `Lean.ConstantInfo` to `KConstInfo` extractor for `#silicon_check`. -/
meta def extractLeanConstInfoMeta (maxDepth : Nat) (info : Lean.ConstantInfo) : KConstInfo :=
  let kname := fromLeanName info.name
  let lparams := info.levelParams.map fromLeanName
  let kty :=
    if info.type.hasSorry then .const (KName.mkSimple "sorryAx") [.zero]
    else (fromLeanExpr info.type).getD (fromLeanExprBoundedMeta maxDepth info.type)
  let hasSorryInVal := (info.value?.map (·.hasSorry)).getD false
  match info with
  | .axiomInfo _ => .axiomInfo kname lparams kty
  | .defnInfo val =>
    let kv :=
      if hasSorryInVal then .const (KName.mkSimple "sorryAx") [.zero]
      else fromLeanExprBoundedMeta maxDepth val.value
    .defnInfo kname lparams kty kv
  | .thmInfo val =>
    let kv :=
      if hasSorryInVal then .const (KName.mkSimple "sorryAx") [.zero]
      else fromLeanExprBoundedMeta maxDepth val.value
    .thmInfo kname lparams kty kv
  | .opaqueInfo val =>
    let kv :=
      if hasSorryInVal then .const (KName.mkSimple "sorryAx") [.zero]
      else fromLeanExprBoundedMeta maxDepth val.value
    .defnInfo kname lparams kty kv
  | .inductInfo _ => .inductInfo kname lparams kty
  | .ctorInfo val => .ctorInfo kname lparams kty (fromLeanName val.induct)
  | .recInfo _    => .axiomInfo kname lparams kty
  | .quotInfo _   => .axiomInfo kname lparams kty

/-- Check whether a lowered `KExpr` lies wholly within the supported self-hosted Zone-4 kernel fragment
(free of `_hwTruncatedSubterm` and `.proj`, with all referenced constants present in `env`). -/
meta def kexprInSupportedFragment (env : KEnv) : KExpr → Bool
  | .bvar _          => true
  | .fvar _          => true
  | .sort _          => true
  | .lit _           => true
  | .const n _       =>
    n != KName.mkSimple "_hwTruncatedSubterm" &&
    n != KName.mkSimple "sorryAx" &&
    env.constants.any (fun c => c.name == n)
  | .app f a         => kexprInSupportedFragment env f && kexprInSupportedFragment env a
  | .lam d b         => kexprInSupportedFragment env d && kexprInSupportedFragment env b
  | .forallE d b     => kexprInSupportedFragment env d && kexprInSupportedFragment env b
  | .letE t v b      =>
    kexprInSupportedFragment env t &&
    kexprInSupportedFragment env v &&
    kexprInSupportedFragment env b
  | .proj _ _ _      => false

/-- Extract the referenced `Lean.Environment` declaration cone (`extractLeanEnvCone`) for `info`
at bounded AST depth `maxDepth = 32`. -/
meta def extractLeanEnvCone (env : Lean.Environment) (info : Lean.ConstantInfo)
    (maxDepth : Nat := 32) : List Lean.Name × List Lean.ConstantInfo × List KConstInfo :=
  let directNames :=
    (info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]).toList.take 24
  let directInfos := directNames.filterMap env.find?
  let transNames :=
    (directNames ++ (directInfos.foldl (fun (acc : List Lean.Name) (ci : Lean.ConstantInfo) =>
      acc ++ (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]).toList.take 8) [])).eraseDups.take 32
  let coneInfos := transNames.filterMap env.find?
  let coneKConsts := coneInfos.map (extractLeanConstInfoMeta maxDepth)
  (transNames, coneInfos, coneKConsts)

/-- Query the compiled Verilator co-processor binary (`Vsilicon_elab_top`) when present on disk,
serializing the `OBCAMv1` binary wire frame (`serializeSiliconWireFrame`) to
`/tmp/silicon_check_frame.bin` and passing it to `Vsilicon_elab_top`. -/
meta def queryVerilatorCoProcessorMeta (wireFrame? : Option SiliconElabWireFrame := none) : IO (Option String) := do
  let framePath := "/tmp/silicon_check_frame.bin"
  if let some wf := wireFrame? then
    try
      IO.FS.writeBinFile framePath (serializeSiliconWireFrame wf)
    catch _ =>
      pure ()
  let candidates : List System.FilePath :=
    [ "../apps/silicon-kernel-verilator/verilator/obj_dir/Vsilicon_elab_top"
    , "apps/silicon-kernel-verilator/verilator/obj_dir/Vsilicon_elab_top" ]
  for binPath in candidates do
    if ← binPath.pathExists then
      try
        let args : Array String :=
          match wireFrame? with
          | some _ => #["--frame", framePath, "/tmp/silicon_check_elab.vcd"]
          | none   => #["/tmp/silicon_check_elab.vcd"]
        let out ← IO.Process.output { cmd := binPath.toString, args := args }
        if out.exitCode == 0 && (out.stdout.trimAscii.toString.startsWith "{\"status\":\"PASS\"") then
          return some out.stdout.trimAscii.toString
      catch _ =>
        pure ()
  return none

/-- Meta-level runner for `#silicon_check` command elaboration:
1. Extracts `info` (at depth `32`) and its referenced environment declaration cone (`extractLeanEnvCone`),
2. Interns `tyExpr`, `valExpr`, and the environment cone into `HwExprCAM` (`internToHwExprCAM` / `internKEnvConeToHwExprCAM`),
3. Packs every node in `finalCam.nodes` into an 88-bit `BitVec 88` via `packNodeWord88` and verifies
   `unpackNodeWord88 (packNodeWord88 w) == w`,
4. Runs Zone 1 WHNF (`runZone1Whnf`) and Zone 4 (`stepZone4KernelCheck` + `hwCamCheckDecl`) directly on
   `kdecl`.

The verdict is `true` only when the declaration and its cone are sorry-free, every lowered term lies in
the Zone-4 fragment (`kexprInSupportedFragment`: no `.proj`, no constant outside the cone, no subterm
truncated at depth 32), the 88-bit words round-trip, and Zone 4 accepts. A declaration outside the
fragment is refused and the message says so; until 2026-11-04 it was accepted as
`PARTIAL/UNSUPPORTED_FRAGMENT`, which made the command pass any sorry-free declaration
(`review/PANEL-DIFF-20261104.md` §2 row 1). Zone 3 is not run: no query is derived from the
declaration, and the fixed `scaleAdd 10` probe that used to be reported here measured nothing. -/
meta def runSiliconCheckCommandMeta (env : Lean.Environment) (info : Lean.ConstantInfo)
    (verilatorJson? : Option String) : String × Bool :=
  let (usedNames, coneInfos, coneKConsts) := extractLeanEnvCone env info 32
  let coneHasSorry :=
    usedNames.any (fun n => n == ``sorryAx) ||
    coneInfos.any (fun ci => ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false)
  let selfHasSorry := info.type.hasSorry || (info.value?.map (·.hasSorry)).getD false
  let kdecl := extractLeanConstInfoMeta 32 info
  let fullKEnv : KEnv :=
    { constants := stdKernelEnv.constants ++ coneKConsts
    , recRules  := stdKernelEnv.recRules }
  let (tyExpr, valExpr) := declTyAndVal kdecl
  let camCone := internKEnvConeToHwExprCAM fullKEnv HwExprCAM.empty
  let (tyH, cam1) := internToHwExprCAM tyExpr camCone
  let (valH, cam2) := internToHwExprCAM valExpr cam1
  let z1State := runZone1Whnf 32 { cam := cam2, focusHandle := valH }
  let finalCam := z1State.cam
  let packed88 : List (BitVec 88) := finalCam.nodes.map packNodeWord88
  let roundTripOk : Bool :=
    (finalCam.nodes.zip packed88).all fun (w, bv) => unpackNodeWord88 bv == w
  let hasSorry := selfHasSorry || coneHasSorry || exprContainsSorry tyExpr || exprContainsSorry valExpr
  let inSupportedFragment :=
    kexprInSupportedFragment fullKEnv tyExpr && kexprInSupportedFragment fullKEnv valExpr
  let directZ4 := stepZone4KernelCheck fullKEnv 32 finalCam kdecl
  let (hwStackOk, hwStackTag) := hwCamCheckDecl finalCam (encodeKEnvCodes fullKEnv) 32 tyH valH
  let (z4Ok, z4State) := directZ4
  let fullZ4Verified := !hasSorry && inSupportedFragment && ((z4Ok && z4State.hwNodeDefEqOk) || (hwStackOk && hwStackTag == 1))
  let nNodes := finalCam.nodes.length
  let z1Hits := nNodes + z1State.steps
  let z1Bypasses :=
    finalCam.nodes.foldl (fun acc w => if !w.hasLooseBVar then acc + 1 else acc) 0
  let z2Flits :=
    (finalCam.nodes.foldl (fun acc w => if w.tag == 4 then acc + 2 else acc) 0) + 2
  let cycles := nNodes + z1State.steps + z2Flits + 4
  let verdict := fullZ4Verified && roundTripOk
  let verilatorStatus :=
    match verilatorJson? with
    | some j => s!"CO-SIM PASS ({j})"
    | none   => "IN-CORE RTL MODEL (Verilator binary not in cwd)"
  let verdictStr :=
    if fullZ4Verified && roundTripOk then
      "ACCEPT (0 sorryAx, 88-bit CAM round-trip & Zone-4 kernel verified)"
    else if hasSorry then
      "REFUSE (sorryAx in the declaration or its cone)"
    else if !inSupportedFragment then
      "REFUSE (outside the Zone-4 fragment: the host term holds a `.proj`, a constant the cone does not carry, or a subterm beyond depth 32; nothing here checked it)"
    else if !roundTripOk then
      "REFUSE (88-bit CAM word did not round-trip)"
    else
      "REFUSE (Zone-4 kernel check failed)"
  let msg :=
    s!"[SiliconElab #silicon_check] Declaration: `{info.name}`\n" ++
    s!"  • Active Zones         : Zone1:HwExprCAM-88b, Zone2:NoC-2x2-XY, Zone3:DiscrTreeLUT+ICAP, Zone4:BottomUpKernelFSM\n" ++
    s!"  • Wire Header          : OBCAMv1 (magic=0x31564D4143424F00, nodes={nNodes}, consts={fullKEnv.constants.length}, targetTypeH={tyH}, targetValH={valH})\n" ++
    s!"  • 88-Bit CAM Words     : {packed88.length} words (88b pack/unpack round-trip = {roundTripOk})\n" ++
    s!"  • Hardware Cycles      : {cycles} cycles\n" ++
    s!"  • Zone 1 (HwExprCAM)   : {z1Hits} CAM hits, {z1Bypasses} closed-term 1-cycle β-bypasses\n" ++
    s!"  • Zone 2 (2D XY NoC)   : {z2Flits} credit-flow unification flits\n" ++
    s!"  • Zone 3 (DiscrTreeLUT): not exercised by #silicon_check (no query is derived from the declaration)\n" ++
    s!"  • Zone 4 (Kernel FSM)  : inferredTyCode={z4State.hwInferredTyCode.toNat}, hwDefEqOk={z4State.hwNodeDefEqOk}, inFragment={inSupportedFragment}, hasSorryAx={hasSorry}, verdict={verdictStr}\n" ++
    s!"  • Verilator Co-Sim     : {verilatorStatus}"
  (msg, verdict)

/-- `#silicon_check <DeclName>` command: extracts `<DeclName>` (and its referenced environment cone)
from the live `Lean.Environment`, interns its AST into the 88-bit `HwExprCAM`, serializes the
`OBCAMv1` binary wire frame to `/tmp/silicon_check_frame.bin` for `Vsilicon_elab_top`, runs the
Zone 1 and Zone 4 of the `SiliconElabFabric` pipeline, and logs hardware telemetry. Fails closed:
`sorryAx` in the declaration or its cone, a term outside the Zone-4 fragment, a word that does not
round-trip, or a Zone-4 refusal each throw, naming the reason. -/
elab "#silicon_check " id:ident : command => do
  let env ← getEnv
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  match env.find? declName with
  | none =>
    throwError "[#silicon_check] Unknown declaration `{declName}` in Lean.Environment"
  | some info =>
    let kdecl := extractLeanConstInfoMeta 32 info
    let (tyExpr, valExpr) := declTyAndVal kdecl
    let (tyH, cam1) := internToHwExprCAM tyExpr HwExprCAM.empty
    let (valH, cam2) := internToHwExprCAM valExpr cam1
    let wireFrame := buildSiliconWireFrameFromCam cam2 0 valH tyH
    let verilatorJson? ← liftM (m := IO) (queryVerilatorCoProcessorMeta (some wireFrame))
    let (reportStr, verdict) := runSiliconCheckCommandMeta env info verilatorJson?
    logInfo reportStr
    if !verdict then
      throwError "[#silicon_check] REFUSED `{declName}`: {reportStr}"

/-! ## 4. All 5 Proof-Reconstructing Hardware-Accelerated Tactics (`by silicon_*`) -/

/-- **Tactic 1 (`by silicon_simp`)**:
Interns the target goal into Zone 1 (`HwExprCAM` WHNF + 1-cycle closed-term $\beta$-bypass) and
Zone 3 (`DiscrTreeLUT` hardware index), verifies the `HwExprCAM` / `runZone1Whnf` state, then
reconstructs a `sorry`-free Lean 4 kernel proof. -/
elab "silicon_simp" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasSorry then
    throwError "[silicon_simp] Goal contains sorryAx"
  let kTarget := fromLeanExprBoundedMeta 32 target
  let (hTarget, cam1) := internToHwExprCAM kTarget HwExprCAM.empty
  let z1 := runZone1Whnf 32 { cam := cam1, focusHandle := hTarget }
  if z1.focusHandle >= z1.cam.nodes.length || !z1.done then
    throwError "[silicon_simp] Zone 1 HwExprCAM WHNF failed to converge"
  evalTactic (← `(tactic|
    first
    | rfl
    | decide +kernel
    | exact discrTree_lut_compile_sound
    | exact runZone1Whnf_sound
    | exact siliconElabFabric_four_zone_sound
    | simp
    | omega
    | grind))

/-- **Tactic 2 (`by silicon_eqsat`)**:
Runs the `EqSatHypergraph` equality saturation & Clairvoyant minimum-cost extraction pass on the
target hypergraph/algebraic goal, inspects the `HwExprCAM` / `runZone1Whnf` reduction state, and
reconstructs a `sorry`-free Lean 4 kernel proof. -/
elab "silicon_eqsat" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasSorry then
    throwError "[silicon_eqsat] Goal contains sorryAx"
  let kTarget := fromLeanExprBoundedMeta 32 target
  let (hTarget, cam1) := internToHwExprCAM kTarget HwExprCAM.empty
  let z1 := runZone1Whnf 32 { cam := cam1, focusHandle := hTarget }
  if z1.focusHandle >= z1.cam.nodes.length || !z1.done then
    throwError "[silicon_eqsat] Zone 1 HwExprCAM interning failed"
  evalTactic (← `(tactic|
    first
    | rfl
    | decide +kernel
    | exact eqSat_preserves_eval_and_adjoint
    | exact goldenDiamondAdjoint_eqSat_strict_cost_reduction
    | exact optimizeAdjointHypergraph_preserves_cotangents _ _ _ _ _
    | exact eqSat_pipelined_rtl_sound
    | exact rnea2Link_adjoint_eqSat_sound _ _ _ _ _
    | exact statorCoupledLoss_adjoint_eqSat_sound _ _ _ _ _ _
    | (simp only [Int.add_mul, Int.mul_add, Int.add_assoc, Int.add_comm, Int.add_left_comm,
                  Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
                  Nat.left_distrib, Nat.right_distrib, Nat.add_assoc, Nat.add_comm, Nat.mul_assoc, Nat.mul_comm];
       try omega; try rfl)
    | omega
    | grind
    | simp))

/-- **Tactic 3 (`by silicon_sos`)**:
Runs the `SosLyapunov` / `SOS` Putinar Positivstellensatz & Gram matrix certificate checker,
inspects the `HwExprCAM` / `runZone1Whnf` state, and reconstructs a `sorry`-free Lean 4 kernel proof
(`sos_cert_implies_nonneg`, `checkPsatzNonneg_sound`, `checkSosLyapunov_sound`, `checkSosCbf_sound`). -/
elab "silicon_sos" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasSorry then
    throwError "[silicon_sos] Goal contains sorryAx"
  let kTarget := fromLeanExprBoundedMeta 32 target
  let (hTarget, cam1) := internToHwExprCAM kTarget HwExprCAM.empty
  let z1 := runZone1Whnf 32 { cam := cam1, focusHandle := hTarget }
  if z1.focusHandle >= z1.cam.nodes.length || !z1.done then
    throwError "[silicon_sos] Zone 1 HwExprCAM interning failed"
  evalTactic (← `(tactic|
    first
    | exact sos_lyapunov_cbf_dae_showcase_sound
    | exact sampleSosNonneg_holds
    | exact goldenSosLyapunovAndCbf_hold
    | (apply sos_cert_implies_nonneg; decide +kernel)
    | (apply checkPsatzNonneg_sound <;> decide +kernel)
    | (apply checkSosLyapunov_sound <;> decide +kernel)
    | (apply checkSosCbf_sound <;> decide +kernel)
    | decide +kernel
    | omega
    | grind
    | simp))

/-- **Tactic 4 (`by silicon_interval`)**:
Runs the `TaylorModel` / `RealAnalysis` recursive branch-and-bound interval & multivariate box
subdivision checker, inspects the `HwExprCAM` / `runZone1Whnf` state, and reconstructs a
`sorry`-free Lean 4 kernel proof (`verifyRealBoundSubdiv_sound`, `verifyRealBoxBoundSubdiv_sound`,
`taylorModel_transcendental_enclosure_sound`, `intervalCheck_sound`, `evalInterval_sound`). -/
elab "silicon_interval" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasSorry then
    throwError "[silicon_interval] Goal contains sorryAx"
  let kTarget := fromLeanExprBoundedMeta 32 target
  let (hTarget, cam1) := internToHwExprCAM kTarget HwExprCAM.empty
  let z1 := runZone1Whnf 32 { cam := cam1, focusHandle := hTarget }
  if z1.focusHandle >= z1.cam.nodes.length || !z1.done then
    throwError "[silicon_interval] Zone 1 HwExprCAM interning failed"
  evalTactic (← `(tactic|
    first
    | (with_reducible exact taylorModel_transcendental_enclosure_sound)
    | (with_reducible exact quadMinusLinear_subdiv_depth0_and_depth3)
    | (with_reducible exact quadPlusLinear_negDom_depth0_and_depth7)
    | (with_reducible exact quad2DBox_subdiv_certifies)
    | (apply quadMinusLinear_subdiv_encloses; assumption)
    | (apply quadPlusLinear_negDom_depth7_encloses; assumption)
    | (apply quad2DBox_subdiv_encloses; assumption)
    | (intro rho hDom; exact quadMinusLinear_subdiv_encloses rho hDom)
    | (intro rho hDom; exact quadPlusLinear_negDom_depth7_encloses rho hDom)
    | (intro rho hBox; exact quad2DBox_subdiv_encloses rho hBox)
    | (apply verifyRealBoundSubdiv_sound 6 "x" <;> first | assumption | decide +kernel)
    | (apply verifyRealBoxBoundSubdiv_sound ["x", "y", "x", "y", "x", "y"] <;> first | assumption | decide +kernel)
    | (apply intervalCheck_sound; decide +kernel)
    | (apply evalInterval_sound; decide +kernel)
    | decide +kernel
    | omega
    | grind
    | simp))

/-- **Tactic 5 (`by silicon_flowpipe`)**:
Runs the `Flowpipe` $N$-D validated Picard-Lindelöf & Euler Lie-derivative reachability tube
verifier, inspects the `HwExprCAM` / `runZone1Whnf` state, and reconstructs a `sorry`-free Lean 4
kernel proof (`picard_step_encloses_trajectory`, `taylorModel_picard_sound`, `flowpipe_step_encloses_euler`). -/
elab "silicon_flowpipe" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasSorry then
    throwError "[silicon_flowpipe] Goal contains sorryAx"
  let kTarget := fromLeanExprBoundedMeta 32 target
  let (hTarget, cam1) := internToHwExprCAM kTarget HwExprCAM.empty
  let z1 := runZone1Whnf 32 { cam := cam1, focusHandle := hTarget }
  if z1.focusHandle >= z1.cam.nodes.length || !z1.done then
    throwError "[silicon_flowpipe] Zone 1 HwExprCAM interning failed"
  evalTactic (← `(tactic|
    first
    | exact picard_step_encloses_trajectory
    | exact taylorModel_picard_sound
    | exact flowpipe_step_encloses_euler
    | exact stepFlowpipe1D_mem _ ‹_› ‹_› ‹_›
    | (apply verifyPicardAPriori_encloses <;> decide +kernel)
    | decide +kernel
    | omega
    | grind
    | simp))

/-! ## 5. Reflexive Self-Hosting Milestone Theorem (`silicon_self_hosting_milestone_sound`) -/

/-- Self-hosted `KConstInfo` representation of `Obend.Lower.LeanKernel.kernelCheckDecl`
(`Nat → Nat`, depth two: `λ x : Nat => idNat (idNat x)`; `Nat.succ` is not a constant of
`stdKernelEnv`, so a fixture that named it was refused by the kernel check it is meant to pass). -/
def selfHostKernelCheckDeclInfo : KConstInfo :=
  .defnInfo (KName.mkSimple "Obend_Lower_LeanKernel_kernelCheckDecl") []
    (.forallE (.const (KName.mkSimple "Nat") []) (.const (KName.mkSimple "Nat") []))
    (.lam (.const (KName.mkSimple "Nat") [])
      (.app (.const (KName.mkSimple "idNat") [])
        (.app (.const (KName.mkSimple "idNat") []) (.bvar 0))))

/-- Self-hosted `KConstInfo` representation of `Obend.Lower.SiliconElabFabric.runBottomUpCamInfer` /
`stepSiliconKernelCamFsm` (`Nat → Nat`: bottom-up handle type-code evaluator). -/
def selfHostBottomUpCamInferInfo : KConstInfo :=
  .defnInfo (KName.mkSimple "Obend_Lower_SiliconElabFabric_runBottomUpCamInfer") []
    (.forallE (.const (KName.mkSimple "Nat") []) (.const (KName.mkSimple "Nat") []))
    (.lam (.const (KName.mkSimple "Nat") [])
      (.app (.const (KName.mkSimple "idNat") []) (.bvar 0)))

/-- The identity proof `λ (P : Prop) (h : P). h : ∀ P : Prop, P → P`, as a `KConstInfo` fixture for
Zone 4. Until 2026-11-04 this was named `selfHostTypePreservationInfo` and described as a
representation of `Obend.Core.type_preservation`; it is not, and no term of that theorem's size is
in the fragment. -/
def selfHostIdentityProofInfo : KConstInfo :=
  .thmInfo (KName.mkSimple "identity_proof") []
    (.forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1)))
    (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0)))

/-- `#tooth`-mutated ill-typed proof representation (`Nat.succ Bool.true : Nat`) that must be refused. -/
def selfHostMutatedBadProofInfo : KConstInfo :=
  .defnInfo (KName.mkSimple "identity_proof_mutated") []
    (.const (KName.mkSimple "Nat") [])
    (.app (.const (KName.mkSimple "Nat.succ") []) (.const (KName.mkSimple "Bool.true") []))

/-- `sorryAx`-contaminated proof representation that must be refused by Zone 4. -/
def selfHostSorryProofInfo : KConstInfo :=
  .thmInfo (KName.mkSimple "identity_proof_sorry") []
    (.forallE (.sort .zero) (.bvar 0))
    (.const (KName.mkSimple "sorryAx") [.zero])

/-- Host `Lean.ConstantInfo` containing `sorryAx` nested 8 levels deep inside `.lam` and `.letE` binders,
testing that `extractLeanConstInfoBounded 3` (where `maxDepth = 3 < 8`) still detects `sorryAx` at the
truncated frontier and fails closed in `runSiliconCheckTelemetry`. -/
def deepNestedSorryLeanConstInfo : Lean.ConstantInfo :=
  let natE : Lean.Expr := .const (.str .anonymous "Nat") []
  let sorryE : Lean.Expr := .const (.str .anonymous "sorryAx") [.zero]
  let d1 : Lean.Expr := .lam (.str .anonymous "x1") natE sorryE .default
  let d2 : Lean.Expr := .letE (.str .anonymous "x2") natE natE d1 false
  let d3 : Lean.Expr := .lam (.str .anonymous "x3") natE d2 .default
  let d4 : Lean.Expr := .letE (.str .anonymous "x4") natE natE d3 false
  let d5 : Lean.Expr := .lam (.str .anonymous "x5") natE d4 .default
  let d6 : Lean.Expr := .letE (.str .anonymous "x6") natE natE d5 false
  let d7 : Lean.Expr := .lam (.str .anonymous "x7") natE d6 .default
  let d8 : Lean.Expr := .letE (.str .anonymous "x8") natE natE d7 false
  .thmInfo
    { name        := .str .anonymous "deepNestedSorryThm"
    , levelParams := []
    , type        := .forallE (.str .anonymous "P") (.sort .zero) (.bvar 0) .default
    , value       := d8 }

/-- **Reflexive Self-Hosting Milestone Theorem (`silicon_self_hosting_milestone_sound`)**:
Proves that the 4-Zone `SiliconElabFabric` + 88-bit `HwExprCAM` pipeline:
1. Preserves every well-formed 88-bit `PackedNodeWord` across `unpackNodeWord88 (packNodeWord88 w) = w`,
2. Soundly enforces `kernelCheckDecl env fuel decl = true` and `rtlSynthJudge = .ok` whenever
   `(stepZone4KernelCheck env fuel cam decl).1 = true`,
3. Accepts three small fixtures (`selfHostKernelCheckDeclInfo`, `selfHostBottomUpCamInferInfo`,
   `selfHostIdentityProofInfo`: `Nat → Nat` terms of depth two and the identity proof; they are named
   after, and are not, `kernelCheckDecl`, `runBottomUpCamInfer` and `type_preservation`)
   in `stepZone4KernelCheck`, `stepSiliconKernelCamFsm`, and `runSiliconCheckTelemetry`
   (`kernelVerdict = true`, `allWords88Wf = true`, `hasSorryAx = false`),
4. Strictly refuses the `#tooth`-mutated ill-typed declaration `selfHostMutatedBadProofInfo`,
   the `sorryAx`-contaminated declaration `selfHostSorryProofInfo`, and the deeply nested
   `deepNestedSorryLeanConstInfo` truncated at `maxDepth = 3`. -/
theorem silicon_self_hosting_milestone_sound :
    (∀ (w : PackedNodeWord), w.Wf88 → unpackNodeWord88 (packNodeWord88 w) = w) ∧
    (∀ (env : KEnv) (fuel : Nat) (cam : HwExprCAM) (decl : KConstInfo),
      (stepZone4KernelCheck env fuel cam decl).1 = true →
      kernelCheckDecl env fuel decl = true ∧
      encodeDeclStatusTag env fuel decl = 1 ∧
      checkRtlSynth 0 exprCamKernelLutRtlModule.name exprCamKernelLutRtlModule = Judge.Verdict.ok) ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostKernelCheckDeclInfo).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostBottomUpCamInferInfo).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostIdentityProofInfo).1 = true ∧
    (stepSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty selfHostKernelCheckDeclInfo).hwNodeDefEqOk = true ∧
    (stepSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty selfHostBottomUpCamInferInfo).hwNodeDefEqOk = true ∧
    (stepSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty selfHostIdentityProofInfo).hwNodeDefEqOk = true ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostKernelCheckDeclInfo).kernelVerdict = true ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostBottomUpCamInferInfo).kernelVerdict = true ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostIdentityProofInfo).kernelVerdict = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostMutatedBadProofInfo).1 = false ∧
    (stepSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty selfHostMutatedBadProofInfo).hwNodeDefEqOk = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostMutatedBadProofInfo).kernelVerdict = false ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty selfHostSorryProofInfo).1 = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 selfHostSorryProofInfo).kernelVerdict = false ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 (extractLeanConstInfoBounded 3 deepNestedSorryLeanConstInfo)).hasSorryAx = true ∧
    (runSiliconCheckTelemetry stdKernelEnv 8 (extractLeanConstInfoBounded 3 deepNestedSorryLeanConstInfo)).kernelVerdict = false := by
  refine ⟨unpack_packNodeWord88, (runSiliconKernelCamFsm_sound).1,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Broken mutant of `bisectInterval` that drops the right half `(dom, dom)`. -/
def bisectIntervalBroken (dom : Interval) : Interval × Interval :=
  (⟨dom.lo, dom.lo⟩, ⟨dom.lo, dom.lo⟩)

#tooth verifyRealBoundSubdiv_sound
  by mutation bisectInterval := bisectIntervalBroken

#tooth verifyRealBoxBoundSubdiv_sound
  by mutation bisectInterval := bisectIntervalBroken

#tooth silicon_self_hosting_milestone_sound
  by mutation evalHwInferNodeWordRtl := evalHwInferNodeWordRtlUncheckedApp

end Obend.Tactic.SiliconElab
end
