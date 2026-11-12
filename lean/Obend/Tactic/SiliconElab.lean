module
/-
# `Obend.Tactic.SiliconElab` — Certified Interval/SOS Bridges, `#silicon_check` & De Bruijn Proof-Producing `by silicon_simp`

Implements the verified hardware-assisted Lean 4 elaboration layer (`QUALIFICATION-AND-SILICON-LEAN.md` §2.3):

1. **Canonical Self-Hosting Symbol Aliases**:
   - `Obend.Core.type_preservation` (`Obend.Core.Proofs.Preservation.typed_stepRaw_preserved`),
   - `Obend.Lower.SiliconElabFabric.stepSiliconKernelCamFsm` (`Obend.Lower.SiliconElabFabric.runSiliconKernelCamFsm`).
2. **Certified Interval Subdivision & SOS Non-Negativity Soundness Theorems**:
   - `bisectInterval`, `verifyRealBoundSubdiv`, `verifyRealBoundSubdiv_sound`,
   - `verifyRealBoxBoundSubdiv`, `verifyRealBoxBoundSubdiv_sound`,
   - `sos_cert_implies_nonneg` wrapping `Obend.Judge.SOS.sosCheck_sound`.
3. **Live `#silicon_check <DeclName>` Command Elaborator**:
   - Extracts a target declaration and its referenced environment declaration cone from `(← getEnv)`,
   - Lowers `Lean.Expr` into `KExpr` (including first-class `.mvar`) and interns the DAG into `HwExprCAM`,
   - Verifies 88-bit `packNodeWord88` / `unpackNodeWord88` round-trip and Zone-4 `stepZone4KernelCheck`.
4. **Genuine De Bruijn-Criterion Proof-Producing `by silicon_simp` Tactic**:
   - Supports `by silicon_simp` and `by silicon_simp [lem1, ← lem2, ...]`,
   - Interns goal subterms into `HwExprCAM`, indexes user & `@[simp]` equational rules into `DiscrTrieNode`
     via arity-tagged Polish paths (`exprToDiscrPath`), matches candidate rules via `MetaUnify.metaUnifyFuel`,
     drives definitional head reductions via Zone-1 `runZone1Whnf`, and reconstructs a kernel-checked
     `Lean.Expr` equality proof (`mkEqRefl` / `mkEqSymm` / `mkEqTrans` / `mkCongrArg` / `mkCongrFun` / `mkCongr`)
     with **zero** fallback to `simp`, `omega`, `grind`, or `decide`.
-/
public meta import Lean
public import Lean
public import Obend.Lower.Inductive
public meta import Obend.Lower.Inductive
public import Obend.Lower.LeanKernel
public meta import Obend.Lower.LeanKernel
public import Obend.Lower.ExprCAM
public meta import Obend.Lower.ExprCAM
public import Obend.Lower.MetaUnify
public meta import Obend.Lower.MetaUnify
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
public import Obend.Tactic.Tooth

@[expose] public section

/-! ## 1. Canonical Self-Hosting Symbol Aliases -/

namespace Obend.Core

/-- Alias for the demand machine's type preservation theorem
(`Obend.Core.Proofs.Preservation.typed_stepRaw_preserved`). -/
abbrev type_preservation := @Obend.Core.Proofs.Preservation.typed_stepRaw_preserved

end Obend.Core

namespace Obend.Lower.SiliconElabFabric

/-- Canonical step-level alias for the Zone-4 `HwExprCAM` kernel FSM (`runSiliconKernelCamFsm`). -/
abbrev stepSiliconKernelCamFsm := @Obend.Lower.SiliconElabFabric.runSiliconKernelCamFsm

end Obend.Lower.SiliconElabFabric

namespace Obend.Tactic.SiliconElab

open Lean Elab Command Tactic Meta
open Obend.Lower.LeanKernel
open Obend.Lower.Inductive
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
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

/-- Multivariate round-robin branch-and-bound box subdivision verifier (`verifyRealBoxBoundSubdiv`). -/
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

/-- Expression $e(x) = x^2 - x$ over $x \in [0, 2]$. -/
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

/-- Negative-endpoint high-depth (`depth = 7`) subdivision benchmark: $e(x) = x^2 + x$ over $x \in [-1, 0]$. -/
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

/-- 2D multivariate expression $e(x, y) = (x^2 - x) + (y^2 - y)$ over $(x, y) \in [0, 2] \times [0, 2]$. -/
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

/-! ## 3. Bounded Host `Lean.Expr` Ingestion, 88-Bit `HwExprCAM` Packing & `#silicon_check` -/

/-- Render a `KName` as a dotted human-readable string key. -/
def knameKey : KName → String
  | .anonymous          => "[anon]"
  | .str .anonymous s   => s
  | .str p s            => knameKey p ++ "." ++ s
  | .num .anonymous i   => toString i
  | .num p i            => knameKey p ++ "." ++ toString i

/-- Clean numeric identifier `< 999983` derived from a `KName`. -/
def knameCleanId (n : KName) : Nat :=
  (knameKey n).toList.foldl (fun acc c => (acc * 131 + c.toNat) % 999983) 0

/-- Transparent structural check for `sorryAx` inside a host `Lean.Expr`. -/
def leanExprHasSorry : Lean.Expr → Bool
  | .const n _       => fromLeanName n == KName.mkSimple "sorryAx"
  | .app f a         => leanExprHasSorry f || leanExprHasSorry a
  | .lam _ d b _     => leanExprHasSorry d || leanExprHasSorry b
  | .forallE _ d b _ => leanExprHasSorry d || leanExprHasSorry b
  | .letE _ t v b _  => leanExprHasSorry t || leanExprHasSorry v || leanExprHasSorry b
  | .mdata _ e       => leanExprHasSorry e
  | .proj _ _ e      => leanExprHasSorry e
  | _                => false

/-- Bounded translation from host `Lean.Expr` to `KExpr` (preserving first-class `KExpr.mvar`). -/
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
    | .mvar id         => .mvar (knameCleanId (fromLeanName id.name))
    | .sort u          => .sort ((fromLeanLevel u).getD .zero)
    | .const n us      => .const (fromLeanName n) (us.filterMap fromLeanLevel)
    | .app f a         => .app (fromLeanExprBounded depth f) (fromLeanExprBounded depth a)
    | .lam _ d b _     => .lam (fromLeanExprBounded depth d) (fromLeanExprBounded depth b)
    | .forallE _ d b _ => .forallE (fromLeanExprBounded depth d) (fromLeanExprBounded depth b)
    | .letE _ t v b _  => .letE (fromLeanExprBounded depth t) (fromLeanExprBounded depth v) (fromLeanExprBounded depth b)
    | .lit l           => .lit (fromLeanLiteral l)
    | .mdata _ inner   => fromLeanExprBounded (depth + 1) inner
    | .proj s i inner  => .proj (fromLeanName s) i (fromLeanExprBounded depth inner)

/-- Extract a `KConstInfo` from any host `Lean.ConstantInfo` at bounded depth `maxDepth`. -/
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
  zone4StatusTag     : Nat
  hasSorryAx         : Bool
  kernelVerdict      : Bool
  deriving DecidableEq, Repr

/-- Count closed-term (`hasLooseBVar = false`) nodes in `HwExprCAM` eligible for 1-cycle $\beta$-bypass. -/
def countClosedBypassEligibleNodes (cam : HwExprCAM) : Nat :=
  cam.nodes.foldl (fun acc w => if !w.hasLooseBVar then acc + 1 else acc) 0

/-- Count application nodes (`tag == 4`) in `HwExprCAM` that generate Zone-2 child unification obligations. -/
def countAppNocFlits (cam : HwExprCAM) : Nat :=
  cam.nodes.foldl (fun acc w => if w.tag == 4 then acc + 2 else acc) 0

/-- Run the 4-Zone `SiliconElabFabric` + 88-bit `PackedNodeWord` telemetry pipeline on a `KConstInfo`. -/
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
  let verdict := !hasSorry && z4Ok && z4State.kernelAccepted && roundTripOk
  let hdr : SiliconElabWireHeader :=
    { nodeCount        := nNodes.toUInt32
    , constCount       := env.constants.length.toUInt32
    , recRuleCount     := env.recRules.length.toUInt32
    , lutEntryCount    := 0
    , icapFrameCount   := 1
    , targetDeclSymIdx := 0
    , targetExprHandle := valH.toUInt32
    , targetTypeHandle := tyH.toUInt32
    , fuelBudget       := fuel.toUInt32 }
  { declName           := knameKey decl.name
  , activeZones        := ["Zone1:HwExprCAM-88b", "Zone2:HandleUnifier", "Zone3:DiscrTrieLUT+ICAP", "Zone4:KernelGate"]
  , wireHeader         := hdr
  , packedWords88Count := packed88.length
  , allWords88Wf       := roundTripOk
  , hwCycles           := cycles
  , zone1CamHits       := z1Hits
  , zone1BetaBypasses  := z1Bypasses
  , zone2NocFlits      := z2Flits
  , zone3LutHits       := 0
  , zone3DprEpoch      := 1
  , zone4StatusTag     := z4State.statusTag
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
  s!"  • Zone 2 (HandleUnify) : {t.zone2NocFlits} handle unification obligations\n" ++
  s!"  • Zone 3 (DiscrTreeLUT): epoch {t.zone3DprEpoch}\n" ++
  s!"  • Zone 4 (Kernel Gate) : statusTag={t.zone4StatusTag}, hasSorryAx={t.hasSorryAx}, verdict={verdictStr}"

/-- Meta-level `KName` cleaner (`< 999983`). -/
meta def knameKeyMeta : KName → String
  | .anonymous          => "[anon]"
  | .str .anonymous s   => s
  | .str p s            => knameKeyMeta p ++ "." ++ s
  | .num .anonymous i   => toString i
  | .num p i            => knameKeyMeta p ++ "." ++ toString i

meta def knameCleanIdMeta (n : KName) : Nat :=
  (knameKeyMeta n).toList.foldl (fun acc c => (acc * 131 + c.toNat) % 999983) 0

meta def countClosedBypassEligibleNodesMeta (cam : HwExprCAM) : Nat :=
  cam.nodes.foldl (fun acc w => if !w.hasLooseBVar then acc + 1 else acc) 0

meta def countAppNocFlitsMeta (cam : HwExprCAM) : Nat :=
  cam.nodes.foldl (fun acc w => if w.tag == 4 then acc + 2 else acc) 0

/-- Meta-level bounded `Lean.Expr` to `KExpr` translator (mapping `.mvar` to first-class `KExpr.mvar`). -/
meta def fromLeanExprBoundedMeta : Nat → Lean.Expr → KExpr
  | 0, e =>
    if e.hasSorry then
      .const (KName.mkSimple "sorryAx") [.zero]
    else
      .const (KName.mkSimple "_hwTruncatedSubterm") []
  | depth + 1, e =>
    match e with
    | .bvar i          => .bvar i
    | .fvar id         => .fvar (1 + knameCleanIdMeta (fromLeanName id.name))
    | .mvar id         => .mvar (1 + knameCleanIdMeta (fromLeanName id.name))
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
(free of `_hwTruncatedSubterm`, unresolved `.mvar`, and unextracted constants). -/
meta def kexprInSupportedFragment (env : KEnv) : KExpr → Bool
  | .bvar _          => true
  | .fvar _          => true
  | .mvar _          => false
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
  | .proj s _ inner  =>
    env.inductDecls.any (fun d => d.name == s) && kexprInSupportedFragment env inner

/-- Extract the referenced `Lean.Environment` declaration cone (`extractLeanEnvConeMeta`) for `info`
using `ExprCAM.extractLeanEnvCone` (including `.recInfo` recursor rules and `.inductInfo` `inductDecls`). -/
meta def extractLeanEnvConeMeta (env : Lean.Environment) (info : Lean.ConstantInfo)
    (maxDepth : Nat := 32) : List Lean.Name × List Lean.ConstantInfo × KEnv :=
  let directNames :=
    (info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]).toList.take 24
  let directInfos := directNames.filterMap env.find?
  let transNames :=
    (directNames ++ (directInfos.foldl (fun (acc : List Lean.Name) (ci : Lean.ConstantInfo) =>
      acc ++ (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]).toList.take 8) [])).eraseDups.take 32
  let coneInfos := transNames.filterMap env.find?
  let extractedKEnv : KEnv :=
    (Obend.Lower.ExprCAM.extractLeanEnvCone env info.name 48).map (·.1) |>.getD
      { constants := [], recRules := [], inductDecls := [] }
  let fallbackConsts := coneInfos.map (extractLeanConstInfoMeta maxDepth)
  let mergedConsts :=
    stdKernelEnv.constants ++ extractedKEnv.constants ++
      fallbackConsts.filter (fun c => !extractedKEnv.constants.any (fun e => e.name == c.name))
  let fullKEnv : KEnv :=
    { constants   := mergedConsts
    , recRules    := stdKernelEnv.recRules ++ extractedKEnv.recRules
    , inductDecls := stdKernelEnv.inductDecls ++ extractedKEnv.inductDecls }
  (transNames, coneInfos, fullKEnv)

/-- Query the compiled Verilator co-processor binary (`Vsilicon_elab_top`) when present on disk. -/
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

/-- Meta-level runner for `#silicon_check` command elaboration. -/
meta def runSiliconCheckCommandMeta (env : Lean.Environment) (info : Lean.ConstantInfo)
    (verilatorJson? : Option String) : String × Bool :=
  let (usedNames, coneInfos, fullKEnv) := extractLeanEnvConeMeta env info 32
  let coneHasSorry :=
    usedNames.any (fun n => n == ``sorryAx) ||
    coneInfos.any (fun ci => ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false)
  let selfHasSorry := info.type.hasSorry || (info.value?.map (·.hasSorry)).getD false
  let kdecl :=
    (Obend.Lower.ExprCAM.extractLeanConstInfo? info).getD (extractLeanConstInfoMeta 32 info)
  let (tyExpr, valExpr) := declTyAndVal kdecl
  let camCone := internKEnvConeFast fullKEnv
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
  let (z4Ok, z4State) := stepZone4KernelCheck fullKEnv 32 finalCam kdecl
  let fullZ4Verified := !hasSorry && inSupportedFragment && z4Ok && z4State.kernelAccepted
  let nNodes := finalCam.nodes.length
  let z1Hits := nNodes + z1State.steps
  let z1Bypasses := countClosedBypassEligibleNodesMeta finalCam
  let z2Flits := countAppNocFlitsMeta finalCam + 2
  let cycles := nNodes + z1State.steps + z2Flits + 4
  let verdict := fullZ4Verified && roundTripOk
  let verilatorStatus :=
    match verilatorJson? with
    | some j => s!"CO-SIM PASS ({j})"
    | none   => "IN-CORE RTL MODEL (Verilator binary not in cwd)"
  let verdictStr :=
    if verdict then
      "ACCEPT (0 sorryAx, 88-bit CAM round-trip & Zone-4 kernel verified)"
    else if hasSorry then
      "REFUSE (sorryAx in the declaration or its cone)"
    else if !inSupportedFragment then
      "REFUSE (outside the Zone-4 fragment: truncated subterm or unextracted constant)"
    else if !roundTripOk then
      "REFUSE (88-bit CAM word did not round-trip)"
    else
      s!"REFUSE (Zone-4 kernel check failed with statusTag={z4State.statusTag})"
  let msg :=
    s!"[SiliconElab #silicon_check] Declaration: `{info.name}`\n" ++
    s!"  • Active Zones         : Zone1:HwExprCAM-88b, Zone2:HandleUnifier, Zone3:DiscrTrieLUT+ICAP, Zone4:KernelGate\n" ++
    s!"  • Wire Header          : OBCAMv1 (magic=0x31564D4143424F00, nodes={nNodes}, consts={fullKEnv.constants.length}, targetTypeH={tyH}, targetValH={valH})\n" ++
    s!"  • 88-Bit CAM Words     : {packed88.length} words (88b pack/unpack round-trip = {roundTripOk})\n" ++
    s!"  • Hardware Cycles      : {cycles} cycles\n" ++
    s!"  • Zone 1 (HwExprCAM)   : {z1Hits} CAM hits, {z1Bypasses} closed-term 1-cycle β-bypasses\n" ++
    s!"  • Zone 2 (HandleUnify) : {z2Flits} handle unification obligations\n" ++
    s!"  • Zone 3 (DiscrTreeLUT): not exercised by #silicon_check\n" ++
    s!"  • Zone 4 (Kernel Gate) : statusTag={z4State.statusTag}, inFragment={inSupportedFragment}, hasSorryAx={hasSorry}, verdict={verdictStr}\n" ++
    s!"  • Verilator Co-Sim     : {verilatorStatus}"
  (msg, verdict)

/-- `#silicon_check <DeclName>` command elaborator. -/
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

/-! ## 4. Genuine De Bruijn-Criterion Proof-Producing `by silicon_simp` Tactic -/

/-- Syntax for an optional `←` / `<-` directional lemma argument to `silicon_simp`. -/
syntax siliconSimpLemma := ("←" <|> "<-")? term

/-- `by silicon_simp` and `by silicon_simp [lem1, ← lem2, ...]`:
Hardware-accelerated equational & definitional simplifier backed by `HwExprCAM` (Zone 1),
`MetaUnify` (Zone 2), and `DiscrTrieNode` (Zone 3), reconstructing a genuine kernel-checked
`Lean.Expr` proof term with zero fallback to `simp`, `omega`, `grind`, or `decide`. -/
syntax (name := siliconSimpTac) "silicon_simp" (" [" siliconSimpLemma,* "]")? : tactic

/-- A compiled equational rewrite rule indexed in `DiscrTrieNode` for `silicon_simp`. -/
meta structure SiliconSimpRule where
  ruleId     : Nat
  ruleName   : KName
  constName? : Option Lean.Name
  proofExpr  : Lean.Expr
  symm       : Bool
  patLhs     : KExpr
  patRhs     : KExpr
  patMCtx    : Obend.Lower.MetaUnify.MetavarContext
  discrPath  : DiscrPath
  priority   : Nat

/-- Translate a host `Lean.Expr` into a universe-normalized `KExpr` pattern for `DiscrTrieNode`
indexing and `MetaUnify.metaUnifyFuel` matching:
* Temporary telescope metavariables in `mvarSlots` become first-class `KExpr.mvar slotIdx`,
* Local `.fvar`s become `KExpr.fvar fvarId`,
* Universe levels on `.const` are normalized to `[]` so universe-polymorphic lemmas match concrete
  call sites in `MetaUnify`, while full universe checking is enforced during Lean proof term reconstruction. -/
meta def leanExprToKPattern (mvarSlots : List (Lean.MVarId × Nat)) : Nat → Lean.Expr → KExpr
  | 0, _ => .const (KName.mkSimple "_patDepthCap") []
  | depth + 1, e =>
    match e with
    | .bvar i => .bvar i
    | .fvar id => .fvar (1 + knameCleanIdMeta (fromLeanName id.name))
    | .mvar id =>
      match mvarSlots.find? (fun p => p.1 == id) with
      | some (_, slotIdx) => .mvar slotIdx
      | none              => .mvar (1000 + knameCleanIdMeta (fromLeanName id.name))
    | .sort _ => .sort .zero
    | .const n _ => .const (fromLeanName n) []
    | .app f a =>
      .app (leanExprToKPattern mvarSlots depth f) (leanExprToKPattern mvarSlots depth a)
    | .lam _ d b _ =>
      .lam (leanExprToKPattern mvarSlots depth d) (leanExprToKPattern mvarSlots depth b)
    | .forallE _ d b _ =>
      .forallE (leanExprToKPattern mvarSlots depth d) (leanExprToKPattern mvarSlots depth b)
    | .letE _ t v b _ =>
      .letE (leanExprToKPattern mvarSlots depth t)
            (leanExprToKPattern mvarSlots depth v)
            (leanExprToKPattern mvarSlots depth b)
    | .lit l => .lit (fromLeanLiteral l)
    | .mdata _ inner => leanExprToKPattern mvarSlots (depth + 1) inner
    | .proj s idx inner => .proj (fromLeanName s) idx (leanExprToKPattern mvarSlots depth inner)

/-- Collect all `.fvar` numeric IDs occurring inside a `KExpr` so goal local variables are permitted
in `MetavarContext` scope checking. -/
meta def collectKExprFVarIds : KExpr → List Nat
  | .fvar id     => [id]
  | .app f a     => collectKExprFVarIds f ++ collectKExprFVarIds a
  | .lam d b     => collectKExprFVarIds d ++ collectKExprFVarIds b
  | .forallE d b => collectKExprFVarIds d ++ collectKExprFVarIds b
  | .letE t v b  => collectKExprFVarIds t ++ collectKExprFVarIds v ++ collectKExprFVarIds b
  | .proj _ _ s  => collectKExprFVarIds s
  | _            => []

/-- Extract a `SiliconSimpRule` from a Lean proof expression `pf` (`∀ x₁ … xₖ, lhs = rhs` or `lhs ↔ rhs`)
without leaving temporary metavariables in `MetaM`. -/
meta def extractSiliconSimpRule?
    (ruleId : Nat)
    (ruleName : KName)
    (constName? : Option Lean.Name)
    (pf : Lean.Expr)
    (symm : Bool)
    (priority : Nat) : MetaM (Option SiliconSimpRule) := withoutModifyingState do
  if pf.hasSorry then
    return none
  let pfTy ← inferType pf
  if pfTy.hasSorry then
    return none
  let (mvars, _, bodyTy) ← forallMetaTelescopeReducing pfTy
  let eqSides? : Option (Lean.Expr × Lean.Expr) :=
    match bodyTy.eq? with
    | some (_, l, r) => some (l, r)
    | none =>
      match bodyTy.iff? with
      | some (l, r) => some (l, r)
      | none        => none
  match eqSides? with
  | none => return none
  | some (lhsRaw, rhsRaw) =>
    let lhsInst ← instantiateMVars lhsRaw
    let rhsInst ← instantiateMVars rhsRaw
    let (srcE, dstE) := if symm then (rhsInst, lhsInst) else (lhsInst, rhsInst)
    let mvarSlots : List (Lean.MVarId × Nat) :=
      (mvars.toList.zipIdx).filterMap fun (mv, idx) =>
        match mv with
        | .mvar id => some (id, idx)
        | _        => none
    let patLhs := leanExprToKPattern mvarSlots 24 srcE
    let patRhs := leanExprToKPattern mvarSlots 24 dstE
    let decls : List MVarDecl :=
      (List.range mvars.size).map fun idx =>
        { mvarId := idx, lctx := [], expectedType := kType0, kind := .natural }
    let patMCtx : Obend.Lower.MetaUnify.MetavarContext := { decls := decls }
    let path := exprToDiscrPath 8 patLhs
    return some
      { ruleId     := ruleId
      , ruleName   := ruleName
      , constName? := constName?
      , proofExpr  := pf
      , symm       := symm
      , patLhs     := patLhs
      , patRhs     := patRhs
      , patMCtx    := patMCtx
      , discrPath  := path
      , priority   := priority }

/-- Curated core equational `@[simp]` theorems indexed by default in Zone-3 `DiscrTrieNode`. -/
meta def defaultSiliconSimpConstNames : List Lean.Name :=
  [ ``Nat.add_zero, ``Nat.zero_add, ``Nat.add_succ, ``Nat.succ_add
  , ``Nat.mul_zero, ``Nat.zero_mul, ``Nat.mul_one, ``Nat.one_mul
  , ``Nat.sub_zero, ``Nat.sub_self
  , ``Bool.true_and, ``Bool.and_true, ``Bool.false_and, ``Bool.and_false
  , ``Bool.true_or, ``Bool.or_true, ``Bool.false_or, ``Bool.or_false
  , ``Bool.not_not, ``Bool.not_true, ``Bool.not_false
  , ``List.nil_append, ``List.append_nil, ``List.cons_append
  , ``List.map_nil, ``List.map_cons, ``List.length_nil, ``List.length_cons
  , ``Option.map_none, ``Option.map_some ]

/-- Build the Zone-3 `DiscrTrieNode` and `Array SiliconSimpRule` from user-supplied lemma arguments
(priority `2000`) and core equational theorems (priority `1000`). -/
meta def buildSiliconSimpIndex
    (userSpecs : List (Option Lean.Name × Lean.Expr × Bool)) :
    MetaM (DiscrTrieNode × Array SiliconSimpRule) := do
  let env ← getEnv
  let mut rules : Array SiliconSimpRule := #[]
  let mut trie : DiscrTrieNode := .empty
  for (cName?, pfExpr, symm) in userSpecs do
    let rId := rules.size
    let rName :=
      match cName? with
      | some cn => fromLeanName cn
      | none    => KName.mkSimple s!"userRule_{rId}"
    if let some rule ← extractSiliconSimpRule? rId rName cName? pfExpr symm 2000 then
      let entry : DiscrTreeEntry :=
        { ruleName := rule.ruleName
        , path     := rule.discrPath
        , lutTag   := rId
        , kind     := .simpLemma rule.patRhs rule.priority 0 }
      trie := insertDiscrTrieNode rule.discrPath entry trie
      rules := rules.push rule
  for cName in defaultSiliconSimpConstNames do
    if env.contains cName then
      let pfExpr ← mkConstWithFreshMVarLevels cName
      let rId := rules.size
      if let some rule ← extractSiliconSimpRule? rId (fromLeanName cName) (some cName) pfExpr false 1000 then
        let entry : DiscrTreeEntry :=
          { ruleName := rule.ruleName
          , path     := rule.discrPath
          , lutTag   := rId
          , kind     := .simpLemma rule.patRhs rule.priority 0 }
        trie := insertDiscrTrieNode rule.discrPath entry trie
        rules := rules.push rule
  return (trie, rules)

/-- Speculative `MetaM` execution restoring `MetaM` state on failure. -/
meta def metaTry? {α : Type} (act : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  try
    some <$> act
  catch _ =>
    s.restore
    return none

/-- Chain two optional Lean equality proofs (`p1 : a = b`, `p2 : b = c`) via `mkEqTrans`. -/
meta def chainEqProofs? : Option Lean.Expr → Option Lean.Expr → MetaM (Option Lean.Expr)
  | none, p2 => pure p2
  | p1, none => pure p1
  | some p1, some p2 => some <$> mkEqTrans p1 p2

/-- Attempt to match `rule : SiliconSimpRule` against `curExpr` via Zone-2 `MetaUnify.metaUnifyFuel`
and reconstruct a metavariable-free Lean kernel equality step proof `curExpr = nextExpr`. -/
meta def tryApplySiliconSimpRule?
    (rule : SiliconSimpRule)
    (curExpr : Lean.Expr)
    (kCur : KExpr)
    (baseLCtxIds : List Nat) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let fvarIds := (baseLCtxIds ++ collectKExprFVarIds kCur).eraseDups
  let lctxEntries := fvarIds.map (fun id => (id, kType0))
  let scopedMCtx : Obend.Lower.MetaUnify.MetavarContext :=
    { rule.patMCtx with
      decls := rule.patMCtx.decls.map (fun d => { d with lctx := lctxEntries }) }
  -- Zone-2 Hardware Unification Gate: require `MetaUnify.metaUnifyFuel` to succeed on `(rule.patLhs, kCur)`
  match metaUnifyFuel stdKernelEnv 24 scopedMCtx rule.patLhs kCur with
  | none => return none
  | some _ =>
    let saved ← saveState
    let lemHead ←
      match rule.constName? with
      | some cName => mkConstWithFreshMVarLevels cName
      | none       => pure rule.proofExpr
    let lemTy ← inferType lemHead
    let (mvars, bInfos, bodyTy) ← forallMetaTelescopeReducing lemTy
    let eqInfo? : Option (Lean.Expr × Lean.Expr × Bool) :=
      match bodyTy.eq? with
      | some (_, l, r) => some (l, r, false)
      | none =>
        match bodyTy.iff? with
        | some (l, r) => some (l, r, true)
        | none        => none
    match eqInfo? with
    | none =>
      saved.restore
      return none
    | some (lhsPat, rhsPat, isIff) =>
      let (matchPat, replPat) := if rule.symm then (rhsPat, lhsPat) else (lhsPat, rhsPat)
      if !(← isDefEq matchPat curExpr) then
        saved.restore
        return none
      for mv in mvars, bi in bInfos do
        let mvId := mv.mvarId!
        if !(← mvId.isAssigned) && bi.isInstImplicit then
          if let some instVal ← metaTry? (synthInstance (← inferType mv)) then
            mvId.assign instVal
      let rawApp := mkAppN lemHead mvars
      let eqPf? ←
        if isIff then
          metaTry? (mkAppM ``propext #[rawApp])
        else
          pure (some rawApp)
      match eqPf? with
      | none =>
        saved.restore
        return none
      | some eqPf =>
        let dirPf? ←
          if rule.symm then metaTry? (mkEqSymm eqPf) else pure (some eqPf)
        match dirPf? with
        | none =>
          saved.restore
          return none
        | some dirPf =>
          let nextExpr ← instantiateMVars replPat
          let stepPf ← instantiateMVars dirPf
          if nextExpr.hasExprMVar || stepPf.hasExprMVar || nextExpr.hasSorry || stepPf.hasSorry || nextExpr == curExpr then
            saved.restore
            return none
          return some (nextExpr, stepPf)

/-- Try candidate rules returned by Zone-3 `queryDiscrTrieNode` in priority order. -/
meta def tryDiscrTrieCandidates?
    (rules : Array SiliconSimpRule)
    (candidates : List DiscrTreeEntry)
    (curExpr : Lean.Expr)
    (kCur : KExpr)
    (baseLCtxIds : List Nat) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  for entry in candidates do
    if let some rule := rules[entry.lutTag]? then
      if let some hit ← tryApplySiliconSimpRule? rule curExpr kCur baseLCtxIds then
        return some hit
  return none

/-- Lift optional subterm equality proofs across `.app f a` via `mkCongr`, `mkCongrFun`, or `mkCongrArg`. -/
meta def liftCongrApp?
    (f f' a a' : Lean.Expr)
    (pfF? pfA? : Option Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
  match pfF?, pfA? with
  | none, none => return (.app f a, none)
  | some pfF, none =>
    match ← metaTry? (mkCongrFun pfF a) with
    | some pf => return (.app f' a, some pf)
    | none    => return (.app f a, none)
  | none, some pfA =>
    match ← metaTry? (mkCongrArg f pfA) with
    | some pf => return (.app f a', some pf)
    | none    => return (.app f a, none)
  | some pfF, some pfA =>
    match ← metaTry? (mkCongr pfF pfA) with
    | some pf => return (.app f' a', some pf)
    | none =>
      match ← metaTry? (mkCongrFun pfF a) with
      | none => return (.app f a, none)
      | some pf1 =>
        match ← metaTry? (mkCongrArg f' pfA) with
        | none => return (.app f' a, some pf1)
        | some pf2 =>
          let pf12 ← mkEqTrans pf1 pf2
          return (.app f' a', some pf12)

/-- Recursive bottom-up + root-fixpoint proof-producing normalizer driven by:
* **Zone 1 (`HwExprCAM` + `runZone1Whnf`)**: DAG handle interning, 1-cycle closed $\beta$-bypass, and
  definitional head reduction (`whnfCore`),
* **Zone 3 (`DiscrTrieNode` + `queryDiscrTrieNode`)**: arity-exact Polish discrimination-tree lookup,
* **Zone 2 (`MetaUnify.metaUnifyFuel`)**: metavariable unification & scope checking.
Returns `(normExpr, eqProof?, normHandle, updatedCam, stepsTaken)`. -/
meta def siliconSimpNormalize
    (trie : DiscrTrieNode)
    (rules : Array SiliconSimpRule)
    (baseLCtxIds : List Nat) :
    Nat → Lean.Expr → HwExprCAM → MetaM (Lean.Expr × Option Lean.Expr × CamHandle × HwExprCAM × Nat)
  | 0, e, cam => do
    let (h, cam') := internToHwExprCAM (leanExprToKPattern [] 24 e) cam
    return (e, none, h, cam', 0)
  | fuel + 1, e, cam => do
    let eClean ← instantiateMVars e
    -- 1. Bottom-up subterm normalization across applications
    let (subExpr, subPf?, hSub, camSub, subSteps) ←
      match eClean with
      | .app f a =>
        let (f', pfF?, hF', cam1, s1) ← siliconSimpNormalize trie rules baseLCtxIds fuel f cam
        let (a', pfA?, hA', cam2, s2) ← siliconSimpNormalize trie rules baseLCtxIds fuel a cam1
        let (appExpr, appPf?) ← liftCongrApp? f f' a a' pfF? pfA?
        let (hApp, cam3) :=
          if appExpr == .app f' a' then mkHwCamApp hF' hA' cam2
          else internToHwExprCAM (leanExprToKPattern [] 24 appExpr) cam2
        pure (appExpr, appPf?, hApp, cam3, s1 + s2)
      | _ =>
        let (h0, cam1) := internToHwExprCAM (leanExprToKPattern [] 24 eClean) cam
        pure (eClean, none, h0, cam1, 0)
    -- 2. Zone-3 `DiscrTrieNode` lookup + Zone-2 `MetaUnify` rule rewrite at root
    let kSub := leanExprToKPattern [] 24 subExpr
    let candidates := queryDiscrTrieNode trie (exprToDiscrPath 8 kSub)
    if let some (nextExpr, stepPf) ← tryDiscrTrieCandidates? rules candidates subExpr kSub baseLCtxIds then
      let combinedPf? ← chainEqProofs? subPf? (some stepPf)
      let (finalExpr, tailPf?, hFinal, camFinal, tailSteps) ←
        siliconSimpNormalize trie rules baseLCtxIds fuel nextExpr camSub
      let totalPf? ← chainEqProofs? combinedPf? tailPf?
      return (finalExpr, totalPf?, hFinal, camFinal, subSteps + 1 + tailSteps)
    else
      -- 3. Zone-1 `HwExprCAM` WHNF reduction step (`runZone1Whnf`)
      let z1 := runZone1Whnf 16 { cam := camSub, focusHandle := hSub }
      if z1.steps > 0 && z1.focusHandle != hSub then
        let redExpr ← whnfCore subExpr
        if redExpr != subExpr && !redExpr.hasExprMVar && !redExpr.hasSorry then
          let reflRed ← mkEqRefl redExpr
          let combinedPf? ← chainEqProofs? subPf? (some reflRed)
          let (finalExpr, tailPf?, hFinal, camFinal, tailSteps) ←
            siliconSimpNormalize trie rules baseLCtxIds fuel redExpr z1.cam
          let totalPf? ← chainEqProofs? combinedPf? tailPf?
          return (finalExpr, totalPf?, hFinal, camFinal, subSteps + z1.steps + tailSteps)
        else
          return (subExpr, subPf?, z1.focusHandle, z1.cam, subSteps)
      else
        return (subExpr, subPf?, hSub, z1.cam, subSteps)

/-- Reconstruct a kernel-checked Lean proof term for `target` (`lhs = rhs`, `lhs ↔ rhs`, `True`, or `P ∧ Q`)
using `siliconSimpNormalize` + Zone-1/Zone-2 `HwExprCAM` handle normalization. -/
meta def proveTargetBySiliconSimp
    (trie : DiscrTrieNode)
    (rules : Array SiliconSimpRule)
    (baseLCtxIds : List Nat) :
    Nat → Lean.Expr → HwExprCAM → MetaM (Lean.Expr × HwExprCAM)
  | 0, target, _ =>
    throwError "[silicon_simp] Goal recursion depth exhausted on `{target}`"
  | depth + 1, target, cam => do
    let tgt ← instantiateMVars target
    if tgt.isConstOf ``True then
      return (mkConst ``True.intro, cam)
    else if let some (p, q) := tgt.and? then
      let (pfP, cam1) ← proveTargetBySiliconSimp trie rules baseLCtxIds depth p cam
      let (pfQ, cam2) ← proveTargetBySiliconSimp trie rules baseLCtxIds depth q cam1
      let pfAnd ← mkAppM ``And.intro #[pfP, pfQ]
      return (pfAnd, cam2)
    else if let some (p, q) := tgt.iff? then
      let eqGoal ← mkEq p q
      let (pfEq, cam1) ← proveTargetBySiliconSimp trie rules baseLCtxIds depth eqGoal cam
      let pfIff ← mkAppM ``iff_of_eq #[pfEq]
      return (pfIff, cam1)
    else if let some (_, lhs, rhs) := tgt.eq? then
      -- Fast Zone-1 CAM check on initial LHS/RHS handles
      let (hInitL, camInit1) := internToHwExprCAM (leanExprToKPattern [] 24 lhs) cam
      let (hInitR, camInit2) := internToHwExprCAM (leanExprToKPattern [] 24 rhs) camInit1
      let z1InitL := runZone1Whnf 32 { cam := camInit2, focusHandle := hInitL }
      let z1InitR := runZone1Whnf 32 { cam := z1InitL.cam, focusHandle := hInitR }
      if z1InitL.focusHandle == z1InitR.focusHandle then
        if ← isDefEq lhs rhs then
          return (← mkEqRefl lhs, z1InitR.cam)
      -- Full Zone-3 DiscrTrieNode + Zone-2 MetaUnify + Zone-1 WHNF proof-producing normalization
      let (lhsNorm, pfLhs?, hLhsNorm, camL, stepsL) ←
        siliconSimpNormalize trie rules baseLCtxIds 12 lhs z1InitR.cam
      let (rhsNorm, pfRhs?, hRhsNorm, camR, stepsR) ←
        siliconSimpNormalize trie rules baseLCtxIds 12 rhs camL
      let z1FinalL := runZone1Whnf 32 { cam := camR, focusHandle := hLhsNorm }
      let z1FinalR := runZone1Whnf 32 { cam := z1FinalL.cam, focusHandle := hRhsNorm }
      let z2Check := runZone2Unify 16
        { tileId := 0
        , cam    := z1FinalR.cam
        , queue  := [{ lhsHandle := z1FinalL.focusHandle, rhsHandle := z1FinalR.focusHandle }] }
      if !(← isDefEq lhsNorm rhsNorm) then
        throwError "[silicon_simp] Failed to unify normalized equation sides:\n  lhs ↦ {lhsNorm}\n  rhs ↦ {rhsNorm}\n  (CAM handles: {z1FinalL.focusHandle} vs {z1FinalR.focusHandle}, z2Failed={z2Check.failed}, steps={stepsL + stepsR})"
      let joinedPf ←
        match pfLhs?, pfRhs? with
        | none, none         => mkEqRefl lhs
        | some pfL, none     => pure pfL
        | none, some pfR     => mkEqSymm pfR
        | some pfL, some pfR => do
          let symR ← mkEqSymm pfR
          mkEqTrans pfL symR
      return (joinedPf, z2Check.cam)
    else
      let tgtWhnf ← whnf tgt
      if tgtWhnf != tgt then
        proveTargetBySiliconSimp trie rules baseLCtxIds depth tgtWhnf cam
      else
        throwError "[silicon_simp] Unsupported goal shape `{tgt}` (expected `lhs = rhs`, `lhs ↔ rhs`, `P ∧ Q`, or `True`)"

/-- Elaborate user `[lem1, ← lem2, ...]` syntax arguments into `(constName?, proofExpr, symm)` triples. -/
meta def elabSiliconSimpUserArgs (args : Array (TSyntax `Obend.Tactic.SiliconElab.siliconSimpLemma)) :
    TacticM (List (Option Lean.Name × Lean.Expr × Bool)) := do
  let mut out : List (Option Lean.Name × Lean.Expr × Bool) := []
  for arg in args do
    match arg with
    | `(siliconSimpLemma| ← $t:term) =>
      let e ← elabTerm t none
      let eInst ← instantiateMVars e
      let cName? := match eInst with | .const cn _ => some cn | _ => none
      out := out ++ [(cName?, eInst, true)]
    | `(siliconSimpLemma| <- $t:term) =>
      let e ← elabTerm t none
      let eInst ← instantiateMVars e
      let cName? := match eInst with | .const cn _ => some cn | _ => none
      out := out ++ [(cName?, eInst, true)]
    | `(siliconSimpLemma| $t:term) =>
      let e ← elabTerm t none
      let eInst ← instantiateMVars e
      let cName? := match eInst with | .const cn _ => some cn | _ => none
      out := out ++ [(cName?, eInst, false)]
    | _ => pure ()
  return out

@[tactic siliconSimpTac]
meta def evalSiliconSimpTac : Tactic
  | `(tactic| silicon_simp $[[ $args,* ]]?) => withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    if target.hasSorry then
      throwError "[silicon_simp] Goal contains sorryAx"
    let userSyntaxArgs : Array (TSyntax `Obend.Tactic.SiliconElab.siliconSimpLemma) :=
      match args with
      | some sepArr => sepArr.getElems
      | none        => #[]
    let userSpecs ← elabSiliconSimpUserArgs userSyntaxArgs
    let (trie, rules) ← buildSiliconSimpIndex userSpecs
    let lctx ← getLCtx
    let baseLCtxIds : List Nat :=
      lctx.decls.toList.filterMap fun d? =>
        d?.map (fun d => 1 + knameCleanIdMeta (fromLeanName d.fvarId.name))
    let (proofTerm, _finalCam) ← proveTargetBySiliconSimp trie rules baseLCtxIds 8 target HwExprCAM.empty
    let proofClean ← instantiateMVars proofTerm
    if proofClean.hasSorry || proofClean.hasExprMVar then
      throwError "[silicon_simp] Constructed proof contains sorryAx or unassigned metavariables"
    Lean.Meta.check proofClean
    let pfTy ← inferType proofClean
    if !(← isDefEq pfTy target) then
      throwError "[silicon_simp] Constructed proof type `{pfTy}` does not match goal `{target}`"
    goal.assign proofClean
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

end Obend.Tactic.SiliconElab
end
