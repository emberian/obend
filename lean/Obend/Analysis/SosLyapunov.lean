module
/-
# Obend.Analysis.SosLyapunov — Sum-of-Squares (SOS) Lyapunov Stability, Control Barrier Functions (CBF) & Index-1 DAE Algebraic Manifold Invariance (`"sos-lyapunov-cbf@1"`)

Implements **Pillar 3B** of the Wave 3 Master Roadmap:
1. **Multivariate Polynomial Partial Differentiation, Gradient & Lie Derivative (`polyToRealExpr`, `polyPartialDeriv`, `polyGradient`, `lieDerivativePoly`)**:
   - Bridges sparse multivariate polynomials `Obend.Judge.SOS.Poly` ($\mathbb{Q}[x_0, \dots, x_{n-1}]$)
     to `Obend.Analysis.RealExpr` and `Obend.Analysis.Diff`,
   - Proves **`polyPartialDeriv_agrees_with_symbolicDeriv_and_reverseAD`**: for every polynomial $p$,
     variable index $v \in \mathbb{N}$, and point $\text{env} : \mathbb{N} \to \mathbb{Q}$, evaluating
     `polyPartialDeriv v p` agrees identically with symbolic differentiation (`symbolicDeriv`),
     forward-mode dual automatic differentiation (`evalDualRat`), recursive reverse-mode AD
     (`reverseGradVar`), and single-pass accumulated reverse-mode AD (`gradReverseAccumulated`)!
2. **Sum-of-Squares (SOS) Nonlinear Lyapunov Stability (`SosLyapunovSpec`, `SosLyapunovWitness`, `checkSosLyapunov`, `checkSosLyapunov_sound`)**:
   - Verifies $V(0) = 0$, strict radial positive definiteness $V(x) - \varepsilon \|x\|^2 \ge 0$
     ($\varepsilon > 0$), and exponential Lie-derivative decay $-\mathcal{L}_f V(x) - \gamma V(x) \ge 0$
     ($\gamma \ge 0$) on a semialgebraic domain $\{g_k(x) \ge 0\}$ via `PositivstellensatzCert`.
3. **Sum-of-Squares Control Barrier Functions (`SosCbfSpec`, `SosCbfWitness`, `checkSosCbf`, `checkSosCbf_sound`)**:
   - Verifies Stengle Positivstellensatz refutation of the unsafe intersection
     $\{x \mid B(x) \ge 0 \;\wedge\; u_{\text{unsafe}}(x) \ge 0\} = \emptyset$ together with
     Nagumo / Ames barrier forward invariance $\mathcal{L}_f B(x) + \alpha B(x) \ge 0$ on the domain.
4. **Index-1 Differential-Algebraic Equation (DAE) Manifold Invariance (`DaeManifoldSpec`, `DaeManifoldWitness`, `checkDaeManifold`, `checkDaeManifold_sound`)**:
   - Verifies algebraic constraint tangency $\mathcal{L}_f h_r \in \langle h_1, \dots, h_m \rangle$
     via Buchberger/Gröbner `checkIdealMembershipCert` and Index-1 algebraic Jacobian regularity
     $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$ ($\delta_{\text{reg}} > 0$) on the manifold.
5. **Universal Judge & Format Registration (`sosLyapunovJudge`, `sosLyapunovFormat` = `"sos-lyapunov-cbf@1"`)**:
   - Instantiates `Judge SosLyapunovProblem SosLyapunovCert` and registers `"sos-lyapunov-cbf@1"`.
-/
public import Obend.Judge.Class
import all Obend.Judge.Class
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.RealAnalysis
public import Obend.Analysis.Groebner
public import Obend.Analysis.Diff
public import Obend.Tactic.Tooth
public section

namespace Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
set_option autoImplicit false

/-! ## 1. Multivariate Polynomial Embedding into `RealExpr`, Partial Derivatives & Lie Derivatives -/

/-- Canonical variable name `"x"`, `"x'"`, `"x''"`, ... for variable index `v : Nat`. -/
@[expose] def polyVarName (v : Nat) : String :=
  String.ofList ('x' :: List.replicate v '\'')

/-- `polyVarName` is injective (`polyVarName v = polyVarName j → v = j`). -/
theorem polyVarName_inj {v j : Nat} (h : polyVarName v = polyVarName j) : v = j := by
  have hLen : (polyVarName v).toList.length = (polyVarName j).toList.length :=
    congrArg (fun s => s.toList.length) h
  dsimp only [polyVarName] at hLen
  rw [String.toList_ofList, String.toList_ofList, List.length_cons, List.length_cons,
      List.length_replicate, List.length_replicate] at hLen
  omega

/-- Boolean equality on `polyVarName` agrees with boolean equality on `Nat` indices. -/
@[simp] theorem polyVarName_beq (v j : Nat) :
    (polyVarName v == polyVarName j) = (v == j) := by
  by_cases h : v = j
  · subst h
    simp
  · have hNe : polyVarName v ≠ polyVarName j := fun hEq => h (polyVarName_inj hEq)
    have h1 : (v == j) = false := beq_false_of_ne h
    have h2 : (polyVarName v == polyVarName j) = false := beq_false_of_ne hNe
    rw [h1, h2]

/-- Lift a variable assignment `env : Nat → CanonicalRat` to a named `RealExpr` assignment
`String → CanonicalRat` such that `polyEnvToRho env (polyVarName v) = env v`. -/
@[expose] def polyEnvToRho (env : Nat → CanonicalRat) (name : String) : CanonicalRat :=
  env (name.toList.length - 1)

@[simp] theorem polyEnvToRho_polyVarName (env : Nat → CanonicalRat) (v : Nat) :
    polyEnvToRho env (polyVarName v) = env v := by
  dsimp only [polyEnvToRho, polyVarName]
  rw [String.toList_ofList, List.length_cons, List.length_replicate]
  exact congrArg env (Nat.add_sub_cancel v 1)

/-- Convert a single variable power $x_j^e$ into a `RealExpr`. -/
@[expose] def varPowerToRealExpr (j : Nat) : Nat → RealExpr
  | 0 => .const 1
  | e + 1 => .mul (.var (polyVarName j)) (varPowerToRealExpr j e)

/-- Convert a sparse `Monomial` $\prod_{(j, e) \in m} x_j^e$ into a `RealExpr`. -/
@[expose] def monomialToRealExpr : Monomial → RealExpr
  | [] => .const 1
  | (j, e) :: rest => .mul (varPowerToRealExpr j e) (monomialToRealExpr rest)

/-- Convert a list of `(Monomial × CanonicalRat)` terms into a `RealExpr`. -/
@[expose] def polyTermsToRealExpr : List (Monomial × CanonicalRat) → RealExpr
  | [] => .const 0
  | (m, c) :: rest => .add (.mul (.const c) (monomialToRealExpr m)) (polyTermsToRealExpr rest)

/-- Embed a multivariate polynomial `p : Poly` into `RealExpr`. -/
@[expose] def polyToRealExpr (p : Poly) : RealExpr :=
  polyTermsToRealExpr p.terms

/-- Evaluating `varPowerToRealExpr j e` under `polyEnvToRho env` equals `ratPow (env j) e`. -/
theorem evalPointPure_varPowerToRealExpr (env : Nat → CanonicalRat) (j : Nat) :
    ∀ (e : Nat), evalPointPure (polyEnvToRho env) (varPowerToRealExpr j e) = ratPow (env j) e
  | 0 => rfl
  | e + 1 => by
    dsimp only [varPowerToRealExpr, evalPointPure, ratPow]
    rw [polyEnvToRho_polyVarName, evalPointPure_varPowerToRealExpr env j e]

/-- Evaluating `monomialToRealExpr m` under `polyEnvToRho env` equals `Monomial.eval env m`. -/
theorem evalPointPure_monomialToRealExpr (env : Nat → CanonicalRat) :
    ∀ (m : Monomial), evalPointPure (polyEnvToRho env) (monomialToRealExpr m) = Monomial.eval env m
  | [] => rfl
  | (j, e) :: rest => by
    dsimp only [monomialToRealExpr, Monomial.eval, evalPointPure]
    rw [evalPointPure_varPowerToRealExpr, evalPointPure_monomialToRealExpr env rest]

/-- Evaluating `polyTermsToRealExpr terms` under `polyEnvToRho env` equals `evalTerms env terms`. -/
theorem evalPointPure_polyTermsToRealExpr (env : Nat → CanonicalRat) :
    ∀ (terms : List (Monomial × CanonicalRat)),
      evalPointPure (polyEnvToRho env) (polyTermsToRealExpr terms) = evalTerms env terms
  | [] => rfl
  | (m, c) :: rest => by
    dsimp only [polyTermsToRealExpr, evalTerms, evalPointPure]
    rw [evalPointPure_monomialToRealExpr, evalPointPure_polyTermsToRealExpr env rest]

/-- **Theorem (`polyToRealExpr_eval`)**:
Evaluating `polyToRealExpr p` via `evalPointPure (polyEnvToRho env)` agrees identically with `p.eval env`. -/
theorem polyToRealExpr_eval (env : Nat → CanonicalRat) (p : Poly) :
    evalPointPure (polyEnvToRho env) (polyToRealExpr p) = p.eval env :=
  evalPointPure_polyTermsToRealExpr env p.terms

/-- Constant polynomial $c \in \mathbb{Q}[x_0, \dots, x_{n-1}]$. -/
@[expose] def polyConst (c : CanonicalRat) : Poly :=
  polyOfTerm [] c

@[simp] theorem polyConst_eval (env : Nat → CanonicalRat) (c : CanonicalRat) :
    (polyConst c).eval env = c := by
  dsimp only [polyConst, polyOfTerm]
  by_cases hc : c == 0
  · have h0 : c = 0 := beq_iff_eq.mp hc
    subst h0
    rfl
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Poly.eval, evalTerms, Monomial.eval]
    grind

/-- Single variable power $x_j^e$ as a normalized `Poly`. -/
@[expose] def varPowerPoly (j : Nat) : Nat → Poly
  | 0 => Poly.one
  | e + 1 => Poly.mul (polyOfTerm [(j, 1)] 1) (varPowerPoly j e)

/-- Partial derivative $\frac{\partial}{\partial x_v}(x_j^e)$ as a normalized `Poly`. -/
@[expose] def derivVarPowerPoly (v j : Nat) : Nat → Poly
  | 0 => Poly.zero
  | e + 1 =>
    let dHead : Poly := if j == v then Poly.one else Poly.zero
    Poly.add
      (Poly.mul dHead (varPowerPoly j e))
      (Poly.mul (polyOfTerm [(j, 1)] 1) (derivVarPowerPoly v j e))

/-- Convert a `Monomial` into a normalized `Poly`. -/
@[expose] def monomialToPoly : Monomial → Poly
  | [] => Poly.one
  | (j, e) :: rest => Poly.mul (varPowerPoly j e) (monomialToPoly rest)

/-- Partial derivative $\frac{\partial}{\partial x_v}\left(\prod_{(j, e) \in m} x_j^e\right)$ via Leibniz product rule. -/
@[expose] def derivMonomialPoly (v : Nat) : Monomial → Poly
  | [] => Poly.zero
  | (j, e) :: rest =>
    Poly.add
      (Poly.mul (derivVarPowerPoly v j e) (monomialToPoly rest))
      (Poly.mul (varPowerPoly j e) (derivMonomialPoly v rest))

/-- Partial derivative of a list of `(Monomial × CanonicalRat)` terms with respect to variable `v`. -/
@[expose] def derivTermsPoly (v : Nat) : List (Monomial × CanonicalRat) → Poly
  | [] => Poly.zero
  | (m, c) :: rest =>
    Poly.add
      (Poly.scale c (derivMonomialPoly v m))
      (derivTermsPoly v rest)

/-- **Formal Partial Derivative of a Multivariate Polynomial (`polyPartialDeriv`)**:
Computes $\frac{\partial p}{\partial x_v} \in \mathbb{Q}[x_0, \dots, x_{n-1}]$. -/
@[expose] def polyPartialDeriv (v : Nat) (p : Poly) : Poly :=
  derivTermsPoly v p.terms

/-- **Polynomial Gradient Vector (`polyGradient`)**:
Computes $\nabla p = \left[\frac{\partial p}{\partial x_0}, \dots, \frac{\partial p}{\partial x_{\text{dim}-1}}\right]$. -/
@[expose] def polyGradient (dim : Nat) (p : Poly) : List Poly :=
  (List.range dim).map (fun i => polyPartialDeriv i p)

/-- Auxiliary accumulator for the polynomial Lie derivative $\sum_{k} \frac{\partial p}{\partial x_{\text{idx}+k}} f_k$. -/
@[expose] def lieDerivativePolyAux (idx : Nat) (p : Poly) : List Poly → Poly
  | [] => Poly.zero
  | f_i :: rest =>
    Poly.add (Poly.mul (polyPartialDeriv idx p) f_i) (lieDerivativePolyAux (idx + 1) p rest)

/-- **Polynomial Lie Derivative (`lieDerivativePoly`)**:
Computes $\mathcal{L}_f V(x) = \nabla V(x) \cdot f(x) = \sum_{i=0}^{n-1} \frac{\partial V}{\partial x_i}(x) \cdot f_i(x)$
along the polynomial vector field `vectorField = [f_0, ..., f_{n-1}]`. -/
@[expose] def lieDerivativePoly (p : Poly) (vectorField : List Poly) : Poly :=
  lieDerivativePolyAux 0 p vectorField

theorem eval_polyOfTerm_var1 (env : Nat → CanonicalRat) (j : Nat) :
    (polyOfTerm [(j, 1)] 1).eval env = env j := by
  change (1 : CanonicalRat) * ((env j * 1) * 1) + 0 = env j
  grind

theorem varPowerPoly_eval (env : Nat → CanonicalRat) (j : Nat) :
    ∀ (e : Nat), (varPowerPoly j e).eval env = ratPow (env j) e
  | 0 => by simp [varPowerPoly, ratPow]
  | e + 1 => by
    dsimp only [varPowerPoly, ratPow]
    rw [Poly.eval_mul, eval_polyOfTerm_var1, varPowerPoly_eval env j e]

theorem monomialToPoly_eval (env : Nat → CanonicalRat) :
    ∀ (m : Monomial), (monomialToPoly m).eval env = Monomial.eval env m
  | [] => by simp [monomialToPoly, Monomial.eval]
  | (j, e) :: rest => by
    dsimp only [monomialToPoly, Monomial.eval]
    rw [Poly.eval_mul, varPowerPoly_eval, monomialToPoly_eval env rest]

theorem derivVarPowerPoly_eval_eq_dual (env : Nat → CanonicalRat) (v j : Nat) :
    ∀ (e : Nat),
      (derivVarPowerPoly v j e).eval env =
        (evalDualRat (polyEnvToRho env) (polyVarName v) (varPowerToRealExpr j e)).der
  | 0 => by simp [derivVarPowerPoly, varPowerToRealExpr, evalDualRat, DualRat.const]
  | e + 1 => by
    dsimp only [derivVarPowerPoly, varPowerToRealExpr, evalDualRat, DualRat.mul, DualRat.var]
    rw [Poly.eval_add, Poly.eval_mul, Poly.eval_mul, eval_polyOfTerm_var1, varPowerPoly_eval]
    rw [derivVarPowerPoly_eval_eq_dual env v j e]
    have hVal : (evalDualRat (polyEnvToRho env) (polyVarName v) (varPowerToRealExpr j e)).val = ratPow (env j) e := by
      rw [(evalDual_fst_eq_eval (polyEnvToRho env) (polyVarName v) (varPowerToRealExpr j e)).1]
      exact evalPointPure_varPowerToRealExpr env j e
    rw [hVal, polyEnvToRho_polyVarName, polyVarName_beq]
    by_cases hjv : j == v <;> simp [hjv]

theorem derivMonomialPoly_eval_eq_dual (env : Nat → CanonicalRat) (v : Nat) :
    ∀ (m : Monomial),
      (derivMonomialPoly v m).eval env =
        (evalDualRat (polyEnvToRho env) (polyVarName v) (monomialToRealExpr m)).der
  | [] => by simp [derivMonomialPoly, monomialToRealExpr, evalDualRat, DualRat.const]
  | (j, e) :: rest => by
    dsimp only [derivMonomialPoly, monomialToRealExpr, evalDualRat, DualRat.mul]
    rw [Poly.eval_add, Poly.eval_mul, Poly.eval_mul, varPowerPoly_eval, monomialToPoly_eval]
    rw [derivVarPowerPoly_eval_eq_dual env v j e, derivMonomialPoly_eval_eq_dual env v rest]
    have hValL : (evalDualRat (polyEnvToRho env) (polyVarName v) (varPowerToRealExpr j e)).val = ratPow (env j) e := by
      rw [(evalDual_fst_eq_eval (polyEnvToRho env) (polyVarName v) (varPowerToRealExpr j e)).1]
      exact evalPointPure_varPowerToRealExpr env j e
    have hValR : (evalDualRat (polyEnvToRho env) (polyVarName v) (monomialToRealExpr rest)).val = Monomial.eval env rest := by
      rw [(evalDual_fst_eq_eval (polyEnvToRho env) (polyVarName v) (monomialToRealExpr rest)).1]
      exact evalPointPure_monomialToRealExpr env rest
    rw [hValL, hValR]

theorem derivTermsPoly_eval_eq_dual (env : Nat → CanonicalRat) (v : Nat) :
    ∀ (terms : List (Monomial × CanonicalRat)),
      (derivTermsPoly v terms).eval env =
        (evalDualRat (polyEnvToRho env) (polyVarName v) (polyTermsToRealExpr terms)).der
  | [] => by simp [derivTermsPoly, polyTermsToRealExpr, evalDualRat, DualRat.const]
  | (m, c) :: rest => by
    dsimp only [derivTermsPoly, polyTermsToRealExpr, evalDualRat, DualRat.add, DualRat.mul, DualRat.const]
    rw [Poly.eval_add, Poly.eval_scale]
    rw [derivMonomialPoly_eval_eq_dual env v m, derivTermsPoly_eval_eq_dual env v rest]
    grind

/-- **Theorem (`polyPartialDeriv_agrees_with_symbolicDeriv_and_reverseAD`)**:
For every polynomial `p : Poly`, variable index `v : Nat`, and rational point `env : Nat → CanonicalRat`,
evaluating the formal polynomial partial derivative `polyPartialDeriv v p` agrees identically with:
1. Symbolic differentiation `evalPointPure rho (symbolicDeriv (polyVarName v) (polyToRealExpr p))`,
2. Forward-mode dual automatic differentiation `(evalDualRat rho (polyVarName v) (polyToRealExpr p)).der`,
3. Recursive reverse-mode AD `reverseGradVar rho (polyVarName v) (polyToRealExpr p)`, and
4. Single-pass accumulated reverse-mode AD `accumulateGradStr (gradReverseAccumulated rho 1 (polyToRealExpr p)) (polyVarName v)`! -/
theorem polyPartialDeriv_agrees_with_symbolicDeriv_and_reverseAD
    (env : Nat → CanonicalRat) (v : Nat) (p : Poly) :
    let rho := polyEnvToRho env
    let vName := polyVarName v
    let expr := polyToRealExpr p
    (polyPartialDeriv v p).eval env = evalPointPure rho (symbolicDeriv vName expr) ∧
    (polyPartialDeriv v p).eval env = (evalDualRat rho vName expr).der ∧
    (polyPartialDeriv v p).eval env = reverseGradVar rho vName expr ∧
    (polyPartialDeriv v p).eval env = accumulateGradStr (gradReverseAccumulated rho 1 expr) vName := by
  dsimp only
  have hDual : (polyPartialDeriv v p).eval env =
      (evalDualRat (polyEnvToRho env) (polyVarName v) (polyToRealExpr p)).der :=
    derivTermsPoly_eval_eq_dual env v p.terms
  have hSym := symbolicDeriv_agrees_with_dual (polyEnvToRho env) (polyVarName v) (polyToRealExpr p)
  have hRev : accumulateGradStr (gradReverseAccumulated (polyEnvToRho env) 1 (polyToRealExpr p)) (polyVarName v) =
      (evalDualRat (polyEnvToRho env) (polyVarName v) (polyToRealExpr p)).der := by
    unfold gradReverseAccumulated
    rw [accumulateGradStr_mergeGradListStr]
    rw [gradReverse_agrees_with_dual (polyEnvToRho env) (polyVarName v) (polyToRealExpr p) 1]
    grind
  refine ⟨?_, hDual, ?_, ?_⟩
  · rw [hDual, ← hSym.1]
  · rw [hDual, hSym.2.2, hSym.1]
  · rw [hDual, hRev]

/-! ## 2. Positivstellensatz Non-Negativity Certificate Checker (`checkPsatzNonneg`) -/

/-- Check that `goal(x) ≥ 0` on the semialgebraic set $\{x \mid \forall g \in \text{ineqs}, g(x) \ge 0 \;\wedge\; \forall h \in \text{eqs}, h(x) = 0\}$
via a `PositivstellensatzCert` verifying the exact polynomial identity:
$$\text{goal}(x) = \sigma_0(x) + \sum_{(s_j, j)} s_j(x) g_j(x) + \sum_{(\lambda_\ell, \ell)} \lambda_\ell(x) h_\ell(x).$$ -/
@[expose] def checkPsatzNonneg
    (goal : Poly)
    (ineqs eqs : List Poly)
    (cert : PositivstellensatzCert) : Bool :=
  if !cert.sigma0.allCoeffsPos then false
  else
    match expandConeSum ineqs cert.coneTerms,
          expandIdealCombination? eqs cert.idealTerms with
    | some conePoly, some idealPoly =>
      let rhs := Poly.add cert.sigma0.expand (Poly.add conePoly idealPoly)
      (Poly.sub goal rhs).isZero
    | _, _ => false

/-- **Theorem (`checkPsatzNonneg_sound`)**:
Whenever `checkPsatzNonneg goal ineqs eqs cert = true`, for every rational state assignment
`env : Nat → CanonicalRat` satisfying `∀ g ∈ ineqs, 0 ≤ g.eval env` and `∀ h ∈ eqs, h.eval env = 0`,
we have `0 ≤ goal.eval env`! -/
theorem checkPsatzNonneg_sound
    (goal : Poly)
    (ineqs eqs : List Poly)
    (cert : PositivstellensatzCert)
    (env : Nat → CanonicalRat)
    (hCheck : checkPsatzNonneg goal ineqs eqs cert = true)
    (hIneqs : ∀ g, g ∈ ineqs → 0 ≤ g.eval env)
    (hEqs : ∀ h, h ∈ eqs → h.eval env = 0) :
    0 ≤ goal.eval env := by
  unfold checkPsatzNonneg at hCheck
  by_cases hPos0 : cert.sigma0.allCoeffsPos = true
  · simp only [hPos0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCheck
    cases hCone : expandConeSum ineqs cert.coneTerms with
    | none => rw [hCone] at hCheck; contradiction
    | some conePoly =>
      rw [hCone] at hCheck
      cases hIdeal : expandIdealCombination? eqs cert.idealTerms with
      | none => rw [hIdeal] at hCheck; contradiction
      | some idealPoly =>
        rw [hIdeal] at hCheck
        dsimp only at hCheck
        have hSubZero := Poly.eval_isZero env
          (Poly.sub goal (Poly.add cert.sigma0.expand (Poly.add conePoly idealPoly))) hCheck
        rw [Poly.eval_sub, Poly.eval_add, Poly.eval_add] at hSubZero
        have hSig0 := SOSPoly.eval_expand_nonneg env cert.sigma0 hPos0
        have hConeNonneg := expandConeSum_eval_nonneg env ineqs hIneqs cert.coneTerms conePoly hCone
        have hIdealZero := expandIdealCombination?_eval_eq_zero env eqs hEqs cert.idealTerms idealPoly hIdeal
        grind
  · simp [hPos0] at hCheck

/-! ## 3. Sum-of-Squares (SOS) Nonlinear Lyapunov Stability (`checkSosLyapunov`, `checkSosLyapunov_sound`) -/

/-- Zero origin assignment `originEnv : Nat → CanonicalRat := fun _ => 0`. -/
@[expose] def originEnv : Nat → CanonicalRat := fun _ => 0

/-- Squared Euclidean norm polynomial $\|x\|^2 = \sum_{i=0}^{\text{dim}-1} x_i^2$. -/
@[expose] def sumVarSquaresPoly : Nat → Poly
  | 0 => Poly.zero
  | i + 1 => Poly.add (sumVarSquaresPoly i) (Poly.sqr (polyOfTerm [(i, 1)] 1))

theorem sumVarSquaresPoly_eval_nonneg (env : Nat → CanonicalRat) :
    ∀ (dim : Nat), 0 ≤ (sumVarSquaresPoly dim).eval env
  | 0 => by simp [sumVarSquaresPoly]
  | i + 1 => by
    dsimp only [sumVarSquaresPoly]
    rw [Poly.eval_add]
    have hIH := sumVarSquaresPoly_eval_nonneg env i
    have hSq := Poly.eval_sq_nonneg env (polyOfTerm [(i, 1)] 1)
    grind

/-- Specification of a nonlinear polynomial ODE $\dot{x} = f(x)$ and candidate Lyapunov function $V(x)$:
* `dim`: state space dimension $n$,
* `vectorField`: polynomial vector field $f = [f_0, \dots, f_{n-1}]$,
* `domainIneqs`: semialgebraic domain constraints $\{g_k(x) \ge 0\}$,
* `lyapunovV`: candidate polynomial Lyapunov function $V(x)$,
* `radialEps`: strict radial positive-definiteness margin $\varepsilon > 0$ ($V(x) \ge \varepsilon \|x\|^2$),
* `decayGamma`: exponential decay rate $\gamma \ge 0$ ($\mathcal{L}_f V(x) \le -\gamma V(x)$). -/
structure SosLyapunovSpec where
  dim         : Nat
  vectorField : List Poly
  domainIneqs : List Poly
  lyapunovV   : Poly
  radialEps   : CanonicalRat
  decayGamma  : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- SOS Positivstellensatz witness for `SosLyapunovSpec`:
* `posDefCert`: certifies $V(x) - \varepsilon \|x\|^2 \ge 0$ on `domainIneqs`,
* `lieDecayCert`: certifies $-\mathcal{L}_f V(x) - \gamma V(x) \ge 0$ on `domainIneqs`. -/
structure SosLyapunovWitness where
  posDefCert   : PositivstellensatzCert
  lieDecayCert : PositivstellensatzCert
  deriving @[expose] DecidableEq, Repr

/-- Computable **SOS Lyapunov Stability Checker** (`checkSosLyapunov`):
Verifies:
1. $\varepsilon > 0$, $\gamma \ge 0$, and $V(0) = 0$,
2. **Strict Positive Definiteness**: $V(x) - \varepsilon \|x\|^2 \ge 0$ via `checkPsatzNonneg`,
3. **Negative-Definite Lie Derivative Decay**: $-\mathcal{L}_f V(x) - \gamma V(x) \ge 0$ via `checkPsatzNonneg`. -/
@[expose] def checkSosLyapunov (spec : SosLyapunovSpec) (w : SosLyapunovWitness) : Bool :=
  let posDefGoal := Poly.sub spec.lyapunovV (Poly.scale spec.radialEps (sumVarSquaresPoly spec.dim))
  let lieV := lieDerivativePoly spec.lyapunovV spec.vectorField
  let lieDecayGoal := Poly.sub (Poly.neg lieV) (Poly.scale spec.decayGamma spec.lyapunovV)
  decide (0 < spec.radialEps) &&
  decide (0 ≤ spec.decayGamma) &&
  decide (spec.lyapunovV.eval originEnv = 0) &&
  checkPsatzNonneg posDefGoal spec.domainIneqs [] w.posDefCert &&
  checkPsatzNonneg lieDecayGoal spec.domainIneqs [] w.lieDecayCert

/-- **Theorem (`checkSosLyapunov_sound`)**:
Whenever `checkSosLyapunov spec w = true`, the candidate Lyapunov function $V(x)$ is a certified
Lyapunov function on the domain $\{x \mid \forall g \in \text{spec.domainIneqs}, g(x) \ge 0\}$:
1. $V(0) = 0$, $\varepsilon > 0$, and $\gamma \ge 0$,
2. For every state `env` in the domain, $V(\text{env}) \ge \varepsilon \|x\|^2 \ge 0$, and
3. For every state `env` in the domain, the Lie derivative satisfies
   $\mathcal{L}_f V(\text{env}) \le -\gamma V(\text{env}) \le 0$! -/
theorem checkSosLyapunov_sound
    (spec : SosLyapunovSpec)
    (w : SosLyapunovWitness)
    (env : Nat → CanonicalRat)
    (hCheck : checkSosLyapunov spec w = true)
    (hDom : ∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval env) :
    0 < spec.radialEps ∧
    0 ≤ spec.decayGamma ∧
    spec.lyapunovV.eval originEnv = 0 ∧
    spec.radialEps * (sumVarSquaresPoly spec.dim).eval env ≤ spec.lyapunovV.eval env ∧
    0 ≤ spec.lyapunovV.eval env ∧
    (lieDerivativePoly spec.lyapunovV spec.vectorField).eval env ≤ -spec.decayGamma * spec.lyapunovV.eval env ∧
    (lieDerivativePoly spec.lyapunovV spec.vectorField).eval env ≤ 0 := by
  unfold checkSosLyapunov at hCheck
  dsimp only at hCheck
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨h1234, hLieCert⟩
  rcases (Bool.and_eq_true _ _).mp h1234 with ⟨h123, hPosCert⟩
  rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hOriginB⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨hEpsB, hGammaB⟩
  have hEps : 0 < spec.radialEps := of_decide_eq_true hEpsB
  have hGamma : 0 ≤ spec.decayGamma := of_decide_eq_true hGammaB
  have hOrigin : spec.lyapunovV.eval originEnv = 0 := of_decide_eq_true hOriginB
  have hPosNonneg := checkPsatzNonneg_sound
    (Poly.sub spec.lyapunovV (Poly.scale spec.radialEps (sumVarSquaresPoly spec.dim)))
    spec.domainIneqs [] w.posDefCert env hPosCert hDom (by intro _ h; cases h)
  rw [Poly.eval_sub, Poly.eval_scale] at hPosNonneg
  have hLieNonneg := checkPsatzNonneg_sound
    (Poly.sub (Poly.neg (lieDerivativePoly spec.lyapunovV spec.vectorField)) (Poly.scale spec.decayGamma spec.lyapunovV))
    spec.domainIneqs [] w.lieDecayCert env hLieCert hDom (by intro _ h; cases h)
  rw [Poly.eval_sub, Poly.eval_neg, Poly.eval_scale] at hLieNonneg
  have hNormNonneg := sumVarSquaresPoly_eval_nonneg env spec.dim
  have hEpsLe : 0 ≤ spec.radialEps := by grind
  have hRadProd0 := Rat.mul_le_mul_of_nonneg_left hNormNonneg hEpsLe
  have hRadProd : 0 ≤ spec.radialEps * (sumVarSquaresPoly spec.dim).eval env := by grind
  have hVNonneg : 0 ≤ spec.lyapunovV.eval env := by grind
  have hGammaVNonneg0 := Rat.mul_le_mul_of_nonneg_left hVNonneg hGamma
  have hGammaVNonneg : 0 ≤ spec.decayGamma * spec.lyapunovV.eval env := by grind
  refine ⟨hEps, hGamma, hOrigin, by grind, hVNonneg, by grind, by grind⟩

/-! ## 4. Sum-of-Squares Control Barrier Functions (`checkSosCbf`, `checkSosCbf_sound`) -/

/-- Specification of a polynomial Control Barrier Function (CBF) $B(x)$ separating the safe set
$\mathcal{C} = \{x \mid B(x) \ge 0\}$ from an unsafe region $\{x \mid u_{\text{unsafe}}(x) \ge 0\}$:
* `vectorField`: closed-loop polynomial vector field $f(x)$,
* `domainIneqs`: operating domain inequality generators $\{g_k(x) \ge 0\}$,
* `barrierB`: barrier polynomial $B(x)$ ($\mathcal{C} = \{x \mid B(x) \ge 0\}$),
* `unsafePoly`: unsafe region polynomial $u_{\text{unsafe}}(x)$ ($\mathcal{U} = \{x \mid u_{\text{unsafe}}(x) \ge 0\}$),
* `classKAlpha`: linear class-$\mathcal{K}$ barrier rate $\alpha \ge 0$ ($\mathcal{L}_f B(x) + \alpha B(x) \ge 0$). -/
structure SosCbfSpec where
  vectorField : List Poly
  domainIneqs : List Poly
  barrierB    : Poly
  unsafePoly  : Poly
  classKAlpha : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- SOS Positivstellensatz witness for `SosCbfSpec`:
* `unsafeRefuteCert`: Stengle Positivstellensatz refutation of $\{B(x) \ge 0, u_{\text{unsafe}}(x) \ge 0\}$,
* `nagumoInvarianceCert`: Positivstellensatz certificate for $\mathcal{L}_f B(x) + \alpha B(x) \ge 0$ on $\mathcal{C} \cap \text{domain}$. -/
structure SosCbfWitness where
  unsafeRefuteCert     : PositivstellensatzCert
  nagumoInvarianceCert : PositivstellensatzCert
  deriving @[expose] DecidableEq, Repr

/-- Computable **SOS Control Barrier Function Checker** (`checkSosCbf`):
Verifies:
1. **Stengle Unsafe Set Refutation**: `positivstellensatzCheck 0 qUnsafe w.unsafeRefuteCert = .ok`,
   certifying that $B(x) \ge 0$ and $u_{\text{unsafe}}(x) \ge 0$ are mutually infeasible on the domain, and
2. **Nagumo / Ames Barrier Forward Invariance**: $\mathcal{L}_f B(x) + \alpha B(x) \ge 0$ on
   $B(x) \ge 0$ and `domainIneqs` via `checkPsatzNonneg`. -/
@[expose] def checkSosCbf (spec : SosCbfSpec) (w : SosCbfWitness) : Bool :=
  let qUnsafe : PositivstellensatzQuery :=
    { strictPos := []
    , nonneg    := spec.barrierB :: spec.unsafePoly :: spec.domainIneqs
    , eqs       := [] }
  let lieB := lieDerivativePoly spec.barrierB spec.vectorField
  let nagumoGoal := Poly.add lieB (Poly.scale spec.classKAlpha spec.barrierB)
  decide (0 ≤ spec.classKAlpha) &&
  decide (positivstellensatzCheck 0 qUnsafe w.unsafeRefuteCert = .ok) &&
  checkPsatzNonneg nagumoGoal (spec.barrierB :: spec.domainIneqs) [] w.nagumoInvarianceCert

/-- **Theorem (`checkSosCbf_sound`)**:
Whenever `checkSosCbf spec w = true`, for every state `env` in the safe set $\mathcal{C}$
(`0 ≤ spec.barrierB.eval env` and `∀ g ∈ spec.domainIneqs, 0 ≤ g.eval env`):
1. **Strict Safety Separation**: `spec.unsafePoly.eval env < 0` (no safe state can ever lie in the
   unsafe region $\{x \mid u_{\text{unsafe}}(x) \ge 0\}$!), and
2. **Nagumo / Ames Forward Invariance**:
   $0 \le \mathcal{L}_f B(\text{env}) + \alpha B(\text{env})$ ($\mathcal{L}_f B(\text{env}) \ge -\alpha B(\text{env})$)! -/
theorem checkSosCbf_sound
    (spec : SosCbfSpec)
    (w : SosCbfWitness)
    (env : Nat → CanonicalRat)
    (hCheck : checkSosCbf spec w = true)
    (hDom : ∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval env)
    (hSafe : 0 ≤ spec.barrierB.eval env) :
    spec.unsafePoly.eval env < 0 ∧
    0 ≤ (lieDerivativePoly spec.barrierB spec.vectorField).eval env +
        spec.classKAlpha * spec.barrierB.eval env := by
  unfold checkSosCbf at hCheck
  dsimp only at hCheck
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨h12, hNagumo⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨_hAlphaB, hRefuteB⟩
  have hRefute : positivstellensatzCheck 0
      { strictPos := [], nonneg := spec.barrierB :: spec.unsafePoly :: spec.domainIneqs, eqs := [] }
      w.unsafeRefuteCert = .ok := of_decide_eq_true hRefuteB
  have hInfeas := positivstellensatz_general_eval_infeasible 0
    { strictPos := [], nonneg := spec.barrierB :: spec.unsafePoly :: spec.domainIneqs, eqs := [] }
    w.unsafeRefuteCert hRefute env
  have hNotUnsafe : ¬ (0 ≤ spec.unsafePoly.eval env) := by
    intro hUnsafe
    apply hInfeas (by intro _ h; cases h)
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg1
      · exact hSafe
      · rcases List.mem_cons.mp hg1 with rfl | hg2
        · exact hUnsafe
        · exact hDom g hg2
    · intro _ h; cases h
  have hSafeDom : ∀ g, g ∈ (spec.barrierB :: spec.domainIneqs) → 0 ≤ g.eval env := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hgDom
    · exact hSafe
    · exact hDom g hgDom
  have hNagumoNonneg := checkPsatzNonneg_sound
    (Poly.add (lieDerivativePoly spec.barrierB spec.vectorField) (Poly.scale spec.classKAlpha spec.barrierB))
    (spec.barrierB :: spec.domainIneqs) [] w.nagumoInvarianceCert env hNagumo hSafeDom (by intro _ h; cases h)
  rw [Poly.eval_add, Poly.eval_scale] at hNagumoNonneg
  exact ⟨by grind, hNagumoNonneg⟩

/-! ## 5. Index-1 DAE Algebraic Manifold Tangency & Regularity (`checkDaeManifold`, `checkDaeManifold_sound`) -/

/-- Alias for Buchberger/Gröbner ideal membership certification `checkIdealMembership` from `Groebner.lean`. -/
abbrev checkIdealMembershipCert (target : Poly) (gens : List Poly) (cert : IdealMembershipCert) : Bool :=
  checkIdealMembership target gens cert

/-- Specification of an Index-1 Differential-Algebraic Equation (DAE) manifold
$\mathcal{M} = \{x \mid h_1(x) = 0, \dots, h_m(x) = 0\}$:
* `vectorField`: differential-algebraic vector field $f(x)$,
* `domainIneqs`: operating domain inequality constraints $\{g_k(x) \ge 0\}$,
* `algConstraints`: algebraic manifold equations $[h_1, \dots, h_m]$,
* `algVars`: indices $[z_1, \dots, z_m]$ of the algebraic variables with respect to which the
  Index-1 Jacobian $\frac{\partial h_i}{\partial x_{z_j}}$ is differentiated (defaults to `[1]`),
* `algJacobianDet`: determinant polynomial $\det J_{\text{alg}}(x) = \det\left(\frac{\partial h}{\partial z}\right)$
  of the algebraic variables (verified against symbolic `computeSymbolicAlgJacobianDet`),
* `regDelta`: strict Index-1 regularity lower bound $\delta_{\text{reg}} > 0$
  ($(\det J_{\text{alg}}(x))^2 \ge \delta_{\text{reg}}$ on $\mathcal{M}$). -/
structure DaeManifoldSpec where
  vectorField    : List Poly
  domainIneqs    : List Poly
  algConstraints : List Poly
  algVars        : List Nat := [1]
  algJacobianDet : Poly
  regDelta       : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- Witness for `DaeManifoldSpec`:
* `tangencyCert`: primary Gröbner/Buchberger ideal membership witness certifying $\mathcal{L}_f h_r \in \langle h_1, \dots, h_m \rangle$,
* `tangencyCerts`: optional per-constraint ideal membership certificates $[c_1, \dots, c_m]$ for multi-constraint DAEs,
* `regularityCert`: Positivstellensatz certificate proving $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$
  modulo `algConstraints` and `domainIneqs`. -/
structure DaeManifoldWitness where
  tangencyCert   : IdealMembershipCert
  tangencyCerts  : List IdealMembershipCert := []
  regularityCert : PositivstellensatzCert
  deriving @[expose] DecidableEq, Repr

/-- Remove the `k`-th element of a list (used for Laplace cofactor expansion). -/
@[expose] def listEraseIdx' {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, k + 1 => x :: listEraseIdx' xs k

/-- Determinant of a square matrix of polynomials given as rows, by Laplace expansion along the
first row: $\det M = \sum_j (-1)^j M_{0,j} \det M^{(0,j)}$. Structural recursion on the row list;
a ragged or empty matrix has determinant `Poly.one` for `[]` (the empty product) and the expansion
is over whatever entries the first row has. -/
@[expose] def polyMatrixDet : List (List Poly) → Poly
  | [] => Poly.one
  | row :: rest =>
    (List.range row.length).foldl
      (fun acc j =>
        let entry := row.getD j Poly.zero
        let sub := rest.map (fun r => listEraseIdx' r j)
        let term := Poly.mul entry (polyMatrixDet sub)
        if j % 2 == 0 then Poly.add acc term else Poly.sub acc term)
      Poly.zero
termination_by rows => rows.length
decreasing_by all_goals simp_wf

/-- The symbolic algebraic Jacobian matrix $J_{i,j} = \partial h_i / \partial x_{v_j}$ as rows. -/
@[expose] def symbolicAlgJacobian (algConstraints : List Poly) (algVars : List Nat) : List (List Poly) :=
  algConstraints.map (fun h => algVars.map (fun v => polyPartialDeriv v h))

/-- Compute the symbolic algebraic Jacobian determinant $\det\left(\frac{\partial h_i}{\partial x_{v_j}}\right)$
by Laplace expansion of `symbolicAlgJacobian` (`Poly.zero` when the system is not square). The
$1 \times 1$ and $2 \times 2$ cases agree with the direct formulas; for $m \ge 3$ this is the full
determinant, not the product of the diagonal partials (which is what this function computed before
2026-11-04 and which is wrong for any non-triangular Jacobian). -/
@[expose] def computeSymbolicAlgJacobianDet (algConstraints : List Poly) (algVars : List Nat) : Poly :=
  if algConstraints.length != algVars.length then
    Poly.zero
  else
    polyMatrixDet (symbolicAlgJacobian algConstraints algVars)

/-- Verify Index-1 DAE regularity (`checkDaeIndex1Regularity`):
1. `spec.algConstraints.length == spec.algVars.length`,
2. `spec.algJacobianDet` equals the symbolic Jacobian determinant
   `computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars`,
3. `0 < spec.regDelta`, and
4. $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$ on $\mathcal{M}$ via `checkPsatzNonneg`. -/
@[expose] def checkDaeIndex1Regularity (spec : DaeManifoldSpec) (regCert : PositivstellensatzCert) : Bool :=
  let symDet := computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars
  let regGoal := Poly.sub (Poly.sqr spec.algJacobianDet) (polyConst spec.regDelta)
  decide (spec.algConstraints.length = spec.algVars.length) &&
  (Poly.sub spec.algJacobianDet symDet).isZero &&
  decide (0 < spec.regDelta) &&
  checkPsatzNonneg regGoal spec.domainIneqs spec.algConstraints regCert

/-- Helper lemma: `List.all` is `true` iff the predicate holds for all members of the list. -/
theorem sos_list_all_iff_forall (p : Poly → Bool) :
    ∀ (xs : List Poly), xs.all p = true ↔ ∀ x, x ∈ xs → p x = true
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | x :: xs => by
    simp only [List.all_cons, Bool.and_eq_true, sos_list_all_iff_forall p xs, List.mem_cons]
    constructor
    · rintro ⟨hx, hxs⟩ y (rfl | hy)
      · exact hx
      · exact hxs y hy
    · intro h
      exact ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩

/-- Helper lemma: `List.any` is `true` iff the predicate holds for some member of the list. -/
theorem sos_list_any_iff_exists (p : IdealMembershipCert → Bool) :
    ∀ (cs : List IdealMembershipCert), cs.any p = true ↔ ∃ c, c ∈ cs ∧ p c = true
  | [] => by
    constructor
    · intro h; cases h
    · rintro ⟨_, h, _⟩; cases h
  | c :: cs => by
    simp only [List.any_cons, Bool.or_eq_true, sos_list_any_iff_exists p cs, List.mem_cons]
    constructor
    · rintro (hc | ⟨c', hc', hp⟩)
      · exact ⟨c, Or.inl rfl, hc⟩
      · exact ⟨c', Or.inr hc', hp⟩
    · rintro ⟨c', rfl | hc', hp⟩
      · exact Or.inl hp
      · exact Or.inr ⟨c', hc', hp⟩

/-- Check ideal membership of $\mathcal{L}_f h_r$ in $\langle h_1, \dots, h_m \rangle$ using either
the primary `w.tangencyCert` or any per-constraint witness in `w.tangencyCerts`. -/
@[expose] def checkConstraintTangency (spec : DaeManifoldSpec) (w : DaeManifoldWitness) (h_r : Poly) : Bool :=
  let lieH := lieDerivativePoly h_r spec.vectorField
  checkIdealMembershipCert lieH spec.algConstraints w.tangencyCert ||
  w.tangencyCerts.any (fun c => checkIdealMembershipCert lieH spec.algConstraints c)

/-- Computable **Index-1 DAE Manifold Invariance & Regularity Checker** (`checkDaeManifold`):
Verifies:
1. **Symbolic Index-1 Jacobian Regularity** (`checkDaeIndex1Regularity`):
   `spec.algJacobianDet` matches `computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars`,
   $\delta_{\text{reg}} > 0$, and $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$ on $\mathcal{M}$
   via `checkPsatzNonneg`, and
2. **Algebraic Manifold Tangency**: for every constraint $h_r \in \text{algConstraints}$, its Lie
   derivative $\mathcal{L}_f h_r$ is certified in $\langle h_1, \dots, h_m \rangle$ via `checkConstraintTangency`. -/
@[expose] def checkDaeManifold (spec : DaeManifoldSpec) (w : DaeManifoldWitness) : Bool :=
  spec.algConstraints.all (checkConstraintTangency spec w) &&
  checkDaeIndex1Regularity spec w.regularityCert

/-- **Theorem (`checkDaeManifold_sound`)**:
Whenever `checkDaeManifold spec w = true`, for every state `env` on the algebraic constraint manifold
$\mathcal{M}$ (`∀ h ∈ spec.algConstraints, h.eval env = 0` and `∀ g ∈ spec.domainIneqs, 0 ≤ g.eval env`):
1. **Exact Manifold Tangency**: for every algebraic constraint $h_r \in \text{spec.algConstraints}$,
   the Lie derivative vanishes identically on $\mathcal{M}$:
   `((lieDerivativePoly h_r spec.vectorField).eval env = 0)`,
2. **Symbolic Jacobian Agreement & Index-1 Non-Singularity**:
   `spec.algJacobianDet.eval env = (computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars).eval env`,
   `spec.regDelta ≤ (Poly.sqr spec.algJacobianDet).eval env`, and `spec.algJacobianDet.eval env ≠ 0`! -/
theorem checkDaeManifold_sound
    (spec : DaeManifoldSpec)
    (w : DaeManifoldWitness)
    (env : Nat → CanonicalRat)
    (hCheck : checkDaeManifold spec w = true)
    (hDom : ∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval env)
    (hManifold : ∀ h, h ∈ spec.algConstraints → h.eval env = 0) :
    0 < spec.regDelta ∧
    (∀ h_r, h_r ∈ spec.algConstraints →
      (lieDerivativePoly h_r spec.vectorField).eval env = 0) ∧
    spec.regDelta ≤ (Poly.sqr spec.algJacobianDet).eval env ∧
    spec.algJacobianDet.eval env ≠ 0 := by
  unfold checkDaeManifold checkDaeIndex1Regularity at hCheck
  dsimp only at hCheck
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨hTangency, hRegAll⟩
  rcases (Bool.and_eq_true _ _).mp hRegAll with ⟨hReg123, hRegCert⟩
  rcases (Bool.and_eq_true _ _).mp hReg123 with ⟨_hReg12, hDeltaB⟩
  have hDelta : 0 < spec.regDelta := of_decide_eq_true hDeltaB
  rw [sos_list_all_iff_forall] at hTangency
  have hRegNonneg := checkPsatzNonneg_sound
    (Poly.sub (Poly.sqr spec.algJacobianDet) (polyConst spec.regDelta))
    spec.domainIneqs spec.algConstraints w.regularityCert env hRegCert hDom hManifold
  rw [Poly.eval_sub, polyConst_eval] at hRegNonneg
  have hDetNeZero : spec.algJacobianDet.eval env ≠ 0 := by
    intro hZero
    have hSqZero : (Poly.sqr spec.algJacobianDet).eval env = 0 := by
      rw [Poly.eval_sqr, hZero]
      grind
    grind
  refine ⟨hDelta, ?_, by grind, hDetNeZero⟩
  intro h_r hMem
  have hTang := hTangency h_r hMem
  unfold checkConstraintTangency at hTang
  dsimp only at hTang
  rcases (Bool.or_eq_true _ _).mp hTang with hPrimary | hAny
  · exact checkIdealMembership_eval_sound
      (lieDerivativePoly h_r spec.vectorField) spec.algConstraints w.tangencyCert hPrimary env hManifold
  · rw [sos_list_any_iff_exists] at hAny
    rcases hAny with ⟨c, _hcMem, hcOk⟩
    exact checkIdealMembership_eval_sound
      (lieDerivativePoly h_r spec.vectorField) spec.algConstraints c hcOk env hManifold

/-- **Theorem (`checkDaeManifold_symbolic_jacobian_sound`)**:
Whenever `checkDaeManifold spec w = true`, the user-supplied `spec.algJacobianDet` evaluates
identically to the symbolic Jacobian determinant `computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars`
and is strictly non-zero across the manifold! -/
theorem checkDaeManifold_symbolic_jacobian_sound
    (spec : DaeManifoldSpec)
    (w : DaeManifoldWitness)
    (env : Nat → CanonicalRat)
    (hCheck : checkDaeManifold spec w = true)
    (hDom : ∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval env)
    (hManifold : ∀ h, h ∈ spec.algConstraints → h.eval env = 0) :
    spec.algJacobianDet.eval env =
      (computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars).eval env ∧
    (computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars).eval env ≠ 0 := by
  have hMain := checkDaeManifold_sound spec w env hCheck hDom hManifold
  unfold checkDaeManifold checkDaeIndex1Regularity at hCheck
  dsimp only at hCheck
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨_, hRegAll⟩
  rcases (Bool.and_eq_true _ _).mp hRegAll with ⟨hReg123, _⟩
  rcases (Bool.and_eq_true _ _).mp hReg123 with ⟨hReg12, _⟩
  rcases (Bool.and_eq_true _ _).mp hReg12 with ⟨_, hSymZero⟩
  have hSub := Poly.eval_isZero env
    (Poly.sub spec.algJacobianDet (computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars)) hSymZero
  rw [Poly.eval_sub] at hSub
  have hEq : spec.algJacobianDet.eval env =
      (computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars).eval env := by grind
  exact ⟨hEq, by rw [← hEq]; exact hMain.2.2.2⟩

/-! ## 6. Universal Judge & Format Registration (`"sos-lyapunov-cbf@1"`) -/

/-- Unified problem bundle for `"sos-lyapunov-cbf@1"` combining nonlinear SOS Lyapunov stability,
SOS Control Barrier Function safety, and Index-1 DAE manifold invariance. -/
structure SosLyapunovProblem where
  lyapunov : SosLyapunovSpec
  cbf      : SosCbfSpec
  dae      : DaeManifoldSpec
  deriving @[expose] DecidableEq, Repr

/-- Unified certificate bundle for `"sos-lyapunov-cbf@1"`. -/
structure SosLyapunovCert where
  lyapunovWitness : SosLyapunovWitness
  cbfWitness      : SosCbfWitness
  daeWitness      : DaeManifoldWitness
  deriving @[expose] DecidableEq, Repr

/-- Refusal clause for `sosLyapunovJudge`. -/
inductive SosLyapunovClause where
  | lyapunovFailed
  | cbfFailed
  | daeManifoldFailed
  deriving @[expose] DecidableEq, Repr

/-- Independent semantic meaning of `SosLyapunovProblem`. -/
def SosLyapunovProblem.SemanticMeaning (prob : SosLyapunovProblem) : Prop :=
  (0 < prob.lyapunov.radialEps ∧
   0 ≤ prob.lyapunov.decayGamma ∧
   prob.lyapunov.lyapunovV.eval originEnv = 0 ∧
   ∀ env : Nat → CanonicalRat,
     (∀ g, g ∈ prob.lyapunov.domainIneqs → 0 ≤ g.eval env) →
     0 ≤ prob.lyapunov.lyapunovV.eval env ∧
     (lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField).eval env ≤ 0) ∧
  (∀ env : Nat → CanonicalRat,
     (∀ g, g ∈ prob.cbf.domainIneqs → 0 ≤ g.eval env) →
     0 ≤ prob.cbf.barrierB.eval env →
     prob.cbf.unsafePoly.eval env < 0 ∧
     0 ≤ (lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField).eval env +
         prob.cbf.classKAlpha * prob.cbf.barrierB.eval env) ∧
  (0 < prob.dae.regDelta ∧
   ∀ env : Nat → CanonicalRat,
     (∀ g, g ∈ prob.dae.domainIneqs → 0 ≤ g.eval env) →
     (∀ h, h ∈ prob.dae.algConstraints → h.eval env = 0) →
     (∀ h_r, h_r ∈ prob.dae.algConstraints →
       (lieDerivativePoly h_r prob.dae.vectorField).eval env = 0) ∧
     prob.dae.algJacobianDet.eval env ≠ 0)

/-- Verdict checker for `sosLyapunovJudge`. -/
@[expose] def checkSosLyapunovProblem
    (_grade : Nat)
    (prob : SosLyapunovProblem)
    (cert : SosLyapunovCert) : Judge.Verdict SosLyapunovClause :=
  if !checkSosLyapunov prob.lyapunov cert.lyapunovWitness then
    .refused .lyapunovFailed []
  else if !checkSosCbf prob.cbf cert.cbfWitness then
    .refused .cbfFailed []
  else if !checkDaeManifold prob.dae cert.daeWitness then
    .refused .daeManifoldFailed []
  else
    .ok

/-- **Theorem (`checkSosLyapunovProblem_sound`)**:
Whenever `checkSosLyapunovProblem fuel prob cert = .ok`, `prob.SemanticMeaning` holds! -/
theorem checkSosLyapunovProblem_sound
    (fuel : Nat)
    (prob : SosLyapunovProblem)
    (cert : SosLyapunovCert)
    (hOk : checkSosLyapunovProblem fuel prob cert = .ok) :
    prob.SemanticMeaning := by
  unfold checkSosLyapunovProblem at hOk
  by_cases hL : checkSosLyapunov prob.lyapunov cert.lyapunovWitness = true
  · simp only [hL, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    by_cases hC : checkSosCbf prob.cbf cert.cbfWitness = true
    · simp only [hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      by_cases hD : checkDaeManifold prob.dae cert.daeWitness = true
      · refine ⟨?_, ?_, ?_⟩
        · have hBase : 0 < prob.lyapunov.radialEps ∧ 0 ≤ prob.lyapunov.decayGamma ∧ prob.lyapunov.lyapunovV.eval originEnv = 0 := by
            unfold checkSosLyapunov at hL
            dsimp only at hL
            rcases (Bool.and_eq_true _ _).mp hL with ⟨h1234, _⟩
            rcases (Bool.and_eq_true _ _).mp h1234 with ⟨h123, _⟩
            rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hOriginB⟩
            rcases (Bool.and_eq_true _ _).mp h12 with ⟨hEpsB, hGammaB⟩
            exact ⟨of_decide_eq_true hEpsB, of_decide_eq_true hGammaB, of_decide_eq_true hOriginB⟩
          refine ⟨hBase.1, hBase.2.1, hBase.2.2, ?_⟩
          intro env hDom
          have hEnv := checkSosLyapunov_sound prob.lyapunov cert.lyapunovWitness env hL hDom
          exact ⟨hEnv.2.2.2.2.1, hEnv.2.2.2.2.2.2⟩
        · intro env hDom hSafe
          exact checkSosCbf_sound prob.cbf cert.cbfWitness env hC hDom hSafe
        · have hDelta : 0 < prob.dae.regDelta := by
            unfold checkDaeManifold checkDaeIndex1Regularity at hD
            dsimp only at hD
            rcases (Bool.and_eq_true _ _).mp hD with ⟨_, hRegAll⟩
            rcases (Bool.and_eq_true _ _).mp hRegAll with ⟨hReg123, _⟩
            rcases (Bool.and_eq_true _ _).mp hReg123 with ⟨_, hDeltaB⟩
            exact of_decide_eq_true hDeltaB
          refine ⟨hDelta, ?_⟩
          intro env hDom hMan
          have hEnv := checkDaeManifold_sound prob.dae cert.daeWitness env hD hDom hMan
          exact ⟨hEnv.2.1, hEnv.2.2.2⟩
      · simp [hD] at hOk
    · simp [hC] at hOk
  · simp [hL] at hOk

/-- Universal Judge instance for `"sos-lyapunov-cbf@1"`. -/
instance sosLyapunovJudge : Judge SosLyapunovProblem SosLyapunovCert where
  Clause := SosLyapunovClause
  Meaning prob _cert := prob.SemanticMeaning
  check := checkSosLyapunovProblem
  sound := by intro r prob cert h; exact checkSosLyapunovProblem_sound r prob cert h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment prob := ∃ cert r, checkSosLyapunovProblem r prob cert = .ok
  complete := by rintro prob ⟨cert, r, h⟩ _; exact ⟨cert, r, h⟩
  mono := by intro r r' o c le hne; rfl

/-! ## 7. Canonical Showcase Models: 2D Nonlinear Cubic Damping, Barrier Safety & Index-1 DAE Manifold -/

/-- Variable $x_0$ as `Poly`. -/
@[expose] def x0Poly : Poly := polyOfTerm [(0, 1)] 1

/-- Variable $x_1$ as `Poly`. -/
@[expose] def x1Poly : Poly := polyOfTerm [(1, 1)] 1

/-- 2D nonlinear cubic-damped oscillator vector field:
$$\dot{x}_0 = -x_0 - x_0^3 + x_1, \qquad \dot{x}_1 = -x_0 - x_1 - x_1^3.$$ -/
@[expose] def cubicDampedVectorField2D : List Poly :=
  [ Poly.add (Poly.neg x0Poly) (Poly.add (Poly.neg (Poly.mul x0Poly (Poly.sqr x0Poly))) x1Poly)
  , Poly.sub (Poly.neg x0Poly) (Poly.add x1Poly (Poly.mul x1Poly (Poly.sqr x1Poly))) ]

/-- Candidate Lyapunov function $V(x_0, x_1) = x_0^2 + x_1^2$ with $\varepsilon = 1/2$, $\gamma = 2$:
$$\mathcal{L}_f V = 2 x_0(-x_0 - x_0^3 + x_1) + 2 x_1(-x_0 - x_1 - x_1^3) = -2(x_0^2 + x_1^2) - 2(x_0^4 + x_1^4),$$
so $-\mathcal{L}_f V - 2 V = 2 x_0^4 + 2 x_1^4 = 2(x_0^2)^2 + 2(x_1^2)^2 \ge 0$! -/
@[expose] def goldenLyapunovSpec2D : SosLyapunovSpec where
  dim         := 2
  vectorField := cubicDampedVectorField2D
  domainIneqs := []
  lyapunovV   := Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly)
  radialEps   := CanonicalRat.mk 1 2
  decayGamma  := 2

/-- SOS witness for `goldenLyapunovSpec2D`:
* $V - \frac{1}{2}(x_0^2 + x_1^2) = \frac{1}{2} x_0^2 + \frac{1}{2} x_1^2$,
* $-\mathcal{L}_f V - 2 V = 2 (x_0^2)^2 + 2 (x_1^2)^2$. -/
@[expose] def goldenLyapunovWitness2D : SosLyapunovWitness where
  posDefCert :=
    { monoidIndices := []
    , sigma0        := { terms := [(CanonicalRat.mk 1 2, x0Poly), (CanonicalRat.mk 1 2, x1Poly)] }
    , coneTerms     := []
    , idealTerms    := [] }
  lieDecayCert :=
    { monoidIndices := []
    , sigma0        := { terms := [(2, Poly.sqr x0Poly), (2, Poly.sqr x1Poly)] }
    , coneTerms     := []
    , idealTerms    := [] }

/-- 2D Control Barrier Function specification on the damped vector field $\dot{x}_0 = -x_0, \dot{x}_1 = -x_1$:
* Safe set $B(x) = 1 - x_0^2 - x_1^2 \ge 0$ (unit disk),
* Unsafe set $u_{\text{unsafe}}(x) = x_0^2 + x_1^2 - 2 \ge 0$ (exterior of radius $\sqrt{2}$),
* Class-$\mathcal{K}$ parameter $\alpha = 2$:
  $\mathcal{L}_f B + 2 B = 2(x_0^2 + x_1^2) + 2(1 - x_0^2 - x_1^2) = 2 \cdot 1^2 \ge 0$! -/
@[expose] def goldenCbfSpec2D : SosCbfSpec where
  vectorField := [Poly.neg x0Poly, Poly.neg x1Poly]
  domainIneqs := []
  barrierB    := Poly.sub Poly.one (Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly))
  unsafePoly  := Poly.sub (Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly)) (polyConst 2)
  classKAlpha := 2

/-- SOS witness for `goldenCbfSpec2D`:
* Stengle refutation: $1 + 1 \cdot B(x) + 1 \cdot u_{\text{unsafe}}(x) = 0$,
* Nagumo invariance: $\mathcal{L}_f B + 2 B = 2 \cdot 1^2$. -/
@[expose] def goldenCbfWitness2D : SosCbfWitness where
  unsafeRefuteCert :=
    { monoidIndices := []
    , sigma0        := { terms := [] }
    , coneTerms     := [({ terms := [(1, Poly.one)] }, 0), ({ terms := [(1, Poly.one)] }, 1)]
    , idealTerms    := [] }
  nagumoInvarianceCert :=
    { monoidIndices := []
    , sigma0        := { terms := [(2, Poly.one)] }
    , coneTerms     := []
    , idealTerms    := [] }

/-- Globally non-singular Index-1 DAE manifold specification on the parabolic constraint manifold
$h_1(x_0, x_1) = x_0^2 + x_1 - 1 = 0$ ($x_1 = 1 - x_0^2$) with algebraic variable $x_1$ (`algVars := [1]`)
under tangent flow $\dot{x}_0 = -x_0, \dot{x}_1 = 2 x_0^2$:
* $\mathcal{L}_f h_1 = 2 x_0(-x_0) + 1 \cdot (2 x_0^2) = 0 \in \langle h_1 \rangle$,
* Exact symbolic algebraic Jacobian $\frac{\partial h_1}{\partial x_1} = 1 = \text{Poly.one}$,
  so $(\det J_{\text{alg}})^2 - \frac{1}{2} = \frac{1}{2} \cdot 1^2 \ge 0$ everywhere! -/
@[expose] def goldenCircleDaeSpec : DaeManifoldSpec where
  vectorField    := [Poly.neg x0Poly, Poly.scale 2 (Poly.sqr x0Poly)]
  domainIneqs    := []
  algConstraints := [Poly.sub (Poly.add (Poly.sqr x0Poly) x1Poly) Poly.one]
  algVars        := [1]
  algJacobianDet := Poly.one
  regDelta       := CanonicalRat.mk 1 2

/-- Witness for `goldenCircleDaeSpec`. -/
@[expose] def goldenCircleDaeWitness : DaeManifoldWitness where
  tangencyCert  := { quotients := [] }
  tangencyCerts := [{ quotients := [] }]
  regularityCert :=
    { monoidIndices := []
    , sigma0        := { terms := [(CanonicalRat.mk 1 2, Poly.one)] }
    , coneTerms     := []
    , idealTerms    := [] }

/-- Canonical problem bundle for `"sos-lyapunov-cbf@1"`. -/
@[expose] def goldenSosProblem : SosLyapunovProblem where
  lyapunov := goldenLyapunovSpec2D
  cbf      := goldenCbfSpec2D
  dae      := goldenCircleDaeSpec

/-- Canonical valid certificate bundle for `"sos-lyapunov-cbf@1"`. -/
@[expose] def goldenSosCert : SosLyapunovCert where
  lyapunovWitness := goldenLyapunovWitness2D
  cbfWitness      := goldenCbfWitness2D
  daeWitness      := goldenCircleDaeWitness

/-- Planted bad certificate bundle for `"sos-lyapunov-cbf@1"` (empty SOS witness for $V - \varepsilon\|x\|^2$). -/
@[expose] def badSosCert : SosLyapunovCert where
  lyapunovWitness :=
    { goldenLyapunovWitness2D with
      posDefCert := { monoidIndices := [], sigma0 := { terms := [] }, coneTerms := [], idealTerms := [] } }
  cbfWitness      := goldenCbfWitness2D
  daeWitness      := goldenCircleDaeWitness

-- fixture kept (2026-11-04): consumed by a proof in this file, Obend/Elab/AutoCert.lean
theorem sosLyapunov_bad_refused :
    checkSosLyapunovProblem 0 goldenSosProblem badSosCert = .refused .lyapunovFailed [] := by
  decide +kernel

/-! ## 8. General Kernel-Reducible JSON AST Encoders & Decoders (`SosJson`, Multivariate Polynomials, Gram Matrices, `SosLyapunovProblem`, and `SosLyapunovCert`) -/

/-- Structural JSON AST avoiding `module Lean`'s opaque `Std.TreeMap.Raw` and avoiding
intermediate `String.ofList` UTF-8 allocations during parsing so byte-level JSON wire proofs
reduce fast inside `decide +kernel`. -/
inductive SosJson where
  | null
  | bool (b : Bool)
  | num  (mantissa : Int) (exponent : Nat)
  | str  (cs : List Char)
  | arr  (elems : List SosJson)
  | obj  (fields : List (List Char × SosJson))

namespace SosJson

@[expose] def ofInt (n : Int) : SosJson := .num n 0
@[expose] def ofNat (n : Nat) : SosJson := .num (Int.ofNat n) 0
@[expose] def ofNatList (ns : List Nat) : SosJson := .arr (ns.map ofNat)
@[expose] def mkObj (kvs : List (String × SosJson)) : SosJson :=
  .obj (kvs.map fun (k, v) => (k.toList, v))

@[expose] def lookupField : List (List Char × SosJson) → List Char → Option SosJson
  | [], _ => none
  | (k0, v0) :: rest, k => if k0 == k then some v0 else lookupField rest k

@[expose] def getObjVal? (j : SosJson) (k : String) : Except String SosJson :=
  match j with
  | .obj fields =>
    match lookupField fields k.toList with
    | some v => .ok v
    | none   => .error s!"property not found: {k}"
  | _ => .error s!"object expected for key '{k}'"

@[expose] def getStr? : SosJson → Except String String
  | .str cs => .ok (String.ofList cs)
  | _       => .error "string expected"

@[expose] def getInt? : SosJson → Except String Int
  | .num m 0 => .ok m
  | _        => .error "integer expected"

@[expose] def getNat? : SosJson → Except String Nat
  | .num (.ofNat n) 0 => .ok n
  | _                 => .error "natural number expected"

@[expose] def getArr? : SosJson → Except String (List SosJson)
  | .arr xs => .ok xs
  | _       => .error "array expected"

@[expose] def getObjStr? (j : SosJson) (k : String) : Except String String :=
  j.getObjVal? k >>= getStr?

@[expose] def getObjInt? (j : SosJson) (k : String) : Except String Int :=
  j.getObjVal? k >>= getInt?

@[expose] def getObjNat? (j : SosJson) (k : String) : Except String Nat :=
  j.getObjVal? k >>= getNat?

@[expose] def getObjNatList? (j : SosJson) (k : String) : Except String (List Nat) := do
  let xs ← j.getObjVal? k >>= getArr?
  xs.mapM getNat?

end SosJson

@[expose] def sosJsonNatWrite : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d : Char :=
      match n % 10 with
      | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
      | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'
    let q := n / 10
    if q == 0 then d :: acc
    else sosJsonNatWrite fuel q (d :: acc)

@[expose] def sosJsonIntWrite : Int → List Char → List Char
  | .ofNat n, acc   => sosJsonNatWrite 24 n acc
  | .negSucc n, acc => '-' :: sosJsonNatWrite 24 (n + 1) acc

@[expose] def sosJsonEscapeWrite : List Char → List Char → List Char
  | [], acc => acc
  | '"' :: cs, acc  => '\\' :: '"' :: sosJsonEscapeWrite cs acc
  | '\\' :: cs, acc => '\\' :: '\\' :: sosJsonEscapeWrite cs acc
  | '\n' :: cs, acc => '\\' :: 'n' :: sosJsonEscapeWrite cs acc
  | '\r' :: cs, acc => '\\' :: 'r' :: sosJsonEscapeWrite cs acc
  | '\t' :: cs, acc => '\\' :: 't' :: sosJsonEscapeWrite cs acc
  | c :: cs, acc    => c :: sosJsonEscapeWrite cs acc

@[expose] def sosJsonQuoteCharsWrite (cs : List Char) (acc : List Char) : List Char :=
  '"' :: sosJsonEscapeWrite cs ('"' :: acc)

@[expose] def sosJsonWriteArrElems (writeVal : SosJson → List Char → List Char) :
    List SosJson → List Char → List Char
  | [], acc => acc
  | [x], acc => writeVal x acc
  | x :: xs, acc => writeVal x (',' :: sosJsonWriteArrElems writeVal xs acc)

@[expose] def sosJsonWriteObjFields (writeVal : SosJson → List Char → List Char) :
    List (List Char × SosJson) → List Char → List Char
  | [], acc => acc
  | [(k, v)], acc => sosJsonQuoteCharsWrite k (':' :: writeVal v acc)
  | (k, v) :: rest, acc =>
    sosJsonQuoteCharsWrite k (':' :: writeVal v (',' :: sosJsonWriteObjFields writeVal rest acc))

/-- Linear-time difference-list serializer for `SosJson` (zero `partial def`, zero intermediate `String` allocations). -/
@[expose] def sosJsonWriteAux : Nat → SosJson → List Char → List Char
  | 0, _, acc => 'n' :: 'u' :: 'l' :: 'l' :: acc
  | _ + 1, .null, acc => 'n' :: 'u' :: 'l' :: 'l' :: acc
  | _ + 1, .bool true, acc => 't' :: 'r' :: 'u' :: 'e' :: acc
  | _ + 1, .bool false, acc => 'f' :: 'a' :: 'l' :: 's' :: 'e' :: acc
  | _ + 1, .num m 0, acc => sosJsonIntWrite m acc
  | _ + 1, .num m e, acc => ((Lean.JsonNumber.mk m e).toString).toList ++ acc
  | _ + 1, .str cs, acc => sosJsonQuoteCharsWrite cs acc
  | fuel + 1, .arr elems, acc =>
    '[' :: sosJsonWriteArrElems (sosJsonWriteAux fuel) elems (']' :: acc)
  | fuel + 1, .obj fields, acc =>
    '{' :: sosJsonWriteObjFields (sosJsonWriteAux fuel) fields ('}' :: acc)

@[expose] def sosJsonCompress (j : SosJson) : String :=
  String.ofList (sosJsonWriteAux 24 j [])

@[expose] def sosJsonSkipWs : List Char → List Char
  | ' ' :: cs => sosJsonSkipWs cs
  | '\n' :: cs => sosJsonSkipWs cs
  | '\r' :: cs => sosJsonSkipWs cs
  | '\t' :: cs => sosJsonSkipWs cs
  | cs => cs

@[expose] def sosJsonParseStrBody : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '"' :: rest, rev => some (rev.reverse, rest)
  | '\\' :: '"' :: rest, rev => sosJsonParseStrBody rest ('"' :: rev)
  | '\\' :: '\\' :: rest, rev => sosJsonParseStrBody rest ('\\' :: rev)
  | '\\' :: '/' :: rest, rev => sosJsonParseStrBody rest ('/' :: rev)
  | '\\' :: 'n' :: rest, rev => sosJsonParseStrBody rest ('\n' :: rev)
  | '\\' :: 'r' :: rest, rev => sosJsonParseStrBody rest ('\r' :: rev)
  | '\\' :: 't' :: rest, rev => sosJsonParseStrBody rest ('\t' :: rev)
  | '\\' :: _, _ => none
  | c :: rest, rev => sosJsonParseStrBody rest (c :: rev)

@[expose] def sosJsonDigitVal? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _   => none

@[expose] def sosJsonParseDigits : List Char → Nat → Bool → Nat × Bool × List Char
  | [], acc, has => (acc, has, [])
  | c :: rest, acc, has =>
    match sosJsonDigitVal? c with
    | some d => sosJsonParseDigits rest (acc * 10 + d) true
    | none   => (acc, has, c :: rest)

@[expose] def sosJsonParseFracDigits : List Char → Nat → Nat → Nat × Nat × List Char
  | [], acc, exp => (acc, exp, [])
  | c :: rest, acc, exp =>
    match sosJsonDigitVal? c with
    | some d => sosJsonParseFracDigits rest (acc * 10 + d) (exp + 1)
    | none   => (acc, exp, c :: rest)

@[expose] def sosJsonParseNum (cs : List Char) : Option ((Int × Nat) × List Char) :=
  let (neg, cs1) :=
    match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (intPart, hasInt, cs2) := sosJsonParseDigits cs1 0 false
  if !hasInt then none
  else
    match cs2 with
    | '.' :: fracCs =>
      let (fracAcc, fracExp, cs3) := sosJsonParseFracDigits fracCs intPart 0
      if fracExp == 0 then none
      else
        let m : Int := if neg then -(Int.ofNat fracAcc) else Int.ofNat fracAcc
        some ((m, fracExp), cs3)
    | _ =>
      let m : Int := if neg then -(Int.ofNat intPart) else Int.ofNat intPart
      some ((m, 0), cs2)

@[expose] def sosJsonParseArrAux (parseElem : List Char → Option (SosJson × List Char)) :
    Nat → List Char → List SosJson → Option (List SosJson × List Char)
  | 0, _, _ => none
  | itemFuel + 1, cs, rev => do
    let (v, cs1) ← parseElem cs
    match sosJsonSkipWs cs1 with
    | ']' :: rest => some ((v :: rev).reverse, rest)
    | ',' :: rest => sosJsonParseArrAux parseElem itemFuel (sosJsonSkipWs rest) (v :: rev)
    | _ => none

@[expose] def sosJsonParseObjAux (parseElem : List Char → Option (SosJson × List Char)) :
    Nat → List Char → List (List Char × SosJson) → Option (List (List Char × SosJson) × List Char)
  | 0, _, _ => none
  | itemFuel + 1, cs, rev =>
    match sosJsonSkipWs cs with
    | '"' :: keyCs => do
      let (k, cs1) ← sosJsonParseStrBody keyCs []
      match sosJsonSkipWs cs1 with
      | ':' :: valCs => do
        let (v, cs2) ← parseElem (sosJsonSkipWs valCs)
        match sosJsonSkipWs cs2 with
        | '}' :: rest => some (((k, v) :: rev).reverse, rest)
        | ',' :: rest => sosJsonParseObjAux parseElem itemFuel rest ((k, v) :: rev)
        | _ => none
      | _ => none
    | _ => none

/-- Linear-time kernel-reducible recursive-descent JSON AST parser (zero `partial def`, zero `List.length` scans). -/
@[expose] def sosJsonParseAux : Nat → List Char → Option (SosJson × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match sosJsonSkipWs cs with
    | [] => none
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
    | '"' :: strCs => do
      let (s, rest) ← sosJsonParseStrBody strCs []
      some (.str s, rest)
    | '[' :: arrCs =>
      match sosJsonSkipWs arrCs with
      | ']' :: rest => some (.arr [], rest)
      | arrCs' => do
        let (items, rest) ← sosJsonParseArrAux (sosJsonParseAux fuel) 256 arrCs' []
        some (.arr items, rest)
    | '{' :: objCs =>
      match sosJsonSkipWs objCs with
      | '}' :: rest => some (.obj [], rest)
      | objCs' => do
        let (fields, rest) ← sosJsonParseObjAux (sosJsonParseAux fuel) 256 objCs' []
        some (.obj fields, rest)
    | numCs => do
      let ((m, e), rest) ← sosJsonParseNum numCs
      some (.num m e, rest)

@[expose] def sosJsonParse (s : String) : Except String SosJson :=
  match sosJsonParseAux 24 s.toList with
  | some (j, rest) =>
    if (sosJsonSkipWs rest).isEmpty then .ok j
    else .error "trailing characters in JSON"
  | none => .error "malformed JSON"

/-- Encode a `CanonicalRat` as an integer when `den = 1` or `{"num": n, "den": d}` otherwise. -/
@[expose] def sosJsonEncodeRat (q : CanonicalRat) : SosJson :=
  if q.den == 1 then .ofInt q.num
  else SosJson.mkObj [("num", .ofInt q.num), ("den", .ofNat q.den)]

/-- Decode a `CanonicalRat` from a JSON integer or `{"num": n, "den": d}` object. -/
@[expose] def decodeRatJson (j : SosJson) : Except String CanonicalRat :=
  match j.getInt? with
  | .ok n => .ok (CanonicalRat.mk n 1)
  | .error _ =>
    match j.getObjInt? "num", j.getObjNat? "den" with
    | .ok n, .ok d =>
      if d == 0 then .error "invalid rational JSON: zero denominator"
      else .ok (CanonicalRat.mk n d)
    | _, _ => .error "invalid rational JSON: expected integer or {num, den}"

/-- Structural polynomial exponentiation $p^k$. -/
@[expose] def sosPolyPow (p : Poly) : Nat → Poly
  | 0     => Poly.one
  | k + 1 => Poly.mul p (sosPolyPow p k)

/-- Encode a sparse `Monomial` as a JSON array of `[v, e]` variable-power pairs. -/
@[expose] def sosJsonEncodeMonomial (m : Monomial) : SosJson :=
  .arr <| m.map fun (v, e) => .arr [.ofNat v, .ofNat e]

/-- Decode a single `(var, exp)` factor from `[v, e]` or `{"var": v, "exp": e}`. -/
@[expose] def decodeMonomialFactorJson (j : SosJson) : Except String (Nat × Nat) :=
  match j.getArr? with
  | .ok [vJ, eJ] => do
    let v ← vJ.getNat?
    let e ← eJ.getNat?
    pure (v, e)
  | _ =>
    match j.getObjNat? "var", j.getObjNat? "exp" with
    | .ok v, .ok e => .ok (v, e)
    | _, _ => .error "invalid monomial factor JSON: expected [var, exp] or {var, exp}"

/-- Decode a sparse `Monomial` from a JSON array of variable-power factors. -/
@[expose] def decodeMonomialJson (j : SosJson) : Except String Monomial := do
  let arr ← j.getArr?
  arr.mapM decodeMonomialFactorJson

/-- Encode a multivariate polynomial `p : Poly` as a JSON array of `[monomial, coeff]` terms. -/
@[expose] def sosJsonEncodePoly (p : Poly) : SosJson :=
  .arr <| p.terms.map fun (m, c) =>
    .arr [sosJsonEncodeMonomial m, sosJsonEncodeRat c]

/-- Decode a single polynomial term from `[monomial, coeff]`, `{"monomial": [...], "coeff": c}`,
`{"vars": [...], "coeff": c}`, or univariate shorthand `{"var": v, "exp": e, "coeff": c}`. -/
@[expose] def decodePolyTermItemJson (item : SosJson) : Except String Poly :=
  match item.getArr? with
  | .ok [monJ, coeffJ] => do
    let mon ← decodeMonomialJson monJ
    let coeff ← decodeRatJson coeffJ
    pure (polyOfTerm mon coeff)
  | _ => do
    let coeffJ ← item.getObjVal? "coeff"
    let coeff ← decodeRatJson coeffJ
    match item.getObjVal? "monomial" with
    | .ok monJ =>
      let mon ← decodeMonomialJson monJ
      pure (polyOfTerm mon coeff)
    | .error _ =>
      match item.getObjVal? "vars" with
      | .ok varsJ =>
        let mon ← decodeMonomialJson varsJ
        pure (polyOfTerm mon coeff)
      | .error _ =>
        match item.getObjNat? "var", item.getObjNat? "exp" with
        | .ok v, .ok e => pure (polyOfTerm [(v, e)] coeff)
        | _, _ => .error "invalid polynomial term JSON: expected [monomial, coeff] or {monomial, coeff}"

/-- Decode a polynomial from a JSON list of monomial term objects. -/
@[expose] def decodePolyTermsJson (arr : List SosJson) : Except String Poly :=
  arr.foldlM (fun acc item => do
    let termPoly ← decodePolyTermItemJson item
    pure (Poly.add acc termPoly)
  ) Poly.zero

/-- Structural fuel-bounded JSON AST decoder for `Poly`. -/
@[expose] def decodePolyJsonAux : Nat → SosJson → Except String Poly
  | 0, _ => .error "invalid polynomial AST JSON: nesting depth exceeded"
  | fuel + 1, j =>
    match j.getInt? with
    | .ok n => .ok (polyConst (CanonicalRat.mk n 1))
    | .error _ =>
      match j.getArr? with
      | .ok arr => decodePolyTermsJson arr
      | .error _ => do
        let op ← j.getObjStr? "op"
        if op == "const" then
          let valJ ← j.getObjVal? "val"
          let q ← decodeRatJson valJ
          pure (polyConst q)
        else if op == "var" then
          let idx ← j.getObjNat? "index"
          pure (polyOfTerm [(idx, 1)] 1)
        else if op == "add" then
          let lJ ← j.getObjVal? "lhs"
          let rJ ← j.getObjVal? "rhs"
          let l ← decodePolyJsonAux fuel lJ
          let r ← decodePolyJsonAux fuel rJ
          pure (Poly.add l r)
        else if op == "sub" then
          let lJ ← j.getObjVal? "lhs"
          let rJ ← j.getObjVal? "rhs"
          let l ← decodePolyJsonAux fuel lJ
          let r ← decodePolyJsonAux fuel rJ
          pure (Poly.sub l r)
        else if op == "mul" then
          let lJ ← j.getObjVal? "lhs"
          let rJ ← j.getObjVal? "rhs"
          let l ← decodePolyJsonAux fuel lJ
          let r ← decodePolyJsonAux fuel rJ
          pure (Poly.mul l r)
        else if op == "neg" then
          let aJ ← j.getObjVal? "arg"
          let a ← decodePolyJsonAux fuel aJ
          pure (Poly.neg a)
        else if op == "sqr" then
          let aJ ← j.getObjVal? "arg"
          let a ← decodePolyJsonAux fuel aJ
          pure (Poly.sqr a)
        else if op == "pow" then
          let aJ ← j.getObjVal? "arg"
          let exp ← j.getObjNat? "exp"
          let a ← decodePolyJsonAux fuel aJ
          pure (sosPolyPow a exp)
        else if op == "scale" then
          let sJ ← j.getObjVal? "scalar"
          let aJ ← j.getObjVal? "arg"
          let s ← decodeRatJson sJ
          let a ← decodePolyJsonAux fuel aJ
          pure (Poly.scale s a)
        else
          .error s!"invalid polynomial AST JSON: unknown op '{op}'"

/-- Decode an arbitrary multivariate polynomial `Poly` from `SosJson`:
supports integer constants, sparse multivariate monomial arrays, and recursive polynomial AST
operators (`const`, `var`, `add`, `sub`, `mul`, `neg`, `sqr`, `pow`, `scale`). -/
@[expose] def decodePolyJson (j : SosJson) : Except String Poly :=
  decodePolyJsonAux 64 j

@[expose] def decodePolyListJson (j : SosJson) : Except String (List Poly) := do
  let arr ← j.getArr?
  arr.mapM decodePolyJson

/-- Convert a rational $L^\top D L$ Gram matrix factorization
$\sum_{i=0}^{r-1} d_i \left(\sum_{j=0}^{m-1} L_{i,j} b_j(x)\right)^2$ into an `SOSPoly`
(requiring positive diagonal weights $d_i > 0$ or dropping zero-weight rows while rejecting $d_i < 0$). -/
@[expose] def buildSOSPolyFromGram
    (diag : List CanonicalRat)
    (basis : List Poly)
    (factors : List (List CanonicalRat)) : Except String SOSPoly := do
  if diag.length != factors.length then
    .error "invalid SOS Gram JSON: gramDiag length must match gramFactors row count"
  else
    let buildRow (pair : CanonicalRat × List CanonicalRat) : Except String (Option (CanonicalRat × Poly)) := do
      let (d, row) := pair
      if row.length != basis.length then
        .error "invalid SOS Gram JSON: gramFactors row length must match gramBasis length"
      else if decide (d < 0) then
        .error "invalid SOS Gram JSON: negative diagonal entry in gramDiag"
      else if decide (d = 0) then
        pure none
      else
        let linComb := (row.zip basis).foldl
          (fun acc (coeff, bPoly) => Poly.add acc (Poly.scale coeff bPoly))
          Poly.zero
        pure (some (d, linComb))
    let optTerms ← (diag.zip factors).mapM buildRow
    pure { terms := optTerms.filterMap id }

@[expose] def sosJsonEncodeSOSPoly (s : SOSPoly) : SosJson :=
  .arr <| s.terms.map fun (w, p) =>
    .arr [sosJsonEncodeRat w, sosJsonEncodePoly p]

@[expose] def decodeSOSTermEntryJson (j : SosJson) : Except String (CanonicalRat × Poly) :=
  match j.getArr? with
  | .ok [wJ, pJ] => do
    let w ← decodeRatJson wJ
    let p ← decodePolyJson pJ
    pure (w, p)
  | _ => do
    let wJ ← j.getObjVal? "weight"
    let pJ ← j.getObjVal? "poly"
    let w ← decodeRatJson wJ
    let p ← decodePolyJson pJ
    pure (w, p)

/-- Decode an `SOSPoly` from either:
1. a JSON array `[[w, p], ...]` or `[{"weight": w, "poly": p}, ...]`,
2. an object `{"terms": [...]}`, or
3. a rational $L^\top D L$ Gram matrix object `{"gramDiag": [...], "gramBasis": [...], "gramFactors": [[...], ...]}`. -/
@[expose] def decodeSOSPolyJson (j : SosJson) : Except String SOSPoly :=
  match j.getArr? with
  | .ok arr => do
    let terms ← arr.mapM decodeSOSTermEntryJson
    pure { terms }
  | .error _ =>
    match j.getObjVal? "terms" with
    | .ok termsJ => do
      let arr ← termsJ.getArr?
      let terms ← arr.mapM decodeSOSTermEntryJson
      pure { terms }
    | .error _ => do
      let diagJ ← j.getObjVal? "gramDiag"
      let basisJ ← j.getObjVal? "gramBasis"
      let factorsJ ← j.getObjVal? "gramFactors"
      let diagArr ← diagJ.getArr?
      let diag ← diagArr.mapM decodeRatJson
      let basis ← decodePolyListJson basisJ
      let factorsArr ← factorsJ.getArr?
      let factors ← factorsArr.mapM fun rowJ => do
        let rArr ← rowJ.getArr?
        rArr.mapM decodeRatJson
      buildSOSPolyFromGram diag basis factors

@[expose] def sosJsonEncodePsatzCert (c : PositivstellensatzCert) : SosJson :=
  SosJson.mkObj
    [ ("monoidIndices", .ofNatList c.monoidIndices)
    , ("sigma0", sosJsonEncodeSOSPoly c.sigma0)
    , ("coneTerms", .arr <| c.coneTerms.map fun (s, idx) =>
        .arr [sosJsonEncodeSOSPoly s, .ofNat idx])
    , ("idealTerms", .arr <| c.idealTerms.map fun (p, idx) =>
        .arr [sosJsonEncodePoly p, .ofNat idx]) ]

@[expose] def decodePsatzCertJson (j : SosJson) : Except String PositivstellensatzCert := do
  let monoidIndices ← j.getObjNatList? "monoidIndices"
  let sig0J ← j.getObjVal? "sigma0"
  let sigma0 ← decodeSOSPolyJson sig0J
  let coneJ ← j.getObjVal? "coneTerms"
  let coneArr ← coneJ.getArr?
  let coneTerms ← coneArr.mapM fun item =>
    match item.getArr? with
    | .ok [sJ, idxJ] => do
      let s ← decodeSOSPolyJson sJ
      let idx ← idxJ.getNat?
      pure (s, idx)
    | _ => do
      let sJ ← item.getObjVal? "sos"
      let s ← decodeSOSPolyJson sJ
      let idx ← item.getObjNat? "index"
      pure (s, idx)
  let idealJ ← j.getObjVal? "idealTerms"
  let idealArr ← idealJ.getArr?
  let idealTerms ← idealArr.mapM fun item =>
    match item.getArr? with
    | .ok [pJ, idxJ] => do
      let p ← decodePolyJson pJ
      let idx ← idxJ.getNat?
      pure (p, idx)
    | _ => do
      let pJ ← item.getObjVal? "poly"
      let p ← decodePolyJson pJ
      let idx ← item.getObjNat? "index"
      pure (p, idx)
  pure { monoidIndices, sigma0, coneTerms, idealTerms }

@[expose] def sosJsonEncodeIdealCert (c : IdealMembershipCert) : SosJson :=
  SosJson.mkObj
    [ ("quotients", .arr <| c.quotients.map fun (q, idx) =>
        .arr [sosJsonEncodePoly q, .ofNat idx]) ]

@[expose] def decodeIdealCertJson (j : SosJson) : Except String IdealMembershipCert := do
  let qJ ← j.getObjVal? "quotients"
  let qArr ← qJ.getArr?
  let quotients ← qArr.mapM fun item =>
    match item.getArr? with
    | .ok [pJ, idxJ] => do
      let p ← decodePolyJson pJ
      let idx ← idxJ.getNat?
      pure (p, idx)
    | _ => do
      let pJ ← item.getObjVal? "poly"
      let p ← decodePolyJson pJ
      let idx ← item.getObjNat? "index"
      pure (p, idx)
  pure { quotients }

@[expose] def sosJsonEncodeLyapunovSpec (s : SosLyapunovSpec) : SosJson :=
  SosJson.mkObj
    [ ("dim", .ofNat s.dim)
    , ("vectorField", .arr <| s.vectorField.map sosJsonEncodePoly)
    , ("domainIneqs", .arr <| s.domainIneqs.map sosJsonEncodePoly)
    , ("lyapunovV", sosJsonEncodePoly s.lyapunovV)
    , ("radialEps", sosJsonEncodeRat s.radialEps)
    , ("decayGamma", sosJsonEncodeRat s.decayGamma) ]

@[expose] def decodeSosLyapunovSpecJson (j : SosJson) : Except String SosLyapunovSpec := do
  let dim ← j.getObjNat? "dim"
  let vfJ ← j.getObjVal? "vectorField"
  let vectorField ← decodePolyListJson vfJ
  let domJ ← j.getObjVal? "domainIneqs"
  let domainIneqs ← decodePolyListJson domJ
  let vJ ← j.getObjVal? "lyapunovV"
  let lyapunovV ← decodePolyJson vJ
  let epsJ ← j.getObjVal? "radialEps"
  let radialEps ← decodeRatJson epsJ
  let gamJ ← j.getObjVal? "decayGamma"
  let decayGamma ← decodeRatJson gamJ
  pure { dim, vectorField, domainIneqs, lyapunovV, radialEps, decayGamma }

@[expose] def sosJsonEncodeCbfSpec (s : SosCbfSpec) : SosJson :=
  SosJson.mkObj
    [ ("vectorField", .arr <| s.vectorField.map sosJsonEncodePoly)
    , ("domainIneqs", .arr <| s.domainIneqs.map sosJsonEncodePoly)
    , ("barrierB", sosJsonEncodePoly s.barrierB)
    , ("unsafePoly", sosJsonEncodePoly s.unsafePoly)
    , ("classKAlpha", sosJsonEncodeRat s.classKAlpha) ]

@[expose] def decodeSosCbfSpecJson (j : SosJson) : Except String SosCbfSpec := do
  let vfJ ← j.getObjVal? "vectorField"
  let vectorField ← decodePolyListJson vfJ
  let domJ ← j.getObjVal? "domainIneqs"
  let domainIneqs ← decodePolyListJson domJ
  let bJ ← j.getObjVal? "barrierB"
  let barrierB ← decodePolyJson bJ
  let uJ ← j.getObjVal? "unsafePoly"
  let unsafePoly ← decodePolyJson uJ
  let aJ ← j.getObjVal? "classKAlpha"
  let classKAlpha ← decodeRatJson aJ
  pure { vectorField, domainIneqs, barrierB, unsafePoly, classKAlpha }

@[expose] def sosJsonEncodeDaeSpec (s : DaeManifoldSpec) : SosJson :=
  SosJson.mkObj
    [ ("vectorField", .arr <| s.vectorField.map sosJsonEncodePoly)
    , ("domainIneqs", .arr <| s.domainIneqs.map sosJsonEncodePoly)
    , ("algConstraints", .arr <| s.algConstraints.map sosJsonEncodePoly)
    , ("algVars", .ofNatList s.algVars)
    , ("algJacobianDet", sosJsonEncodePoly s.algJacobianDet)
    , ("regDelta", sosJsonEncodeRat s.regDelta) ]

@[expose] def decodeDaeManifoldSpecJson (j : SosJson) : Except String DaeManifoldSpec := do
  let vfJ ← j.getObjVal? "vectorField"
  let vectorField ← decodePolyListJson vfJ
  let domJ ← j.getObjVal? "domainIneqs"
  let domainIneqs ← decodePolyListJson domJ
  let algCJ ← j.getObjVal? "algConstraints"
  let algConstraints ← decodePolyListJson algCJ
  let algVars ← j.getObjNatList? "algVars"
  let detJ ← j.getObjVal? "algJacobianDet"
  let algJacobianDet ← decodePolyJson detJ
  let delJ ← j.getObjVal? "regDelta"
  let regDelta ← decodeRatJson delJ
  pure { vectorField, domainIneqs, algConstraints, algVars, algJacobianDet, regDelta }

/-- Render an `SosLyapunovProblem` deterministically as a complete JSON AST string. -/
@[expose] def renderSosLyapunovProblemJson (p : SosLyapunovProblem) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("lyapunov", sosJsonEncodeLyapunovSpec p.lyapunov)
    , ("cbf", sosJsonEncodeCbfSpec p.cbf)
    , ("dae", sosJsonEncodeDaeSpec p.dae) ]

/-- General JSON AST decoder for `SosLyapunovProblem` parsing arbitrary multivariate polynomial
vector fields, domain inequalities, Lyapunov functions, CBF barriers, and Index-1 DAE manifolds. -/
@[expose] def decodeSosLyapunovProblem (s : String) : Except String SosLyapunovProblem :=
  match sosJsonParse s with
  | .error err => .error s!"invalid SosLyapunovProblem JSON: {err}"
  | .ok j =>
    match j.getObjVal? "lyapunov", j.getObjVal? "cbf", j.getObjVal? "dae" with
    | .ok lyapJ, .ok cbfJ, .ok daeJ => do
      let lyapunov ← decodeSosLyapunovSpecJson lyapJ
      let cbf ← decodeSosCbfSpecJson cbfJ
      let dae ← decodeDaeManifoldSpecJson daeJ
      pure { lyapunov, cbf, dae }
    | _, _, _ =>
      .error "invalid SosLyapunovProblem JSON: missing required fields"

@[expose] def sosJsonEncodeLyapunovWitness (w : SosLyapunovWitness) : SosJson :=
  SosJson.mkObj
    [ ("posDefCert", sosJsonEncodePsatzCert w.posDefCert)
    , ("lieDecayCert", sosJsonEncodePsatzCert w.lieDecayCert) ]

@[expose] def decodeSosLyapunovWitnessJson (j : SosJson) : Except String SosLyapunovWitness := do
  let posJ ← j.getObjVal? "posDefCert"
  let lieJ ← j.getObjVal? "lieDecayCert"
  let posDefCert ← decodePsatzCertJson posJ
  let lieDecayCert ← decodePsatzCertJson lieJ
  pure { posDefCert, lieDecayCert }

@[expose] def sosJsonEncodeCbfWitness (w : SosCbfWitness) : SosJson :=
  SosJson.mkObj
    [ ("unsafeRefuteCert", sosJsonEncodePsatzCert w.unsafeRefuteCert)
    , ("nagumoInvarianceCert", sosJsonEncodePsatzCert w.nagumoInvarianceCert) ]

@[expose] def decodeSosCbfWitnessJson (j : SosJson) : Except String SosCbfWitness := do
  let uJ ← j.getObjVal? "unsafeRefuteCert"
  let nJ ← j.getObjVal? "nagumoInvarianceCert"
  let unsafeRefuteCert ← decodePsatzCertJson uJ
  let nagumoInvarianceCert ← decodePsatzCertJson nJ
  pure { unsafeRefuteCert, nagumoInvarianceCert }

@[expose] def sosJsonEncodeDaeWitness (w : DaeManifoldWitness) : SosJson :=
  SosJson.mkObj
    [ ("tangencyCert", sosJsonEncodeIdealCert w.tangencyCert)
    , ("tangencyCerts", .arr <| w.tangencyCerts.map sosJsonEncodeIdealCert)
    , ("regularityCert", sosJsonEncodePsatzCert w.regularityCert) ]

@[expose] def decodeDaeManifoldWitnessJson (j : SosJson) : Except String DaeManifoldWitness := do
  let tcJ ← j.getObjVal? "tangencyCert"
  let tangencyCert ← decodeIdealCertJson tcJ
  let tcsJ ← j.getObjVal? "tangencyCerts"
  let tcsArr ← tcsJ.getArr?
  let tangencyCerts ← tcsArr.mapM decodeIdealCertJson
  let regJ ← j.getObjVal? "regularityCert"
  let regularityCert ← decodePsatzCertJson regJ
  pure { tangencyCert, tangencyCerts, regularityCert }

/-- Render an `SosLyapunovCert` deterministically as a complete JSON AST string. -/
@[expose] def renderSosLyapunovCertJson (c : SosLyapunovCert) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("lyapunovWitness", sosJsonEncodeLyapunovWitness c.lyapunovWitness)
    , ("cbfWitness", sosJsonEncodeCbfWitness c.cbfWitness)
    , ("daeWitness", sosJsonEncodeDaeWitness c.daeWitness) ]

/-- General JSON AST decoder for `SosLyapunovCert` parsing arbitrary SOS / Gram matrix
Positivstellensatz witnesses and Gröbner ideal membership certificates. -/
@[expose] def decodeSosLyapunovCert (s : String) : Except String SosLyapunovCert :=
  match sosJsonParse s with
  | .error err => .error s!"invalid SosLyapunovCert JSON: {err}"
  | .ok j =>
    match j.getObjVal? "lyapunovWitness", j.getObjVal? "cbfWitness", j.getObjVal? "daeWitness" with
    | .ok lyapWJ, .ok cbfWJ, .ok daeWJ => do
      let lyapunovWitness ← decodeSosLyapunovWitnessJson lyapWJ
      let cbfWitness ← decodeSosCbfWitnessJson cbfWJ
      let daeWitness ← decodeDaeManifoldWitnessJson daeWJ
      pure { lyapunovWitness, cbfWitness, daeWitness }
    | _, _, _ =>
      .error "invalid SosLyapunovCert JSON: missing required fields"

/-- Registered `Obend.Judge.Format` for `"sos-lyapunov-cbf@1"`. -/
@[expose] def sosLyapunovFormat : Format where
  name        := "sos-lyapunov-cbf"
  version     := "1"
  Obj         := SosLyapunovProblem
  Cert        := SosLyapunovCert
  decodeObj   := decodeSosLyapunovProblem
  decodeCert  := decodeSosLyapunovCert
  trust       := .kernel
  regime      := .decidable
  bad         := (goldenSosProblem, badSosCert)
  badGrade    := 0
  bad_refused := ⟨SosLyapunovClause.lyapunovFailed, [], sosLyapunov_bad_refused⟩

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (h ▸ rfl) else isFalse (fun heq => by injection heq; contradiction)
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (h ▸ rfl) else isFalse (fun heq => by injection heq; contradiction)
  | .error _, .ok _ => isFalse (fun heq => by injection heq)
  | .ok _, .error _ => isFalse (fun heq => by injection heq)

theorem decodeSosLyapunovProblem_refuses_empty_json :
    decodeSosLyapunovProblem "{}" =
      .error "invalid SosLyapunovProblem JSON: missing required fields" := by
  decide +kernel

/-- **Empty JSON Refusal Theorem (`sosLyapunovFormat_refuses_empty_json`)**:
    Verifies that `sosLyapunovFormat.checkBytes` rejects empty JSON `"{}"` payloads with `.refused (.malformed ...)`. -/
theorem sosLyapunovFormat_refuses_empty_json :
    sosLyapunovFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid SosLyapunovProblem JSON: missing required fields") [] := by
  unfold Judge.Format.checkBytes sosLyapunovFormat
  dsimp only
  rw [decodeSosLyapunovProblem_refuses_empty_json]
  rfl

/-- **Theorem (`sos_lyapunov_cbf_dae_showcase_sound`)**:
Verifies that the 2D cubic nonlinear Lyapunov certificate, 2D disk Control Barrier Function certificate,
Index-1 algebraic manifold DAE certificate, and unified `"sos-lyapunov-cbf@1"` judge all pass! -/
-- fixture kept (2026-11-04): consumed by Obend/Tactic/SiliconElab.lean
theorem sos_lyapunov_cbf_dae_showcase_sound :
    checkSosLyapunov goldenLyapunovSpec2D goldenLyapunovWitness2D = true ∧
    checkSosCbf goldenCbfSpec2D goldenCbfWitness2D = true ∧
    checkDaeManifold goldenCircleDaeSpec goldenCircleDaeWitness = true ∧
    checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok := by
  decide +kernel

end Obend.Analysis
end
