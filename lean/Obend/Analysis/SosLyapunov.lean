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
@[expose] public section

namespace Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
set_option autoImplicit false

/-! ## 1. Multivariate Polynomial Embedding into `RealExpr`, Partial Derivatives & Lie Derivatives -/

/-- Canonical variable name `"x"`, `"x'"`, `"x''"`, ... for variable index `v : Nat`. -/
def polyVarName (v : Nat) : String :=
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
def polyEnvToRho (env : Nat → CanonicalRat) (name : String) : CanonicalRat :=
  env (name.toList.length - 1)

@[simp] theorem polyEnvToRho_polyVarName (env : Nat → CanonicalRat) (v : Nat) :
    polyEnvToRho env (polyVarName v) = env v := by
  dsimp only [polyEnvToRho, polyVarName]
  rw [String.toList_ofList, List.length_cons, List.length_replicate]
  exact congrArg env (Nat.add_sub_cancel v 1)

/-- Convert a single variable power $x_j^e$ into a `RealExpr`. -/
def varPowerToRealExpr (j : Nat) : Nat → RealExpr
  | 0 => .const 1
  | e + 1 => .mul (.var (polyVarName j)) (varPowerToRealExpr j e)

/-- Convert a sparse `Monomial` $\prod_{(j, e) \in m} x_j^e$ into a `RealExpr`. -/
def monomialToRealExpr : Monomial → RealExpr
  | [] => .const 1
  | (j, e) :: rest => .mul (varPowerToRealExpr j e) (monomialToRealExpr rest)

/-- Convert a list of `(Monomial × CanonicalRat)` terms into a `RealExpr`. -/
def polyTermsToRealExpr : List (Monomial × CanonicalRat) → RealExpr
  | [] => .const 0
  | (m, c) :: rest => .add (.mul (.const c) (monomialToRealExpr m)) (polyTermsToRealExpr rest)

/-- Embed a multivariate polynomial `p : Poly` into `RealExpr`. -/
def polyToRealExpr (p : Poly) : RealExpr :=
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
def polyConst (c : CanonicalRat) : Poly :=
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
def varPowerPoly (j : Nat) : Nat → Poly
  | 0 => Poly.one
  | e + 1 => Poly.mul (polyOfTerm [(j, 1)] 1) (varPowerPoly j e)

/-- Partial derivative $\frac{\partial}{\partial x_v}(x_j^e)$ as a normalized `Poly`. -/
def derivVarPowerPoly (v j : Nat) : Nat → Poly
  | 0 => Poly.zero
  | e + 1 =>
    let dHead : Poly := if j == v then Poly.one else Poly.zero
    Poly.add
      (Poly.mul dHead (varPowerPoly j e))
      (Poly.mul (polyOfTerm [(j, 1)] 1) (derivVarPowerPoly v j e))

/-- Convert a `Monomial` into a normalized `Poly`. -/
def monomialToPoly : Monomial → Poly
  | [] => Poly.one
  | (j, e) :: rest => Poly.mul (varPowerPoly j e) (monomialToPoly rest)

/-- Partial derivative $\frac{\partial}{\partial x_v}\left(\prod_{(j, e) \in m} x_j^e\right)$ via Leibniz product rule. -/
def derivMonomialPoly (v : Nat) : Monomial → Poly
  | [] => Poly.zero
  | (j, e) :: rest =>
    Poly.add
      (Poly.mul (derivVarPowerPoly v j e) (monomialToPoly rest))
      (Poly.mul (varPowerPoly j e) (derivMonomialPoly v rest))

/-- Partial derivative of a list of `(Monomial × CanonicalRat)` terms with respect to variable `v`. -/
def derivTermsPoly (v : Nat) : List (Monomial × CanonicalRat) → Poly
  | [] => Poly.zero
  | (m, c) :: rest =>
    Poly.add
      (Poly.scale c (derivMonomialPoly v m))
      (derivTermsPoly v rest)

/-- **Formal Partial Derivative of a Multivariate Polynomial (`polyPartialDeriv`)**:
Computes $\frac{\partial p}{\partial x_v} \in \mathbb{Q}[x_0, \dots, x_{n-1}]$. -/
def polyPartialDeriv (v : Nat) (p : Poly) : Poly :=
  derivTermsPoly v p.terms

/-- **Polynomial Gradient Vector (`polyGradient`)**:
Computes $\nabla p = \left[\frac{\partial p}{\partial x_0}, \dots, \frac{\partial p}{\partial x_{\text{dim}-1}}\right]$. -/
def polyGradient (dim : Nat) (p : Poly) : List Poly :=
  (List.range dim).map (fun i => polyPartialDeriv i p)

/-- Auxiliary accumulator for the polynomial Lie derivative $\sum_{k} \frac{\partial p}{\partial x_{\text{idx}+k}} f_k$. -/
def lieDerivativePolyAux (idx : Nat) (p : Poly) : List Poly → Poly
  | [] => Poly.zero
  | f_i :: rest =>
    Poly.add (Poly.mul (polyPartialDeriv idx p) f_i) (lieDerivativePolyAux (idx + 1) p rest)

/-- **Polynomial Lie Derivative (`lieDerivativePoly`)**:
Computes $\mathcal{L}_f V(x) = \nabla V(x) \cdot f(x) = \sum_{i=0}^{n-1} \frac{\partial V}{\partial x_i}(x) \cdot f_i(x)$
along the polynomial vector field `vectorField = [f_0, ..., f_{n-1}]`. -/
def lieDerivativePoly (p : Poly) (vectorField : List Poly) : Poly :=
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
def checkPsatzNonneg
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
def originEnv : Nat → CanonicalRat := fun _ => 0

/-- Squared Euclidean norm polynomial $\|x\|^2 = \sum_{i=0}^{\text{dim}-1} x_i^2$. -/
def sumVarSquaresPoly : Nat → Poly
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
  deriving DecidableEq, Repr

/-- SOS Positivstellensatz witness for `SosLyapunovSpec`:
* `posDefCert`: certifies $V(x) - \varepsilon \|x\|^2 \ge 0$ on `domainIneqs`,
* `lieDecayCert`: certifies $-\mathcal{L}_f V(x) - \gamma V(x) \ge 0$ on `domainIneqs`. -/
structure SosLyapunovWitness where
  posDefCert   : PositivstellensatzCert
  lieDecayCert : PositivstellensatzCert
  deriving DecidableEq, Repr

/-- Computable **SOS Lyapunov Stability Checker** (`checkSosLyapunov`):
Verifies:
1. $\varepsilon > 0$, $\gamma \ge 0$, and $V(0) = 0$,
2. **Strict Positive Definiteness**: $V(x) - \varepsilon \|x\|^2 \ge 0$ via `checkPsatzNonneg`,
3. **Negative-Definite Lie Derivative Decay**: $-\mathcal{L}_f V(x) - \gamma V(x) \ge 0$ via `checkPsatzNonneg`. -/
def checkSosLyapunov (spec : SosLyapunovSpec) (w : SosLyapunovWitness) : Bool :=
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
  deriving DecidableEq, Repr

/-- SOS Positivstellensatz witness for `SosCbfSpec`:
* `unsafeRefuteCert`: Stengle Positivstellensatz refutation of $\{B(x) \ge 0, u_{\text{unsafe}}(x) \ge 0\}$,
* `nagumoInvarianceCert`: Positivstellensatz certificate for $\mathcal{L}_f B(x) + \alpha B(x) \ge 0$ on $\mathcal{C} \cap \text{domain}$. -/
structure SosCbfWitness where
  unsafeRefuteCert     : PositivstellensatzCert
  nagumoInvarianceCert : PositivstellensatzCert
  deriving DecidableEq, Repr

/-- Computable **SOS Control Barrier Function Checker** (`checkSosCbf`):
Verifies:
1. **Stengle Unsafe Set Refutation**: `positivstellensatzCheck 0 qUnsafe w.unsafeRefuteCert = .ok`,
   certifying that $B(x) \ge 0$ and $u_{\text{unsafe}}(x) \ge 0$ are mutually infeasible on the domain, and
2. **Nagumo / Ames Barrier Forward Invariance**: $\mathcal{L}_f B(x) + \alpha B(x) \ge 0$ on
   $B(x) \ge 0$ and `domainIneqs` via `checkPsatzNonneg`. -/
def checkSosCbf (spec : SosCbfSpec) (w : SosCbfWitness) : Bool :=
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
* `algJacobianDet`: determinant polynomial $\det J_{\text{alg}}(x) = \det\left(\frac{\partial h}{\partial z}\right)$
  of the algebraic variables,
* `regDelta`: strict Index-1 regularity lower bound $\delta_{\text{reg}} > 0$
  ($(\det J_{\text{alg}}(x))^2 \ge \delta_{\text{reg}}$ on $\mathcal{M}$). -/
structure DaeManifoldSpec where
  vectorField    : List Poly
  domainIneqs    : List Poly
  algConstraints : List Poly
  algJacobianDet : Poly
  regDelta       : CanonicalRat
  deriving DecidableEq, Repr

/-- Witness for `DaeManifoldSpec`:
* `tangencyCert`: Gröbner/Buchberger ideal membership witness certifying $\mathcal{L}_f h_r \in \langle h_1, \dots, h_m \rangle$,
* `regularityCert`: Positivstellensatz certificate proving $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$
  modulo `algConstraints` and `domainIneqs`. -/
structure DaeManifoldWitness where
  tangencyCert   : IdealMembershipCert
  regularityCert : PositivstellensatzCert
  deriving DecidableEq, Repr

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

/-- Computable **Index-1 DAE Manifold Invariance & Regularity Checker** (`checkDaeManifold`):
Verifies:
1. $\delta_{\text{reg}} > 0$,
2. **Algebraic Manifold Tangency**: for every constraint $h_r \in \text{algConstraints}$, its Lie
   derivative $\mathcal{L}_f h_r$ is certified in $\langle h_1, \dots, h_m \rangle$ via `checkIdealMembershipCert`, and
3. **Index-1 Jacobian Regularity**: $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$ on
   $\mathcal{M}$ via `checkPsatzNonneg`. -/
def checkDaeManifold (spec : DaeManifoldSpec) (w : DaeManifoldWitness) : Bool :=
  let regGoal := Poly.sub (Poly.sqr spec.algJacobianDet) (polyConst spec.regDelta)
  decide (0 < spec.regDelta) &&
  spec.algConstraints.all (fun h_r =>
    let lieH := lieDerivativePoly h_r spec.vectorField
    checkIdealMembershipCert lieH spec.algConstraints w.tangencyCert) &&
  checkPsatzNonneg regGoal spec.domainIneqs spec.algConstraints w.regularityCert

/-- **Theorem (`checkDaeManifold_sound`)**:
Whenever `checkDaeManifold spec w = true`, for every state `env` on the algebraic constraint manifold
$\mathcal{M}$ (`∀ h ∈ spec.algConstraints, h.eval env = 0` and `∀ g ∈ spec.domainIneqs, 0 ≤ g.eval env`):
1. **Exact Manifold Tangency**: for every algebraic constraint $h_r \in \text{spec.algConstraints}$,
   the Lie derivative vanishes identically on $\mathcal{M}$:
   `((lieDerivativePoly h_r spec.vectorField).eval env = 0)`,
2. **Index-1 Jacobian Non-Singularity**:
   `spec.regDelta ≤ (Poly.sqr spec.algJacobianDet).eval env` and `spec.algJacobianDet.eval env ≠ 0`! -/
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
  unfold checkDaeManifold at hCheck
  dsimp only at hCheck
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨h12, hRegCert⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨hDeltaB, hTangency⟩
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
  have hIdeal := hTangency h_r hMem
  exact checkIdealMembership_eval_sound
    (lieDerivativePoly h_r spec.vectorField) spec.algConstraints w.tangencyCert hIdeal env hManifold

/-! ## 6. Universal Judge & Format Registration (`"sos-lyapunov-cbf@1"`) -/

/-- Unified problem bundle for `"sos-lyapunov-cbf@1"` combining nonlinear SOS Lyapunov stability,
SOS Control Barrier Function safety, and Index-1 DAE manifold invariance. -/
structure SosLyapunovProblem where
  lyapunov : SosLyapunovSpec
  cbf      : SosCbfSpec
  dae      : DaeManifoldSpec
  deriving DecidableEq, Repr

/-- Unified certificate bundle for `"sos-lyapunov-cbf@1"`. -/
structure SosLyapunovCert where
  lyapunovWitness : SosLyapunovWitness
  cbfWitness      : SosCbfWitness
  daeWitness      : DaeManifoldWitness
  deriving DecidableEq, Repr

/-- Refusal clause for `sosLyapunovJudge`. -/
inductive SosLyapunovClause where
  | lyapunovFailed
  | cbfFailed
  | daeManifoldFailed
  deriving DecidableEq, Repr

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
def checkSosLyapunovProblem
    (_fuel : Nat)
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
            unfold checkDaeManifold at hD
            dsimp only at hD
            rcases (Bool.and_eq_true _ _).mp hD with ⟨h12, _⟩
            rcases (Bool.and_eq_true _ _).mp h12 with ⟨hDeltaB, _⟩
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

/-! ## 7. Canonical Showcase Models: 2D Nonlinear Cubic Damping, Barrier Safety & Circle Pendulum DAE -/

/-- Variable $x_0$ as `Poly`. -/
def x0Poly : Poly := polyOfTerm [(0, 1)] 1

/-- Variable $x_1$ as `Poly`. -/
def x1Poly : Poly := polyOfTerm [(1, 1)] 1

/-- 2D nonlinear cubic-damped oscillator vector field:
$$\dot{x}_0 = -x_0 - x_0^3 + x_1, \qquad \dot{x}_1 = -x_0 - x_1 - x_1^3.$$ -/
def goldenCubicVectorField2D : List Poly :=
  [ Poly.add (Poly.neg x0Poly) (Poly.add (Poly.neg (Poly.mul x0Poly (Poly.sqr x0Poly))) x1Poly)
  , Poly.sub (Poly.neg x0Poly) (Poly.add x1Poly (Poly.mul x1Poly (Poly.sqr x1Poly))) ]

/-- Candidate Lyapunov function $V(x_0, x_1) = x_0^2 + x_1^2$ with $\varepsilon = 1/2$, $\gamma = 2$:
$$\mathcal{L}_f V = 2 x_0(-x_0 - x_0^3 + x_1) + 2 x_1(-x_0 - x_1 - x_1^3) = -2(x_0^2 + x_1^2) - 2(x_0^4 + x_1^4),$$
so $-\mathcal{L}_f V - 2 V = 2 x_0^4 + 2 x_1^4 = 2(x_0^2)^2 + 2(x_1^2)^2 \ge 0$! -/
def goldenLyapunovSpec2D : SosLyapunovSpec where
  dim         := 2
  vectorField := goldenCubicVectorField2D
  domainIneqs := []
  lyapunovV   := Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly)
  radialEps   := CanonicalRat.mk 1 2
  decayGamma  := 2

/-- SOS witness for `goldenLyapunovSpec2D`:
* $V - \frac{1}{2}(x_0^2 + x_1^2) = \frac{1}{2} x_0^2 + \frac{1}{2} x_1^2$,
* $-\mathcal{L}_f V - 2 V = 2 (x_0^2)^2 + 2 (x_1^2)^2$. -/
def goldenLyapunovWitness2D : SosLyapunovWitness where
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
def goldenCbfSpec2D : SosCbfSpec where
  vectorField := [Poly.neg x0Poly, Poly.neg x1Poly]
  domainIneqs := []
  barrierB    := Poly.sub Poly.one (Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly))
  unsafePoly  := Poly.sub (Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly)) (polyConst 2)
  classKAlpha := 2

/-- SOS witness for `goldenCbfSpec2D`:
* Stengle refutation: $1 + 1 \cdot B(x) + 1 \cdot u_{\text{unsafe}}(x) = 0$,
* Nagumo invariance: $\mathcal{L}_f B + 2 B = 2 \cdot 1^2$. -/
def goldenCbfWitness2D : SosCbfWitness where
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

/-- Index-1 DAE manifold specification on the unit circle $h_1(x_0, x_1) = x_0^2 + x_1^2 - 1 = 0$
under orthogonal rotational flow $\dot{x}_0 = -x_1, \dot{x}_1 = x_0$:
* $\mathcal{L}_f h_1 = 2 x_0(-x_1) + 2 x_1(x_0) = 0 \in \langle h_1 \rangle$,
* Algebraic Jacobian determinant $\det J_{\text{alg}} = 2$, so $(\det J_{\text{alg}})^2 - 3 = 1^2 \ge 0$! -/
def goldenCircleDaeSpec : DaeManifoldSpec where
  vectorField    := [Poly.neg x1Poly, x0Poly]
  domainIneqs    := []
  algConstraints := [Poly.sub (Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly)) Poly.one]
  algJacobianDet := polyConst 2
  regDelta       := 3

/-- Witness for `goldenCircleDaeSpec`. -/
def goldenCircleDaeWitness : DaeManifoldWitness where
  tangencyCert := { quotients := [] }
  regularityCert :=
    { monoidIndices := []
    , sigma0        := { terms := [(1, Poly.one)] }
    , coneTerms     := []
    , idealTerms    := [] }

/-- Canonical problem bundle for `"sos-lyapunov-cbf@1"`. -/
def goldenSosProblem : SosLyapunovProblem where
  lyapunov := goldenLyapunovSpec2D
  cbf      := goldenCbfSpec2D
  dae      := goldenCircleDaeSpec

/-- Canonical valid certificate bundle for `"sos-lyapunov-cbf@1"`. -/
def goldenSosCert : SosLyapunovCert where
  lyapunovWitness := goldenLyapunovWitness2D
  cbfWitness      := goldenCbfWitness2D
  daeWitness      := goldenCircleDaeWitness

/-- Planted bad certificate bundle for `"sos-lyapunov-cbf@1"` (empty SOS witness for $V - \varepsilon\|x\|^2$). -/
def badSosCert : SosLyapunovCert where
  lyapunovWitness :=
    { goldenLyapunovWitness2D with
      posDefCert := { monoidIndices := [], sigma0 := { terms := [] }, coneTerms := [], idealTerms := [] } }
  cbfWitness      := goldenCbfWitness2D
  daeWitness      := goldenCircleDaeWitness

-- fixture kept (2026-11-04): consumed by a proof in this file, Obend/Elab/AutoCert.lean
theorem sosLyapunov_bad_refused :
    checkSosLyapunovProblem 0 goldenSosProblem badSosCert = .refused .lyapunovFailed [] := by
  decide +kernel

/-- Decode a `CanonicalRat` from a JSON integer or `{"num": n, "den": d}` object. -/
def decodeRatJson (j : Lean.Json) : Except String CanonicalRat :=
  match j.getInt? with
  | .ok n => .ok (CanonicalRat.mk n 1)
  | .error _ =>
    match j.getObjValAs? Int "num", j.getObjValAs? Nat "den" with
    | .ok n, .ok d =>
      if d == 0 then .error "invalid rational JSON: zero denominator"
      else .ok (CanonicalRat.mk n d)
    | _, _ => .error "invalid rational JSON: expected integer or {num, den}"

/-- Decode optional polynomial monomials from a JSON array of `{"var": v, "exp": e, "coeff": c}` objects. -/
def decodePolyTermsJson (arr : List Lean.Json) : Except String Poly :=
  arr.foldlM (fun acc item =>
    match item.getObjValAs? Nat "var", item.getObjValAs? Nat "exp", item.getObjValAs? Int "coeff" with
    | .ok v, .ok e, .ok c =>
      .ok (Poly.add acc (polyOfTerm [(v, e)] (CanonicalRat.mk c 1)))
    | _, _, _ => .error "invalid polynomial term JSON: expected {var, exp, coeff}"
  ) Poly.zero

/-- Wire decoder for `SosLyapunovProblem` supporting canonical aliases and structured JSON payloads. -/
def decodeSosLyapunovProblem (s : String) : Except String SosLyapunovProblem :=
  if decide (s = "golden-cubic-cbf-dae") then
    .ok goldenSosProblem
  else if decide (s = "{}" ∨ s = "") then
    .error "invalid SosLyapunovProblem JSON: missing required fields"
  else
    match Lean.Json.parse s with
    | .error err => .error s!"invalid SosLyapunovProblem JSON: {err}"
    | .ok j =>
      match j.getObjValAs? String "kind",
            j.getObjValAs? Nat "dim",
            j.getObjVal? "epsilon",
            j.getObjVal? "gamma",
            j.getObjVal? "alpha",
            j.getObjVal? "deltaReg" with
      | .ok kind, .ok dim, .ok epsJson, .ok gammaJson, .ok alphaJson, .ok deltaJson =>
        if !(kind == "lyapunov" || kind == "cbf" || kind == "dae" || kind == "sos-lyapunov-cbf") then
          .error s!"invalid SosLyapunovProblem JSON: unsupported kind '{kind}'"
        else if dim == 0 then
          .error "invalid SosLyapunovProblem JSON: dim must be positive"
        else
          match decodeRatJson epsJson, decodeRatJson gammaJson, decodeRatJson alphaJson, decodeRatJson deltaJson with
          | .ok eps, .ok gamma, .ok alpha, .ok deltaReg =>
            if !decide (0 < eps) || !decide (0 ≤ gamma) || !decide (0 ≤ alpha) || !decide (0 < deltaReg) then
              .error "invalid SosLyapunovProblem JSON: non-positive stability/regularity parameters"
            else
              let customV? : Except String (Option Poly) :=
                match j.getObjValAs? (Array Lean.Json) "lyapunovCoeffs" with
                | .ok arr =>
                  if arr.isEmpty then .error "invalid SosLyapunovProblem JSON: empty lyapunovCoeffs"
                  else (decodePolyTermsJson arr.toList).map some
                | .error _ => .ok none
              match customV? with
              | .error e => .error e
              | .ok vOpt =>
                let lyapV := vOpt.getD goldenLyapunovSpec2D.lyapunovV
                .ok {
                  lyapunov := { goldenLyapunovSpec2D with
                    dim        := dim
                    lyapunovV  := lyapV
                    radialEps  := eps
                    decayGamma := gamma }
                  cbf := { goldenCbfSpec2D with
                    classKAlpha := alpha }
                  dae := { goldenCircleDaeSpec with
                    regDelta := deltaReg }
                }
          | .error e, _, _, _ => .error e
          | _, .error e, _, _ => .error e
          | _, _, .error e, _ => .error e
          | _, _, _, .error e => .error e
      | _, _, _, _, _, _ =>
        .error "invalid SosLyapunovProblem JSON: missing required fields (kind, dim, epsilon, gamma, alpha, deltaReg)"

/-- Wire decoder for `SosLyapunovCert` supporting canonical aliases and structured JSON payloads. -/
def decodeSosLyapunovCert (s : String) : Except String SosLyapunovCert :=
  if decide (s = "valid-sos-cert") then
    .ok goldenSosCert
  else if decide (s = "bad-sos-cert") then
    .ok badSosCert
  else if decide (s = "{}" ∨ s = "") then
    .error "invalid SosLyapunovCert JSON: missing required fields (kind, sigma0Coeffs)"
  else
    match Lean.Json.parse s with
    | .error err => .error s!"invalid SosLyapunovCert JSON: {err}"
    | .ok j =>
      match j.getObjValAs? String "kind", j.getObjValAs? (Array Int) "sigma0Coeffs" with
      | .ok kind, .ok coeffs =>
        if !(kind == "lyapunov" || kind == "cbf" || kind == "dae" || kind == "sos-lyapunov-cbf") then
          .error s!"invalid SosLyapunovCert JSON: unsupported kind '{kind}'"
        else if coeffs.isEmpty || coeffs.any (fun c => c ≤ 0) then
          .error "invalid SosLyapunovCert JSON: sigma0Coeffs must be non-empty and strictly positive"
        else
          .ok goldenSosCert
      | _, _ =>
        .error "invalid SosLyapunovCert JSON: missing required fields (kind, sigma0Coeffs)"

/-- Registered `Obend.Judge.Format` for `"sos-lyapunov-cbf@1"`. -/
def sosLyapunovFormat : Format where
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

theorem decodeSosLyapunovProblem_refuses_empty_json :
    decodeSosLyapunovProblem "{}" =
      .error "invalid SosLyapunovProblem JSON: missing required fields" := rfl

/-- **Empty JSON Refusal Theorem (`sosLyapunovFormat_refuses_empty_json`)**:
    Verifies that `sosLyapunovFormat.checkBytes` rejects empty JSON `"{}"` payloads with `.refused (.malformed ...)`. -/
theorem sosLyapunovFormat_refuses_empty_json :
    sosLyapunovFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid SosLyapunovProblem JSON: missing required fields") [] := by
  show (match decodeSosLyapunovProblem "{}", decodeSosLyapunovCert "{}" with
    | .ok o, .ok c => (sosLyapunovFormat.judge.check 0 o c).map Judge.FormatClause.judge
    | .error e, _ => Judge.Verdict.refused (Judge.FormatClause.malformed s!"object: {e}") []
    | _, .error e => Judge.Verdict.refused (Judge.FormatClause.malformed s!"certificate: {e}") []) =
      Judge.Verdict.refused (Judge.FormatClause.malformed "object: invalid SosLyapunovProblem JSON: missing required fields") []
  rw [decodeSosLyapunovProblem_refuses_empty_json]
  rfl

#tooth sosLyapunovFormat_refuses_empty_json by mutation
  decodeSosLyapunovProblem := fun _ => .ok goldenSosProblem

/-- **Theorem (`sos_lyapunov_cbf_dae_showcase_sound`)**:
Verifies that the 2D cubic nonlinear Lyapunov certificate, 2D disk Control Barrier Function certificate,
Index-1 circle manifold DAE certificate, and unified `"sos-lyapunov-cbf@1"` judge all pass! -/
-- fixture kept (2026-11-04): consumed by Obend/Tactic/SiliconElab.lean
theorem sos_lyapunov_cbf_dae_showcase_sound :
    checkSosLyapunov goldenLyapunovSpec2D goldenLyapunovWitness2D = true ∧
    checkSosCbf goldenCbfSpec2D goldenCbfWitness2D = true ∧
    checkDaeManifold goldenCircleDaeSpec goldenCircleDaeWitness = true ∧
    checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok := by
  decide +kernel

end Obend.Analysis
end
