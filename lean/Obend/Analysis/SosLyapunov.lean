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
   - The judge's `Fragment` is `SosLyapunovProblemCertifiable` (scope conditions, quadratic-module
     memberships, a Stengle identity and ideal combinations, stated over the polynomial ring), and
     `sosLyapunovProblemCertifiable_iff_check_ok` proves it is exactly the set of problems the
     checker accepts a certificate for.
-/
public import Obend.Judge.Class
import all Obend.Judge.Class
public import Obend.Judge.RealAnalysis
import all Obend.Judge.RealAnalysis
public import Obend.Analysis.RealAnalysis
import all Obend.Analysis.RealAnalysis
public import Obend.Analysis.Groebner
import all Obend.Analysis.Groebner
public import Obend.Analysis.Diff
public section

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
@[expose] def varPowerPoly (j : Nat) : Nat → Poly
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

/-- `checkPsatzNonneg` accepts a non-zero goal: $x_0^2 = 1 \cdot x_0^2$ is its own SOS certificate. -/
theorem checkPsatzNonneg_inhabited :
    ∃ goal ineqs eqs cert, checkPsatzNonneg goal ineqs eqs cert = true ∧ 0 < goal.terms.length := by
  refine ⟨Poly.sqr (polyOfTerm [(0, 1)] 1), [], [],
    { monoidIndices := [], sigma0 := { terms := [(1, polyOfTerm [(0, 1)] 1)] },
      coneTerms := [], idealTerms := [] }, ?_⟩
  decide +kernel

/-- What an acceptance of `checkPsatzNonneg` consists of. -/
theorem checkPsatzNonneg_true_elim
    (goal : Poly) (ineqs eqs : List Poly) (cert : PositivstellensatzCert)
    (hCheck : checkPsatzNonneg goal ineqs eqs cert = true) :
    cert.sigma0.allCoeffsPos = true ∧
    ∃ conePoly idealPoly,
      expandConeSum ineqs cert.coneTerms = some conePoly ∧
      expandIdealCombination? eqs cert.idealTerms = some idealPoly ∧
      (Poly.sub goal (Poly.add cert.sigma0.expand (Poly.add conePoly idealPoly))).isZero = true := by
  unfold checkPsatzNonneg at hCheck
  by_cases hPos0 : cert.sigma0.allCoeffsPos = true
  · simp only [hPos0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCheck
    rcases Option.eq_none_or_eq_some (expandConeSum ineqs cert.coneTerms) with hCone | ⟨conePoly, hCone⟩
    · rw [hCone] at hCheck; contradiction
    · rw [hCone] at hCheck
      rcases Option.eq_none_or_eq_some (expandIdealCombination? eqs cert.idealTerms) with
        hIdeal | ⟨idealPoly, hIdeal⟩
      · rw [hIdeal] at hCheck; contradiction
      · rw [hIdeal] at hCheck
        dsimp only at hCheck
        exact ⟨hPos0, conePoly, idealPoly, hCone, hIdeal, hCheck⟩
  · simp [hPos0] at hCheck

/-- The converse of `checkPsatzNonneg_true_elim`. -/
theorem checkPsatzNonneg_true_intro
    (goal : Poly) (ineqs eqs : List Poly) (cert : PositivstellensatzCert) (conePoly idealPoly : Poly)
    (hPos0 : cert.sigma0.allCoeffsPos = true)
    (hCone : expandConeSum ineqs cert.coneTerms = some conePoly)
    (hIdeal : expandIdealCombination? eqs cert.idealTerms = some idealPoly)
    (hZero : (Poly.sub goal (Poly.add cert.sigma0.expand (Poly.add conePoly idealPoly))).isZero = true) :
    checkPsatzNonneg goal ineqs eqs cert = true := by
  unfold checkPsatzNonneg
  simp only [hPos0, hCone, hIdeal, hZero, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- **`goal` is in the quadratic module of `ineqs` modulo the ideal of `eqs`**: it equals, as a
polynomial, a positive-weight SOS term plus a cone sum over `ineqs` plus an ideal combination of
`eqs`. Stated over the relations of `Obend.Analysis.Groebner`; nothing is run. -/
def PsatzNonnegCertifiable (goal : Poly) (ineqs eqs : List Poly) : Prop :=
  ∃ (sigma0 : SOSPoly) (coneTerms : List (SOSPoly × Nat)) (idealTerms : List (Poly × Nat))
    (conePoly idealPoly : Poly),
    PosSosWeights sigma0 ∧
    ConeSumRel ineqs coneTerms conePoly ∧
    IdealCombRel eqs idealTerms idealPoly ∧
    (Poly.sub goal (Poly.add sigma0.expand (Poly.add conePoly idealPoly))).terms = []

theorem psatzNonnegCertifiable_iff (goal : Poly) (ineqs eqs : List Poly) :
    PsatzNonnegCertifiable goal ineqs eqs ↔ ∃ cert, checkPsatzNonneg goal ineqs eqs cert = true := by
  unfold PsatzNonnegCertifiable
  constructor
  · rintro ⟨sigma0, coneTerms, idealTerms, conePoly, idealPoly, hPos, hCone, hIdeal, hZero⟩
    exact ⟨⟨[], sigma0, coneTerms, idealTerms⟩,
      checkPsatzNonneg_true_intro goal ineqs eqs ⟨[], sigma0, coneTerms, idealTerms⟩ conePoly idealPoly
        ((posSosWeights_iff sigma0).mp hPos)
        ((coneSumRel_iff ineqs coneTerms conePoly).mp hCone)
        ((idealCombRel_iff eqs idealTerms idealPoly).mp hIdeal)
        ((polyTermsNil_iff_isZero _).mp hZero)⟩
  · rintro ⟨cert, hCheck⟩
    obtain ⟨hPos0, conePoly, idealPoly, hCone, hIdeal, hZero⟩ :=
      checkPsatzNonneg_true_elim goal ineqs eqs cert hCheck
    exact ⟨cert.sigma0, cert.coneTerms, cert.idealTerms, conePoly, idealPoly,
      (posSosWeights_iff cert.sigma0).mpr hPos0,
      (coneSumRel_iff ineqs cert.coneTerms conePoly).mpr hCone,
      (idealCombRel_iff eqs cert.idealTerms idealPoly).mpr hIdeal,
      (polyTermsNil_iff_isZero _).mpr hZero⟩

/-! ## 3. Sum-of-Squares (SOS) Nonlinear Lyapunov Stability (`checkSosLyapunov`, `checkSosLyapunov_sound`) -/

/-- Zero origin assignment `originEnv : Nat → CanonicalRat := fun _ => 0`. -/
def originEnv : Nat → CanonicalRat := fun _ => 0

/-- Check that every active variable factor `(v, e)` (`e ≠ 0`) in monomial `m` satisfies `v < dim`. -/
def monomialVarsBounded (dim : Nat) : Monomial → Bool
  | [] => true
  | (v, e) :: rest => (decide (e = 0) || decide (v < dim)) && monomialVarsBounded dim rest

/-- Check that every nonzero term in `p` only references state variables `v < dim`. -/
def polyTermsVarsBounded (dim : Nat) : List (Monomial × CanonicalRat) → Bool
  | [] => true
  | (m, c) :: rest => (decide (c = 0) || monomialVarsBounded dim m) && polyTermsVarsBounded dim rest

/-- Check that polynomial `p` only references state variables `0 ≤ v < dim`. -/
def polyVarsBounded (dim : Nat) (p : Poly) : Bool :=
  polyTermsVarsBounded dim p.terms

/-- Check pairwise distinctness of a `List Nat` (used for Index-1 algebraic variable lists). -/
def natListNodupB : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && natListNodupB xs

theorem monomialVarsBounded_iff (dim : Nat) (m : Monomial) :
    monomialVarsBounded dim m = true ↔ ∀ ve ∈ m, ve.2 = 0 ∨ ve.1 < dim := by
  induction m with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    constructor
    · intro hB ve hve
      dsimp only [monomialVarsBounded] at hB
      rcases (Bool.and_eq_true _ _).mp hB with ⟨hHead, hRest⟩
      rcases List.mem_cons.mp hve with hEq | hTl
      · rw [hEq]
        rcases (Bool.or_eq_true _ _).mp hHead with he0 | hvLt
        · exact Or.inl (of_decide_eq_true he0)
        · exact Or.inr (of_decide_eq_true hvLt)
      · exact ih.mp hRest ve hTl
    · intro hAll
      dsimp only [monomialVarsBounded]
      refine (Bool.and_eq_true _ _).mpr
        ⟨?_, ih.mpr (fun ve hve => hAll ve (List.mem_cons.mpr (Or.inr hve)))⟩
      rcases hAll (v, e) (List.mem_cons.mpr (Or.inl rfl)) with he0 | hvLt
      · exact (Bool.or_eq_true _ _).mpr (Or.inl (decide_eq_true he0))
      · exact (Bool.or_eq_true _ _).mpr (Or.inr (decide_eq_true hvLt))

theorem polyTermsVarsBounded_iff (dim : Nat) (terms : List (Monomial × CanonicalRat)) :
    polyTermsVarsBounded dim terms = true ↔
      ∀ mc ∈ terms, mc.2 = 0 ∨ ∀ ve ∈ mc.1, ve.2 = 0 ∨ ve.1 < dim := by
  induction terms with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    constructor
    · intro hB mc hmc
      dsimp only [polyTermsVarsBounded] at hB
      rcases (Bool.and_eq_true _ _).mp hB with ⟨hHead, hRest⟩
      rcases List.mem_cons.mp hmc with hEq | hTl
      · rw [hEq]
        rcases (Bool.or_eq_true _ _).mp hHead with hc0 | hmB
        · exact Or.inl (of_decide_eq_true hc0)
        · exact Or.inr ((monomialVarsBounded_iff dim m).mp hmB)
      · exact ih.mp hRest mc hTl
    · intro hAll
      dsimp only [polyTermsVarsBounded]
      refine (Bool.and_eq_true _ _).mpr
        ⟨?_, ih.mpr (fun mc hmc => hAll mc (List.mem_cons.mpr (Or.inr hmc)))⟩
      rcases hAll (m, c) (List.mem_cons.mpr (Or.inl rfl)) with hc0 | hmB
      · exact (Bool.or_eq_true _ _).mpr (Or.inl (decide_eq_true hc0))
      · exact (Bool.or_eq_true _ _).mpr (Or.inr ((monomialVarsBounded_iff dim m).mpr hmB))

/-- Every term of `p` with a non-zero coefficient mentions, with a non-zero exponent, only state
variables `v < dim`. -/
def PolyVarsBoundedProp (dim : Nat) (p : Poly) : Prop :=
  ∀ mc ∈ p.terms, mc.2 = 0 ∨ ∀ ve ∈ mc.1, ve.2 = 0 ∨ ve.1 < dim

theorem polyVarsBoundedProp_iff (dim : Nat) (p : Poly) :
    PolyVarsBoundedProp dim p ↔ polyVarsBounded dim p = true := by
  unfold PolyVarsBoundedProp polyVarsBounded
  exact (polyTermsVarsBounded_iff dim p.terms).symm

theorem natListNodupB_iff (xs : List Nat) : natListNodupB xs = true ↔ xs.Nodup := by
  induction xs with
  | nil => simp [natListNodupB]
  | cons x xs ih => simp [natListNodupB, ih]

theorem monomialVarsBounded_eval_congr
    (dim : Nat) (env₁ env₂ : Nat → CanonicalRat)
    (hAgree : ∀ v, v < dim → env₁ v = env₂ v) :
    ∀ (m : Monomial),
      monomialVarsBounded dim m = true →
      Monomial.eval env₁ m = Monomial.eval env₂ m
  | [], _ => rfl
  | (v, e) :: rest, hB => by
    dsimp only [monomialVarsBounded, Monomial.eval] at hB ⊢
    rcases (Bool.and_eq_true _ _).mp hB with ⟨hHead, hRest⟩
    rw [monomialVarsBounded_eval_congr dim env₁ env₂ hAgree rest hRest]
    rcases (Bool.or_eq_true _ _).mp hHead with he0 | hvLt
    · have he : e = 0 := of_decide_eq_true he0
      subst he
      rfl
    · have hv : v < dim := of_decide_eq_true hvLt
      rw [hAgree v hv]

theorem polyTermsVarsBounded_eval_congr
    (dim : Nat) (env₁ env₂ : Nat → CanonicalRat)
    (hAgree : ∀ v, v < dim → env₁ v = env₂ v) :
    ∀ (terms : List (Monomial × CanonicalRat)),
      polyTermsVarsBounded dim terms = true →
      evalTerms env₁ terms = evalTerms env₂ terms
  | [], _ => rfl
  | (m, c) :: rest, hB => by
    dsimp only [polyTermsVarsBounded, evalTerms] at hB ⊢
    rcases (Bool.and_eq_true _ _).mp hB with ⟨hHead, hRest⟩
    rw [polyTermsVarsBounded_eval_congr dim env₁ env₂ hAgree rest hRest]
    rcases (Bool.or_eq_true _ _).mp hHead with hc0 | hmB
    · have hc : c = 0 := of_decide_eq_true hc0
      subst hc
      grind
    · rw [monomialVarsBounded_eval_congr dim env₁ env₂ hAgree m hmB]

/-- **Theorem (`polyVarsBounded_eval_congr`)**:
Whenever `polyVarsBounded dim p = true`, evaluating `p` depends exclusively on state coordinates
`0 ≤ v < dim` (`(∀ v < dim, env₁ v = env₂ v) → p.eval env₁ = p.eval env₂`). -/
theorem polyVarsBounded_eval_congr
    (dim : Nat) (p : Poly) (env₁ env₂ : Nat → CanonicalRat)
    (hB : polyVarsBounded dim p = true)
    (hAgree : ∀ v, v < dim → env₁ v = env₂ v) :
    p.eval env₁ = p.eval env₂ :=
  polyTermsVarsBounded_eval_congr dim env₁ env₂ hAgree p.terms hB

/-- Helper lemma: `List.all` is `true` iff the predicate holds for all members of the list. -/
theorem sos_list_all_iff_forall {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.all p = true ↔ ∀ x, x ∈ xs → p x = true
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | x :: xs => by
    simp only [List.all_cons, Bool.and_eq_true, sos_list_all_iff_forall p xs, List.mem_cons]
    constructor
    · rintro ⟨hx, hxs⟩ y (rfl | hy)
      · exact hx
      · exact hxs y hy
    · intro h
      exact ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩

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

theorem rat_sq_pos_of_ne_zero {x : CanonicalRat} (hx : x ≠ 0) : 0 < x * x := by
  by_cases hPos : 0 < x
  · exact Rat.mul_pos hPos hPos
  · have hNegPos : 0 < -x := by grind
    have hProd := Rat.mul_pos hNegPos hNegPos
    grind

/-- Strictly positive squared Euclidean norm `0 < ‖x‖²` whenever any state coordinate
`v < dim` is non-zero (`env v ≠ 0`). -/
theorem sumVarSquaresPoly_eval_pos_of_coord_ne_zero
    (env : Nat → CanonicalRat) :
    ∀ (dim v : Nat), v < dim → env v ≠ 0 → 0 < (sumVarSquaresPoly dim).eval env
  | 0, _, hv, _ => nomatch hv
  | i + 1, v, hv, hNe => by
    dsimp only [sumVarSquaresPoly]
    rw [Poly.eval_add, Poly.eval_sqr, eval_polyOfTerm_var1]
    by_cases hvi : v = i
    · subst hvi
      have hNonneg := sumVarSquaresPoly_eval_nonneg env v
      have hSqPos := rat_sq_pos_of_ne_zero hNe
      grind
    · have hvLt : v < i := by omega
      have hIH := sumVarSquaresPoly_eval_pos_of_coord_ne_zero env i v hvLt hNe
      have hSqNonneg : 0 ≤ env i * env i := by
        by_cases hz : env i = 0
        · rw [hz]; grind
        · have hp := rat_sq_pos_of_ne_zero hz; grind
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

/-- Structural dimension and variable-index well-formedness check for `SosLyapunovSpec`. -/
def checkSosLyapunovDims (spec : SosLyapunovSpec) : Bool :=
  decide (0 < spec.dim) &&
  decide (spec.vectorField.length = spec.dim) &&
  polyVarsBounded spec.dim spec.lyapunovV &&
  spec.vectorField.all (polyVarsBounded spec.dim) &&
  spec.domainIneqs.all (polyVarsBounded spec.dim)

/-- Computable **SOS Lyapunov Stability Checker** (`checkSosLyapunov`):
Verifies:
0. **Dimension & Variable-Scope Well-Formedness**: `0 < spec.dim`, `spec.vectorField.length = spec.dim`,
   and all polynomials in `spec` reference only variables `0 ≤ v < spec.dim`,
1. $\varepsilon > 0$, $\gamma \ge 0$, and $V(0) = 0$,
2. **Strict Positive Definiteness**: $V(x) - \varepsilon \|x\|^2 \ge 0$ via `checkPsatzNonneg`,
3. **Negative-Definite Lie Derivative Decay**: $-\mathcal{L}_f V(x) - \gamma V(x) \ge 0$ via `checkPsatzNonneg`. -/
def checkSosLyapunov (spec : SosLyapunovSpec) (w : SosLyapunovWitness) : Bool :=
  let posDefGoal := Poly.sub spec.lyapunovV (Poly.scale spec.radialEps (sumVarSquaresPoly spec.dim))
  let lieV := lieDerivativePoly spec.lyapunovV spec.vectorField
  let lieDecayGoal := Poly.sub (Poly.neg lieV) (Poly.scale spec.decayGamma spec.lyapunovV)
  checkSosLyapunovDims spec &&
  decide (0 < spec.radialEps) &&
  decide (0 ≤ spec.decayGamma) &&
  decide (spec.lyapunovV.eval originEnv = 0) &&
  checkPsatzNonneg posDefGoal spec.domainIneqs [] w.posDefCert &&
  checkPsatzNonneg lieDecayGoal spec.domainIneqs [] w.lieDecayCert

/-- **Theorem (`checkSosLyapunov_sound`)**:
Whenever `checkSosLyapunov spec w = true`, the ODE $\dot{x} = f(x)$ has verified state dimension
`0 < spec.dim` with `spec.vectorField.length = spec.dim` and variable scope bounded by `spec.dim`,
and $V(x)$ is a certified Lyapunov function on $\{x \mid \forall g \in \text{spec.domainIneqs}, g(x) \ge 0\}$:
1. $0 < \text{spec.dim}$, $\text{spec.vectorField.length} = \text{spec.dim}$, $V(0) = 0$, $\varepsilon > 0$, $\gamma \ge 0$,
2. For every state `env` in the domain, $V(\text{env}) \ge \varepsilon \|x\|^2 \ge 0$, and
3. For every state `env` in the domain, $\mathcal{L}_f V(\text{env}) \le -\gamma V(\text{env}) \le 0$! -/
theorem checkSosLyapunov_sound
    (spec : SosLyapunovSpec)
    (w : SosLyapunovWitness)
    (env : Nat → CanonicalRat)
    (hCheck : checkSosLyapunov spec w = true)
    (hDom : ∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval env) :
    0 < spec.dim ∧
    spec.vectorField.length = spec.dim ∧
    polyVarsBounded spec.dim spec.lyapunovV = true ∧
    (∀ f, f ∈ spec.vectorField → polyVarsBounded spec.dim f = true) ∧
    0 < spec.radialEps ∧
    0 ≤ spec.decayGamma ∧
    spec.lyapunovV.eval originEnv = 0 ∧
    spec.radialEps * (sumVarSquaresPoly spec.dim).eval env ≤ spec.lyapunovV.eval env ∧
    0 ≤ spec.lyapunovV.eval env ∧
    (lieDerivativePoly spec.lyapunovV spec.vectorField).eval env ≤ -spec.decayGamma * spec.lyapunovV.eval env ∧
    (lieDerivativePoly spec.lyapunovV spec.vectorField).eval env ≤ 0 := by
  unfold checkSosLyapunov checkSosLyapunovDims at hCheck
  dsimp only at hCheck
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨h12345, hLieCert⟩
  rcases (Bool.and_eq_true _ _).mp h12345 with ⟨h1234, hPosCert⟩
  rcases (Bool.and_eq_true _ _).mp h1234 with ⟨h123, hOriginB⟩
  rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hGammaB⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨hDims, hEpsB⟩
  rcases (Bool.and_eq_true _ _).mp hDims with ⟨hD1234, _hDomVars⟩
  rcases (Bool.and_eq_true _ _).mp hD1234 with ⟨hD123, hVfVars⟩
  rcases (Bool.and_eq_true _ _).mp hD123 with ⟨hD12, hVVars⟩
  rcases (Bool.and_eq_true _ _).mp hD12 with ⟨hDimPosB, hVfLenB⟩
  have hDimPos : 0 < spec.dim := of_decide_eq_true hDimPosB
  have hVfLen : spec.vectorField.length = spec.dim := of_decide_eq_true hVfLenB
  rw [sos_list_all_iff_forall] at hVfVars
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
  refine ⟨hDimPos, hVfLen, hVVars, hVfVars, hEps, hGamma, hOrigin, by grind, hVNonneg, by grind, by grind⟩

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

/-- Structural dimension and variable-index well-formedness check for `SosCbfSpec`. -/
def checkSosCbfDims (spec : SosCbfSpec) : Bool :=
  let dim := spec.vectorField.length
  decide (0 < dim) &&
  polyVarsBounded dim spec.barrierB &&
  polyVarsBounded dim spec.unsafePoly &&
  spec.vectorField.all (polyVarsBounded dim) &&
  spec.domainIneqs.all (polyVarsBounded dim)

/-- Computable **SOS Control Barrier Function Checker** (`checkSosCbf`):
Verifies:
0. **Dimension & Variable-Scope Well-Formedness**: `0 < spec.vectorField.length` and all polynomials
   in `spec` reference only variables `< spec.vectorField.length`,
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
  checkSosCbfDims spec &&
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
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨h123, hNagumo⟩
  rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hRefuteB⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨_hDims, _hAlphaB⟩
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
  deriving DecidableEq, Repr

/-- Witness for `DaeManifoldSpec`:
* `tangencyCert`: primary Gröbner/Buchberger ideal membership witness certifying $\mathcal{L}_f h_r \in \langle h_1, \dots, h_m \rangle$,
* `tangencyCerts`: optional per-constraint ideal membership certificates $[c_1, \dots, c_m]$ for multi-constraint DAEs,
* `regularityCert`: Positivstellensatz certificate proving $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$
  modulo `algConstraints` and `domainIneqs`. -/
structure DaeManifoldWitness where
  tangencyCert   : IdealMembershipCert
  tangencyCerts  : List IdealMembershipCert := []
  regularityCert : PositivstellensatzCert
  deriving DecidableEq, Repr

/-- Remove the `k`-th element of a list (used for Laplace cofactor expansion). -/
def listEraseIdx' {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, k + 1 => x :: listEraseIdx' xs k

/-- Determinant of a square matrix of polynomials given as rows, by Laplace expansion along the
first row: $\det M = \sum_j (-1)^j M_{0,j} \det M^{(0,j)}$. Structural recursion on the row list;
a ragged or empty matrix has determinant `Poly.one` for `[]` (the empty product) and the expansion
is over whatever entries the first row has. -/
def polyMatrixDet : List (List Poly) → Poly
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
def symbolicAlgJacobian (algConstraints : List Poly) (algVars : List Nat) : List (List Poly) :=
  algConstraints.map (fun h => algVars.map (fun v => polyPartialDeriv v h))

/-- Compute the symbolic algebraic Jacobian determinant $\det\left(\frac{\partial h_i}{\partial x_{v_j}}\right)$
by Laplace expansion of `symbolicAlgJacobian` (`Poly.zero` when the system is not square). -/
def computeSymbolicAlgJacobianDet (algConstraints : List Poly) (algVars : List Nat) : Poly :=
  if algConstraints.length != algVars.length then
    Poly.zero
  else
    polyMatrixDet (symbolicAlgJacobian algConstraints algVars)

/-- Structural dimension and variable-index well-formedness check for `DaeManifoldSpec`. -/
def checkDaeManifoldDims (spec : DaeManifoldSpec) : Bool :=
  let dim := spec.vectorField.length
  decide (0 < dim) &&
  decide (spec.algConstraints.length = spec.algVars.length) &&
  natListNodupB spec.algVars &&
  spec.algVars.all (fun v => decide (v < dim)) &&
  polyVarsBounded dim spec.algJacobianDet &&
  spec.algConstraints.all (polyVarsBounded dim) &&
  spec.vectorField.all (polyVarsBounded dim) &&
  spec.domainIneqs.all (polyVarsBounded dim)

/-- Verify Index-1 DAE regularity (`checkDaeIndex1Regularity`):
1. `checkDaeManifoldDims spec`,
2. `spec.algJacobianDet` equals the symbolic Jacobian determinant
   `computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars`,
3. `0 < spec.regDelta`, and
4. $(\det J_{\text{alg}}(x))^2 - \delta_{\text{reg}} \ge 0$ on $\mathcal{M}$ via `checkPsatzNonneg`. -/
def checkDaeIndex1Regularity (spec : DaeManifoldSpec) (regCert : PositivstellensatzCert) : Bool :=
  let symDet := computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars
  let regGoal := Poly.sub (Poly.sqr spec.algJacobianDet) (polyConst spec.regDelta)
  checkDaeManifoldDims spec &&
  (Poly.sub spec.algJacobianDet symDet).isZero &&
  decide (0 < spec.regDelta) &&
  checkPsatzNonneg regGoal spec.domainIneqs spec.algConstraints regCert

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
def checkConstraintTangency (spec : DaeManifoldSpec) (w : DaeManifoldWitness) (h_r : Poly) : Bool :=
  let lieH := lieDerivativePoly h_r spec.vectorField
  checkIdealMembershipCert lieH spec.algConstraints w.tangencyCert ||
  w.tangencyCerts.any (fun c => checkIdealMembershipCert lieH spec.algConstraints c)

/-- Computable **Index-1 DAE Manifold Invariance & Regularity Checker** (`checkDaeManifold`):
Verifies:
1. **Dimension, Variable-Scope & Symbolic Index-1 Jacobian Regularity** (`checkDaeIndex1Regularity`), and
2. **Algebraic Manifold Tangency**: for every constraint $h_r \in \text{algConstraints}$, its Lie
   derivative $\mathcal{L}_f h_r$ is certified in $\langle h_1, \dots, h_m \rangle$ via `checkConstraintTangency`. -/
def checkDaeManifold (spec : DaeManifoldSpec) (w : DaeManifoldWitness) : Bool :=
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
  deriving DecidableEq, Repr

/-- Unified certificate bundle for `"sos-lyapunov-cbf@1"`. -/
structure SosLyapunovCert where
  lyapunovWitness : SosLyapunovWitness
  cbfWitness      : SosCbfWitness
  daeWitness      : DaeManifoldWitness
  deriving DecidableEq, Repr

/-- Refusal clause for `sosLyapunovJudge`, distinguishing structural/witness-carrying counterexamples
(which genuinely refute `SosLyapunovProblem.SemanticMeaning`) from certificate-only diagnostics. -/
inductive SosLyapunovClause where
  | malformedDimensionOrParam
  | lyapunovRadialNonpos (witness : List CanonicalRat)
  | lyapunovLieAscent (witness : List CanonicalRat)
  | cbfUnsafeOverlap (witness : List CanonicalRat)
  | cbfNagumoViolation (witness : List CanonicalRat)
  | daeManifoldViolation (witness : List CanonicalRat)
  | lyapunovFailed
  | cbfFailed
  | daeManifoldFailed
  deriving DecidableEq, Repr

/-- Structural well-formedness check across all three components of `SosLyapunovProblem`. -/
def checkSosProblemWellFormed (prob : SosLyapunovProblem) : Bool :=
  checkSosLyapunovDims prob.lyapunov &&
  decide (0 < prob.lyapunov.radialEps) &&
  decide (0 ≤ prob.lyapunov.decayGamma) &&
  decide (prob.lyapunov.lyapunovV.eval originEnv = 0) &&
  checkSosCbfDims prob.cbf &&
  decide (0 ≤ prob.cbf.classKAlpha) &&
  checkDaeManifoldDims prob.dae &&
  decide (0 < prob.dae.regDelta)

/-- Dimension and variable scope of a Lyapunov specification (stated over the polynomial ring). -/
def LyapunovSpecWellScoped (spec : SosLyapunovSpec) : Prop :=
  0 < spec.dim ∧
  spec.vectorField.length = spec.dim ∧
  PolyVarsBoundedProp spec.dim spec.lyapunovV ∧
  (∀ f ∈ spec.vectorField, PolyVarsBoundedProp spec.dim f) ∧
  (∀ g ∈ spec.domainIneqs, PolyVarsBoundedProp spec.dim g)

theorem lyapunovSpecWellScoped_iff (spec : SosLyapunovSpec) :
    LyapunovSpecWellScoped spec ↔ checkSosLyapunovDims spec = true := by
  unfold LyapunovSpecWellScoped checkSosLyapunovDims
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, polyVarsBoundedProp_iff,
    and_assoc]

/-- Dimension and variable scope of a barrier specification (stated over the polynomial ring). -/
def CbfSpecWellScoped (spec : SosCbfSpec) : Prop :=
  0 < spec.vectorField.length ∧
  PolyVarsBoundedProp spec.vectorField.length spec.barrierB ∧
  PolyVarsBoundedProp spec.vectorField.length spec.unsafePoly ∧
  (∀ f ∈ spec.vectorField, PolyVarsBoundedProp spec.vectorField.length f) ∧
  (∀ g ∈ spec.domainIneqs, PolyVarsBoundedProp spec.vectorField.length g)

theorem cbfSpecWellScoped_iff (spec : SosCbfSpec) :
    CbfSpecWellScoped spec ↔ checkSosCbfDims spec = true := by
  unfold CbfSpecWellScoped checkSosCbfDims
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, polyVarsBoundedProp_iff,
    and_assoc]

/-- Dimension, squareness, distinct algebraic variables and variable scope of a DAE manifold
specification (stated over the polynomial ring). -/
def DaeSpecWellScoped (spec : DaeManifoldSpec) : Prop :=
  0 < spec.vectorField.length ∧
  spec.algConstraints.length = spec.algVars.length ∧
  spec.algVars.Nodup ∧
  (∀ v ∈ spec.algVars, v < spec.vectorField.length) ∧
  PolyVarsBoundedProp spec.vectorField.length spec.algJacobianDet ∧
  (∀ h ∈ spec.algConstraints, PolyVarsBoundedProp spec.vectorField.length h) ∧
  (∀ f ∈ spec.vectorField, PolyVarsBoundedProp spec.vectorField.length f) ∧
  (∀ g ∈ spec.domainIneqs, PolyVarsBoundedProp spec.vectorField.length g)

theorem daeSpecWellScoped_iff (spec : DaeManifoldSpec) :
    DaeSpecWellScoped spec ↔ checkDaeManifoldDims spec = true := by
  unfold DaeSpecWellScoped checkDaeManifoldDims
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, polyVarsBoundedProp_iff,
    natListNodupB_iff, and_assoc]

/-- Independent semantic validity of a nonlinear polynomial Lyapunov specification `spec`:
well-scoped dimensions, `ε > 0`, `γ ≥ 0`, `V(0) = 0`, strict radial positive-definiteness
`ε ‖x‖² ≤ V(x)` (hence `V(x) > 0` for all `x ≠ 0` in the domain), and exponential Lie-derivative
decay `L_f V(x) ≤ -γ V(x) ≤ 0` across `{g_k(x) ≥ 0}`. -/
def ValidSosLyapunovSpec (spec : SosLyapunovSpec) : Prop :=
  LyapunovSpecWellScoped spec ∧
  0 < spec.dim ∧
  spec.vectorField.length = spec.dim ∧
  0 < spec.radialEps ∧
  0 ≤ spec.decayGamma ∧
  spec.lyapunovV.eval originEnv = 0 ∧
  ∀ env : Nat → CanonicalRat,
    (∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval env) →
    spec.radialEps * (sumVarSquaresPoly spec.dim).eval env ≤ spec.lyapunovV.eval env ∧
    0 ≤ spec.lyapunovV.eval env ∧
    (lieDerivativePoly spec.lyapunovV spec.vectorField).eval env ≤ -spec.decayGamma * spec.lyapunovV.eval env ∧
    (lieDerivativePoly spec.lyapunovV spec.vectorField).eval env ≤ 0

/-- Independent semantic meaning of `SosLyapunovProblem`. -/
def SosLyapunovProblem.SemanticMeaning (prob : SosLyapunovProblem) : Prop :=
  ValidSosLyapunovSpec prob.lyapunov ∧
  (CbfSpecWellScoped prob.cbf ∧
   0 ≤ prob.cbf.classKAlpha ∧
   ∀ env : Nat → CanonicalRat,
     (∀ g, g ∈ prob.cbf.domainIneqs → 0 ≤ g.eval env) →
     0 ≤ prob.cbf.barrierB.eval env →
     prob.cbf.unsafePoly.eval env < 0 ∧
     0 ≤ (lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField).eval env +
         prob.cbf.classKAlpha * prob.cbf.barrierB.eval env) ∧
  (DaeSpecWellScoped prob.dae ∧
   0 < prob.dae.regDelta ∧
   ∀ env : Nat → CanonicalRat,
     (∀ g, g ∈ prob.dae.domainIneqs → 0 ≤ g.eval env) →
     (∀ h, h ∈ prob.dae.algConstraints → h.eval env = 0) →
     (∀ h_r, h_r ∈ prob.dae.algConstraints →
       (lieDerivativePoly h_r prob.dae.vectorField).eval env = 0) ∧
     prob.dae.algJacobianDet.eval env =
       (computeSymbolicAlgJacobianDet prob.dae.algConstraints prob.dae.algVars).eval env ∧
     prob.dae.regDelta ≤ (Poly.sqr prob.dae.algJacobianDet).eval env ∧
     prob.dae.algJacobianDet.eval env ≠ 0)

/-- True iff `pt` has at least one non-zero state coordinate `0 ≤ v < dim` (`ρ ≠ 0`). -/
def pointHasNonZeroCoord (dim : Nat) (pt : List CanonicalRat) : Bool :=
  (List.range dim).any fun v => decide (ratPointEnv pt v ≠ 0)

/-- Non-origin radial positive-definiteness violation witness (`ρ ≠ 0`, `g_k(ρ) ≥ 0`, and either
`V(ρ) ≤ 0` or `V(ρ) < ε ‖ρ‖²`). -/
def evalLyapunovRadialNonpos (spec : SosLyapunovSpec) (pt : List CanonicalRat) : Bool :=
  let ρ := ratPointEnv pt
  pointHasNonZeroCoord spec.dim pt &&
  (spec.domainIneqs.all fun g => decide (0 ≤ g.eval ρ)) &&
  (decide (spec.lyapunovV.eval ρ ≤ 0) ||
   decide (spec.lyapunovV.eval ρ < spec.radialEps * (sumVarSquaresPoly spec.dim).eval ρ))

/-- Lie-derivative ascent or decay-rate violation witness (`g_k(ρ) ≥ 0` and
`L_f V(ρ) > 0` or `L_f V(ρ) > -γ V(ρ)`) with precomputed `lieV`. -/
def evalLyapunovLieAscentWithLie (spec : SosLyapunovSpec) (lieV : Poly) (pt : List CanonicalRat) : Bool :=
  let ρ := ratPointEnv pt
  (spec.domainIneqs.all fun g => decide (0 ≤ g.eval ρ)) &&
  (decide (0 < lieV.eval ρ) ||
   decide (-spec.decayGamma * spec.lyapunovV.eval ρ < lieV.eval ρ))

/-- Lie-derivative ascent or decay-rate violation witness (`g_k(ρ) ≥ 0`,
`L_f V(ρ) > 0` or `L_f V(ρ) > -γ V(ρ)`). -/
def evalLyapunovLieAscent (spec : SosLyapunovSpec) (pt : List CanonicalRat) : Bool :=
  evalLyapunovLieAscentWithLie spec (lieDerivativePoly spec.lyapunovV spec.vectorField) pt

/-- Control Barrier Function unsafe-set overlap witness (`B(ρ) ≥ 0 ∧ u_unsafe(ρ) ≥ 0` on `{g_k(ρ) ≥ 0}`). -/
def evalCbfUnsafeOverlap (spec : SosCbfSpec) (pt : List CanonicalRat) : Bool :=
  let ρ := ratPointEnv pt
  decide (0 ≤ spec.barrierB.eval ρ) &&
  decide (0 ≤ spec.unsafePoly.eval ρ) &&
  (spec.domainIneqs.all fun g => decide (0 ≤ g.eval ρ))

/-- Control Barrier Function Nagumo forward-invariance violation witness
(`B(ρ) ≥ 0 ∧ L_f B(ρ) + α B(ρ) < 0` on `{g_k(ρ) ≥ 0}`) with precomputed `lieB`. -/
def evalCbfNagumoViolationWithLie (spec : SosCbfSpec) (lieB : Poly) (pt : List CanonicalRat) : Bool :=
  let ρ := ratPointEnv pt
  decide (0 ≤ spec.barrierB.eval ρ) &&
  (spec.domainIneqs.all fun g => decide (0 ≤ g.eval ρ)) &&
  decide (lieB.eval ρ + spec.classKAlpha * spec.barrierB.eval ρ < 0)

/-- Control Barrier Function Nagumo forward-invariance violation witness
(`B(ρ) ≥ 0 ∧ L_f B(ρ) + α B(ρ) < 0` on `{g_k(ρ) ≥ 0}`). -/
def evalCbfNagumoViolation (spec : SosCbfSpec) (pt : List CanonicalRat) : Bool :=
  evalCbfNagumoViolationWithLie spec (lieDerivativePoly spec.barrierB spec.vectorField) pt

/-- Index-1 DAE manifold tangency, symbolic Jacobian mismatch, `regDelta` regularity shortfall,
or algebraic Jacobian singularity violation witness on `{h_r(ρ) = 0 ∧ g_k(ρ) ≥ 0}`. -/
def evalDaeManifoldViolation (spec : DaeManifoldSpec) (pt : List CanonicalRat) : Bool :=
  let ρ := ratPointEnv pt
  (spec.algConstraints.all fun h => decide (h.eval ρ = 0)) &&
  (spec.domainIneqs.all fun g => decide (0 ≤ g.eval ρ)) &&
  ((spec.algConstraints.any fun h_r => decide ((lieDerivativePoly h_r spec.vectorField).eval ρ ≠ 0)) ||
   decide (spec.algJacobianDet.eval ρ ≠
     (computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars).eval ρ) ||
   decide ((Poly.sqr spec.algJacobianDet).eval ρ < spec.regDelta) ||
   decide (spec.algJacobianDet.eval ρ = 0))

/-- Polynomials inspected to seed quadratic-vertex and linear-root rational candidates at grade `0`. -/
def sosLyapunovSeedPolys (prob : SosLyapunovProblem) (lieV lieB : Poly) : List Poly :=
  prob.lyapunov.lyapunovV :: lieV :: prob.cbf.barrierB :: lieB :: prob.cbf.unsafePoly ::
  prob.dae.algJacobianDet ::
  (prob.lyapunov.domainIneqs ++ prob.cbf.domainIneqs ++ prob.dae.algConstraints ++ prob.dae.domainIneqs)

/-- Complete polynomial list evaluated across `evalSosLyapunovCandidate` (used to bound active state variables). -/
def sosLyapunovAllPolys (prob : SosLyapunovProblem) : List Poly :=
  let lieV := lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField
  let lieB := lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField
  let symDet := computeSymbolicAlgJacobianDet prob.dae.algConstraints prob.dae.algVars
  let sumSq := sumVarSquaresPoly prob.lyapunov.dim
  let lieHs := prob.dae.algConstraints.map (fun h_r => lieDerivativePoly h_r prob.dae.vectorField)
  sumSq :: symDet :: (lieHs ++ sosLyapunovSeedPolys prob lieV lieB)

/-- State-space search dimension across all three components and derived polynomials of `prob`. -/
def sosLyapunovSearchDim (prob : SosLyapunovProblem) : Nat :=
  max (polyListVarBound (sosLyapunovAllPolys prob))
    (max prob.lyapunov.dim (max prob.cbf.vectorField.length prob.dae.vectorField.length))

def evalSosLyapunovCandidateWithLie
    (prob : SosLyapunovProblem) (lieV lieB : Poly) (pt : List CanonicalRat) :
    Option SosLyapunovClause :=
  if evalLyapunovRadialNonpos prob.lyapunov pt then
    some (.lyapunovRadialNonpos pt)
  else if evalLyapunovLieAscentWithLie prob.lyapunov lieV pt then
    some (.lyapunovLieAscent pt)
  else if evalCbfUnsafeOverlap prob.cbf pt then
    some (.cbfUnsafeOverlap pt)
  else if evalCbfNagumoViolationWithLie prob.cbf lieB pt then
    some (.cbfNagumoViolation pt)
  else if evalDaeManifoldViolation prob.dae pt then
    some (.daeManifoldViolation pt)
  else
    none

/-- Evaluate whether rational point `pt` is a concrete refuting counterexample to `prob`. -/
def evalSosLyapunovCandidate (prob : SosLyapunovProblem) (pt : List CanonicalRat) :
    Option SosLyapunovClause :=
  evalSosLyapunovCandidateWithLie prob
    (lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField)
    (lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField) pt

def findSosLyapunovRefutationAtShell (shell : Nat) (prob : SosLyapunovProblem) :
    Option SosLyapunovClause :=
  let dim := sosLyapunovSearchDim prob
  let lieV := lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField
  let lieB := lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField
  let cands :=
    if shell == 0 then
      let rawSeeds := polyListSeedPoints dim (sosLyapunovSeedPolys prob lieV lieB)
      rawSeeds.filter (pointHasNonZeroCoord dim) ++ [[]]
    else
      ratTuplesOfDim dim shell
  cands.findSome? (evalSosLyapunovCandidateWithLie prob lieV lieB)

/-- Grade-indexed multi-point rational counterexample search for `SosLyapunovProblem`.
Uses `Judge.deepen` so refutation verdicts remain monotonically stable across `r ≤ r'`. -/
def findSosLyapunovRefutation (grade : Nat) (prob : SosLyapunovProblem) :
    Option SosLyapunovClause :=
  Judge.deepen (fun g => findSosLyapunovRefutationAtShell g prob) grade

/-- Canonical empty refutation-probe certificate bundle triggering unbounded grade-indexed
rational counterexample search when algebraic checks do not accept. -/
def sosLyapunovSearchProbe : SosLyapunovCert where
  lyapunovWitness :=
    { posDefCert   := positivstellensatzSearchProbe
    , lieDecayCert := positivstellensatzSearchProbe }
  cbfWitness :=
    { unsafeRefuteCert     := positivstellensatzSearchProbe
    , nagumoInvarianceCert := positivstellensatzSearchProbe }
  daeWitness :=
    { tangencyCert   := ⟨[]⟩
    , tangencyCerts  := []
    , regularityCert := positivstellensatzSearchProbe }

def sosLyapunovIsSearchProbe (cert : SosLyapunovCert) : Bool :=
  decide (cert = sosLyapunovSearchProbe)

/-- Clauses that constructively refute `prob.SemanticMeaning` for ALL candidate certificates. -/
def sosLyapunovRefutes : SosLyapunovClause → Bool
  | .malformedDimensionOrParam => true
  | .lyapunovRadialNonpos _    => true
  | .lyapunovLieAscent _       => true
  | .cbfUnsafeOverlap _        => true
  | .cbfNagumoViolation _      => true
  | .daeManifoldViolation _    => true
  | .lyapunovFailed            => false
  | .cbfFailed                 => false
  | .daeManifoldFailed         => false

/-- Verdict checker for `sosLyapunovJudge`:
* Checks structural well-formedness first (`.malformedDimensionOrParam`),
* Accepts (`.ok`) iff all three algebraic component witnesses verify,
* On the canonical probe `sosLyapunovSearchProbe`, searches rational shells `0..grade` via `Judge.deepen`
  for non-origin Lyapunov / CBF / DAE counterexample witnesses (`judge_mono_probe_dichotomy`),
* On non-probe certificates, reports the failing component diagnostic. -/
def checkSosLyapunovProblem
    (grade : Nat)
    (prob : SosLyapunovProblem)
    (cert : SosLyapunovCert) : Judge.Verdict SosLyapunovClause :=
  if !checkSosProblemWellFormed prob then
    .refused .malformedDimensionOrParam []
  else if checkSosLyapunov prob.lyapunov cert.lyapunovWitness &&
          checkSosCbf prob.cbf cert.cbfWitness &&
          checkDaeManifold prob.dae cert.daeWitness then
    .ok
  else if sosLyapunovIsSearchProbe cert then
    match findSosLyapunovRefutation grade prob with
    | some clause => .refused clause []
    | none        => .uncovered
  else if !checkSosLyapunov prob.lyapunov cert.lyapunovWitness then
    .refused .lyapunovFailed []
  else if !checkSosCbf prob.cbf cert.cbfWitness then
    .refused .cbfFailed []
  else
    .refused .daeManifoldFailed []

/-- **Theorem (`checkSosLyapunovProblem_sound`)**:
Whenever `checkSosLyapunovProblem fuel prob cert = .ok`, `prob.SemanticMeaning` holds! -/
theorem checkSosLyapunovProblem_sound
    (fuel : Nat)
    (prob : SosLyapunovProblem)
    (cert : SosLyapunovCert)
    (hOk : checkSosLyapunovProblem fuel prob cert = .ok) :
    prob.SemanticMeaning := by
  unfold checkSosLyapunovProblem at hOk
  by_cases hWf : checkSosProblemWellFormed prob = true
  · simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    by_cases hAll : (checkSosLyapunov prob.lyapunov cert.lyapunovWitness &&
        checkSosCbf prob.cbf cert.cbfWitness &&
        checkDaeManifold prob.dae cert.daeWitness) = true
    · rcases (Bool.and_eq_true _ _).mp hAll with ⟨hLC, hD⟩
      rcases (Bool.and_eq_true _ _).mp hLC with ⟨hL, hC⟩
      unfold checkSosProblemWellFormed at hWf
      rcases (Bool.and_eq_true _ _).mp hWf with ⟨hWf1_7, hDeltaB⟩
      rcases (Bool.and_eq_true _ _).mp hWf1_7 with ⟨hWf1_6, hDaeDims⟩
      rcases (Bool.and_eq_true _ _).mp hWf1_6 with ⟨hWf1_5, hAlphaB⟩
      rcases (Bool.and_eq_true _ _).mp hWf1_5 with ⟨hWf1_4, hCbfDims⟩
      rcases (Bool.and_eq_true _ _).mp hWf1_4 with ⟨hWf1_3, hOriginB⟩
      rcases (Bool.and_eq_true _ _).mp hWf1_3 with ⟨hWf1_2, hGammaB⟩
      rcases (Bool.and_eq_true _ _).mp hWf1_2 with ⟨hLyapDims, hEpsB⟩
      have hLyapDimsCopy := hLyapDims
      unfold checkSosLyapunovDims at hLyapDimsCopy
      rcases (Bool.and_eq_true _ _).mp hLyapDimsCopy with ⟨hLD1_4, _⟩
      rcases (Bool.and_eq_true _ _).mp hLD1_4 with ⟨hLD1_3, _⟩
      rcases (Bool.and_eq_true _ _).mp hLD1_3 with ⟨hLD1_2, _⟩
      rcases (Bool.and_eq_true _ _).mp hLD1_2 with ⟨hDimPosB, hVfLenB⟩
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨(lyapunovSpecWellScoped_iff prob.lyapunov).mpr hLyapDims,
                of_decide_eq_true hDimPosB, of_decide_eq_true hVfLenB,
                of_decide_eq_true hEpsB, of_decide_eq_true hGammaB, of_decide_eq_true hOriginB, ?_⟩
        intro env hDom
        have hEnv := checkSosLyapunov_sound prob.lyapunov cert.lyapunovWitness env hL hDom
        exact ⟨hEnv.2.2.2.2.2.2.2.1, hEnv.2.2.2.2.2.2.2.2.1, hEnv.2.2.2.2.2.2.2.2.2.1, hEnv.2.2.2.2.2.2.2.2.2.2⟩
      · refine ⟨(cbfSpecWellScoped_iff prob.cbf).mpr hCbfDims, of_decide_eq_true hAlphaB, ?_⟩
        intro env hDom hSafe
        exact checkSosCbf_sound prob.cbf cert.cbfWitness env hC hDom hSafe
      · refine ⟨(daeSpecWellScoped_iff prob.dae).mpr hDaeDims, of_decide_eq_true hDeltaB, ?_⟩
        intro env hDom hMan
        have hEnv := checkDaeManifold_sound prob.dae cert.daeWitness env hD hDom hMan
        have hSym := checkDaeManifold_symbolic_jacobian_sound prob.dae cert.daeWitness env hD hDom hMan
        exact ⟨hEnv.2.1, hSym.1, hEnv.2.2.1, hEnv.2.2.2⟩
    · simp only [hAll, Bool.false_eq_true, ↓reduceIte] at hOk
      split at hOk
      · split at hOk <;> contradiction
      · split at hOk
        · contradiction
        · split at hOk <;> contradiction
  · simp [hWf] at hOk

theorem pointHasNonZeroCoord_iff (dim : Nat) (pt : List CanonicalRat) :
    pointHasNonZeroCoord dim pt = true ↔ ∃ v, v < dim ∧ ratPointEnv pt v ≠ 0 := by
  unfold pointHasNonZeroCoord
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v, hvMem, hvNe⟩
    exact ⟨v, List.mem_range.mp hvMem, of_decide_eq_true hvNe⟩
  · rintro ⟨v, hvLt, hvNe⟩
    exact ⟨v, List.mem_range.mpr hvLt, decide_eq_true hvNe⟩

/-- **Theorem (`lyapunovRadialNonpos_refutes_spec`)**:
Any non-zero rational witness `pt` (`ρ ≠ 0` on `0..dim-1`) in `{g_k(ρ) ≥ 0}` with `V(ρ) ≤ 0` or
`V(ρ) < ε ‖ρ‖²` strictly refutes `ValidSosLyapunovSpec spec`. -/
theorem lyapunovRadialNonpos_refutes_spec
    {spec : SosLyapunovSpec} {pt : List CanonicalRat}
    (hRad : evalLyapunovRadialNonpos spec pt = true) :
    ¬ ValidSosLyapunovSpec spec := by
  intro hValid
  unfold evalLyapunovRadialNonpos at hRad
  rcases (Bool.and_eq_true _ _).mp hRad with ⟨hNzDom, hViolB⟩
  rcases (Bool.and_eq_true _ _).mp hNzDom with ⟨hNz, hDomB⟩
  obtain ⟨v, hvLt, hvNe⟩ := (pointHasNonZeroCoord_iff spec.dim pt).mp hNz
  have hDom : ∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval (ratPointEnv pt) :=
    fun g hg => of_decide_eq_true (List.all_eq_true.mp hDomB g hg)
  obtain ⟨_, _, _, hEpsPos, _, _, hAll⟩ := hValid
  have hSpecPt := (hAll (ratPointEnv pt) hDom).1
  rcases (Bool.or_eq_true _ _).mp hViolB with hVLeB | hMarginLtB
  · have hVLe : spec.lyapunovV.eval (ratPointEnv pt) ≤ 0 := of_decide_eq_true hVLeB
    have hNormPos := sumVarSquaresPoly_eval_pos_of_coord_ne_zero (ratPointEnv pt) spec.dim v hvLt hvNe
    have hProdPos : 0 < spec.radialEps * (sumVarSquaresPoly spec.dim).eval (ratPointEnv pt) :=
      Rat.mul_pos hEpsPos hNormPos
    grind
  · have hMarginLt : spec.lyapunovV.eval (ratPointEnv pt) <
        spec.radialEps * (sumVarSquaresPoly spec.dim).eval (ratPointEnv pt) :=
      of_decide_eq_true hMarginLtB
    grind

/-- **Theorem (`lyapunovLieAscent_refutes_spec`)**:
Any rational witness `pt` in `{g_k(ρ) ≥ 0}` with `L_f V(ρ) > 0` or `L_f V(ρ) > -γ V(ρ)`
strictly refutes `ValidSosLyapunovSpec spec`. -/
theorem lyapunovLieAscent_refutes_spec
    {spec : SosLyapunovSpec} {pt : List CanonicalRat}
    (hAsc : evalLyapunovLieAscent spec pt = true) :
    ¬ ValidSosLyapunovSpec spec := by
  intro hValid
  unfold evalLyapunovLieAscent evalLyapunovLieAscentWithLie at hAsc
  rcases (Bool.and_eq_true _ _).mp hAsc with ⟨hDomB, hViolB⟩
  have hDom : ∀ g, g ∈ spec.domainIneqs → 0 ≤ g.eval (ratPointEnv pt) :=
    fun g hg => of_decide_eq_true (List.all_eq_true.mp hDomB g hg)
  obtain ⟨_, _, _, _, _, _, hAll⟩ := hValid
  have hSpecPt := hAll (ratPointEnv pt) hDom
  rcases (Bool.or_eq_true _ _).mp hViolB with hLiePosB | hDecayViolB
  · have hLiePos : 0 < (lieDerivativePoly spec.lyapunovV spec.vectorField).eval (ratPointEnv pt) :=
      of_decide_eq_true hLiePosB
    have hLieLe := hSpecPt.2.2.2
    grind
  · have hDecayViol : -spec.decayGamma * spec.lyapunovV.eval (ratPointEnv pt) <
        (lieDerivativePoly spec.lyapunovV spec.vectorField).eval (ratPointEnv pt) :=
      of_decide_eq_true hDecayViolB
    have hDecayLe := hSpecPt.2.2.1
    grind

/-- **Theorem (`cbfUnsafeOverlap_refutes_problem`)**:
Any rational witness `pt` in `{g_k(ρ) ≥ 0}` satisfying `B(ρ) ≥ 0 ∧ u_unsafe(ρ) ≥ 0`
strictly refutes `prob.SemanticMeaning`. -/
theorem cbfUnsafeOverlap_refutes_problem
    {prob : SosLyapunovProblem} {pt : List CanonicalRat}
    (hCbf : evalCbfUnsafeOverlap prob.cbf pt = true) :
    ¬ prob.SemanticMeaning := by
  intro hMean
  unfold evalCbfUnsafeOverlap at hCbf
  rcases (Bool.and_eq_true _ _).mp hCbf with ⟨hBU, hDomB⟩
  rcases (Bool.and_eq_true _ _).mp hBU with ⟨hSafeB, hUnsafeB⟩
  have hSafe : 0 ≤ prob.cbf.barrierB.eval (ratPointEnv pt) := of_decide_eq_true hSafeB
  have hUnsafe : 0 ≤ prob.cbf.unsafePoly.eval (ratPointEnv pt) := of_decide_eq_true hUnsafeB
  have hDom : ∀ g, g ∈ prob.cbf.domainIneqs → 0 ≤ g.eval (ratPointEnv pt) :=
    fun g hg => of_decide_eq_true (List.all_eq_true.mp hDomB g hg)
  have hSep := (hMean.2.1.2.2 (ratPointEnv pt) hDom hSafe).1
  grind

/-- **Theorem (`cbfNagumoViolation_refutes_problem`)**:
Any rational witness `pt` in `{g_k(ρ) ≥ 0}` satisfying `B(ρ) ≥ 0 ∧ L_f B(ρ) + α B(ρ) < 0`
strictly refutes `prob.SemanticMeaning`. -/
theorem cbfNagumoViolation_refutes_problem
    {prob : SosLyapunovProblem} {pt : List CanonicalRat}
    (hNag : evalCbfNagumoViolation prob.cbf pt = true) :
    ¬ prob.SemanticMeaning := by
  intro hMean
  unfold evalCbfNagumoViolation evalCbfNagumoViolationWithLie at hNag
  rcases (Bool.and_eq_true _ _).mp hNag with ⟨hSafeDom, hNegB⟩
  rcases (Bool.and_eq_true _ _).mp hSafeDom with ⟨hSafeB, hDomB⟩
  have hSafe : 0 ≤ prob.cbf.barrierB.eval (ratPointEnv pt) := of_decide_eq_true hSafeB
  have hDom : ∀ g, g ∈ prob.cbf.domainIneqs → 0 ≤ g.eval (ratPointEnv pt) :=
    fun g hg => of_decide_eq_true (List.all_eq_true.mp hDomB g hg)
  have hNeg : (lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField).eval (ratPointEnv pt) +
      prob.cbf.classKAlpha * prob.cbf.barrierB.eval (ratPointEnv pt) < 0 :=
    of_decide_eq_true hNegB
  have hNagSem := (hMean.2.1.2.2 (ratPointEnv pt) hDom hSafe).2
  grind

/-- **Theorem (`daeManifoldViolation_refutes_problem`)**:
Any rational witness `pt` on `{h_r(ρ) = 0 ∧ g_k(ρ) ≥ 0}` where `L_f h_r(ρ) ≠ 0`,
`det J_alg(ρ) ≠ symDet(ρ)`, `(det J_alg(ρ))^2 < regDelta`, or `det J_alg(ρ) = 0`
strictly refutes `prob.SemanticMeaning`. -/
theorem daeManifoldViolation_refutes_problem
    {prob : SosLyapunovProblem} {pt : List CanonicalRat}
    (hDae : evalDaeManifoldViolation prob.dae pt = true) :
    ¬ prob.SemanticMeaning := by
  intro hMean
  unfold evalDaeManifoldViolation at hDae
  rcases (Bool.and_eq_true _ _).mp hDae with ⟨hManDom, hViol⟩
  rcases (Bool.and_eq_true _ _).mp hManDom with ⟨hManB, hDomB⟩
  have hMan : ∀ h, h ∈ prob.dae.algConstraints → h.eval (ratPointEnv pt) = 0 :=
    fun h hh => of_decide_eq_true (List.all_eq_true.mp hManB h hh)
  have hDom : ∀ g, g ∈ prob.dae.domainIneqs → 0 ≤ g.eval (ratPointEnv pt) :=
    fun g hg => of_decide_eq_true (List.all_eq_true.mp hDomB g hg)
  have hDaeSem := hMean.2.2.2.2 (ratPointEnv pt) hDom hMan
  rcases (Bool.or_eq_true _ _).mp hViol with hLeft2 | hDetZeroB
  · rcases (Bool.or_eq_true _ _).mp hLeft2 with hLeft1 | hRegLtB
    · rcases (Bool.or_eq_true _ _).mp hLeft1 with hTangViol | hSymMismatchB
      · obtain ⟨h_r, hMem, hNeB⟩ := List.any_eq_true.mp hTangViol
        exact (of_decide_eq_true hNeB) (hDaeSem.1 h_r hMem)
      · exact (of_decide_eq_true hSymMismatchB) hDaeSem.2.1
    · have hRegLt := of_decide_eq_true hRegLtB
      have hRegGe := hDaeSem.2.2.1
      grind
  · exact hDaeSem.2.2.2 (of_decide_eq_true hDetZeroB)

theorem list_findSome?_some {α β : Type} (f : α → Option β) :
    ∀ {xs : List α} {b : β}, xs.findSome? f = some b → ∃ a, a ∈ xs ∧ f a = some b
  | [], _, h => nomatch h
  | x :: xs, b, h => by
    simp only [List.findSome?] at h
    cases hx : f x with
    | some b0 =>
      rw [hx] at h
      injection h with hEq
      subst hEq
      exact ⟨x, List.Mem.head xs, hx⟩
    | none =>
      rw [hx] at h
      obtain ⟨a, haMem, haEq⟩ := list_findSome?_some f h
      exact ⟨a, List.Mem.tail x haMem, haEq⟩

theorem list_findSome?_exists_of_mem {α β : Type} (f : α → Option β)
    (xs : List α) {x : α} {b : β} (hx : x ∈ xs) (hfx : f x = some b) :
    ∃ w, xs.findSome? f = some w := by
  induction xs with
  | nil => nomatch hx
  | cons hd tl ih =>
    simp only [List.findSome?]
    cases hhd : f hd with
    | some w => exact ⟨w, rfl⟩
    | none =>
      rcases List.mem_cons.mp hx with rfl | htl
      · rw [hfx] at hhd; cases hhd
      · exact ih htl

theorem evalSosLyapunovCandidate_refutes
    {prob : SosLyapunovProblem} {pt : List CanonicalRat} {k : SosLyapunovClause}
    (hCand : evalSosLyapunovCandidate prob pt = some k) :
    sosLyapunovRefutes k = true ∧ ¬ prob.SemanticMeaning := by
  unfold evalSosLyapunovCandidate evalSosLyapunovCandidateWithLie at hCand
  by_cases h1 : evalLyapunovRadialNonpos prob.lyapunov pt = true
  · rw [h1] at hCand
    simp only [↓reduceIte, Option.some.injEq] at hCand
    subst hCand
    exact ⟨by unfold sosLyapunovRefutes; rfl, fun hMean => lyapunovRadialNonpos_refutes_spec h1 hMean.1⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hCand
    by_cases h2 : evalLyapunovLieAscent prob.lyapunov pt = true
    · change evalLyapunovLieAscentWithLie prob.lyapunov
        (lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField) pt = true at h2
      rw [h2] at hCand
      simp only [↓reduceIte, Option.some.injEq] at hCand
      subst hCand
      exact ⟨by unfold sosLyapunovRefutes; rfl, fun hMean => lyapunovLieAscent_refutes_spec h2 hMean.1⟩
    · change ¬ evalLyapunovLieAscentWithLie prob.lyapunov
        (lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField) pt = true at h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte] at hCand
      by_cases h3 : evalCbfUnsafeOverlap prob.cbf pt = true
      · rw [h3] at hCand
        simp only [↓reduceIte, Option.some.injEq] at hCand
        subst hCand
        exact ⟨by unfold sosLyapunovRefutes; rfl, cbfUnsafeOverlap_refutes_problem h3⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hCand
        by_cases h3n : evalCbfNagumoViolation prob.cbf pt = true
        · change evalCbfNagumoViolationWithLie prob.cbf
            (lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField) pt = true at h3n
          rw [h3n] at hCand
          simp only [↓reduceIte, Option.some.injEq] at hCand
          subst hCand
          exact ⟨by unfold sosLyapunovRefutes; rfl, cbfNagumoViolation_refutes_problem h3n⟩
        · change ¬ evalCbfNagumoViolationWithLie prob.cbf
            (lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField) pt = true at h3n
          simp only [h3n, Bool.false_eq_true, ↓reduceIte] at hCand
          by_cases h4 : evalDaeManifoldViolation prob.dae pt = true
          · rw [h4] at hCand
            simp only [↓reduceIte, Option.some.injEq] at hCand
            subst hCand
            exact ⟨by unfold sosLyapunovRefutes; rfl, daeManifoldViolation_refutes_problem h4⟩
          · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hCand
            cases hCand

theorem findSosLyapunovRefutationAtShell_sound
    {shell : Nat} {prob : SosLyapunovProblem} {k : SosLyapunovClause}
    (hShell : findSosLyapunovRefutationAtShell shell prob = some k) :
    sosLyapunovRefutes k = true ∧ ¬ prob.SemanticMeaning := by
  unfold findSosLyapunovRefutationAtShell at hShell
  obtain ⟨pt, _, hCand⟩ := list_findSome?_some _ hShell
  exact evalSosLyapunovCandidate_refutes hCand

theorem findSosLyapunovRefutation_sound
    {grade : Nat} {prob : SosLyapunovProblem} {k : SosLyapunovClause}
    (hFind : findSosLyapunovRefutation grade prob = some k) :
    sosLyapunovRefutes k = true ∧ ¬ prob.SemanticMeaning := by
  obtain ⟨_, _, hi⟩ := Judge.deepen_some _ hFind
  exact findSosLyapunovRefutationAtShell_sound hi

theorem checkSosLyapunovProblem_refuted
    {r : Nat} {prob : SosLyapunovProblem} {cert : SosLyapunovCert}
    {k : SosLyapunovClause} {p : List Nat}
    (hRef : checkSosLyapunovProblem r prob cert = .refused k p)
    (hRefutes : sosLyapunovRefutes k = true) :
    ¬ prob.SemanticMeaning := by
  unfold checkSosLyapunovProblem at hRef
  by_cases hWf : checkSosProblemWellFormed prob = true
  · simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
    by_cases hAll : (checkSosLyapunov prob.lyapunov cert.lyapunovWitness &&
        checkSosCbf prob.cbf cert.cbfWitness &&
        checkDaeManifold prob.dae cert.daeWitness) = true
    · simp only [hAll, ↓reduceIte] at hRef
      cases hRef
    · simp only [hAll, Bool.false_eq_true, ↓reduceIte] at hRef
      split at hRef
      · cases hFind : findSosLyapunovRefutation r prob with
        | none => rw [hFind] at hRef; cases hRef
        | some k0 =>
          rw [hFind] at hRef
          injection hRef with hEq _
          subst hEq
          exact (findSosLyapunovRefutation_sound hFind).2
      · split at hRef
        · injection hRef with hEq _; subst hEq; cases hRefutes
        · split at hRef
          · injection hRef with hEq _; subst hEq; cases hRefutes
          · injection hRef with hEq _; subst hEq; cases hRefutes
  · intro hMean
    rcases hMean with ⟨⟨hLyapScoped, _hDimPos, _hVfLen, hEps, hGamma, hOrigin, _⟩,
                       ⟨hCbfScoped, hAlpha, _⟩,
                       ⟨hDaeScoped, hDelta, _⟩⟩
    have hLyapDims := (lyapunovSpecWellScoped_iff prob.lyapunov).mp hLyapScoped
    have hCbfDims := (cbfSpecWellScoped_iff prob.cbf).mp hCbfScoped
    have hDaeDims := (daeSpecWellScoped_iff prob.dae).mp hDaeScoped
    have hWfTrue : checkSosProblemWellFormed prob = true := by
      unfold checkSosProblemWellFormed
      simp [hLyapDims, hEps, hGamma, hOrigin, hCbfDims, hAlpha, hDaeDims, hDelta]
    exact hWf hWfTrue

theorem checkSosLyapunovProblem_mono
    {r r' : Nat} {prob : SosLyapunovProblem} {cert : SosLyapunovCert}
    (le : r ≤ r') (hne : checkSosLyapunovProblem r prob cert ≠ .uncovered) :
    checkSosLyapunovProblem r' prob cert = checkSosLyapunovProblem r prob cert := by
  unfold checkSosLyapunovProblem at hne ⊢
  split
  · rfl
  · split
    · rfl
    · split
      · rename_i hWf hAll hProbe
        simp only [hWf, hAll, Bool.false_eq_true, ↓reduceIte, hProbe] at hne
        cases hFind : findSosLyapunovRefutation r prob with
        | none =>
          rw [hFind] at hne
          exact False.elim (hne rfl)
        | some clause =>
          have hFind' : findSosLyapunovRefutation r' prob = some clause :=
            Judge.deepen_mono _ hFind le
          simp only [hFind']
      · split
        · rfl
        · split <;> rfl

/-! ### The certifiable fragment, stated over the polynomial ring

What it is for a problem to have a certificate, said without running a checker: scope conditions
as quantified statements over terms (`LyapunovSpecWellScoped`, `CbfSpecWellScoped`, `DaeSpecWellScoped`),
positivity claims as memberships in a quadratic module (`PsatzNonnegCertifiable`), the unsafe-set
separation as a Stengle identity (`StenglePositivstellensatzRefutable`), and manifold tangency as
an ideal combination (`IdealCombRel`). `sosLyapunovProblemCertifiable_iff_check_ok` proves this is
exactly the set of problems the checker accepts some certificate for. -/

/-- **A Lyapunov function with algebraic certificates**: well scoped, `ε > 0`, `γ ≥ 0`, `V(0) = 0`,
and both `V - ε‖x‖²` and `-L_f V - γ V` lie in the quadratic module of the domain. -/
def LyapunovAlgebraicallyCertifiable (spec : SosLyapunovSpec) : Prop :=
  LyapunovSpecWellScoped spec ∧
  0 < spec.radialEps ∧
  0 ≤ spec.decayGamma ∧
  spec.lyapunovV.eval originEnv = 0 ∧
  PsatzNonnegCertifiable
    (Poly.sub spec.lyapunovV (Poly.scale spec.radialEps (sumVarSquaresPoly spec.dim)))
    spec.domainIneqs [] ∧
  PsatzNonnegCertifiable
    (Poly.sub (Poly.neg (lieDerivativePoly spec.lyapunovV spec.vectorField))
      (Poly.scale spec.decayGamma spec.lyapunovV))
    spec.domainIneqs []

theorem lyapunovAlgebraicallyCertifiable_iff (spec : SosLyapunovSpec) :
    LyapunovAlgebraicallyCertifiable spec ↔ ∃ w, checkSosLyapunov spec w = true := by
  unfold LyapunovAlgebraicallyCertifiable
  constructor
  · rintro ⟨hDims, hEps, hGamma, hOrigin, hPos, hLie⟩
    obtain ⟨c1, hc1⟩ := (psatzNonnegCertifiable_iff _ _ _).mp hPos
    obtain ⟨c2, hc2⟩ := (psatzNonnegCertifiable_iff _ _ _).mp hLie
    refine ⟨⟨c1, c2⟩, ?_⟩
    unfold checkSosLyapunov
    dsimp only
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨(lyapunovSpecWellScoped_iff spec).mp hDims, hEps⟩, hGamma⟩, hOrigin⟩, hc1⟩, hc2⟩
  · rintro ⟨w, hCheck⟩
    unfold checkSosLyapunov at hCheck
    dsimp only at hCheck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hCheck
    obtain ⟨⟨⟨⟨⟨hDims, hEps⟩, hGamma⟩, hOrigin⟩, hc1⟩, hc2⟩ := hCheck
    exact ⟨(lyapunovSpecWellScoped_iff spec).mpr hDims, hEps, hGamma, hOrigin,
      (psatzNonnegCertifiable_iff _ _ _).mpr ⟨w.posDefCert, hc1⟩,
      (psatzNonnegCertifiable_iff _ _ _).mpr ⟨w.lieDecayCert, hc2⟩⟩

/-- **A barrier with algebraic certificates**: well scoped, `α ≥ 0`, a Stengle identity refuting
`B ≥ 0 ∧ u ≥ 0` on the domain, and `L_f B + α B` in the quadratic module of `B` and the domain. -/
def CbfAlgebraicallyCertifiable (spec : SosCbfSpec) : Prop :=
  CbfSpecWellScoped spec ∧
  0 ≤ spec.classKAlpha ∧
  StenglePositivstellensatzRefutable
    { strictPos := []
    , nonneg    := spec.barrierB :: spec.unsafePoly :: spec.domainIneqs
    , eqs       := [] } ∧
  PsatzNonnegCertifiable
    (Poly.add (lieDerivativePoly spec.barrierB spec.vectorField)
      (Poly.scale spec.classKAlpha spec.barrierB))
    (spec.barrierB :: spec.domainIneqs) []

theorem cbfAlgebraicallyCertifiable_iff (spec : SosCbfSpec) :
    CbfAlgebraicallyCertifiable spec ↔ ∃ w, checkSosCbf spec w = true := by
  unfold CbfAlgebraicallyCertifiable
  constructor
  · rintro ⟨hDims, hAlpha, hRef, hNag⟩
    obtain ⟨c1, r, hc1⟩ := (stenglePositivstellensatzRefutable_iff_check_ok _).mp hRef
    have hc1' := (positivstellensatzCheck_ok_grade_irrelevant r 0 _ c1).mp hc1
    obtain ⟨c2, hc2⟩ := (psatzNonnegCertifiable_iff _ _ _).mp hNag
    refine ⟨⟨c1, c2⟩, ?_⟩
    unfold checkSosCbf
    dsimp only
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨(cbfSpecWellScoped_iff spec).mp hDims, hAlpha⟩, hc1'⟩, hc2⟩
  · rintro ⟨w, hCheck⟩
    unfold checkSosCbf at hCheck
    dsimp only at hCheck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hCheck
    obtain ⟨⟨⟨hDims, hAlpha⟩, hc1⟩, hc2⟩ := hCheck
    exact ⟨(cbfSpecWellScoped_iff spec).mpr hDims, hAlpha,
      (stenglePositivstellensatzRefutable_iff_check_ok _).mpr ⟨w.unsafeRefuteCert, 0, hc1⟩,
      (psatzNonnegCertifiable_iff _ _ _).mpr ⟨w.nagumoInvarianceCert, hc2⟩⟩

/-- One witness per element, collected into a list (a finite choice, by induction on the list). -/
theorem list_exists_any_of_forall_exists {α β : Type} (p : α → β → Bool) (xs : List α)
    (h : ∀ x ∈ xs, ∃ c, p x c = true) :
    ∃ cs : List β, ∀ x ∈ xs, cs.any (p x) = true := by
  induction xs with
  | nil => exact ⟨[], fun _ hx => (nomatch hx)⟩
  | cons x xs ih =>
    obtain ⟨c, hc⟩ := h x (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨cs, hcs⟩ := ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))
    refine ⟨c :: cs, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with hEq | hTl
    · rw [hEq]
      simp only [List.any_cons, hc, Bool.true_or]
    · simp only [List.any_cons, hcs y hTl, Bool.or_true]

/-- **An index-1 DAE manifold with algebraic certificates**: well scoped, the stated Jacobian
determinant is the symbolic one, `δ > 0`, `det² - δ` lies in the quadratic module of the domain
modulo the constraint ideal, and every constraint's Lie derivative is an ideal combination of the
constraints. -/
def DaeAlgebraicallyCertifiable (spec : DaeManifoldSpec) : Prop :=
  DaeSpecWellScoped spec ∧
  (Poly.sub spec.algJacobianDet
    (computeSymbolicAlgJacobianDet spec.algConstraints spec.algVars)).terms = [] ∧
  0 < spec.regDelta ∧
  PsatzNonnegCertifiable
    (Poly.sub (Poly.sqr spec.algJacobianDet) (polyConst spec.regDelta))
    spec.domainIneqs spec.algConstraints ∧
  ∀ h_r ∈ spec.algConstraints, ∃ (quotients : List (Poly × Nat)) (comb : Poly),
    IdealCombRel spec.algConstraints quotients comb ∧
    (Poly.sub (lieDerivativePoly h_r spec.vectorField) comb).terms = []

theorem daeAlgebraicallyCertifiable_iff (spec : DaeManifoldSpec) :
    DaeAlgebraicallyCertifiable spec ↔ ∃ w, checkDaeManifold spec w = true := by
  unfold DaeAlgebraicallyCertifiable
  constructor
  · rintro ⟨hDims, hDet, hDelta, hReg, hTang⟩
    obtain ⟨cReg, hcReg⟩ := (psatzNonnegCertifiable_iff _ _ _).mp hReg
    obtain ⟨certs, hCerts⟩ := list_exists_any_of_forall_exists
      (fun (h_r : Poly) (c : IdealMembershipCert) =>
        checkIdealMembership (lieDerivativePoly h_r spec.vectorField) spec.algConstraints c)
      spec.algConstraints
      (fun h_r hMem => by
        obtain ⟨quotients, comb, hComb, hZero⟩ := hTang h_r hMem
        exact ⟨⟨quotients⟩,
          (checkIdealMembership_true_iff _ _ ⟨quotients⟩).mpr ⟨comb, hComb, hZero⟩⟩)
    refine ⟨{ tangencyCert := ⟨[]⟩, tangencyCerts := certs, regularityCert := cReg }, ?_⟩
    unfold checkDaeManifold checkDaeIndex1Regularity
    dsimp only
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ⟨⟨(daeSpecWellScoped_iff spec).mp hDims, (polyTermsNil_iff_isZero _).mp hDet⟩,
      hDelta⟩, hcReg⟩
    rw [sos_list_all_iff_forall]
    intro h_r hMem
    unfold checkConstraintTangency
    dsimp only
    exact (Bool.or_eq_true _ _).mpr (Or.inr (hCerts h_r hMem))
  · rintro ⟨w, hCheck⟩
    unfold checkDaeManifold checkDaeIndex1Regularity at hCheck
    dsimp only at hCheck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hCheck
    obtain ⟨hTang, ⟨⟨hDims, hDet⟩, hDelta⟩, hReg⟩ := hCheck
    rw [sos_list_all_iff_forall] at hTang
    refine ⟨(daeSpecWellScoped_iff spec).mpr hDims, (polyTermsNil_iff_isZero _).mpr hDet, hDelta,
      (psatzNonnegCertifiable_iff _ _ _).mpr ⟨w.regularityCert, hReg⟩, ?_⟩
    intro h_r hMem
    have hT := hTang h_r hMem
    unfold checkConstraintTangency at hT
    dsimp only at hT
    rcases (Bool.or_eq_true _ _).mp hT with hPrimary | hAny
    · obtain ⟨comb, hComb, hZero⟩ := (checkIdealMembership_true_iff _ _ _).mp hPrimary
      exact ⟨w.tangencyCert.quotients, comb, hComb, hZero⟩
    · rw [sos_list_any_iff_exists] at hAny
      obtain ⟨c, _, hc⟩ := hAny
      obtain ⟨comb, hComb, hZero⟩ := (checkIdealMembership_true_iff _ _ _).mp hc
      exact ⟨c.quotients, comb, hComb, hZero⟩

/-- **The problems `"sos-lyapunov-cbf@1"` is complete for**: each of the three components has its
algebraic certificates. -/
def SosLyapunovProblemCertifiable (prob : SosLyapunovProblem) : Prop :=
  LyapunovAlgebraicallyCertifiable prob.lyapunov ∧
  CbfAlgebraicallyCertifiable prob.cbf ∧
  DaeAlgebraicallyCertifiable prob.dae

/-- An acceptance of `checkSosLyapunovProblem` is the four component checks. -/
theorem checkSosLyapunovProblem_ok_iff (r : Nat) (prob : SosLyapunovProblem) (cert : SosLyapunovCert) :
    checkSosLyapunovProblem r prob cert = .ok ↔
      checkSosProblemWellFormed prob = true ∧
      checkSosLyapunov prob.lyapunov cert.lyapunovWitness = true ∧
      checkSosCbf prob.cbf cert.cbfWitness = true ∧
      checkDaeManifold prob.dae cert.daeWitness = true := by
  unfold checkSosLyapunovProblem
  constructor
  · intro hOk
    by_cases hWf : checkSosProblemWellFormed prob = true
    · simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      by_cases hAll : (checkSosLyapunov prob.lyapunov cert.lyapunovWitness &&
          checkSosCbf prob.cbf cert.cbfWitness &&
          checkDaeManifold prob.dae cert.daeWitness) = true
      · rcases (Bool.and_eq_true _ _).mp hAll with ⟨hLC, hD⟩
        rcases (Bool.and_eq_true _ _).mp hLC with ⟨hL, hC⟩
        exact ⟨hWf, hL, hC, hD⟩
      · simp only [hAll, Bool.false_eq_true, ↓reduceIte] at hOk
        split at hOk
        · split at hOk <;> contradiction
        · split at hOk
          · contradiction
          · split at hOk <;> contradiction
    · simp [hWf] at hOk
  · rintro ⟨hWf, hL, hC, hD⟩
    simp only [hWf, hL, hC, hD, Bool.not_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte]

/-- The three component checks already contain every clause of the well-formedness gate. -/
theorem checkSosProblemWellFormed_of_checks (prob : SosLyapunovProblem) (cert : SosLyapunovCert)
    (hL : checkSosLyapunov prob.lyapunov cert.lyapunovWitness = true)
    (hC : checkSosCbf prob.cbf cert.cbfWitness = true)
    (hD : checkDaeManifold prob.dae cert.daeWitness = true) :
    checkSosProblemWellFormed prob = true := by
  unfold checkSosLyapunov at hL
  unfold checkSosCbf at hC
  unfold checkDaeManifold checkDaeIndex1Regularity at hD
  dsimp only at hL hC hD
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hL hC hD
  obtain ⟨⟨⟨⟨⟨hLD, hEps⟩, hGamma⟩, hOrigin⟩, _⟩, _⟩ := hL
  obtain ⟨⟨⟨hCD, hAlpha⟩, _⟩, _⟩ := hC
  obtain ⟨_, ⟨⟨hDD, _⟩, hDelta⟩, _⟩ := hD
  unfold checkSosProblemWellFormed
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨hLD, hEps⟩, hGamma⟩, hOrigin⟩, hCD⟩, hAlpha⟩, hDD⟩, hDelta⟩

/-- **Theorem (`sosLyapunovProblemCertifiable_iff_check_ok`)**: the checker accepts some
certificate for `prob` exactly when `prob` is algebraically certifiable. -/
theorem sosLyapunovProblemCertifiable_iff_check_ok (prob : SosLyapunovProblem) :
    SosLyapunovProblemCertifiable prob ↔ ∃ cert r, checkSosLyapunovProblem r prob cert = .ok := by
  unfold SosLyapunovProblemCertifiable
  constructor
  · rintro ⟨hL, hC, hD⟩
    obtain ⟨wL, hwL⟩ := (lyapunovAlgebraicallyCertifiable_iff prob.lyapunov).mp hL
    obtain ⟨wC, hwC⟩ := (cbfAlgebraicallyCertifiable_iff prob.cbf).mp hC
    obtain ⟨wD, hwD⟩ := (daeAlgebraicallyCertifiable_iff prob.dae).mp hD
    exact ⟨⟨wL, wC, wD⟩, 0, (checkSosLyapunovProblem_ok_iff 0 prob ⟨wL, wC, wD⟩).mpr
      ⟨checkSosProblemWellFormed_of_checks prob ⟨wL, wC, wD⟩ hwL hwC hwD, hwL, hwC, hwD⟩⟩
  · rintro ⟨cert, r, hOk⟩
    obtain ⟨_, hL, hC, hD⟩ := (checkSosLyapunovProblem_ok_iff r prob cert).mp hOk
    exact ⟨(lyapunovAlgebraicallyCertifiable_iff prob.lyapunov).mpr ⟨cert.lyapunovWitness, hL⟩,
      (cbfAlgebraicallyCertifiable_iff prob.cbf).mpr ⟨cert.cbfWitness, hC⟩,
      (daeAlgebraicallyCertifiable_iff prob.dae).mpr ⟨cert.daeWitness, hD⟩⟩

/-- **Finite-Height Rational Counterexample Completeness (`sosLyapunov_rational_counterexample_complete`)**:
Whenever `prob` is well-formed and has a rational state counterexample `pt : List CanonicalRat`
(`pt.length = sosLyapunovSearchDim prob`, coordinate height `≤ B`, `1 ≤ B`) detected by
`evalSosLyapunovCandidate prob pt = some k0`, `checkSosLyapunovProblem B prob sosLyapunovSearchProbe`
discovers a concrete refuting witness `k` (`sosLyapunovRefutes k = true`) and refutes `prob.SemanticMeaning`. -/
theorem sosLyapunov_rational_counterexample_complete
    (prob : SosLyapunovProblem) (pt : List CanonicalRat) (k0 : SosLyapunovClause) (B : Nat)
    (hWf : checkSosProblemWellFormed prob = true)
    (hB1 : 1 ≤ B)
    (hLen : pt.length = sosLyapunovSearchDim prob)
    (hCoords : ∀ x ∈ pt, x.num.natAbs ≤ B ∧ x.den ≤ B)
    (hCand : evalSosLyapunovCandidate prob pt = some k0) :
    ∃ k, checkSosLyapunovProblem B prob sosLyapunovSearchProbe = .refused k [] ∧
         sosLyapunovRefutes k = true ∧
         ¬ prob.SemanticMeaning := by
  have hMem : pt ∈ ratTuplesOfDim (sosLyapunovSearchDim prob) B := by
    rw [← hLen]
    exact mem_ratTuplesOfDim B pt hCoords
  have hShell : ∃ w0, findSosLyapunovRefutationAtShell B prob = some w0 := by
    unfold findSosLyapunovRefutationAtShell
    have hNe0 : (B == 0) = false := beq_false_of_ne (by omega)
    rw [hNe0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact list_findSome?_exists_of_mem _ _ hMem hCand
  obtain ⟨w0, hw0⟩ := hShell
  obtain ⟨k, hkDeep⟩ := Judge.deepen_isSome (fun g => findSosLyapunovRefutationAtShell g prob) hw0
  change findSosLyapunovRefutation B prob = some k at hkDeep
  obtain ⟨hkRefutes, hNotMean⟩ := findSosLyapunovRefutation_sound hkDeep
  have hNotAll : (checkSosLyapunov prob.lyapunov sosLyapunovSearchProbe.lyapunovWitness &&
      checkSosCbf prob.cbf sosLyapunovSearchProbe.cbfWitness &&
      checkDaeManifold prob.dae sosLyapunovSearchProbe.daeWitness) = false := by
    cases hAll : (checkSosLyapunov prob.lyapunov sosLyapunovSearchProbe.lyapunovWitness &&
        checkSosCbf prob.cbf sosLyapunovSearchProbe.cbfWitness &&
        checkDaeManifold prob.dae sosLyapunovSearchProbe.daeWitness) with
    | false => rfl
    | true =>
      rcases (Bool.and_eq_true _ _).mp hAll with ⟨hLC, hD⟩
      rcases (Bool.and_eq_true _ _).mp hLC with ⟨hL, hC⟩
      have hOk : checkSosLyapunovProblem B prob sosLyapunovSearchProbe = .ok :=
        (checkSosLyapunovProblem_ok_iff B prob sosLyapunovSearchProbe).mpr ⟨hWf, hL, hC, hD⟩
      exact False.elim (hNotMean (checkSosLyapunovProblem_sound B prob sosLyapunovSearchProbe hOk))
  have hProbe : sosLyapunovIsSearchProbe sosLyapunovSearchProbe = true :=
    decide_eq_true rfl
  refine ⟨k, ?_, hkRefutes, hNotMean⟩
  unfold checkSosLyapunovProblem
  simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotAll, hProbe, hkDeep]

/-- **Semantic Rational State-Space Counterexample Completeness (`sosLyapunov_semantic_violation_complete`)**:
For **any** `prob : SosLyapunovProblem` and **any** rational state assignment `env : Nat → CanonicalRat`
(with no well-formedness or support restriction), if `env` exhibits any radial positive-definiteness
violation, Lie-derivative ascent/decay violation, CBF unsafe-set overlap, CBF Nagumo invariance
violation, or Index-1 DAE manifold violation, there exist a finite `grade` and refuting clause `k` at
which `checkSosLyapunovProblem grade prob sosLyapunovSearchProbe` refutes `prob.SemanticMeaning`. -/
theorem sosLyapunov_semantic_violation_complete
    (prob : SosLyapunovProblem) (env : Nat → CanonicalRat)
    (hViol :
      ((∃ v < prob.lyapunov.dim, env v ≠ 0) ∧
       (∀ g ∈ prob.lyapunov.domainIneqs, 0 ≤ g.eval env) ∧
       (prob.lyapunov.lyapunovV.eval env ≤ 0 ∨
        prob.lyapunov.lyapunovV.eval env < prob.lyapunov.radialEps * (sumVarSquaresPoly prob.lyapunov.dim).eval env)) ∨
      ((∀ g ∈ prob.lyapunov.domainIneqs, 0 ≤ g.eval env) ∧
       (0 < (lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField).eval env ∨
        -prob.lyapunov.decayGamma * prob.lyapunov.lyapunovV.eval env <
          (lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField).eval env)) ∨
      (0 ≤ prob.cbf.barrierB.eval env ∧ 0 ≤ prob.cbf.unsafePoly.eval env ∧
       ∀ g ∈ prob.cbf.domainIneqs, 0 ≤ g.eval env) ∨
      (0 ≤ prob.cbf.barrierB.eval env ∧
       (∀ g ∈ prob.cbf.domainIneqs, 0 ≤ g.eval env) ∧
       (lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField).eval env +
         prob.cbf.classKAlpha * prob.cbf.barrierB.eval env < 0) ∨
      ((∀ h ∈ prob.dae.algConstraints, h.eval env = 0) ∧
       (∀ g ∈ prob.dae.domainIneqs, 0 ≤ g.eval env) ∧
       ((∃ h_r ∈ prob.dae.algConstraints, (lieDerivativePoly h_r prob.dae.vectorField).eval env ≠ 0) ∨
        prob.dae.algJacobianDet.eval env ≠
          (computeSymbolicAlgJacobianDet prob.dae.algConstraints prob.dae.algVars).eval env ∨
        (Poly.sqr prob.dae.algJacobianDet).eval env < prob.dae.regDelta ∨
        prob.dae.algJacobianDet.eval env = 0))) :
    ∃ grade k,
      checkSosLyapunovProblem grade prob sosLyapunovSearchProbe = .refused k [] ∧
      sosLyapunovRefutes k = true ∧
      ¬ prob.SemanticMeaning := by
  cases hWf : checkSosProblemWellFormed prob with
  | false =>
    have hRef0 : checkSosLyapunovProblem 0 prob sosLyapunovSearchProbe = .refused .malformedDimensionOrParam [] := by
      unfold checkSosLyapunovProblem; simp [hWf]
    exact ⟨0, .malformedDimensionOrParam, hRef0, rfl, checkSosLyapunovProblem_refuted hRef0 rfl⟩
  | true =>
    let dim := sosLyapunovSearchDim prob
    let pt := (List.range dim).map env
    let B := ratTupleHeightBound pt
    have hAgree : ∀ v, v < dim → ratPointEnv pt v = env v :=
      fun v hv => ratPointEnv_map_range dim env hv
    have hAllEq : ∀ p ∈ sosLyapunovAllPolys prob, p.eval (ratPointEnv pt) = p.eval env := by
      intro p hp
      have hLe1 : polyVarBound p ≤ polyListVarBound (sosLyapunovAllPolys prob) :=
        polyVarBound_le_polyListVarBound hp
      have hLe2 : polyListVarBound (sosLyapunovAllPolys prob) ≤ dim := by
        unfold dim sosLyapunovSearchDim; omega
      exact polyVarBound_eval_congr (Nat.le_trans hLe1 hLe2) hAgree
    let lieV := lieDerivativePoly prob.lyapunov.lyapunovV prob.lyapunov.vectorField
    let lieB := lieDerivativePoly prob.cbf.barrierB prob.cbf.vectorField
    have hSeedEq : ∀ p ∈ sosLyapunovSeedPolys prob lieV lieB, p.eval (ratPointEnv pt) = p.eval env :=
      fun p hp => hAllEq p (List.Mem.tail _ (List.Mem.tail _ (List.mem_append_right _ hp)))
    have hVEq : prob.lyapunov.lyapunovV.eval (ratPointEnv pt) = prob.lyapunov.lyapunovV.eval env :=
      hSeedEq _ (List.Mem.head _)
    have hLieVEq : lieV.eval (ratPointEnv pt) = lieV.eval env :=
      hSeedEq _ (List.Mem.tail _ (List.Mem.head _))
    have hBEq : prob.cbf.barrierB.eval (ratPointEnv pt) = prob.cbf.barrierB.eval env :=
      hSeedEq _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hLieBEq : lieB.eval (ratPointEnv pt) = lieB.eval env :=
      hSeedEq _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hUEq : prob.cbf.unsafePoly.eval (ratPointEnv pt) = prob.cbf.unsafePoly.eval env :=
      hSeedEq _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    have hDetEq : prob.dae.algJacobianDet.eval (ratPointEnv pt) = prob.dae.algJacobianDet.eval env :=
      hSeedEq _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
    have hSumSqEq : (sumVarSquaresPoly prob.lyapunov.dim).eval (ratPointEnv pt) =
        (sumVarSquaresPoly prob.lyapunov.dim).eval env :=
      hAllEq _ (List.Mem.head _)
    have hSymDetEq : (computeSymbolicAlgJacobianDet prob.dae.algConstraints prob.dae.algVars).eval (ratPointEnv pt) =
        (computeSymbolicAlgJacobianDet prob.dae.algConstraints prob.dae.algVars).eval env :=
      hAllEq _ (List.Mem.tail _ (List.Mem.head _))
    have hTailMem : ∀ p ∈ prob.lyapunov.domainIneqs ++ prob.cbf.domainIneqs ++
        prob.dae.algConstraints ++ prob.dae.domainIneqs, p.eval (ratPointEnv pt) = p.eval env :=
      fun p hp => hSeedEq p (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hp))))))
    have hCandSome : ∃ k0, evalSosLyapunovCandidate prob pt = some k0 := by
      change ∃ k0, evalSosLyapunovCandidateWithLie prob lieV lieB pt = some k0
      unfold evalSosLyapunovCandidateWithLie
      by_cases h1 : evalLyapunovRadialNonpos prob.lyapunov pt = true
      · exact ⟨.lyapunovRadialNonpos pt, by simp [h1]⟩
      · by_cases h2 : evalLyapunovLieAscentWithLie prob.lyapunov lieV pt = true
        · exact ⟨.lyapunovLieAscent pt, by simp [h1, h2]⟩
        · by_cases h3 : evalCbfUnsafeOverlap prob.cbf pt = true
          · exact ⟨.cbfUnsafeOverlap pt, by simp [h1, h2, h3]⟩
          · by_cases h4 : evalCbfNagumoViolationWithLie prob.cbf lieB pt = true
            · exact ⟨.cbfNagumoViolation pt, by simp [h1, h2, h3, h4]⟩
            · by_cases h5 : evalDaeManifoldViolation prob.dae pt = true
              · exact ⟨.daeManifoldViolation pt, by simp [h1, h2, h3, h4, h5]⟩
              · exfalso
                rcases hViol with ⟨⟨v, hvLt, hvNe⟩, hDom, hRad⟩ | ⟨hDom, hLie⟩ | ⟨hB, hU, hDom⟩ | ⟨hB, hDom, hNag⟩ | ⟨hMan, hDom, hDae⟩
                · apply h1; unfold evalLyapunovRadialNonpos
                  have hvDim : v < dim := by unfold dim sosLyapunovSearchDim; omega
                  have hNz : pointHasNonZeroCoord prob.lyapunov.dim pt = true :=
                    (pointHasNonZeroCoord_iff _ _).mpr ⟨v, hvLt, by rw [hAgree v hvDim]; exact hvNe⟩
                  simp only [hNz, Bool.true_and, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
                  refine ⟨fun g hg => ?_, ?_⟩
                  · rw [hTailMem g (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hg)))]
                    exact hDom g hg
                  · rw [hVEq, hSumSqEq]; exact hRad
                · apply h2; unfold evalLyapunovLieAscentWithLie
                  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
                  refine ⟨fun g hg => ?_, ?_⟩
                  · rw [hTailMem g (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hg)))]
                    exact hDom g hg
                  · rw [hLieVEq, hVEq]; exact hLie
                · apply h3; unfold evalCbfUnsafeOverlap
                  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by rw [hBEq]; exact hB, by rw [hUEq]; exact hU⟩, fun g hg => ?_⟩
                  rw [hTailMem g (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg)))]
                  exact hDom g hg
                · apply h4; unfold evalCbfNagumoViolationWithLie
                  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by rw [hBEq]; exact hB, fun g hg => ?_⟩, ?_⟩
                  · rw [hTailMem g (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg)))]
                    exact hDom g hg
                  · rw [hLieBEq, hBEq]; exact hNag
                · apply h5; unfold evalDaeManifoldViolation
                  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
                  refine ⟨⟨fun h hh => ?_, fun g hg => ?_⟩, ?_⟩
                  · rw [hTailMem h (List.mem_append_left _ (List.mem_append_right _ hh))]; exact hMan h hh
                  · rw [hTailMem g (List.mem_append_right _ hg)]; exact hDom g hg
                  · rcases hDae with ⟨h_r, hm, hne⟩ | hSym | hReg | hZero
                    · refine Or.inl (Or.inl (Or.inl ⟨h_r, hm, ?_⟩))
                      have hLieHEq := hAllEq (lieDerivativePoly h_r prob.dae.vectorField)
                        (List.Mem.tail _ (List.Mem.tail _ (List.mem_append_left _ (List.mem_map.mpr ⟨h_r, hm, rfl⟩))))
                      rw [hLieHEq]; exact hne
                    · refine Or.inl (Or.inl (Or.inr ?_))
                      rw [hDetEq, hSymDetEq]; exact hSym
                    · refine Or.inl (Or.inr ?_)
                      rw [Poly.eval_sqr, hDetEq, ← Poly.eval_sqr]; exact hReg
                    · refine Or.inr ?_
                      rw [hDetEq]; exact hZero
    obtain ⟨k0, hk0⟩ := hCandSome
    obtain ⟨k, hCheck, hkRefutes, hNotMean⟩ :=
      sosLyapunov_rational_counterexample_complete prob pt k0 B hWf
        (one_le_ratTupleHeightBound pt)
        (by simp [pt, dim])
        (fun _ hx => coord_le_ratTupleHeightBound hx)
        hk0
    exact ⟨B, k, hCheck, hkRefutes, hNotMean⟩

/-- Universal Judge instance for `"sos-lyapunov-cbf@1"`. -/
instance sosLyapunovJudge : Judge SosLyapunovProblem SosLyapunovCert where
  Clause := SosLyapunovClause
  Meaning prob _cert := prob.SemanticMeaning
  check := checkSosLyapunovProblem
  sound := by intro r prob cert h; exact checkSosLyapunovProblem_sound r prob cert h
  refutes := sosLyapunovRefutes
  refuted := by
    intro r prob cert k p hCheck hRefutes _c'
    exact checkSosLyapunovProblem_refuted hCheck hRefutes
  Fragment := SosLyapunovProblemCertifiable
  complete := by
    intro prob hFrag _
    exact (sosLyapunovProblemCertifiable_iff_check_ok prob).mp hFrag
  mono := fun le hne => checkSosLyapunovProblem_mono le hne

/-! ## 7. Reference 2D Nonlinear Cubic Damping, Barrier Safety, Index-1 DAE & Non-Origin Counterexample Refutations -/

/-- Variable $x_0$ as `Poly`. -/
def x0Poly : Poly := polyOfTerm [(0, 1)] 1

/-- Variable $x_1$ as `Poly`. -/
def x1Poly : Poly := polyOfTerm [(1, 1)] 1

/-- 2D nonlinear cubic-damped oscillator vector field:
$$\dot{x}_0 = -x_0 - x_0^3 + x_1, \qquad \dot{x}_1 = -x_0 - x_1 - x_1^3.$$ -/
def cubicDampedVectorField2D : List Poly :=
  [ Poly.add (Poly.neg x0Poly) (Poly.add (Poly.neg (Poly.mul x0Poly (Poly.sqr x0Poly))) x1Poly)
  , Poly.sub (Poly.neg x0Poly) (Poly.add x1Poly (Poly.mul x1Poly (Poly.sqr x1Poly))) ]

/-- Candidate Lyapunov function $V(x_0, x_1) = x_0^2 + x_1^2$ with $\varepsilon = 1/2$, $\gamma = 2$:
$$\mathcal{L}_f V = 2 x_0(-x_0 - x_0^3 + x_1) + 2 x_1(-x_0 - x_1 - x_1^3) = -2(x_0^2 + x_1^2) - 2(x_0^4 + x_1^4),$$
so $-\mathcal{L}_f V - 2 V = 2 x_0^4 + 2 x_1^4 = 2(x_0^2)^2 + 2(x_1^2)^2 \ge 0$! -/
def cubicDampedLyapunovSpec2D : SosLyapunovSpec where
  dim         := 2
  vectorField := cubicDampedVectorField2D
  domainIneqs := []
  lyapunovV   := Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly)
  radialEps   := CanonicalRat.mk 1 2
  decayGamma  := 2

/-- SOS witness for `cubicDampedLyapunovSpec2D`:
* $V - \frac{1}{2}(x_0^2 + x_1^2) = \frac{1}{2} x_0^2 + \frac{1}{2} x_1^2$,
* $-\mathcal{L}_f V - 2 V = 2 (x_0^2)^2 + 2 (x_1^2)^2$. -/
def cubicDampedLyapunovWitness2D : SosLyapunovWitness where
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
def unitDiskCbfSpec2D : SosCbfSpec where
  vectorField := [Poly.neg x0Poly, Poly.neg x1Poly]
  domainIneqs := []
  barrierB    := Poly.sub Poly.one (Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly))
  unsafePoly  := Poly.sub (Poly.add (Poly.sqr x0Poly) (Poly.sqr x1Poly)) (polyConst 2)
  classKAlpha := 2

/-- SOS witness for `unitDiskCbfSpec2D`:
* Stengle refutation: $1 + 1 \cdot B(x) + 1 \cdot u_{\text{unsafe}}(x) = 0$,
* Nagumo invariance: $\mathcal{L}_f B + 2 B = 2 \cdot 1^2$. -/
def unitDiskCbfWitness2D : SosCbfWitness where
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
def parabolicManifoldDaeSpec2D : DaeManifoldSpec where
  vectorField    := [Poly.neg x0Poly, Poly.scale 2 (Poly.sqr x0Poly)]
  domainIneqs    := []
  algConstraints := [Poly.sub (Poly.add (Poly.sqr x0Poly) x1Poly) Poly.one]
  algVars        := [1]
  algJacobianDet := Poly.one
  regDelta       := CanonicalRat.mk 1 2

/-- Witness for `parabolicManifoldDaeSpec2D`. -/
def parabolicManifoldDaeWitness2D : DaeManifoldWitness where
  tangencyCert  := { quotients := [] }
  tangencyCerts := [{ quotients := [] }]
  regularityCert :=
    { monoidIndices := []
    , sigma0        := { terms := [(CanonicalRat.mk 1 2, Poly.one)] }
    , coneTerms     := []
    , idealTerms    := [] }

/-- Reference 2D cubic-damped Lyapunov + unit-disk CBF + parabolic DAE problem bundle for `"sos-lyapunov-cbf@1"`. -/
def cubicDampedCbfDaeProblem2D : SosLyapunovProblem where
  lyapunov := cubicDampedLyapunovSpec2D
  cbf      := unitDiskCbfSpec2D
  dae      := parabolicManifoldDaeSpec2D

/-- Valid SOS/Gröbner certificate bundle for `cubicDampedCbfDaeProblem2D`. -/
def cubicDampedCbfDaeCert2D : SosLyapunovCert where
  lyapunovWitness := cubicDampedLyapunovWitness2D
  cbfWitness      := unitDiskCbfWitness2D
  daeWitness      := parabolicManifoldDaeWitness2D

/-- Planted bad certificate bundle for `"sos-lyapunov-cbf@1"` (empty SOS witness for $V - \varepsilon\|x\|^2$). -/
def badSosCert : SosLyapunovCert where
  lyapunovWitness :=
    { cubicDampedLyapunovWitness2D with
      posDefCert := { monoidIndices := [], sigma0 := { terms := [] }, coneTerms := [], idealTerms := [] } }
  cbfWitness      := unitDiskCbfWitness2D
  daeWitness      := parabolicManifoldDaeWitness2D

theorem sosLyapunov_bad_refused :
    checkSosLyapunovProblem 0 cubicDampedCbfDaeProblem2D badSosCert = .refused .lyapunovFailed [] := by
  decide +kernel

/-- Outside-basin reverse-cubic system $\dot{x}_0 = -x_0 + x_0^3, \dot{x}_1 = -x_1$ with $V = x_0^2 + x_1^2$
and exponential decay rate $\gamma = 1$: locally exponentially decaying inside the basin (`x_0 = 1/2`,
where $\mathcal{L}_f V = -3/8 \le -1/4$), but escaping outside the basin (`x_0 = 2`, $\mathcal{L}_f V = +24 > 0$). -/
def reverseCubicEscapeProblem2D : SosLyapunovProblem :=
  { cubicDampedCbfDaeProblem2D with
    lyapunov :=
      { cubicDampedLyapunovSpec2D with
        decayGamma  := 1
        vectorField :=
          [ Poly.add (Poly.neg x0Poly) (Poly.mul x0Poly (Poly.sqr x0Poly))
          , Poly.neg x1Poly ] } }

theorem reverseCubicEscape_refuted_outside_basin :
    evalLyapunovLieAscent reverseCubicEscapeProblem2D.lyapunov [CanonicalRat.mk 1 2, 0] = false ∧
    evalLyapunovLieAscent reverseCubicEscapeProblem2D.lyapunov [2, 0] = true ∧
    (match checkSosLyapunovProblem 0 reverseCubicEscapeProblem2D sosLyapunovSearchProbe with
     | .refused (.lyapunovLieAscent w) [] =>
       pointHasNonZeroCoord 2 w && evalLyapunovLieAscent reverseCubicEscapeProblem2D.lyapunov w
     | _ => false) = true ∧
    ¬ ValidSosLyapunovSpec reverseCubicEscapeProblem2D.lyapunov ∧
    ¬ reverseCubicEscapeProblem2D.SemanticMeaning := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact lyapunovLieAscent_refutes_spec (pt := [2, 0]) (by decide +kernel)
  · intro hMean
    exact lyapunovLieAscent_refutes_spec (pt := [2, 0]) (by decide +kernel) hMean.1

private theorem findSosLyapunovRefutation_inhabited :
    ∃ k1 k2,
      findSosLyapunovRefutationAtShell 0 reverseCubicEscapeProblem2D = some k1 ∧
      findSosLyapunovRefutation 0 reverseCubicEscapeProblem2D = some k2 := by
  have h1 : (findSosLyapunovRefutationAtShell 0 reverseCubicEscapeProblem2D).isSome = true := by
    decide +kernel
  have h2 : (findSosLyapunovRefutation 0 reverseCubicEscapeProblem2D).isSome = true := by
    decide +kernel
  cases hs1 : findSosLyapunovRefutationAtShell 0 reverseCubicEscapeProblem2D with
  | none => rw [hs1] at h1; cases h1
  | some k1 =>
    cases hs2 : findSosLyapunovRefutation 0 reverseCubicEscapeProblem2D with
    | none => rw [hs2] at h2; cases h2
    | some k2 => exact ⟨k1, k2, rfl, rfl⟩

/-- Indefinite saddle energy $V(x_0, x_1) = x_0^2 - x_1^2$: passes `V(0) = 0` and is positive along
the $x_0$-axis, yet `sosLyapunovJudge` refutes it off-origin along the $x_1$-axis (`V(0, 1) = -1 ≤ 0`). -/
def indefiniteEnergyProblem2D : SosLyapunovProblem :=
  { cubicDampedCbfDaeProblem2D with
    lyapunov :=
      { cubicDampedLyapunovSpec2D with
        lyapunovV := Poly.sub (Poly.sqr x0Poly) (Poly.sqr x1Poly) } }

theorem indefiniteEnergy_refuted_off_origin :
    indefiniteEnergyProblem2D.lyapunov.lyapunovV.eval originEnv = 0 ∧
    (match checkSosLyapunovProblem 0 indefiniteEnergyProblem2D sosLyapunovSearchProbe with
     | .refused (.lyapunovRadialNonpos w) [] =>
       pointHasNonZeroCoord 2 w && evalLyapunovRadialNonpos indefiniteEnergyProblem2D.lyapunov w
     | _ => false) = true ∧
    ¬ ValidSosLyapunovSpec indefiniteEnergyProblem2D.lyapunov :=
  ⟨by decide +kernel,
   by decide +kernel,
   lyapunovRadialNonpos_refutes_spec (pt := [0, 1]) (by decide +kernel)⟩

/-- Shifted non-origin CBF unsafe-set overlap: safe disk $B(x) = 1 - (x_0 - 3)^2 - x_1^2 \ge 0$
centered at $(3, 0)$ (so $B(0, 0) = -8 < 0$ at the origin!) overlapping $u_{\text{unsafe}}(x) = x_0 - 3 \ge 0$.
Quadratic-vertex seeding discovers the non-origin overlap witness at grade `0`. -/
def shiftedDiskOverlapProblem2D : SosLyapunovProblem :=
  let dx := Poly.sub x0Poly (polyConst 3)
  { cubicDampedCbfDaeProblem2D with
    cbf :=
      { unitDiskCbfSpec2D with
        barrierB   := Poly.sub Poly.one (Poly.add (Poly.sqr dx) (Poly.sqr x1Poly))
        unsafePoly := dx } }

theorem shiftedDiskOverlap_refuted_away_from_origin :
    evalCbfUnsafeOverlap shiftedDiskOverlapProblem2D.cbf [] = false ∧
    (match checkSosLyapunovProblem 0 shiftedDiskOverlapProblem2D sosLyapunovSearchProbe with
     | .refused (.cbfUnsafeOverlap w) [] =>
       pointHasNonZeroCoord 2 w && evalCbfUnsafeOverlap shiftedDiskOverlapProblem2D.cbf w
     | _ => false) = true ∧
    ¬ shiftedDiskOverlapProblem2D.SemanticMeaning :=
  ⟨by decide +kernel,
   by decide +kernel,
   cbfUnsafeOverlap_refutes_problem (pt := [3, 0]) (by decide +kernel)⟩

/-- Non-origin CBF Nagumo forward-invariance violation: unit-disk safe set $B(x) = 1 - x_0^2 - x_1^2 \ge 0$
with disjoint unsafe set $x_0^2 + x_1^2 - 2 \ge 0$ and $\alpha = 1$, under outward drift $\dot{x}_0 = 2 x_0, \dot{x}_1 = 0$.
At the origin $(0, 0)$, $\mathcal{L}_f B + B = +1 \ge 0$ holds (`evalCbfNagumoViolation ... [] = false`),
yet on the boundary $(1, 0)$, $B(1, 0) = 0 \ge 0$ while $\mathcal{L}_f B(1, 0) + B(1, 0) = -4 < 0$! -/
def outwardDriftNagumoProblem2D : SosLyapunovProblem :=
  { cubicDampedCbfDaeProblem2D with
    cbf :=
      { unitDiskCbfSpec2D with
        vectorField := [Poly.scale 2 x0Poly, Poly.zero]
        classKAlpha := 1 } }

theorem outwardDriftNagumo_refuted_off_origin :
    evalCbfNagumoViolation outwardDriftNagumoProblem2D.cbf [] = false ∧
    (match checkSosLyapunovProblem 0 outwardDriftNagumoProblem2D sosLyapunovSearchProbe with
     | .refused (.cbfNagumoViolation w) [] =>
       pointHasNonZeroCoord 2 w && evalCbfNagumoViolation outwardDriftNagumoProblem2D.cbf w
     | _ => false) = true ∧
    ¬ outwardDriftNagumoProblem2D.SemanticMeaning :=
  ⟨by decide +kernel,
   by decide +kernel,
   cbfNagumoViolation_refutes_problem (pt := [1, 0]) (by decide +kernel)⟩

/-- Non-origin Index-1 DAE manifold tangency violation on $h_1(x_0, x_1) = x_0^2 + x_1 - 1 = 0$
under non-tangent flow $\dot{x}_0 = -x_0, \dot{x}_1 = 0$: the origin $(0, 0)$ is not on the manifold
(`evalDaeManifoldViolation ... [] = false`), yet at $(1, 0) \in \mathcal{M}$, $\mathcal{L}_f h_1(1, 0) = -2 \ne 0$! -/
def nonTangentParabolicDaeProblem2D : SosLyapunovProblem :=
  { cubicDampedCbfDaeProblem2D with
    dae :=
      { parabolicManifoldDaeSpec2D with
        vectorField := [Poly.neg x0Poly, Poly.zero] } }

theorem nonTangentParabolicDae_refuted_off_origin :
    evalDaeManifoldViolation nonTangentParabolicDaeProblem2D.dae [] = false ∧
    (match checkSosLyapunovProblem 0 nonTangentParabolicDaeProblem2D sosLyapunovSearchProbe with
     | .refused (.daeManifoldViolation w) [] =>
       pointHasNonZeroCoord 2 w && evalDaeManifoldViolation nonTangentParabolicDaeProblem2D.dae w
     | _ => false) = true ∧
    ¬ nonTangentParabolicDaeProblem2D.SemanticMeaning :=
  ⟨by decide +kernel,
   by decide +kernel,
   daeManifoldViolation_refutes_problem (pt := [1, 0]) (by decide +kernel)⟩

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

def ofInt (n : Int) : SosJson := .num n 0
def ofNat (n : Nat) : SosJson := .num (Int.ofNat n) 0
def ofNatList (ns : List Nat) : SosJson := .arr (ns.map ofNat)
def mkObj (kvs : List (String × SosJson)) : SosJson :=
  .obj (kvs.map fun (k, v) => (k.toList, v))

@[expose] def lookupField : List (List Char × SosJson) → List Char → Option SosJson
  | [], _ => none
  | (k0, v0) :: rest, k => if k0 == k then some v0 else lookupField rest k

abbrev getObjVal? (j : SosJson) (k : String) : Except String SosJson :=
  match j with
  | .obj fields =>
    match lookupField fields k.toList with
    | some v => .ok v
    | none   => .error s!"property not found: {k}"
  | _ => .error s!"object expected for key '{k}'"

abbrev getStr? (j : SosJson) : Except String String :=
  match j with
  | .str cs => .ok (String.ofList cs)
  | _       => .error "string expected"

abbrev getInt? (j : SosJson) : Except String Int :=
  match j with
  | .num m 0 => .ok m
  | _        => .error "integer expected"

abbrev getNat? (j : SosJson) : Except String Nat :=
  match j with
  | .num (.ofNat n) 0 => .ok n
  | _                 => .error "natural number expected"

abbrev getArr? (j : SosJson) : Except String (List SosJson) :=
  match j with
  | .arr xs => .ok xs
  | _       => .error "array expected"

abbrev getObjStr? (j : SosJson) (k : String) : Except String String :=
  j.getObjVal? k >>= getStr?

abbrev getObjInt? (j : SosJson) (k : String) : Except String Int :=
  j.getObjVal? k >>= getInt?

abbrev getObjNat? (j : SosJson) (k : String) : Except String Nat :=
  j.getObjVal? k >>= getNat?

abbrev getObjNatList? (j : SosJson) (k : String) : Except String (List Nat) := do
  let xs ← j.getObjVal? k >>= getArr?
  xs.mapM getNat?

end SosJson

def sosJsonNatWriteCore : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d : Char :=
      match n % 10 with
      | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
      | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'
    let q := n / 10
    if q == 0 then d :: acc
    else sosJsonNatWriteCore fuel q (d :: acc)

/-- Unbounded decimal `Nat` serializer: guarantees at least `n.log2 + 2` digits of fuel
(`digits_10(n) ≤ bits_2(n) < n.log2 + 2`), eliminating the `fuel = 24` leading-digit truncation
bug (`10^24 -> "000...0" -> 0`). -/
def sosJsonNatWrite (fuel n : Nat) (acc : List Char) : List Char :=
  sosJsonNatWriteCore (Nat.max fuel (n.log2 + 2)) n acc

def sosJsonIntWrite : Int → List Char → List Char
  | .ofNat n, acc   => sosJsonNatWrite (n.log2 + 2) n acc
  | .negSucc n, acc => '-' :: sosJsonNatWrite ((n + 1).log2 + 2) (n + 1) acc

def sosJsonEscapeWrite : List Char → List Char → List Char
  | [], acc => acc
  | '"' :: cs, acc  => '\\' :: '"' :: sosJsonEscapeWrite cs acc
  | '\\' :: cs, acc => '\\' :: '\\' :: sosJsonEscapeWrite cs acc
  | '\n' :: cs, acc => '\\' :: 'n' :: sosJsonEscapeWrite cs acc
  | '\r' :: cs, acc => '\\' :: 'r' :: sosJsonEscapeWrite cs acc
  | '\t' :: cs, acc => '\\' :: 't' :: sosJsonEscapeWrite cs acc
  | c :: cs, acc    => c :: sosJsonEscapeWrite cs acc

def sosJsonQuoteCharsWrite (cs : List Char) (acc : List Char) : List Char :=
  '"' :: sosJsonEscapeWrite cs ('"' :: acc)

def sosJsonWriteArrElems (writeVal : SosJson → List Char → List Char) :
    List SosJson → List Char → List Char
  | [], acc => acc
  | [x], acc => writeVal x acc
  | x :: xs, acc => writeVal x (',' :: sosJsonWriteArrElems writeVal xs acc)

def sosJsonWriteObjFields (writeVal : SosJson → List Char → List Char) :
    List (List Char × SosJson) → List Char → List Char
  | [], acc => acc
  | [(k, v)], acc => sosJsonQuoteCharsWrite k (':' :: writeVal v acc)
  | (k, v) :: rest, acc =>
    sosJsonQuoteCharsWrite k (':' :: writeVal v (',' :: sosJsonWriteObjFields writeVal rest acc))

mutual
def sosJsonWriteVal : SosJson → List Char → List Char
  | .null, acc => 'n' :: 'u' :: 'l' :: 'l' :: acc
  | .bool true, acc => 't' :: 'r' :: 'u' :: 'e' :: acc
  | .bool false, acc => 'f' :: 'a' :: 'l' :: 's' :: 'e' :: acc
  | .num m 0, acc => sosJsonIntWrite m acc
  | .num m e, acc =>
    sosJsonIntWrite m ('e' :: '-' :: sosJsonNatWrite (e.log2 + 2) e acc)
  | .str cs, acc => sosJsonQuoteCharsWrite cs acc
  | .arr elems, acc => '[' :: sosJsonWriteArr elems (']' :: acc)
  | .obj fields, acc => '{' :: sosJsonWriteObj fields ('}' :: acc)
termination_by structural j => j

def sosJsonWriteArr : List SosJson → List Char → List Char
  | [], acc => acc
  | [x], acc => sosJsonWriteVal x acc
  | x :: xs, acc => sosJsonWriteVal x (',' :: sosJsonWriteArr xs acc)
termination_by structural xs => xs

def sosJsonWriteObj : List (List Char × SosJson) → List Char → List Char
  | [], acc => acc
  | [(k, v)], acc => sosJsonQuoteCharsWrite k (':' :: sosJsonWriteVal v acc)
  | (k, v) :: rest, acc =>
    sosJsonQuoteCharsWrite k (':' :: sosJsonWriteVal v (',' :: sosJsonWriteObj rest acc))
termination_by structural fs => fs
end

/-- Structural difference-list serializer for `SosJson` (never clamps deep JSON to `"null"`). -/
def sosJsonWriteAux (_fuel : Nat) (j : SosJson) (acc : List Char) : List Char :=
  sosJsonWriteVal j acc

def sosJsonCompress (j : SosJson) : String :=
  String.ofList (sosJsonWriteVal j [])

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

abbrev sosJsonDigitVal? : Char → Option Nat
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

abbrev sosJsonParseSciExp (m : Int) (fracExp : Nat) (cs : List Char) : Option ((Int × Nat) × List Char) :=
  match cs with
  | 'e' :: expCs | 'E' :: expCs =>
    let (expNeg, expDigitsCs) :=
      match expCs with
      | '-' :: r => (true, r)
      | '+' :: r => (false, r)
      | _ => (false, expCs)
    let (sciExp, hasExp, rest) := sosJsonParseDigits expDigitsCs 0 false
    if !hasExp || decide (4096 < sciExp) then none
    else if expNeg then
      some ((m, fracExp + sciExp), rest)
    else if decide (fracExp ≤ sciExp) then
      let scale : Int := Int.ofNat (10 ^ (sciExp - fracExp))
      some ((m * scale, 0), rest)
    else
      some ((m, fracExp - sciExp), rest)
  | _ => some ((m, fracExp), cs)

abbrev sosJsonParseNum (cs : List Char) : Option ((Int × Nat) × List Char) :=
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
        sosJsonParseSciExp m fracExp cs3
    | _ =>
      let m : Int := if neg then -(Int.ofNat intPart) else Int.ofNat intPart
      sosJsonParseSciExp m 0 cs2

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

/-- Kernel-reducible recursive-descent JSON AST parser with input-length-proportional fuel. -/
def sosJsonParseAux : Nat → List Char → Option (SosJson × List Char)
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
        let (items, rest) ← sosJsonParseArrAux (sosJsonParseAux fuel) (arrCs'.length + 1) arrCs' []
        some (.arr items, rest)
    | '{' :: objCs =>
      match sosJsonSkipWs objCs with
      | '}' :: rest => some (.obj [], rest)
      | objCs' => do
        let (fields, rest) ← sosJsonParseObjAux (sosJsonParseAux fuel) (objCs'.length + 1) objCs' []
        some (.obj fields, rest)
    | numCs => do
      let ((m, e), rest) ← sosJsonParseNum numCs
      some (.num m e, rest)

def sosJsonParse (s : String) : Except String SosJson :=
  let cs := s.toList
  match sosJsonParseAux (cs.length + 1) cs with
  | some (j, rest) =>
    if (sosJsonSkipWs rest).isEmpty then .ok j
    else .error "trailing characters in JSON"
  | none => .error "malformed JSON"

/-- Encode a `CanonicalRat` as an integer when `den = 1` or `{"num": n, "den": d}` otherwise. -/
def sosJsonEncodeRat (q : CanonicalRat) : SosJson :=
  if q.den == 1 then .ofInt q.num
  else SosJson.mkObj [("num", .ofInt q.num), ("den", .ofNat q.den)]

/-- Decode a `CanonicalRat` from an arbitrary-precision JSON integer, decimal/scientific number
(`.num m e` = $m / 10^e$), or `{"num": n, "den": d}` object. -/
def decodeRatJson (j : SosJson) : Except String CanonicalRat :=
  match j with
  | .num m 0 => .ok (CanonicalRat.mk m 1)
  | .num m e =>
    if decide (e ≤ 4096) then
      .ok (CanonicalRat.mk m (10 ^ e))
    else
      .error "invalid rational JSON: decimal exponent exceeds 4096"
  | _ =>
    match j.getObjInt? "num", j.getObjNat? "den" with
    | .ok n, .ok d =>
      if d == 0 then .error "invalid rational JSON: zero denominator"
      else .ok (CanonicalRat.mk n d)
    | _, _ => .error "invalid rational JSON: expected number or {num, den}"

/-- Structural polynomial exponentiation $p^k$. -/
def sosPolyPow (p : Poly) : Nat → Poly
  | 0     => Poly.one
  | k + 1 => Poly.mul p (sosPolyPow p k)

/-- Encode a sparse `Monomial` as a JSON array of `[v, e]` variable-power pairs. -/
def sosJsonEncodeMonomial (m : Monomial) : SosJson :=
  .arr <| m.map fun (v, e) => .arr [.ofNat v, .ofNat e]

/-- Decode a single `(var, exp)` factor from `[v, e]` or `{"var": v, "exp": e}`. -/
def decodeMonomialFactorJson (j : SosJson) : Except String (Nat × Nat) :=
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
def decodeMonomialJson (j : SosJson) : Except String Monomial := do
  let arr ← j.getArr?
  arr.mapM decodeMonomialFactorJson

/-- Encode a multivariate polynomial `p : Poly` as a JSON array of `[monomial, coeff]` terms. -/
def sosJsonEncodePoly (p : Poly) : SosJson :=
  .arr <| p.terms.map fun (m, c) =>
    .arr [sosJsonEncodeMonomial m, sosJsonEncodeRat c]

/-- Decode a single polynomial term from `[monomial, coeff]`, `{"monomial": [...], "coeff": c}`,
`{"vars": [...], "coeff": c}`, or univariate shorthand `{"var": v, "exp": e, "coeff": c}`. -/
def decodePolyTermItemJson (item : SosJson) : Except String Poly :=
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
def decodePolyTermsJson (arr : List SosJson) : Except String Poly :=
  arr.foldlM (fun acc item => do
    let termPoly ← decodePolyTermItemJson item
    pure (Poly.add acc termPoly)
  ) Poly.zero

mutual
def sosJsonAstSize : SosJson → Nat
  | .arr xs => 1 + sosJsonAstArrSize xs
  | .obj fs => 1 + sosJsonAstObjSize fs
  | _ => 1
termination_by structural j => j

def sosJsonAstArrSize : List SosJson → Nat
  | [] => 0
  | x :: xs => sosJsonAstSize x + sosJsonAstArrSize xs
termination_by structural xs => xs

def sosJsonAstObjSize : List (List Char × SosJson) → Nat
  | [] => 0
  | (_, v) :: fs => sosJsonAstSize v + sosJsonAstObjSize fs
termination_by structural fs => fs
end

/-- Structural JSON AST decoder for `Poly`. -/
def decodePolyJsonAux : Nat → SosJson → Except String Poly
  | 0, _ => .error "invalid polynomial AST JSON: nesting depth exceeded"
  | fuel + 1, j =>
    match j with
    | .num _ _ => do
      let q ← decodeRatJson j
      pure (polyConst q)
    | _ =>
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
supports integer/decimal constants, sparse multivariate monomial arrays, and recursive polynomial AST
operators (`const`, `var`, `add`, `sub`, `mul`, `neg`, `sqr`, `pow`, `scale`). -/
def decodePolyJson (j : SosJson) : Except String Poly :=
  decodePolyJsonAux (sosJsonAstSize j + 1) j

def decodePolyListJson (j : SosJson) : Except String (List Poly) := do
  let arr ← j.getArr?
  arr.mapM decodePolyJson

/-- Convert a rational $L^\top D L$ Gram matrix factorization
$\sum_{i=0}^{r-1} d_i \left(\sum_{j=0}^{m-1} L_{i,j} b_j(x)\right)^2$ into an `SOSPoly`
(requiring positive diagonal weights $d_i > 0$ or dropping zero-weight rows while rejecting $d_i < 0$). -/
def buildSOSPolyFromGram
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

def sosJsonEncodeSOSPoly (s : SOSPoly) : SosJson :=
  .arr <| s.terms.map fun (w, p) =>
    .arr [sosJsonEncodeRat w, sosJsonEncodePoly p]

def decodeSOSTermEntryJson (j : SosJson) : Except String (CanonicalRat × Poly) :=
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
def decodeSOSPolyJson (j : SosJson) : Except String SOSPoly :=
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

def sosJsonEncodePsatzCert (c : PositivstellensatzCert) : SosJson :=
  SosJson.mkObj
    [ ("monoidIndices", .ofNatList c.monoidIndices)
    , ("sigma0", sosJsonEncodeSOSPoly c.sigma0)
    , ("coneTerms", .arr <| c.coneTerms.map fun (s, idx) =>
        .arr [sosJsonEncodeSOSPoly s, .ofNat idx])
    , ("idealTerms", .arr <| c.idealTerms.map fun (p, idx) =>
        .arr [sosJsonEncodePoly p, .ofNat idx]) ]

def decodePsatzCertJson (j : SosJson) : Except String PositivstellensatzCert := do
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

def sosJsonEncodeIdealCert (c : IdealMembershipCert) : SosJson :=
  SosJson.mkObj
    [ ("quotients", .arr <| c.quotients.map fun (q, idx) =>
        .arr [sosJsonEncodePoly q, .ofNat idx]) ]

def decodeIdealCertJson (j : SosJson) : Except String IdealMembershipCert := do
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

def sosJsonEncodeLyapunovSpec (s : SosLyapunovSpec) : SosJson :=
  SosJson.mkObj
    [ ("dim", .ofNat s.dim)
    , ("vectorField", .arr <| s.vectorField.map sosJsonEncodePoly)
    , ("domainIneqs", .arr <| s.domainIneqs.map sosJsonEncodePoly)
    , ("lyapunovV", sosJsonEncodePoly s.lyapunovV)
    , ("radialEps", sosJsonEncodeRat s.radialEps)
    , ("decayGamma", sosJsonEncodeRat s.decayGamma) ]

def decodeSosLyapunovSpecJson (j : SosJson) : Except String SosLyapunovSpec := do
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

def sosJsonEncodeCbfSpec (s : SosCbfSpec) : SosJson :=
  SosJson.mkObj
    [ ("vectorField", .arr <| s.vectorField.map sosJsonEncodePoly)
    , ("domainIneqs", .arr <| s.domainIneqs.map sosJsonEncodePoly)
    , ("barrierB", sosJsonEncodePoly s.barrierB)
    , ("unsafePoly", sosJsonEncodePoly s.unsafePoly)
    , ("classKAlpha", sosJsonEncodeRat s.classKAlpha) ]

def decodeSosCbfSpecJson (j : SosJson) : Except String SosCbfSpec := do
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

def sosJsonEncodeDaeSpec (s : DaeManifoldSpec) : SosJson :=
  SosJson.mkObj
    [ ("vectorField", .arr <| s.vectorField.map sosJsonEncodePoly)
    , ("domainIneqs", .arr <| s.domainIneqs.map sosJsonEncodePoly)
    , ("algConstraints", .arr <| s.algConstraints.map sosJsonEncodePoly)
    , ("algVars", .ofNatList s.algVars)
    , ("algJacobianDet", sosJsonEncodePoly s.algJacobianDet)
    , ("regDelta", sosJsonEncodeRat s.regDelta) ]

def decodeDaeManifoldSpecJson (j : SosJson) : Except String DaeManifoldSpec := do
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
def renderSosLyapunovProblemJson (p : SosLyapunovProblem) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("lyapunov", sosJsonEncodeLyapunovSpec p.lyapunov)
    , ("cbf", sosJsonEncodeCbfSpec p.cbf)
    , ("dae", sosJsonEncodeDaeSpec p.dae) ]

/-- General JSON AST decoder for `SosLyapunovProblem` parsing arbitrary multivariate polynomial
vector fields, domain inequalities, Lyapunov functions, CBF barriers, and Index-1 DAE manifolds. -/
def decodeSosLyapunovProblem (s : String) : Except String SosLyapunovProblem :=
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

def sosJsonEncodeLyapunovWitness (w : SosLyapunovWitness) : SosJson :=
  SosJson.mkObj
    [ ("posDefCert", sosJsonEncodePsatzCert w.posDefCert)
    , ("lieDecayCert", sosJsonEncodePsatzCert w.lieDecayCert) ]

def decodeSosLyapunovWitnessJson (j : SosJson) : Except String SosLyapunovWitness := do
  let posJ ← j.getObjVal? "posDefCert"
  let lieJ ← j.getObjVal? "lieDecayCert"
  let posDefCert ← decodePsatzCertJson posJ
  let lieDecayCert ← decodePsatzCertJson lieJ
  pure { posDefCert, lieDecayCert }

def sosJsonEncodeCbfWitness (w : SosCbfWitness) : SosJson :=
  SosJson.mkObj
    [ ("unsafeRefuteCert", sosJsonEncodePsatzCert w.unsafeRefuteCert)
    , ("nagumoInvarianceCert", sosJsonEncodePsatzCert w.nagumoInvarianceCert) ]

def decodeSosCbfWitnessJson (j : SosJson) : Except String SosCbfWitness := do
  let uJ ← j.getObjVal? "unsafeRefuteCert"
  let nJ ← j.getObjVal? "nagumoInvarianceCert"
  let unsafeRefuteCert ← decodePsatzCertJson uJ
  let nagumoInvarianceCert ← decodePsatzCertJson nJ
  pure { unsafeRefuteCert, nagumoInvarianceCert }

def sosJsonEncodeDaeWitness (w : DaeManifoldWitness) : SosJson :=
  SosJson.mkObj
    [ ("tangencyCert", sosJsonEncodeIdealCert w.tangencyCert)
    , ("tangencyCerts", .arr <| w.tangencyCerts.map sosJsonEncodeIdealCert)
    , ("regularityCert", sosJsonEncodePsatzCert w.regularityCert) ]

def decodeDaeManifoldWitnessJson (j : SosJson) : Except String DaeManifoldWitness := do
  let tcJ ← j.getObjVal? "tangencyCert"
  let tangencyCert ← decodeIdealCertJson tcJ
  let tcsJ ← j.getObjVal? "tangencyCerts"
  let tcsArr ← tcsJ.getArr?
  let tangencyCerts ← tcsArr.mapM decodeIdealCertJson
  let regJ ← j.getObjVal? "regularityCert"
  let regularityCert ← decodePsatzCertJson regJ
  pure { tangencyCert, tangencyCerts, regularityCert }

/-- Render an `SosLyapunovCert` deterministically as a complete JSON AST string. -/
def renderSosLyapunovCertJson (c : SosLyapunovCert) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("lyapunovWitness", sosJsonEncodeLyapunovWitness c.lyapunovWitness)
    , ("cbfWitness", sosJsonEncodeCbfWitness c.cbfWitness)
    , ("daeWitness", sosJsonEncodeDaeWitness c.daeWitness) ]

/-- General JSON AST decoder for `SosLyapunovCert` parsing arbitrary SOS / Gram matrix
Positivstellensatz witnesses and Gröbner ideal membership certificates. -/
def decodeSosLyapunovCert (s : String) : Except String SosLyapunovCert :=
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
def sosLyapunovFormat : Format where
  name        := "sos-lyapunov-cbf"
  version     := "1"
  Obj         := SosLyapunovProblem
  Cert        := SosLyapunovCert
  decodeObj   := decodeSosLyapunovProblem
  decodeCert  := decodeSosLyapunovCert
  trust       := .kernel
  regime      := .decidable
  bad         := (cubicDampedCbfDaeProblem2D, badSosCert)
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

/-- Concrete verification of the 2D cubic nonlinear Lyapunov certificate, 2D disk Control Barrier
Function certificate, Index-1 algebraic manifold DAE certificate, and `"sos-lyapunov-cbf@1"` judge. -/
theorem cubic_lyapunov_cbf_dae_2d_accepted :
    checkSosLyapunov cubicDampedLyapunovSpec2D cubicDampedLyapunovWitness2D = true ∧
    checkSosCbf unitDiskCbfSpec2D unitDiskCbfWitness2D = true ∧
    checkDaeManifold parabolicManifoldDaeSpec2D parabolicManifoldDaeWitness2D = true ∧
    checkSosLyapunovProblem 1 cubicDampedCbfDaeProblem2D cubicDampedCbfDaeCert2D = .ok := by
  decide +kernel

end Obend.Analysis
end
