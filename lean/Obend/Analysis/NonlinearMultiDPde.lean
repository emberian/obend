module
public import Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox

/-!
# Multi-Dimensional Nonlinear Conservation Laws (`Obend.Analysis.NonlinearMultiDPde`)

Verified mathematical core for `D`-dimensional, `m`-component nonlinear conservation laws
`∂_t U + Σ_{d < D} ∂_{x_d} F_d(U; p) = 0` over `Rat`: guarded rational `FluxExpr`s with static
positivity domains (`DomainValid`), exact multivariable Fréchet Taylor remainders
(`symJacobian_frechet_taylor`), cleared-denominator rational polynomial reflection
(`checkFluxEqReflective_sound`), 2nd-order nonlinear MUSCL-`minmod` Rusanov TVD stability
(`tvd_rusanov_minmod_step_nonincreasing`), Tadmor discrete entropy dissipation
(`tadmor_rusanov_entropy_dissipative`), and arbitrary-dimension Lie/Strang sweep conservation.
-/

public section
namespace Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox
set_option autoImplicit false

/-! ## 1. Guarded Rational Flux AST & Positivity Domains -/

/-- Deep-embedded nonlinear rational expression over state variables `U_i` and parameters `p_k`. -/
inductive FluxExpr where
  | const (q : Rat) | var (idx : Nat) | param (idx : Nat) | neg (a : FluxExpr)
  | add (a b : FluxExpr) | sub (a b : FluxExpr) | mul (a b : FluxExpr) | invSafe (den : FluxExpr)
  deriving DecidableEq, Repr

/-- Convenience constructor for guarded division `num / den`. -/
@[expose] def FluxExpr.divSafe (num den : FluxExpr) : FluxExpr := .mul num (.invSafe den)

/-- Point environment assigning rational values to conserved state components and parameters. -/
structure FluxEnv where
  state : Nat → Rat
  params : Nat → Rat

/-- Evaluate a `FluxExpr` at `env`. -/
@[expose] def evalFlux : FluxExpr → FluxEnv → Rat
  | .const q, _ => q
  | .var idx, env => env.state idx
  | .param idx, env => env.params idx
  | .neg a, env => -(evalFlux a env)
  | .add a b, env => evalFlux a env + evalFlux b env
  | .sub a b, env => evalFlux a env - evalFlux b env
  | .mul a b, env => evalFlux a env * evalFlux b env
  | .invSafe d, env => (1 : Rat) / evalFlux d env

/-- Recursive non-vanishing denominator condition for every `invSafe` node in `e`. -/
@[expose] def DenomNonzero : FluxExpr → FluxEnv → Prop
  | .const _, _ | .var _, _ | .param _, _ => True
  | .neg a, env => DenomNonzero a env
  | .add a b, env | .sub a b, env | .mul a b, env => DenomNonzero a env ∧ DenomNonzero b env
  | .invSafe d, env => evalFlux d env ≠ 0 ∧ DenomNonzero d env

/-- Declared positivity assumption on either a conserved variable (`ρ > 0`) or parameter (`m > 0`). -/
inductive PosTarget where
  | stateVar (idx : Nat) | paramVar (idx : Nat)
  deriving DecidableEq, Repr

/-- `env` satisfies every strict positivity constraint in `dom`. -/
@[expose] def DomainValid (dom : List PosTarget) (env : FluxEnv) : Prop :=
  ∀ t ∈ dom, match t with | .stateVar i => 0 < env.state i | .paramVar p => 0 < env.params p

/-- Static syntactic check certifying `0 < evalFlux e env` under `DomainValid dom env`. -/
def checkExprPositive (dom : List PosTarget) : FluxExpr → Bool
  | .const q => decide (0 < q)
  | .var i => dom.contains (.stateVar i)
  | .param p => dom.contains (.paramVar p)
  | .neg (.const q) => decide (q < 0)
  | .neg _ | .sub _ _ => false
  | .add a b | .mul a b => checkExprPositive dom a && checkExprPositive dom b
  | .invSafe d => checkExprPositive dom d

/-- Static syntactic check certifying that every denominator in `e` is strictly positive on `dom`. -/
def checkExprDomainSafe (dom : List PosTarget) : FluxExpr → Bool
  | .const _ | .var _ | .param _ => true
  | .neg a => checkExprDomainSafe dom a
  | .add a b | .sub a b | .mul a b => checkExprDomainSafe dom a && checkExprDomainSafe dom b
  | .invSafe d => checkExprPositive dom d && checkExprDomainSafe dom d

theorem rat_mul_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := fun hz =>
  (Rat.mul_eq_zero.mp hz).elim ha hb
theorem rat_eq_of_mul_cancel {a b d : Rat} (hd : d ≠ 0) (h : a * d = b * d) : a = b := by
  rcases Rat.mul_eq_zero.mp (show (a - b) * d = 0 by grind) with hsub | hdc
  · grind
  · exact absurd hdc hd
theorem rat_div_one (q : Rat) : q / (1 : Rat) = q := by
  have hc : (q / (1 : Rat)) * 1 = q := Rat.div_mul_cancel (by decide); grind
theorem rat_inv_one_div_pos {x : Rat} (hx : 0 < x) : 0 < (1 : Rat) / x := by
  have hc : ((1 : Rat) / x) * x = 1 := Rat.div_mul_cancel (by grind)
  by_cases hpos : (0 : Rat) < (1 : Rat) / x
  · exact hpos
  · have hm := Rat.mul_le_mul_of_nonneg_right (by grind : (1 : Rat) / x ≤ 0) (Rat.le_of_lt hx); grind

theorem checkExprPositive_sound (dom : List PosTarget) (e : FluxExpr) (env : FluxEnv)
    (hPos : checkExprPositive dom e = true) (hDom : DomainValid dom env) :
    0 < evalFlux e env := by
  induction e with
  | const q => simp only [checkExprPositive, decide_eq_true_eq] at hPos; exact hPos
  | var i | param i => simp only [checkExprPositive, List.contains_iff_mem] at hPos; exact hDom _ hPos
  | neg a _ =>
    cases a with
    | const q => simp only [checkExprPositive, decide_eq_true_eq] at hPos; simp only [evalFlux]; grind
    | _ => simp [checkExprPositive] at hPos
  | add a b iha ihb =>
    simp only [checkExprPositive, Bool.and_eq_true] at hPos
    have ha := iha hPos.1; have hb := ihb hPos.2; simp only [evalFlux]; grind
  | sub _ _ => simp [checkExprPositive] at hPos
  | mul a b iha ihb =>
    simp only [checkExprPositive, Bool.and_eq_true] at hPos
    exact Rat.mul_pos (iha hPos.1) (ihb hPos.2)
  | invSafe d ihd => exact rat_inv_one_div_pos (ihd hPos)

example : checkExprPositive [.stateVar 0] (.invSafe (.var 0)) = true ∧
    DomainValid [.stateVar 0] ⟨fun _ => 2, fun _ => 1⟩ :=
  ⟨by decide +kernel, fun t ht => by simp at ht; subst ht; decide +kernel⟩

/-- Every expression accepted by `checkExprDomainSafe dom` has non-zero denominators on `dom`. -/
theorem checkExprDomainSafe_implies_denomNonzero (dom : List PosTarget) (e : FluxExpr)
    (env : FluxEnv) (hSafe : checkExprDomainSafe dom e = true) (hDom : DomainValid dom env) :
    DenomNonzero e env := by
  induction e with
  | const _ | var _ | param _ => trivial
  | neg a iha => exact iha hSafe
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    simp only [checkExprDomainSafe, Bool.and_eq_true] at hSafe
    exact ⟨iha hSafe.1, ihb hSafe.2⟩
  | invSafe d ihd =>
    simp only [checkExprDomainSafe, Bool.and_eq_true] at hSafe
    have hpos := checkExprPositive_sound dom d env hSafe.1 hDom
    exact ⟨by grind, ihd hSafe.2⟩

/-! ## 2. Verified Symbolic Fréchet Differentiation & Exact Algebraic Taylor Remainder -/

/-- Exact symbolic partial derivative `∂e / ∂U_j` (chain, product, and safe reciprocal rules). -/
@[expose] def symPartial (j : Nat) : FluxExpr → FluxExpr
  | .const _ | .param _ => .const 0
  | .var i => if i == j then .const 1 else .const 0
  | .neg a => .neg (symPartial j a)
  | .add a b => .add (symPartial j a) (symPartial j b)
  | .sub a b => .sub (symPartial j a) (symPartial j b)
  | .mul a b => .add (.mul (symPartial j a) b) (.mul a (symPartial j b))
  | .invSafe d => .neg (.mul (symPartial j d) (.mul (.invSafe d) (.invSafe d)))

/-- Symbolic Jacobian matrix `J_{i, j}(U) = ∂F_i / ∂U_j` for an `m`-component flux vector. -/
@[expose] def symJacobian (m : Nat) (flux : List FluxExpr) : List (List FluxExpr) :=
  flux.map fun fi => (List.range m).map fun j => symPartial j fi

/-- Evaluate a symbolic Jacobian matrix at `env` into a `Mat` (`Nat → Nat → Rat`). -/
def evalSymJacobianMat (jac : List (List FluxExpr)) (env : FluxEnv) : Mat :=
  fun i j => evalFlux (getOr (getOr jac i []) j (.const 0)) env

theorem symPartial_preserves_domainSafe (dom : List PosTarget) (j : Nat) (e : FluxExpr)
    (hSafe : checkExprDomainSafe dom e = true) :
    checkExprDomainSafe dom (symPartial j e) = true := by
  induction e with
  | const _ | param _ => rfl
  | var i => simp only [symPartial]; split <;> rfl
  | neg a iha => simpa [symPartial, checkExprDomainSafe] using iha hSafe
  | add a b iha ihb | sub a b iha ihb =>
    simp only [checkExprDomainSafe, Bool.and_eq_true] at hSafe
    simp [symPartial, checkExprDomainSafe, iha hSafe.1, ihb hSafe.2]
  | mul a b iha ihb =>
    simp only [checkExprDomainSafe, Bool.and_eq_true] at hSafe
    simp [symPartial, checkExprDomainSafe, hSafe.1, hSafe.2, iha hSafe.1, ihb hSafe.2]
  | invSafe d ihd =>
    simp only [checkExprDomainSafe, Bool.and_eq_true] at hSafe
    simp [symPartial, checkExprDomainSafe, hSafe.1, hSafe.2, ihd hSafe.2]

/-- Perturb the first `m` state coordinates along direction `V` by step `h`: `U + h · V`. -/
def shiftVecEnv (m : Nat) (env : FluxEnv) (h : Rat) (V : Vec) : FluxEnv :=
  { env with state := fun i => if i < m then env.state i + h * V i else env.state i }

/-- Directional derivative `Σ_{j < m} (∂e / ∂U_j)(env) · V_j`. -/
def evalDirectionalDeriv (m : Nat) (e : FluxExpr) (env : FluxEnv) (V : Vec) : Rat :=
  sumTo m fun j => evalFlux (symPartial j e) env * V j

/-- Exact rational 2nd-order Taylor remainder `R(U, V, h)` satisfying
`e(U + h V) - e(U) = h · D_V e(U) + h² · R(U, V, h)`. -/
def symDirectionalRem (m : Nat) : FluxExpr → FluxEnv → Vec → Rat → Rat
  | .const _, _, _, _ | .var _, _, _, _ | .param _, _, _, _ => 0
  | .neg a, env, V, h => -(symDirectionalRem m a env V h)
  | .add a b, env, V, h => symDirectionalRem m a env V h + symDirectionalRem m b env V h
  | .sub a b, env, V, h => symDirectionalRem m a env V h - symDirectionalRem m b env V h
  | .mul a b, env, V, h =>
    let a0 := evalFlux a env; let b0 := evalFlux b env
    let da := evalDirectionalDeriv m a env V; let db := evalDirectionalDeriv m b env V
    let ra := symDirectionalRem m a env V h; let rb := symDirectionalRem m b env V h
    ra * b0 + a0 * rb + (da + h * ra) * (db + h * rb)
  | .invSafe d, env, V, h =>
    let d0 := evalFlux d env; let d1 := evalFlux d (shiftVecEnv m env h V)
    let dd := evalDirectionalDeriv m d env V; let rd := symDirectionalRem m d env V h
    (dd * (dd + h * rd) - rd * d0) / (d0 * d0 * d1)

theorem evalDirectionalDeriv_const (m : Nat) (q : Rat) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.const q) env V = 0 := by
  unfold evalDirectionalDeriv; rw [show (fun j => evalFlux (symPartial j (.const q)) env * V j) =
    (fun _ => 0) by funext j; simp [symPartial, evalFlux], sumTo_zero]

theorem evalDirectionalDeriv_param (m p : Nat) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.param p) env V = 0 := by
  unfold evalDirectionalDeriv; rw [show (fun j => evalFlux (symPartial j (.param p)) env * V j) =
    (fun _ => 0) by funext j; simp [symPartial, evalFlux], sumTo_zero]

theorem evalDirectionalDeriv_var (m i : Nat) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.var i) env V = if i < m then V i else 0 := by
  unfold evalDirectionalDeriv
  by_cases hi : i < m
  · simp only [hi, ↓reduceIte]
    rw [show sumTo m (fun j => evalFlux (symPartial j (.var i)) env * V j) =
        sumTo m (fun j => (if i = j then 1 else 0) * V j) from sumTo_congr fun j _ => by
      simp only [symPartial]; by_cases hij : i = j
      · subst hij; simp [evalFlux]
      · simp [hij, beq_false_of_ne hij, evalFlux], sumTo_delta m i hi V]
  · simp only [hi, ↓reduceIte]
    rw [show sumTo m (fun j => evalFlux (symPartial j (.var i)) env * V j) = sumTo m (fun _ => 0) from
      sumTo_congr fun j hj => by simp [symPartial, beq_false_of_ne (by omega : i ≠ j), evalFlux],
      sumTo_zero]

theorem evalDirectionalDeriv_neg (m : Nat) (a : FluxExpr) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.neg a) env V = -(evalDirectionalDeriv m a env V) := by
  unfold evalDirectionalDeriv
  rw [show (fun j => evalFlux (symPartial j (.neg a)) env * V j) =
      (fun j => (-1 : Rat) * (evalFlux (symPartial j a) env * V j)) by
    funext j; simp only [symPartial, evalFlux]; grind, sumTo_mul_left]; grind

theorem evalDirectionalDeriv_add (m : Nat) (a b : FluxExpr) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.add a b) env V =
      evalDirectionalDeriv m a env V + evalDirectionalDeriv m b env V := by
  unfold evalDirectionalDeriv; rw [← sumTo_add]
  exact sumTo_congr fun j _ => by simp only [symPartial, evalFlux]; grind

theorem evalDirectionalDeriv_sub (m : Nat) (a b : FluxExpr) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.sub a b) env V =
      evalDirectionalDeriv m a env V - evalDirectionalDeriv m b env V := by
  unfold evalDirectionalDeriv
  rw [show (fun j => evalFlux (symPartial j (.sub a b)) env * V j) =
      (fun j => evalFlux (symPartial j a) env * V j +
        (-1 : Rat) * (evalFlux (symPartial j b) env * V j)) by
    funext j; simp only [symPartial, evalFlux]; grind, sumTo_add, sumTo_mul_left]; grind

theorem evalDirectionalDeriv_mul (m : Nat) (a b : FluxExpr) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.mul a b) env V =
      evalDirectionalDeriv m a env V * evalFlux b env +
      evalFlux a env * evalDirectionalDeriv m b env V := by
  unfold evalDirectionalDeriv
  rw [show (fun j => evalFlux (symPartial j (.mul a b)) env * V j) =
      (fun j => evalFlux b env * (evalFlux (symPartial j a) env * V j) +
        evalFlux a env * (evalFlux (symPartial j b) env * V j)) by
    funext j; simp only [symPartial, evalFlux]; grind, sumTo_add, sumTo_mul_left, sumTo_mul_left]; grind

theorem evalDirectionalDeriv_invSafe (m : Nat) (d : FluxExpr) (env : FluxEnv) (V : Vec) :
    evalDirectionalDeriv m (.invSafe d) env V =
      -(evalDirectionalDeriv m d env V * (((1 : Rat) / evalFlux d env) * ((1 : Rat) / evalFlux d env))) := by
  unfold evalDirectionalDeriv
  rw [show (fun j => evalFlux (symPartial j (.invSafe d)) env * V j) =
      (fun j => (-(((1 : Rat) / evalFlux d env) * ((1 : Rat) / evalFlux d env))) *
        (evalFlux (symPartial j d) env * V j)) by
    funext j; simp only [symPartial, evalFlux]; grind, sumTo_mul_left]; grind

theorem rat_inv_taylor_identity (d0 d1 dd rd h : Rat)
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hdd : d1 - d0 = h * dd + (h * h) * rd) :
    (1 : Rat) / d1 - (1 : Rat) / d0 =
      h * (-(dd * (((1 : Rat) / d0) * ((1 : Rat) / d0)))) +
      (h * h) * ((dd * (dd + h * rd) - rd * d0) / (d0 * d0 * d1)) := by
  have hd021 : d0 * d0 * d1 ≠ 0 := rat_mul_ne_zero (rat_mul_ne_zero hd0 hd0) hd1
  apply rat_eq_of_mul_cancel hd021
  have hc0 : ((1 : Rat) / d0) * d0 = 1 := Rat.div_mul_cancel hd0
  have hc1 : ((1 : Rat) / d1) * d1 = 1 := Rat.div_mul_cancel hd1
  have hcRem : ((dd * (dd + h * rd) - rd * d0) / (d0 * d0 * d1)) * (d0 * d0 * d1) =
      dd * (dd + h * rd) - rd * d0 := Rat.div_mul_cancel hd021
  have hL1 : ((1 : Rat) / d1) * (d0 * d0 * d1) = d0 * d0 := by
    calc _ = (((1 : Rat) / d1) * d1) * (d0 * d0) := by grind
      _ = d0 * d0 := by rw [hc1]; grind
  have hL0 : ((1 : Rat) / d0) * (d0 * d0 * d1) = d0 * d1 := by
    calc _ = (((1 : Rat) / d0) * d0) * (d0 * d1) := by grind
      _ = d0 * d1 := by rw [hc0]; grind
  have hDer : (h * (-(dd * (((1 : Rat) / d0) * ((1 : Rat) / d0))))) * (d0 * d0 * d1) = -(h * dd * d1) := by
    calc _ = -(h * dd * d1 * (((1 : Rat) / d0) * d0) * (((1 : Rat) / d0) * d0)) := by grind
      _ = -(h * dd * d1) := by rw [hc0]; grind
  have hRem2 : ((h * h) * ((dd * (dd + h * rd) - rd * d0) / (d0 * d0 * d1))) * (d0 * d0 * d1) =
      (h * h) * (dd * (dd + h * rd) - rd * d0) := by
    calc _ = (h * h) * (((dd * (dd + h * rd) - rd * d0) / (d0 * d0 * d1)) * (d0 * d0 * d1)) := by grind
      _ = _ := by rw [hcRem]
  calc ((1 : Rat) / d1 - (1 : Rat) / d0) * (d0 * d0 * d1)
    _ = d0 * d0 - d0 * d1 := by rw [ ← hL1, ← hL0]; grind
    _ = -(h * dd * d1) + (h * h) * (dd * (dd + h * rd) - rd * d0) := by
        rw [show d1 = d0 + h * dd + (h * h) * rd by grind]; grind
    _ = _ := by rw [← hDer, ← hRem2]; grind

/-- **Exact Multivariable Fréchet Taylor Decomposition (`symExpr_frechet_taylor`)**:
For every guarded rational expression `e`, state perturbation `V`, and step `h` keeping
denominators non-zero, `e(U + h V) - e(U) = h · D_V e(U) + h² · R(U, V, h)`. -/
theorem symExpr_frechet_taylor (m : Nat) (e : FluxExpr) (env : FluxEnv) (V : Vec) (h : Rat)
    (hDen0 : DenomNonzero e env) (hDen1 : DenomNonzero e (shiftVecEnv m env h V)) :
    evalFlux e (shiftVecEnv m env h V) - evalFlux e env =
      h * evalDirectionalDeriv m e env V + (h * h) * symDirectionalRem m e env V h := by
  induction e with
  | const q => rw [evalDirectionalDeriv_const]; simp only [evalFlux, symDirectionalRem]; grind
  | param p => rw [evalDirectionalDeriv_param]; simp only [evalFlux, shiftVecEnv, symDirectionalRem]; grind
  | var i => rw [evalDirectionalDeriv_var]; simp only [evalFlux, shiftVecEnv, symDirectionalRem]; split <;> grind
  | neg a iha =>
    rw [evalDirectionalDeriv_neg]; have ha := iha hDen0 hDen1
    simp only [evalFlux, symDirectionalRem] at ha ⊢; grind
  | add a b iha ihb =>
    rw [evalDirectionalDeriv_add]; have ha := iha hDen0.1 hDen1.1; have hb := ihb hDen0.2 hDen1.2
    simp only [evalFlux, symDirectionalRem] at ha hb ⊢; grind
  | sub a b iha ihb =>
    rw [evalDirectionalDeriv_sub]; have ha := iha hDen0.1 hDen1.1; have hb := ihb hDen0.2 hDen1.2
    simp only [evalFlux, symDirectionalRem] at ha hb ⊢; grind
  | mul a b iha ihb =>
    rw [evalDirectionalDeriv_mul]; have ha := iha hDen0.1 hDen1.1; have hb := ihb hDen0.2 hDen1.2
    have ha1 : evalFlux a (shiftVecEnv m env h V) =
        evalFlux a env + h * evalDirectionalDeriv m a env V + (h * h) * symDirectionalRem m a env V h := by grind
    have hb1 : evalFlux b (shiftVecEnv m env h V) =
        evalFlux b env + h * evalDirectionalDeriv m b env V + (h * h) * symDirectionalRem m b env V h := by grind
    simp only [evalFlux, symDirectionalRem]; rw [ha1, hb1]; grind
  | invSafe d ihd =>
    rw [evalDirectionalDeriv_invSafe]; have hd := ihd hDen0.2 hDen1.2
    simp only [evalFlux, symDirectionalRem]
    exact rat_inv_taylor_identity _ _ _ _ h hDen0.1 hDen1.1 hd

theorem getOr_map_lt {α β : Type} (xs : List α) (f : α → β) (i : Nat) (da : α) (db : β)
    (hi : i < xs.length) : getOr (xs.map f) i db = f (getOr xs i da) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons _ xs ih => cases i with | zero => rfl | succ i => exact ih i (by simpa using hi)

theorem getOr_range_lt (m j d : Nat) (hj : j < m) : getOr (List.range m) j d = j := by
  have h1 : (List.range m)[j]? = some j := List.getElem?_range hj
  have h2 : ∀ (xs : List Nat) (k : Nat), xs[k]? = some j → getOr xs k d = j := by
    intro xs; induction xs with
    | nil => intro k hk; simp at hk
    | cons _ xs ih => intro k hk; cases k with | zero => simp at hk; exact hk | succ k => exact ih k (by simpa using hk)
  exact h2 (List.range m) j h1

/-- **Vector Jacobian Fréchet Theorem (`symJacobian_frechet_taylor`)**:
The symbolic Jacobian `symJacobian m flux` evaluated at `env` is the exact Fréchet derivative of
`flux`: for every component `i < m` (`flux.length = m`) and domain-valid perturbation `U + h V`,
`F_i(U + h V) - F_i(U) = h · (J(U) V)_i + h² · R_i(U, V, h)`. -/
theorem symJacobian_frechet_taylor (dom : List PosTarget) (m : Nat) (flux : List FluxExpr)
    (hLen : flux.length = m)
    (hSafe : ∀ i, i < m → checkExprDomainSafe dom (getOr flux i (.const 0)) = true)
    (env : FluxEnv) (V : Vec) (h : Rat)
    (hDom0 : DomainValid dom env) (hDom1 : DomainValid dom (shiftVecEnv m env h V))
    (i : Nat) (hi : i < m) :
    evalFlux (getOr flux i (.const 0)) (shiftVecEnv m env h V) -
      evalFlux (getOr flux i (.const 0)) env =
      h * mulVec m (evalSymJacobianMat (symJacobian m flux) env) V i +
      (h * h) * symDirectionalRem m (getOr flux i (.const 0)) env V h := by
  have hDen0 := checkExprDomainSafe_implies_denomNonzero dom _ env (hSafe i hi) hDom0
  have hDen1 := checkExprDomainSafe_implies_denomNonzero dom _ (shiftVecEnv m env h V) (hSafe i hi) hDom1
  rw [symExpr_frechet_taylor m (getOr flux i (.const 0)) env V h hDen0 hDen1]
  rw [show evalDirectionalDeriv m (getOr flux i (.const 0)) env V =
      mulVec m (evalSymJacobianMat (symJacobian m flux) env) V i from by
    unfold evalDirectionalDeriv mulVec evalSymJacobianMat symJacobian
    refine sumTo_congr fun j hj => ?_
    have hRow := getOr_map_lt flux (fun fi => (List.range m).map fun k => symPartial k fi)
      i (FluxExpr.const 0) ([] : List FluxExpr) (by omega)
    have hCol := getOr_map_lt (List.range m) (fun k => symPartial k (getOr flux i (FluxExpr.const 0)))
      j 0 (FluxExpr.const 0) (by simp [hj])
    rw [hRow, hCol, getOr_range_lt m j 0 hj]]

/-! ## 3. Reflective Multivariate Polynomial & Cleared-Denominator Rational Normalizer -/

abbrev Monomial := List (Nat × Nat)
abbrev CanonPoly := List (Monomial × Rat)

structure RatCanon where
  num : CanonPoly
  den : CanonPoly
  deriving DecidableEq, Repr

def evalMono (atomVal : Nat → Rat) : Monomial → Rat
  | [] => 1
  | (v, k) :: rest => (atomVal v) ^ k * evalMono atomVal rest

def evalCanonPoly (atomVal : Nat → Rat) : CanonPoly → Rat
  | [] => 0
  | (m, c) :: rest => c * evalMono atomVal m + evalCanonPoly atomVal rest

def lexLtMono : Monomial → Monomial → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | (v1, k1) :: r1, (v2, k2) :: r2 =>
    if v1 == v2 then (if k1 == k2 then lexLtMono r1 r2 else decide (k1 < k2))
    else decide (v1 < v2)

def mulMono : Monomial → Monomial → Monomial
  | [], m2 => m2
  | m1, [] => m1
  | (v1, k1) :: r1, (v2, k2) :: r2 =>
    if v1 < v2 then (v1, k1) :: mulMono r1 ((v2, k2) :: r2)
    else if v2 < v1 then (v2, k2) :: mulMono ((v1, k1) :: r1) r2
    else (v1, k1 + k2) :: mulMono r1 r2
termination_by m1 m2 => m1.length + m2.length

theorem rat_pow_add (x : Rat) (a b : Nat) : x ^ (a + b) = x ^ a * x ^ b := by
  induction b with
  | zero => simp [Rat.pow_zero]
  | succ b ih => rw [Nat.add_succ, Rat.pow_succ, ih, Rat.pow_succ]; grind

theorem evalMono_mulMono (atomVal : Nat → Rat) (m1 m2 : Monomial) :
    evalMono atomVal (mulMono m1 m2) = evalMono atomVal m1 * evalMono atomVal m2 := by
  match m1, m2 with
  | [], m2 => simp [mulMono, evalMono]
  | (v1, k1) :: r1, [] => simp [mulMono, evalMono]
  | (v1, k1) :: r1, (v2, k2) :: r2 =>
    simp only [mulMono]; split
    · simp only [evalMono, evalMono_mulMono atomVal r1 ((v2, k2) :: r2)]; grind
    · split
      · simp only [evalMono, evalMono_mulMono atomVal ((v1, k1) :: r1) r2]; grind
      · have hv : v1 = v2 := by omega
        subst hv; simp only [evalMono, rat_pow_add, evalMono_mulMono atomVal r1 r2]; grind
termination_by m1.length + m2.length

def polyConst (q : Rat) : CanonPoly := if q == 0 then [] else [([], q)]
def polyAtom (a : Nat) : CanonPoly := [([(a, 1)], 1)]
def polyNeg (p : CanonPoly) : CanonPoly := p.map fun (m, c) => (m, -c)

def polyAdd : CanonPoly → CanonPoly → CanonPoly
  | [], p2 => p2
  | p1, [] => p1
  | (m1, c1) :: r1, (m2, c2) :: r2 =>
    if m1 == m2 then
      let c := c1 + c2
      if c == 0 then polyAdd r1 r2 else (m1, c) :: polyAdd r1 r2
    else if lexLtMono m1 m2 then (m1, c1) :: polyAdd r1 ((m2, c2) :: r2)
    else (m2, c2) :: polyAdd ((m1, c1) :: r1) r2
termination_by p1 p2 => p1.length + p2.length

def polySub (p1 p2 : CanonPoly) : CanonPoly := polyAdd p1 (polyNeg p2)

def polyScaleTerm (m : Monomial) (c : Rat) : CanonPoly → CanonPoly
  | [] => []
  | (m2, c2) :: rest =>
    let prodC := c * c2
    if prodC == 0 then polyScaleTerm m c rest
    else polyAdd [(mulMono m m2, prodC)] (polyScaleTerm m c rest)

def polyMul : CanonPoly → CanonPoly → CanonPoly
  | [], _ => []
  | (m, c) :: rest, p2 => polyAdd (polyScaleTerm m c p2) (polyMul rest p2)

theorem evalCanonPoly_const (atomVal : Nat → Rat) (q : Rat) :
    evalCanonPoly atomVal (polyConst q) = q := by
  unfold polyConst; by_cases hq : q = 0
  · subst hq; simp [evalCanonPoly]
  · simp only [beq_false_of_ne hq, Bool.false_eq_true, ↓reduceIte, evalCanonPoly, evalMono]; grind

theorem evalCanonPoly_atom (atomVal : Nat → Rat) (a : Nat) :
    evalCanonPoly atomVal (polyAtom a) = atomVal a := by
  simp only [polyAtom, evalCanonPoly, evalMono, Rat.pow_succ, Rat.pow_zero]; grind

theorem evalCanonPoly_neg (atomVal : Nat → Rat) (p : CanonPoly) :
    evalCanonPoly atomVal (polyNeg p) = -(evalCanonPoly atomVal p) := by
  induction p with
  | nil => simp [polyNeg, evalCanonPoly]
  | cons mc rest ih =>
    rcases mc with ⟨m, c⟩
    change evalCanonPoly atomVal ((m, -c) :: polyNeg rest) = _
    simp only [evalCanonPoly]; rw [ih]; grind

theorem evalCanonPoly_add (atomVal : Nat → Rat) (p1 p2 : CanonPoly) :
    evalCanonPoly atomVal (polyAdd p1 p2) =
      evalCanonPoly atomVal p1 + evalCanonPoly atomVal p2 := by
  match p1, p2 with
  | [], p2 => simp only [polyAdd, evalCanonPoly]; grind
  | (m1, c1) :: r1, [] => simp only [polyAdd, evalCanonPoly]; grind
  | (m1, c1) :: r1, (m2, c2) :: r2 =>
    simp only [polyAdd]
    by_cases hm : m1 = m2
    · subst hm; simp only [beq_self_eq_true, ↓reduceIte]
      by_cases hc : c1 + c2 = 0
      · simp only [beq_iff_eq.mpr hc, ↓reduceIte, evalCanonPoly_add atomVal r1 r2, evalCanonPoly]; grind
      · simp only [beq_false_of_ne hc, Bool.false_eq_true, ↓reduceIte, evalCanonPoly,
          evalCanonPoly_add atomVal r1 r2]; grind
    · simp only [beq_false_of_ne hm, Bool.false_eq_true, ↓reduceIte]; split
      · simp only [evalCanonPoly, evalCanonPoly_add atomVal r1 ((m2, c2) :: r2)]; grind
      · simp only [evalCanonPoly, evalCanonPoly_add atomVal ((m1, c1) :: r1) r2]; grind
termination_by p1.length + p2.length

theorem evalCanonPoly_sub (atomVal : Nat → Rat) (p1 p2 : CanonPoly) :
    evalCanonPoly atomVal (polySub p1 p2) =
      evalCanonPoly atomVal p1 - evalCanonPoly atomVal p2 := by
  rw [polySub, evalCanonPoly_add, evalCanonPoly_neg]; grind

theorem evalCanonPoly_scaleTerm (atomVal : Nat → Rat) (m : Monomial) (c : Rat) (p : CanonPoly) :
    evalCanonPoly atomVal (polyScaleTerm m c p) =
      c * evalMono atomVal m * evalCanonPoly atomVal p := by
  induction p with
  | nil => simp [polyScaleTerm, evalCanonPoly]
  | cons mc rest ih =>
    rcases mc with ⟨m2, c2⟩; simp only [polyScaleTerm]
    by_cases hp : c * c2 = 0
    · simp only [beq_iff_eq.mpr hp, ↓reduceIte, ih, evalCanonPoly]
      have h0 : c * evalMono atomVal m * (c2 * evalMono atomVal m2) =
          (c * c2) * (evalMono atomVal m * evalMono atomVal m2) := by grind
      rw [hp] at h0; grind
    · simp only [beq_false_of_ne hp, Bool.false_eq_true, ↓reduceIte, evalCanonPoly_add, ih,
        evalCanonPoly, evalMono_mulMono]; grind

theorem evalCanonPoly_mul (atomVal : Nat → Rat) (p1 p2 : CanonPoly) :
    evalCanonPoly atomVal (polyMul p1 p2) =
      evalCanonPoly atomVal p1 * evalCanonPoly atomVal p2 := by
  induction p1 with
  | nil => simp [polyMul, evalCanonPoly]
  | cons mc rest ih =>
    rcases mc with ⟨m, c⟩
    simp only [polyMul, evalCanonPoly_add, evalCanonPoly_scaleTerm, ih, evalCanonPoly]; grind

def fluxAtomEnv (env : FluxEnv) (atom : Nat) : Rat :=
  if atom % 2 == 0 then env.state (atom / 2) else env.params (atom / 2)

def toRatCanon : FluxExpr → RatCanon
  | .const q => ⟨polyConst q, polyConst 1⟩
  | .var i => ⟨polyAtom (2 * i), polyConst 1⟩
  | .param p => ⟨polyAtom (2 * p + 1), polyConst 1⟩
  | .neg a => let ra := toRatCanon a; ⟨polyNeg ra.num, ra.den⟩
  | .add a b =>
    let ra := toRatCanon a; let rb := toRatCanon b
    ⟨polyAdd (polyMul ra.num rb.den) (polyMul rb.num ra.den), polyMul ra.den rb.den⟩
  | .sub a b =>
    let ra := toRatCanon a; let rb := toRatCanon b
    ⟨polySub (polyMul ra.num rb.den) (polyMul rb.num ra.den), polyMul ra.den rb.den⟩
  | .mul a b =>
    let ra := toRatCanon a; let rb := toRatCanon b
    ⟨polyMul ra.num rb.num, polyMul ra.den rb.den⟩
  | .invSafe d => let rd := toRatCanon d; ⟨rd.den, rd.num⟩

theorem rat_add_frac {n1 d1 n2 d2 : Rat} (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) :
    n1 / d1 + n2 / d2 = (n1 * d2 + n2 * d1) / (d1 * d2) := by
  have hd12 := rat_mul_ne_zero hd1 hd2
  apply rat_eq_of_mul_cancel hd12; rw [Rat.div_mul_cancel hd12]
  have hc1 := Rat.div_mul_cancel hd1 (a := n1); have hc2 := Rat.div_mul_cancel hd2 (a := n2)
  calc (n1 / d1 + n2 / d2) * (d1 * d2)
    _ = ((n1 / d1) * d1) * d2 + ((n2 / d2) * d2) * d1 := by grind
    _ = n1 * d2 + n2 * d1 := by rw [hc1, hc2]

theorem rat_sub_frac {n1 d1 n2 d2 : Rat} (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) :
    n1 / d1 - n2 / d2 = (n1 * d2 - n2 * d1) / (d1 * d2) := by
  have hd12 := rat_mul_ne_zero hd1 hd2
  apply rat_eq_of_mul_cancel hd12; rw [Rat.div_mul_cancel hd12]
  have hc1 := Rat.div_mul_cancel hd1 (a := n1); have hc2 := Rat.div_mul_cancel hd2 (a := n2)
  calc (n1 / d1 - n2 / d2) * (d1 * d2)
    _ = ((n1 / d1) * d1) * d2 - ((n2 / d2) * d2) * d1 := by grind
    _ = n1 * d2 - n2 * d1 := by rw [hc1, hc2]

theorem rat_mul_frac {n1 d1 n2 d2 : Rat} (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) :
    (n1 / d1) * (n2 / d2) = (n1 * n2) / (d1 * d2) := by
  have hd12 := rat_mul_ne_zero hd1 hd2
  apply rat_eq_of_mul_cancel hd12; rw [Rat.div_mul_cancel hd12]
  have hc1 := Rat.div_mul_cancel hd1 (a := n1); have hc2 := Rat.div_mul_cancel hd2 (a := n2)
  calc ((n1 / d1) * (n2 / d2)) * (d1 * d2)
    _ = ((n1 / d1) * d1) * ((n2 / d2) * d2) := by grind
    _ = n1 * n2 := by rw [hc1, hc2]

theorem rat_inv_frac {n d : Rat} (hn : n ≠ 0) (hd : d ≠ 0) :
    (1 : Rat) / (n / d) = d / n := by
  have hnd : n / d ≠ 0 := fun hz => by
    have hc := Rat.div_mul_cancel hd (a := n); rw [hz] at hc; simp at hc; exact hn hc.symm
  apply rat_eq_of_mul_cancel hnd; rw [Rat.div_mul_cancel hnd]
  apply rat_eq_of_mul_cancel hd
  have hdn := Rat.div_mul_cancel hn (a := d); have hnd2 := Rat.div_mul_cancel hd (a := n)
  calc (1 : Rat) * d = (d / n) * n := by rw [hdn]; grind
    _ = ((d / n) * (n / d)) * d := by rw [← hnd2]; grind

theorem toRatCanon_sound (e : FluxExpr) (env : FluxEnv) (hDen : DenomNonzero e env) :
    evalCanonPoly (fluxAtomEnv env) (toRatCanon e).den ≠ 0 ∧
    evalFlux e env =
      evalCanonPoly (fluxAtomEnv env) (toRatCanon e).num /
      evalCanonPoly (fluxAtomEnv env) (toRatCanon e).den := by
  induction e with
  | const q =>
    refine ⟨by simp [toRatCanon, evalCanonPoly_const], ?_⟩
    simp [toRatCanon, evalCanonPoly_const, evalFlux, rat_div_one]
  | var i =>
    have hatom : fluxAtomEnv env (2 * i) = env.state i := by
      unfold fluxAtomEnv; simp [show (2 * i) % 2 = 0 by omega, show (2 * i) / 2 = i by omega]
    refine ⟨by simp [toRatCanon, evalCanonPoly_const], ?_⟩
    simp [toRatCanon, evalCanonPoly_atom, evalCanonPoly_const, hatom, evalFlux, rat_div_one]
  | param p =>
    have hatom : fluxAtomEnv env (2 * p + 1) = env.params p := by
      unfold fluxAtomEnv; simp [show (2 * p + 1) % 2 = 1 by omega, show (2 * p + 1) / 2 = p by omega]
    refine ⟨by simp [toRatCanon, evalCanonPoly_const], ?_⟩
    simp [toRatCanon, evalCanonPoly_atom, evalCanonPoly_const, hatom, evalFlux, rat_div_one]
  | neg a iha =>
    obtain ⟨hda, hea⟩ := iha hDen
    refine ⟨hda, ?_⟩; simp only [toRatCanon, evalCanonPoly_neg, evalFlux, hea]
    apply rat_eq_of_mul_cancel hda
    have hc1 := Rat.div_mul_cancel hda (a := evalCanonPoly (fluxAtomEnv env) (toRatCanon a).num)
    have hc2 := Rat.div_mul_cancel hda (a := -(evalCanonPoly (fluxAtomEnv env) (toRatCanon a).num))
    grind
  | add a b iha ihb =>
    obtain ⟨hda, hea⟩ := iha hDen.1; obtain ⟨hdb, heb⟩ := ihb hDen.2
    exact ⟨by rw [toRatCanon, evalCanonPoly_mul]; exact rat_mul_ne_zero hda hdb,
      by simp only [toRatCanon, evalCanonPoly_add, evalCanonPoly_mul, evalFlux, hea, heb]; exact rat_add_frac hda hdb⟩
  | sub a b iha ihb =>
    obtain ⟨hda, hea⟩ := iha hDen.1; obtain ⟨hdb, heb⟩ := ihb hDen.2
    exact ⟨by rw [toRatCanon, evalCanonPoly_mul]; exact rat_mul_ne_zero hda hdb,
      by simp only [toRatCanon, evalCanonPoly_sub, evalCanonPoly_mul, evalFlux, hea, heb]; exact rat_sub_frac hda hdb⟩
  | mul a b iha ihb =>
    obtain ⟨hda, hea⟩ := iha hDen.1; obtain ⟨hdb, heb⟩ := ihb hDen.2
    exact ⟨by rw [toRatCanon, evalCanonPoly_mul]; exact rat_mul_ne_zero hda hdb,
      by simp only [toRatCanon, evalCanonPoly_mul, evalFlux, hea, heb]; exact rat_mul_frac hda hdb⟩
  | invSafe d ihd =>
    obtain ⟨hdd, hed⟩ := ihd hDen.2
    have hnd : evalCanonPoly (fluxAtomEnv env) (toRatCanon d).num ≠ 0 := fun hz => by
      have h0 : evalFlux d env = 0 := by
        rw [hed, hz]; exact rat_eq_of_mul_cancel hdd (by rw [Rat.div_mul_cancel hdd]; simp)
      exact hDen.1 h0
    exact ⟨hnd, by simp only [toRatCanon, evalFlux, hed]; exact rat_inv_frac hnd hdd⟩

/-- Executable reflective equality decider for guarded rational `FluxExpr`s. -/
def checkFluxEqReflective (dom : List PosTarget) (e1 e2 : FluxExpr) : Bool :=
  checkExprDomainSafe dom e1 &&
  checkExprDomainSafe dom e2 &&
  let r1 := toRatCanon e1; let r2 := toRatCanon e2
  (polySub (polyMul r1.num r2.den) (polyMul r2.num r1.den)).isEmpty

/-- **Reflective Rational Normalizer Soundness (`checkFluxEqReflective_sound`)**:
When `checkFluxEqReflective dom e1 e2 = true`, `evalFlux e1 env = evalFlux e2 env` holds at every
domain-valid assignment `env`. -/
theorem checkFluxEqReflective_sound (dom : List PosTarget) (e1 e2 : FluxExpr)
    (hCheck : checkFluxEqReflective dom e1 e2 = true) :
    ∀ env : FluxEnv, DomainValid dom env → evalFlux e1 env = evalFlux e2 env := by
  unfold checkFluxEqReflective at hCheck
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hCheck
  obtain ⟨⟨hs1, hs2⟩, hCross⟩ := hCheck
  intro env hDom
  obtain ⟨hden1, hev1⟩ := toRatCanon_sound e1 env
    (checkExprDomainSafe_implies_denomNonzero dom e1 env hs1 hDom)
  obtain ⟨hden2, hev2⟩ := toRatCanon_sound e2 env
    (checkExprDomainSafe_implies_denomNonzero dom e2 env hs2 hDom)
  have hCrossZero : evalCanonPoly (fluxAtomEnv env)
      (polySub (polyMul (toRatCanon e1).num (toRatCanon e2).den)
               (polyMul (toRatCanon e2).num (toRatCanon e1).den)) = 0 := by rw [hCross]; rfl
  rw [evalCanonPoly_sub, evalCanonPoly_mul, evalCanonPoly_mul] at hCrossZero
  rw [hev1, hev2]
  apply rat_eq_of_mul_cancel hden1
  apply rat_eq_of_mul_cancel hden2
  have hc1 := Rat.div_mul_cancel hden1 (a := evalCanonPoly (fluxAtomEnv env) (toRatCanon e1).num)
  have hc2 := Rat.div_mul_cancel hden2 (a := evalCanonPoly (fluxAtomEnv env) (toRatCanon e2).num)
  calc _ = evalCanonPoly (fluxAtomEnv env) (toRatCanon e1).num *
           evalCanonPoly (fluxAtomEnv env) (toRatCanon e2).den := by rw [hc1]
    _ = evalCanonPoly (fluxAtomEnv env) (toRatCanon e2).num *
        evalCanonPoly (fluxAtomEnv env) (toRatCanon e1).den := by grind
    _ = evalCanonPoly (fluxAtomEnv env) (toRatCanon e1).den *
        ((evalCanonPoly (fluxAtomEnv env) (toRatCanon e2).num /
          evalCanonPoly (fluxAtomEnv env) (toRatCanon e2).den) *
         evalCanonPoly (fluxAtomEnv env) (toRatCanon e2).den) := by rw [hc2]; grind
    _ = _ := by grind

example : checkFluxEqReflective [.stateVar 0]
    (.mul (.var 0) (.invSafe (.var 0))) (.const 1) = true := by decide +kernel

/-! ## 4. Nonlinear Fluctuations, Generic 2nd-Order `minmod` TVD & Tadmor Entropy Decay -/

theorem nextCell_prevCell (N i : Nat) (hN : 0 < N) (hi : i < N) :
    nextCell N (prevCell N i) = i := by
  unfold prevCell nextCell
  by_cases h0 : i = 0
  · subst h0; simp [show N - 1 + 1 = N by omega]
  · simp [h0, show i - 1 + 1 = i by omega, show ¬ (i = N) by omega]

theorem prevCell_nextCell (N i : Nat) :
    prevCell N (nextCell N i) = i := by
  unfold nextCell prevCell; by_cases h1 : i + 1 = N <;> simp [h1] <;> omega

def shiftStateVars (offset : Nat) : FluxExpr → FluxExpr
  | .const q => .const q
  | .var i => .var (offset + i)
  | .param p => .param p
  | .neg a => .neg (shiftStateVars offset a)
  | .add a b => .add (shiftStateVars offset a) (shiftStateVars offset b)
  | .sub a b => .sub (shiftStateVars offset a) (shiftStateVars offset b)
  | .mul a b => .mul (shiftStateVars offset a) (shiftStateVars offset b)
  | .invSafe d => .invSafe (shiftStateVars offset d)

def twoStateEnv (m : Nat) (params : Nat → Rat) (uL uR : Vec) : FluxEnv where
  state := fun i => if i < m then uL i else uR (i - m)
  params := params

theorem evalFlux_shiftStateVars_right (m : Nat) (params : Nat → Rat) (uL uR : Vec) (e : FluxExpr) :
    evalFlux (shiftStateVars m e) (twoStateEnv m params uL uR) = evalFlux e ⟨uR, params⟩ := by
  induction e with
  | const _ | param _ => rfl
  | var i =>
    simp only [shiftStateVars, evalFlux, twoStateEnv]
    simp [show ¬ (m + i < m) by omega, show (m + i) - m = i by omega]
  | neg a iha => simp [shiftStateVars, evalFlux, iha]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | invSafe a iha =>
    simp_all [shiftStateVars, evalFlux]

/-- Nonlinear Rusanov / Lax–Friedrichs numerical flux:
`F̂(U_L, U_R) = 1/2 (F(U_L) + F(U_R)) - (λ_max / 2) (U_R - U_L)`. -/
def rusanovNonlinearFlux (flux : List FluxExpr) (params : Nat → Rat) (aMax : Rat)
    (uL uR : Vec) : Vec := fun i =>
  let fL := evalFlux (getOr flux i (.const 0)) ⟨uL, params⟩
  let fR := evalFlux (getOr flux i (.const 0)) ⟨uR, params⟩
  (1 / 2 : Rat) * (fL + fR) - (aMax / 2) * (uR i - uL i)

def rusanovFluctMinus (flux : List FluxExpr) (params : Nat → Rat) (aMax : Rat)
    (uL uR : Vec) : Vec :=
  fun i => rusanovNonlinearFlux flux params aMax uL uR i - evalFlux (getOr flux i (.const 0)) ⟨uL, params⟩

def rusanovFluctPlus (flux : List FluxExpr) (params : Nat → Rat) (aMax : Rat)
    (uL uR : Vec) : Vec :=
  fun i => evalFlux (getOr flux i (.const 0)) ⟨uR, params⟩ - rusanovNonlinearFlux flux params aMax uL uR i

theorem rusanovNonlinearFlux_consistent (flux : List FluxExpr) (params : Nat → Rat)
    (aMax : Rat) (u : Vec) (i : Nat) :
    rusanovNonlinearFlux flux params aMax u u i = evalFlux (getOr flux i (.const 0)) ⟨u, params⟩ := by
  simp only [rusanovNonlinearFlux]; grind

theorem rusanovFluct_conservation (flux : List FluxExpr) (params : Nat → Rat)
    (aMax : Rat) (uL uR : Vec) (i : Nat) :
    rusanovFluctMinus flux params aMax uL uR i + rusanovFluctPlus flux params aMax uL uR i =
      evalFlux (getOr flux i (.const 0)) ⟨uR, params⟩ -
      evalFlux (getOr flux i (.const 0)) ⟨uL, params⟩ ∧
    rusanovFluctMinus flux params aMax uL uL i = 0 ∧
    rusanovFluctPlus flux params aMax uL uL i = 0 := by
  simp only [rusanovFluctMinus, rusanovFluctPlus, rusanovNonlinearFlux]
  exact ⟨by grind, by grind, by grind⟩

def musclReconstructLeft (uPrev uCurr uNext : Rat) : Rat :=
  uCurr - (1 / 2 : Rat) * minmod (uCurr - uPrev) (uNext - uCurr)

def musclReconstructRight (uPrev uCurr uNext : Rat) : Rat :=
  uCurr + (1 / 2 : Rat) * minmod (uCurr - uPrev) (uNext - uCurr)

/-- 2nd-order linearity preservation on `u_0 - s, u_0, u_0 + s` for positive OR negative `s`. -/
theorem muscl_minmod_linear_exact (u0 s : Rat) :
    musclReconstructLeft (u0 - s) u0 (u0 + s) = u0 - (1 / 2 : Rat) * s ∧
    musclReconstructRight (u0 - s) u0 (u0 + s) = u0 + (1 / 2 : Rat) * s := by
  simp [musclReconstructLeft, musclReconstructRight,
    show u0 - (u0 - s) = s by grind, show (u0 + s) - u0 = s by grind, minmod_self]

theorem muscl_minmod_mirror_symm (uPrev uCurr uNext : Rat) :
    musclReconstructLeft uNext uCurr uPrev = musclReconstructRight uPrev uCurr uNext := by
  unfold musclReconstructLeft musclReconstructRight
  rw [show uCurr - uNext = -(uNext - uCurr) by grind,
      show uPrev - uCurr = -(uCurr - uPrev) by grind, minmod_neg, minmod_comm]; grind

def totalVariation1D (N : Nat) (u : Nat → Rat) : Rat :=
  sumTo N fun i => ratAbs (u (nextCell N i) - u i)

theorem ratAbs_neg (x : Rat) : ratAbs (-x) = ratAbs x := by unfold ratAbs; split <;> split <;> grind
theorem ratAbs_add_le (x y : Rat) : ratAbs (x + y) ≤ ratAbs x + ratAbs y := by
  unfold ratAbs; (repeat' split) <;> grind
theorem ratAbs_of_nonneg {x : Rat} (hx : 0 ≤ x) : ratAbs x = x := by unfold ratAbs; split <;> grind
theorem ratAbs_bounds_iff {x M : Rat} :
    ratAbs x ≤ M ↔ (-M ≤ x ∧ x ≤ M) := by unfold ratAbs; split <;> grind

/-- **Harten's Incremental TVD Theorem (`harten_incremental_tvd`)**:
Any periodic update `u'_i = u_i + C_i (u_{i+1} - u_i) - D_{i-1} (u_i - u_{i-1})` with
`0 ≤ C_i`, `0 ≤ D_i`, and `C_i + D_i ≤ 1` is Total-Variation Diminishing (`TV(u') ≤ TV(u)`). -/
theorem harten_incremental_tvd (N : Nat) (u : Nat → Rat) (C D : Nat → Rat)
    (hC : ∀ i, 0 ≤ C i) (hD : ∀ i, 0 ≤ D i) (hCD : ∀ i, C i + D i ≤ 1) :
    let u' : Nat → Rat := fun i =>
      u i + C i * (u (nextCell N i) - u i) - D (prevCell N i) * (u i - u (prevCell N i))
    totalVariation1D N u' ≤ totalVariation1D N u := by
  intro u'
  cases N with
  | zero => simp [totalVariation1D, sumTo]
  | succ n =>
    let N := n + 1
    have hBound : ∀ i, i < N →
        ratAbs (u' (nextCell N i) - u' i) ≤
          (1 - C i - D i) * ratAbs (u (nextCell N i) - u i) +
          C (nextCell N i) * ratAbs (u (nextCell N (nextCell N i)) - u (nextCell N i)) +
          D (prevCell N i) * ratAbs (u i - u (prevCell N i)) := by
      intro i hi
      rw [show u' (nextCell N i) - u' i =
          ((1 - C i - D i) * (u (nextCell N i) - u i) +
            C (nextCell N i) * (u (nextCell N (nextCell N i)) - u (nextCell N i))) +
          D (prevCell N i) * (u i - u (prevCell N i)) by
        dsimp only [u']; rw [prevCell_nextCell N i]; grind]
      have htri1 := ratAbs_add_le
        ((1 - C i - D i) * (u (nextCell N i) - u i) +
          C (nextCell N i) * (u (nextCell N (nextCell N i)) - u (nextCell N i)))
        (D (prevCell N i) * (u i - u (prevCell N i)))
      have htri2 := ratAbs_add_le
        ((1 - C i - D i) * (u (nextCell N i) - u i))
        (C (nextCell N i) * (u (nextCell N (nextCell N i)) - u (nextCell N i)))
      have hm1 : ratAbs ((1 - C i - D i) * (u (nextCell N i) - u i)) =
          (1 - C i - D i) * ratAbs (u (nextCell N i) - u i) := by
        rw [ratAbs_mul, ratAbs_of_nonneg (by have := hCD i; grind)]
      have hm2 : ratAbs (C (nextCell N i) * (u (nextCell N (nextCell N i)) - u (nextCell N i))) =
          C (nextCell N i) * ratAbs (u (nextCell N (nextCell N i)) - u (nextCell N i)) := by
        rw [ratAbs_mul, ratAbs_of_nonneg (hC (nextCell N i))]
      have hm3 : ratAbs (D (prevCell N i) * (u i - u (prevCell N i))) =
          D (prevCell N i) * ratAbs (u i - u (prevCell N i)) := by
        rw [ratAbs_mul, ratAbs_of_nonneg (hD (prevCell N i))]
      rw [hm3] at htri1; rw [hm1, hm2] at htri2; grind
    unfold totalVariation1D
    have hSumLe := sumTo_le hBound
    have hShiftPrev :
        sumTo N (fun i => D (prevCell N i) * ratAbs (u i - u (prevCell N i))) =
        sumTo N (fun i => D i * ratAbs (u (nextCell N i) - u i)) := by
      rw [show sumTo N (fun i => D (prevCell N i) * ratAbs (u i - u (prevCell N i))) =
          sumTo N (fun i => D (prevCell N i) * ratAbs (u (nextCell N (prevCell N i)) - u (prevCell N i))) from
        sumTo_congr fun i hi => by rw [nextCell_prevCell N i (by omega) hi]]
      exact sumTo_prev N (fun j => D j * ratAbs (u (nextCell N j) - u j))
    rw [sumTo_add, sumTo_add, sumTo_next N (fun j => C j * ratAbs (u (nextCell N j) - u j)),
        hShiftPrev, ← sumTo_add, ← sumTo_add] at hSumLe
    rw [show sumTo N (fun i =>
          (1 - C i - D i) * ratAbs (u (nextCell N i) - u i) +
          C i * ratAbs (u (nextCell N i) - u i) +
          D i * ratAbs (u (nextCell N i) - u i)) =
        sumTo N (fun i => ratAbs (u (nextCell N i) - u i)) from
      sumTo_congr fun i _ => by grind] at hSumLe
    exact hSumLe

/-- 2nd-order MUSCL-`minmod` Rusanov 1D step for a scalar nonlinear flux `f`. -/
def musclMinmodRusanov1DStep (f : Rat → Rat) (aMax ν : Rat) (N : Nat) (u : Nat → Rat) :
    Nat → Rat :=
  let slope := fun j => minmod (u j - u (prevCell N j)) (u (nextCell N j) - u j)
  let uFaceL := fun j => u j + (1 / 2 : Rat) * slope j
  let uFaceR := fun j => u (nextCell N j) - (1 / 2 : Rat) * slope (nextCell N j)
  let numFlux := fun j =>
    (1 / 2 : Rat) * (f (uFaceL j) + f (uFaceR j)) - (aMax / 2) * (uFaceR j - uFaceL j)
  fun i => u i - ν * (numFlux i - numFlux (prevCell N i))

def minmodRatio (a b : Rat) : Rat := if b == 0 then 0 else minmod a b / b

theorem minmodRatio_bounds (a b : Rat) :
    0 ≤ minmodRatio a b ∧ minmodRatio a b ≤ 1 ∧ minmod a b = minmodRatio a b * b := by
  unfold minmodRatio
  by_cases hb : b = 0
  · subst hb; simp only [beq_self_eq_true, ↓reduceIte, minmod_sign_change a 0 (by grind)]
    exact ⟨by decide, by decide, by grind⟩
  · simp only [beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte]
    have htvd := minmod_tvd a b
    have heq : minmod a b = (minmod a b / b) * b := (Rat.div_mul_cancel hb).symm
    have hbb_pos : 0 < b * b := by
      have hnn := Interval.rat_sq_nonneg b; have hne := rat_mul_ne_zero hb hb; grind
    have hprod1 : (minmod a b / b) * (b * b) = minmod a b * b := by
      calc _ = ((minmod a b / b) * b) * b := by grind
        _ = minmod a b * b := by rw [← heq]
    refine ⟨?_, ?_, heq⟩
    · by_cases h0 : 0 ≤ minmod a b / b; · exact h0
      · have := Rat.mul_lt_mul_of_pos_right (by grind : minmod a b / b < 0) hbb_pos; grind
    · by_cases h1 : minmod a b / b ≤ 1; · exact h1
      · have := Rat.mul_lt_mul_of_pos_right (by grind : 1 < minmod a b / b) hbb_pos; grind

theorem minmodRatio_left_bounds (a b : Rat) :
    ∃ r : Rat, 0 ≤ r ∧ r ≤ 1 ∧ minmod a b = r * a := by
  rw [minmod_comm]
  exact ⟨minmodRatio b a, (minmodRatio_bounds b a).1, (minmodRatio_bounds b a).2.1,
    (minmodRatio_bounds b a).2.2⟩

theorem lip_half_shift_mono (aMax df dx : Rat) (haMax : 0 ≤ aMax)
    (hL : ratAbs df ≤ aMax * ratAbs dx) :
    0 ≤ ((1 / 2 : Rat) * (df + aMax * dx)) * dx ∧
    ratAbs ((1 / 2 : Rat) * (df + aMax * dx)) ≤ aMax * ratAbs dx := by
  have hM : 0 ≤ aMax * ratAbs dx := Rat.mul_nonneg haMax (ratAbs_nonneg dx)
  obtain ⟨hlo, hhi⟩ := ratAbs_bounds_iff.mp hL
  by_cases hdx : 0 ≤ dx
  · rw [ratAbs_of_nonneg hdx] at hlo hhi hM ⊢
    have hg0 : 0 ≤ (1 / 2 : Rat) * (df + aMax * dx) := by grind
    exact ⟨Rat.mul_nonneg hg0 hdx, by rw [ratAbs_of_nonneg hg0]; grind⟩
  · have hdxn : 0 ≤ -dx := by grind
    have habs : ratAbs dx = -dx := by unfold ratAbs; split <;> grind
    rw [habs] at hlo hhi hM ⊢
    have hgn : 0 ≤ -((1 / 2 : Rat) * (df + aMax * dx)) := by grind
    have hprod := Rat.mul_nonneg hgn hdxn
    exact ⟨by grind, by rw [← ratAbs_neg ((1 / 2 : Rat) * (df + aMax * dx)), ratAbs_of_nonneg hgn]; grind⟩

theorem harten_coeff_quot_bounds (ν aMax γ num Δ : Rat)
    (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (hΔ : Δ ≠ 0)
    (hMono : 0 ≤ num * (γ * Δ))
    (hLip : ratAbs num ≤ aMax * ratAbs (γ * Δ)) :
    0 ≤ (ν * num) / Δ ∧ (ν * num) / Δ ≤ ν * aMax * γ := by
  have hΔ2_pos : 0 < Δ * Δ := by
    have hnn := Interval.rat_sq_nonneg Δ; have hne := rat_mul_ne_zero hΔ hΔ; grind
  have hNonneg : 0 ≤ (ν * num) / Δ := by
    by_cases h0 : 0 ≤ (ν * num) / Δ
    · exact h0
    · have hm1 := Rat.mul_lt_mul_of_pos_right (by grind : (ν * num) / Δ < 0) hΔ2_pos
      have hcanc : ((ν * num) / Δ) * (Δ * Δ) = (ν * num) * Δ := by
        calc _ = (((ν * num) / Δ) * Δ) * Δ := by grind
          _ = (ν * num) * Δ := by rw [Rat.div_mul_cancel hΔ]
      rw [hcanc] at hm1
      by_cases hg0 : γ = 0
      · subst hg0
        have hr0 : ratAbs (0 * Δ) = 0 := by simp [ratAbs]
        rw [hr0, Rat.mul_zero] at hLip
        have hz : num = 0 := by unfold ratAbs at hLip; split at hLip <;> grind
        rw [hz] at hm1; simp at hm1
      · have hprod := Rat.mul_nonneg hν hMono
        have hneg := Rat.mul_lt_mul_of_pos_left hm1 (by grind : 0 < γ)
        grind
  refine ⟨hNonneg, ?_⟩
  have habsΔ : 0 < ratAbs Δ := by unfold ratAbs; split <;> grind
  have hbound : ((ν * num) / Δ) * ratAbs Δ ≤ (ν * aMax * γ) * ratAbs Δ := by
    have heqabs : ratAbs (((ν * num) / Δ) * Δ) = ((ν * num) / Δ) * ratAbs Δ := by
      rw [ratAbs_mul, ratAbs_of_nonneg hNonneg]
    rw [Rat.div_mul_cancel hΔ] at heqabs
    rw [← heqabs, ratAbs_mul, ratAbs_of_nonneg hν]
    have h1 := Rat.mul_le_mul_of_nonneg_left hLip hν
    rw [ratAbs_mul, ratAbs_of_nonneg hγ] at h1; grind
  by_cases hle : (ν * num) / Δ ≤ ν * aMax * γ
  · exact hle
  · have := Rat.mul_lt_mul_of_pos_right (by grind : ν * aMax * γ < (ν * num) / Δ) habsΔ; grind

/-- **Nonlinear 2nd-Order MUSCL-`minmod` Rusanov TVD Theorem (`tvd_rusanov_minmod_step_nonincreasing`)**:
For *every* nonlinear scalar flux `f` satisfying `|f(y) - f(x)| ≤ aMax * |y - x|` (`0 ≤ aMax`),
under `0 ≤ ν` and `2 * ν * aMax ≤ 1`, 2nd-order MUSCL-`minmod` Rusanov is Total-Variation Diminishing. -/
theorem tvd_rusanov_minmod_step_nonincreasing (f : Rat → Rat) (aMax ν : Rat)
    (haMax : 0 ≤ aMax) (hν : 0 ≤ ν) (hcfl : 2 * ν * aMax ≤ 1)
    (hLip : ∀ x y : Rat, ratAbs (f y - f x) ≤ aMax * ratAbs (y - x))
    (N : Nat) (u : Nat → Rat) :
    totalVariation1D N (musclMinmodRusanov1DStep f aMax ν N u) ≤ totalVariation1D N u := by
  let fPlus := fun x => (1 / 2 : Rat) * (f x + aMax * x)
  let fMinus := fun x => (1 / 2 : Rat) * (f x - aMax * x)
  have hfPlus : ∀ x y : Rat, 0 ≤ (fPlus y - fPlus x) * (y - x) ∧
      ratAbs (fPlus y - fPlus x) ≤ aMax * ratAbs (y - x) := fun x y => by
    simpa [show fPlus y - fPlus x = (1 / 2 : Rat) * ((f y - f x) + aMax * (y - x)) by grind] using
      lip_half_shift_mono aMax (f y - f x) (y - x) haMax (hLip x y)
  have hfMinus : ∀ x y : Rat, 0 ≤ (-(fMinus y - fMinus x)) * (y - x) ∧
      ratAbs (-(fMinus y - fMinus x)) ≤ aMax * ratAbs (y - x) := fun x y => by
    have hLneg : ratAbs (-(f y - f x)) ≤ aMax * ratAbs (y - x) := by rw [ratAbs_neg]; exact hLip x y
    simpa [show -(fMinus y - fMinus x) = (1 / 2 : Rat) * (-(f y - f x) + aMax * (y - x)) by grind] using
      lip_half_shift_mono aMax (-(f y - f x)) (y - x) haMax hLneg
  cases N with
  | zero => simp [totalVariation1D, sumTo]
  | succ n =>
    let N := n + 1
    let slope := fun j => minmod (u j - u (prevCell N j)) (u (nextCell N j) - u j)
    let uFaceL := fun j => u j + (1 / 2 : Rat) * slope j
    let uFaceR := fun j => u (nextCell N j) - (1 / 2 : Rat) * slope (nextCell N j)
    let Δ := fun j => u (nextCell N j) - u j
    let C := fun j =>
      if Δ j == 0 then 0 else (ν * (-(fMinus (uFaceR j) - fMinus (uFaceR (prevCell N j))))) / Δ j
    let D := fun j =>
      if Δ j == 0 then 0 else (ν * (fPlus (uFaceL (nextCell N j)) - fPlus (uFaceL j))) / Δ j
    have hAlphaBeta : ∀ j, j < N →
        ∃ α β : Rat, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 2 ∧
          uFaceL (nextCell N j) - uFaceL j = α * Δ j ∧
          uFaceR j - uFaceR (prevCell N j) = β * Δ j := by
      intro j hj
      have r1 := minmodRatio_bounds (u j - u (prevCell N j)) (Δ j)
      obtain ⟨r2, hr2_0, hr2_1, hr2_eq⟩ := minmodRatio_left_bounds
        (u (nextCell N j) - u (prevCell N (nextCell N j)))
        (u (nextCell N (nextCell N j)) - u (nextCell N j))
      let q1 := minmodRatio (u j - u (prevCell N j)) (Δ j)
      have hs1 : slope j = q1 * Δ j := r1.2.2
      have hs2 : slope (nextCell N j) = r2 * Δ j := by
        dsimp only [slope, Δ]; rw [prevCell_nextCell N j] at hr2_eq ⊢; exact hr2_eq
      refine ⟨1 + (1 / 2 : Rat) * r2 - (1 / 2 : Rat) * q1,
              1 + (1 / 2 : Rat) * q1 - (1 / 2 : Rat) * r2,
              by have := r1.1; have := r1.2.1; grind,
              by have := r1.1; have := r1.2.1; grind, by grind, ?_, ?_⟩
      · dsimp only [uFaceL]; rw [hs1, hs2]; grind
      · dsimp only [uFaceR]; rw [nextCell_prevCell N j (by omega) hj, hs1, hs2]; grind
    have hCD_bounds : ∀ j, j < N → 0 ≤ C j ∧ 0 ≤ D j ∧ C j + D j ≤ 1 := by
      intro j hj
      obtain ⟨α, β, hα0, hβ0, hsum2, hFaceL, hFaceR⟩ := hAlphaBeta j hj
      by_cases hΔ : Δ j = 0
      · dsimp only [C, D]; rw [beq_iff_eq.mpr hΔ]; simp only [↓reduceIte]; exact ⟨Rat.le_refl, Rat.le_refl, by grind⟩
      · simp only [C, D, beq_false_of_ne hΔ, Bool.false_eq_true, ↓reduceIte]
        have hmC := hfMinus (uFaceR (prevCell N j)) (uFaceR j); rw [hFaceR] at hmC
        have hmD := hfPlus (uFaceL j) (uFaceL (nextCell N j)); rw [hFaceL] at hmD
        have hCb := harten_coeff_quot_bounds ν aMax β _ (Δ j) hν hβ0 hΔ hmC.1 hmC.2
        have hDb := harten_coeff_quot_bounds ν aMax α _ (Δ j) hν hα0 hΔ hmD.1 hmD.2
        refine ⟨hCb.1, hDb.1, ?_⟩
        calc _ ≤ ν * aMax * (α + β) := by grind
          _ = 2 * ν * aMax := by rw [hsum2]; grind
          _ ≤ 1 := hcfl
    let C' := fun j => if j < N then C j else 0
    let D' := fun j => if j < N then D j else 0
    have hC' : ∀ j, 0 ≤ C' j := fun j => by
      simp only [C']; split
      · exact (hCD_bounds j ‹_›).1
      · exact Rat.le_refl
    have hD' : ∀ j, 0 ≤ D' j := fun j => by
      simp only [D']; split
      · exact (hCD_bounds j ‹_›).2.1
      · exact Rat.le_refl
    have hCD' : ∀ j, C' j + D' j ≤ 1 := fun j => by
      simp only [C', D']; split
      · exact (hCD_bounds j ‹_›).2.2
      · grind
    have hStepEq : ∀ i, i < N →
        musclMinmodRusanov1DStep f aMax ν N u i =
          u i + C' i * (u (nextCell N i) - u i) - D' (prevCell N i) * (u i - u (prevCell N i)) := by
      intro i hi
      have hprev_lt : prevCell N i < N := by unfold prevCell; split <;> omega
      obtain ⟨_, _, _, _, _, _, hFaceRi⟩ := hAlphaBeta i hi
      obtain ⟨_, _, _, _, _, hFaceLp, _⟩ := hAlphaBeta (prevCell N i) hprev_lt
      have hCi_prod : C' i * Δ i = ν * (-(fMinus (uFaceR i) - fMinus (uFaceR (prevCell N i)))) := by
        simp only [C', hi, ↓reduceIte, C]
        by_cases hΔi : Δ i = 0
        · have hzR : uFaceR i = uFaceR (prevCell N i) := by rw [hΔi] at hFaceRi; grind
          rw [beq_iff_eq.mpr hΔi, hΔi, hzR]; simp only [↓reduceIte]; grind
        · simp only [beq_false_of_ne hΔi, Bool.false_eq_true, ↓reduceIte]; exact Rat.div_mul_cancel hΔi
      have hDp_prod : D' (prevCell N i) * Δ (prevCell N i) =
          ν * (fPlus (uFaceL (nextCell N (prevCell N i))) - fPlus (uFaceL (prevCell N i))) := by
        simp only [D', hprev_lt, ↓reduceIte, D]
        by_cases hΔp : Δ (prevCell N i) = 0
        · have hzL : uFaceL (nextCell N (prevCell N i)) = uFaceL (prevCell N i) := by
            rw [hΔp] at hFaceLp; grind
          rw [beq_iff_eq.mpr hΔp, hΔp, hzL]; simp only [↓reduceIte]; grind
        · simp only [beq_false_of_ne hΔp, Bool.false_eq_true, ↓reduceIte]; exact Rat.div_mul_cancel hΔp
      have hΔp_eq : u i - u (prevCell N i) = Δ (prevCell N i) := by
        simp only [Δ, nextCell_prevCell N i (by omega) hi]
      rw [hΔp_eq, show u (nextCell N i) - u i = Δ i from rfl, hCi_prod, hDp_prod,
          nextCell_prevCell N i (by omega) hi]
      simp only [musclMinmodRusanov1DStep, fPlus, fMinus, uFaceL, uFaceR, slope, N]; grind
    rw [show totalVariation1D N (musclMinmodRusanov1DStep f aMax ν N u) =
        totalVariation1D N (fun i =>
          u i + C' i * (u (nextCell N i) - u i) - D' (prevCell N i) * (u i - u (prevCell N i))) from by
      unfold totalVariation1D; refine sumTo_congr fun i hi => ?_
      rw [hStepEq i hi, hStepEq (nextCell N i) (by unfold nextCell; split <;> omega)]]
    exact harten_incremental_tvd N u C' D' hC' hD' hCD'

/-- **Tadmor Discrete Entropy Dissipation Theorem (`tadmor_rusanov_entropy_dissipative`)**:
Let `fEC` satisfy Tadmor's shuffle condition `⟨v_R - v_L, fEC(U_L, U_R)⟩ = ψ(U_R) - ψ(U_L)`.
Adding Rusanov dissipation `-(λ / 2)(U_R - U_L)` (`λ ≥ 0`) makes periodic entropy flux difference
`Σ_i ⟨v_i, F_{i+1/2} - F_{i-1/2}⟩ ≥ (λ / 2) Σ_i ⟨Δv, ΔU⟩ ≥ 0`. -/
theorem tadmor_rusanov_entropy_dissipative (m N : Nat)
    (v : Vec → Vec) (psi : Vec → Rat) (fEC : Vec → Vec → Vec) (lam : Rat)
    (hLam : 0 ≤ lam)
    (hTadmor : ∀ uL uR : Vec, dot m (fun c => v uR c - v uL c) (fEC uL uR) = psi uR - psi uL)
    (hMono : ∀ uL uR : Vec, 0 ≤ dot m (fun c => v uR c - v uL c) (fun c => uR c - uL c))
    (U : Nat → Vec) :
    let fES : Vec → Vec → Vec := fun uL uR c => fEC uL uR c - (lam / 2) * (uR c - uL c)
    sumTo N (fun i =>
      dot m (v (U i)) (fun c => fES (U i) (U (nextCell N i)) c - fES (U (prevCell N i)) (U i) c)) ≥
      (lam / 2) * sumTo N (fun i =>
        dot m (fun c => v (U (nextCell N i)) c - v (U i) c)
              (fun c => U (nextCell N i) c - U i c)) ∧
    0 ≤ sumTo N (fun i =>
      dot m (v (U i)) (fun c => fES (U i) (U (nextCell N i)) c - fES (U (prevCell N i)) (U i) c)) := by
  intro fES
  have hParts :
      sumTo N (fun i =>
        dot m (v (U i)) (fun c => fES (U i) (U (nextCell N i)) c - fES (U (prevCell N i)) (U i) c)) =
      sumTo N (fun i =>
        -(dot m (fun c => v (U (nextCell N i)) c - v (U i) c) (fES (U i) (U (nextCell N i))))) := by
    cases N with
    | zero => simp [sumTo]
    | succ n =>
      let N' := n + 1
      have hSplit :
          sumTo N' (fun i =>
            dot m (v (U i)) (fun c => fES (U i) (U (nextCell N' i)) c - fES (U (prevCell N' i)) (U i) c)) =
          sumTo N' (fun i => dot m (v (U i)) (fES (U i) (U (nextCell N' i)))) +
          (-1 : Rat) * sumTo N' (fun i => dot m (v (U i)) (fES (U (prevCell N' i)) (U i))) := by
        rw [← sumTo_mul_left, ← sumTo_add]
        refine sumTo_congr fun i _ => ?_
        unfold dot; rw [← sumTo_mul_left, ← sumTo_add]; exact sumTo_congr fun c _ => by grind
      have hShift :
          sumTo N' (fun i => dot m (v (U i)) (fES (U (prevCell N' i)) (U i))) =
          sumTo N' (fun i => dot m (v (U (nextCell N' i))) (fES (U i) (U (nextCell N' i)))) := by
        rw [show sumTo N' (fun i => dot m (v (U i)) (fES (U (prevCell N' i)) (U i))) =
            sumTo N' (fun i =>
              dot m (v (U (nextCell N' (prevCell N' i))))
                    (fES (U (prevCell N' i)) (U (nextCell N' (prevCell N' i))))) from
          sumTo_congr fun i hi => by rw [nextCell_prevCell N' i (by omega) hi]]
        exact sumTo_prev N' (fun j => dot m (v (U (nextCell N' j))) (fES (U j) (U (nextCell N' j))))
      rw [hSplit, hShift, ← sumTo_mul_left, ← sumTo_add]
      refine sumTo_congr fun i _ => ?_
      unfold dot; rw [← sumTo_mul_left, ← sumTo_add]
      rw [show -(sumTo m fun c => (v (U (nextCell N' i)) c - v (U i) c) * fES (U i) (U (nextCell N' i)) c) =
          sumTo m (fun c => -((v (U (nextCell N' i)) c - v (U i) c) * fES (U i) (U (nextCell N' i)) c)) by
        rw [show (fun c => -((v (U (nextCell N' i)) c - v (U i) c) * fES (U i) (U (nextCell N' i)) c)) =
            (fun c => (-1 : Rat) * ((v (U (nextCell N' i)) c - v (U i) c) * fES (U i) (U (nextCell N' i)) c)) by
          funext c; grind, sumTo_mul_left]; grind]
      exact sumTo_congr fun c _ => by grind
  have hFace : ∀ i,
      -(dot m (fun c => v (U (nextCell N i)) c - v (U i) c) (fES (U i) (U (nextCell N i)))) =
      -(psi (U (nextCell N i)) - psi (U i)) +
      (lam / 2) * dot m (fun c => v (U (nextCell N i)) c - v (U i) c)
                        (fun c => U (nextCell N i) c - U i c) := fun i => by
    have hLin : dot m (fun c => v (U (nextCell N i)) c - v (U i) c) (fES (U i) (U (nextCell N i))) =
        dot m (fun c => v (U (nextCell N i)) c - v (U i) c) (fEC (U i) (U (nextCell N i))) +
        (-(lam / 2)) * dot m (fun c => v (U (nextCell N i)) c - v (U i) c)
                             (fun c => U (nextCell N i) c - U i c) := by
      unfold dot fES; rw [← sumTo_mul_left, ← sumTo_add]; exact sumTo_congr fun c _ => by grind
    rw [hLin, hTadmor]; grind
  have hPsiTelescope : sumTo N (fun i => -(psi (U (nextCell N i)) - psi (U i))) = 0 := by
    rw [show sumTo N (fun i => -(psi (U (nextCell N i)) - psi (U i))) =
        sumTo N (fun i => psi (U i) + (-1 : Rat) * psi (U (nextCell N i))) from
      sumTo_congr fun i _ => by grind, sumTo_add, sumTo_mul_left,
      sumTo_next N (fun i => psi (U i))]; grind
  rw [hParts, funext hFace, sumTo_add, hPsiTelescope, sumTo_mul_left, Rat.zero_add]
  exact ⟨Rat.le_refl, Rat.mul_nonneg (by grind) (sumTo_nonneg fun i _ => hMono (U i) (U (nextCell N i)))⟩

/-! ## 5. Arbitrary-Dimension (`1D/2D/3D/Phase-Space`) Directional Sweeps & Conservation -/

@[expose] def gridCellCount (dims : List Nat) : Nat := dims.foldr (· * ·) 1

abbrev MultiDGrid := Nat → Vec

def totalGridIntegral (dims : List Nat) (U : MultiDGrid) (c : Nat) : Rat :=
  sumTo (gridCellCount dims) fun idx => U idx c

def decodeMultiIdx : List Nat → Nat → List Nat
  | [], _ => []
  | _ :: ds, idx =>
    let stride := gridCellCount ds
    if stride == 0 then 0 :: decodeMultiIdx ds 0
    else (idx / stride) :: decodeMultiIdx ds (idx % stride)

def encodeMultiIdx : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: ds, [] => encodeMultiIdx ds []
  | _ :: ds, c :: cs => c * gridCellCount ds + encodeMultiIdx ds cs

theorem gridCellCount_pos (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) :
    0 < gridCellCount dims := by
  induction dims with
  | nil => simp [gridCellCount]
  | cons N ds ih =>
    simp only [gridCellCount, List.foldr_cons]
    exact Nat.mul_pos (hPos N List.mem_cons_self) (ih fun M hM => hPos M (List.mem_cons_of_mem _ hM))

theorem encode_decode_multiIdx (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) (idx : Nat)
    (hIdx : idx < gridCellCount dims) :
    encodeMultiIdx dims (decodeMultiIdx dims idx) = idx := by
  induction dims generalizing idx with
  | nil => simp [gridCellCount] at hIdx; subst idx; rfl
  | cons N ds ih =>
    have hDsPos : 0 < gridCellCount ds :=
      gridCellCount_pos ds fun M hM => hPos M (List.mem_cons_of_mem _ hM)
    simp only [decodeMultiIdx, beq_false_of_ne (by omega : gridCellCount ds ≠ 0),
      Bool.false_eq_true, ↓reduceIte, encodeMultiIdx]
    rw [ih (fun M hM => hPos M (List.mem_cons_of_mem _ hM)) (idx % gridCellCount ds)
      (Nat.mod_lt idx hDsPos), Nat.mul_comm, Nat.div_add_mod]

theorem getOr_mem_of_lt {α : Type} (xs : List α) (k : Nat) (d : α) (hk : k < xs.length) :
    getOr xs k d ∈ xs := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih => cases k with | zero => exact List.mem_cons_self | succ k => exact List.mem_cons_of_mem _ (ih k (by simpa using hk))

structure AxisFiber where outer : Nat
                          axisLen : Nat
                          inner : Nat

def axisFiberDims (dims : List Nat) (axis : Nat) : AxisFiber :=
  ⟨gridCellCount (dims.take axis), getOr dims axis 1, gridCellCount (dims.drop (axis + 1))⟩

theorem gridCellCount_append (xs ys : List Nat) :
    gridCellCount (xs ++ ys) = gridCellCount xs * gridCellCount ys := by
  induction xs with
  | nil => simp [gridCellCount]
  | cons x xs ih => unfold gridCellCount at ih ⊢; simp only [List.cons_append, List.foldr_cons]; rw [ih, Nat.mul_assoc]

theorem dims_split_at_axis (dims : List Nat) (axis : Nat) (hAxis : axis < dims.length) :
    dims = dims.take axis ++ [getOr dims axis 1] ++ dims.drop (axis + 1) := by
  induction dims generalizing axis with
  | nil => simp at hAxis
  | cons d ds ih =>
    cases axis with
    | zero => simp [getOr]
    | succ a => simp only [List.take_succ_cons, List.drop_succ_cons, getOr, List.cons_append]; exact congrArg (d :: ·) (ih a (by simpa using hAxis))

theorem axisFiberDims_prod (dims : List Nat) (axis : Nat) (hAxis : axis < dims.length) :
    let f := axisFiberDims dims axis
    gridCellCount dims = f.outer * (f.axisLen * f.inner) := by
  have hEq := congrArg gridCellCount (dims_split_at_axis dims axis hAxis)
  rw [List.append_assoc, gridCellCount_append, gridCellCount_append,
      show gridCellCount [getOr dims axis 1] = getOr dims axis 1 by simp [gridCellCount]] at hEq
  exact hEq

def axisPeriodicNeighbor (dims : List Nat) (axis : Nat) (isNext : Bool) (idx : Nat) : Nat :=
  let f := axisFiberDims dims axis
  let block := f.axisLen * f.inner
  if block == 0 || f.inner == 0 then idx
  else
    let outerIdx := idx / block
    let rem := idx % block
    let coord := rem / f.inner
    let innerIdx := rem % f.inner
    let coord' := if isNext then nextCell f.axisLen coord else prevCell f.axisLen coord
    outerIdx * block + coord' * f.inner + innerIdx

theorem sumTo_add_len (M K : Nat) (g : Nat → Rat) :
    sumTo (M + K) g = sumTo M g + sumTo K (fun k => g (M + k)) := by
  induction K with
  | zero => simp only [Nat.add_zero, sumTo]; grind
  | succ K ih => rw [Nat.add_succ, sumTo, ih, sumTo]; grind

theorem sumTo_mul_split (A B : Nat) (f : Nat → Rat) :
    sumTo (A * B) f = sumTo A (fun a => sumTo B (fun b => f (a * B + b))) := by
  induction A with
  | zero => simp [sumTo]
  | succ A ih => rw [Nat.succ_mul, sumTo_add_len (A * B) B f, ih, sumTo]

theorem axisPeriodicNeighbor_fiber (dims : List Nat) (axis : Nat) (isNext : Bool)
    (hAxis : axis < dims.length) (hPos : ∀ N ∈ dims, 0 < N)
    (o k r : Nat) (hk : k < (axisFiberDims dims axis).axisLen)
    (hr : r < (axisFiberDims dims axis).inner) :
    let f := axisFiberDims dims axis
    let cellAt := fun c => o * (f.axisLen * f.inner) + (c * f.inner + r)
    axisPeriodicNeighbor dims axis isNext (cellAt k) =
      cellAt (if isNext then nextCell f.axisLen k else prevCell f.axisLen k) := by
  intro f cellAt
  have hk' : k < f.axisLen := hk
  have hr' : r < f.inner := hr
  have hAxisPos : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims axis 1 hAxis)
  have hInnerPos : 0 < f.inner :=
    gridCellCount_pos _ fun M hM => hPos M (List.mem_of_mem_drop hM)
  have hBlockPos : 0 < f.axisLen * f.inner := Nat.mul_pos hAxisPos hInnerPos
  unfold axisPeriodicNeighbor
  have hb0 : (((axisFiberDims dims axis).axisLen * (axisFiberDims dims axis).inner == 0) ||
      ((axisFiberDims dims axis).inner == 0)) = false := by
    change ((f.axisLen * f.inner == 0) || (f.inner == 0)) = false
    simp [beq_false_of_ne (by omega : f.axisLen * f.inner ≠ 0),
          beq_false_of_ne (by omega : f.inner ≠ 0)]
  dsimp only []
  rw [hb0]; simp only [Bool.false_eq_true, ↓reduceIte]
  change (cellAt k / (f.axisLen * f.inner)) * (f.axisLen * f.inner) +
      (if isNext then nextCell f.axisLen ((cellAt k % (f.axisLen * f.inner)) / f.inner)
       else prevCell f.axisLen ((cellAt k % (f.axisLen * f.inner)) / f.inner)) * f.inner +
      ((cellAt k % (f.axisLen * f.inner)) % f.inner) = _
  have hrem_lt : k * f.inner + r < f.axisLen * f.inner := by
    have h2 := Nat.mul_le_mul_right f.inner (show k + 1 ≤ f.axisLen by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2; omega
  have hdiv1 : (o * (f.axisLen * f.inner) + (k * f.inner + r)) / (f.axisLen * f.inner) = o := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBlockPos, Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
  have hmod1 : (o * (f.axisLen * f.inner) + (k * f.inner + r)) % (f.axisLen * f.inner) =
      k * f.inner + r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem_lt]
  have hdiv2 : (k * f.inner + r) / f.inner = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hInnerPos, Nat.div_eq_of_lt hr', Nat.zero_add]
  have hmod2 : (k * f.inner + r) % f.inner = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr']
  dsimp only [cellAt]
  rw [hdiv1, hmod1, hdiv2, hmod2, Nat.add_assoc]

/-- One conservative finite-volume directional sweep along `axis` with Courant ratio `ν = Δt / Δx_d`. -/
def evalDirectionalSweep (dims : List Nat) (axis : Nat) (ν : Rat)
    (numFlux : Vec → Vec → Vec) (U : MultiDGrid) : MultiDGrid :=
  if axis < dims.length then
    fun idx c =>
      let idxPrev := axisPeriodicNeighbor dims axis false idx
      let idxNext := axisPeriodicNeighbor dims axis true idx
      U idx c - ν * (numFlux (U idx) (U idxNext) c - numFlux (U idxPrev) (U idx) c)
  else U

/-- **Directional Sweep Integral Conservation (`directionalSweep_conserves_integral`)**:
On any `D`-dimensional periodic grid `dims` (with positive extents), sweeping along `axis` with
*any* single-valued interface flux `numFlux` conserves `totalGridIntegral` identically. -/
theorem directionalSweep_conserves_integral (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (axis : Nat) (ν : Rat)
    (numFlux : Vec → Vec → Vec) (U : MultiDGrid) (c : Nat) :
    totalGridIntegral dims (evalDirectionalSweep dims axis ν numFlux U) c =
      totalGridIntegral dims U c := by
  unfold evalDirectionalSweep
  by_cases hAxis : axis < dims.length
  · simp only [hAxis, ↓reduceIte]
    unfold totalGridIntegral
    let f := axisFiberDims dims axis
    have hAxisPos : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims axis 1 hAxis)
    rw [axisFiberDims_prod dims axis hAxis,
        sumTo_mul_split f.outer (f.axisLen * f.inner),
        sumTo_mul_split f.outer (f.axisLen * f.inner)]
    refine sumTo_congr fun o _ => ?_
    rw [sumTo_mul_split f.axisLen f.inner, sumTo_mul_split f.axisLen f.inner,
        sumTo_comm f.axisLen f.inner, sumTo_comm f.axisLen f.inner]
    refine sumTo_congr fun r hr => ?_
    let cellAt := fun k => o * (f.axisLen * f.inner) + (k * f.inner + r)
    rw [show sumTo f.axisLen (fun k =>
          U (cellAt k) c -
            ν * (numFlux (U (cellAt k)) (U (axisPeriodicNeighbor dims axis true (cellAt k))) c -
                 numFlux (U (axisPeriodicNeighbor dims axis false (cellAt k))) (U (cellAt k)) c)) =
        sumTo f.axisLen (fun k =>
          U (cellAt k) c +
            ((-ν) * numFlux (U (cellAt k)) (U (cellAt (nextCell f.axisLen k))) c +
             ν * numFlux (U (cellAt (prevCell f.axisLen k))) (U (cellAt k)) c)) from
      sumTo_congr fun k hk => by
        rw [axisPeriodicNeighbor_fiber dims axis true hAxis hPos o k r hk hr,
            axisPeriodicNeighbor_fiber dims axis false hAxis hPos o k r hk hr]
        simp only [↓reduceIte, Bool.false_eq_true]; grind,
      sumTo_add, sumTo_add, sumTo_mul_left, sumTo_mul_left]
    have hPrevShift :
        sumTo f.axisLen (fun k => numFlux (U (cellAt (prevCell f.axisLen k))) (U (cellAt k)) c) =
        sumTo f.axisLen (fun k => numFlux (U (cellAt k)) (U (cellAt (nextCell f.axisLen k))) c) := by
      rw [show sumTo f.axisLen (fun k => numFlux (U (cellAt (prevCell f.axisLen k))) (U (cellAt k)) c) =
          sumTo f.axisLen (fun k =>
            numFlux (U (cellAt (prevCell f.axisLen k)))
                    (U (cellAt (nextCell f.axisLen (prevCell f.axisLen k)))) c) from
        sumTo_congr fun k hk => by rw [nextCell_prevCell f.axisLen k hAxisPos hk]]
      exact sumTo_prev f.axisLen (fun j => numFlux (U (cellAt j)) (U (cellAt (nextCell f.axisLen j))) c)
    rw [hPrevShift]; grind
  · simp [hAxis]

def evalSweepSchedule (dims : List Nat) :
    List (Nat × Rat × (Vec → Vec → Vec)) → MultiDGrid → MultiDGrid
  | [], U => U
  | (axis, ν, nf) :: rest, U =>
    evalSweepSchedule dims rest (evalDirectionalSweep dims axis ν nf U)

def evalMultiDSweep (dims : List Nat) (ν : Rat)
    (axisFluxes : Nat → Vec → Vec → Vec) (U : MultiDGrid) : MultiDGrid :=
  evalSweepSchedule dims ((List.range dims.length).map fun d => (d, ν, axisFluxes d)) U

def evalStrangSweep (dims : List Nat) (ν : Rat)
    (axisFluxes : Nat → Vec → Vec → Vec) (U : MultiDGrid) : MultiDGrid :=
  let half := (List.range dims.length).map fun d => (d, ν / 2, axisFluxes d)
  evalSweepSchedule dims (half ++ half.reverse) U

theorem sweepSchedule_conserves_integral (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (sched : List (Nat × Rat × (Vec → Vec → Vec))) (U : MultiDGrid) (c : Nat) :
    totalGridIntegral dims (evalSweepSchedule dims sched U) c =
      totalGridIntegral dims U c := by
  induction sched generalizing U with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨axis, ν, nf⟩
    simp only [evalSweepSchedule, ih, directionalSweep_conserves_integral dims hPos axis ν nf U c]

/-- **Multi-Dimensional Mass/Momentum/Energy/Charge Conservation (`multiDSweep_conserves_total_mass_momentum_energy`)**:
Both `evalMultiDSweep` (Lie) and `evalStrangSweep` (2nd-order Strang) conserve `totalGridIntegral`
for every component `c` across arbitrary spatial/phase-space dimensions `D`. -/
theorem multiDSweep_conserves_total_mass_momentum_energy (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (ν : Rat)
    (axisFluxes : Nat → Vec → Vec → Vec) (U : MultiDGrid) (c : Nat) :
    totalGridIntegral dims (evalMultiDSweep dims ν axisFluxes U) c = totalGridIntegral dims U c ∧
    totalGridIntegral dims (evalStrangSweep dims ν axisFluxes U) c = totalGridIntegral dims U c :=
  ⟨sweepSchedule_conserves_integral dims hPos _ U c,
   sweepSchedule_conserves_integral dims hPos _ U c⟩

/-! ## 6. Declarative Nonlinear Multi-D Conservation-Law Spec & Multi-Turn Rollout -/

inductive SlopeLimiterKind where | firstOrder | minmod deriving DecidableEq, Repr

structure ConservationLawSpec where
  name : String
  coords : List String
  vars : List String
  params : List (String × Rat)
  domain : List PosTarget
  fluxes : List (List FluxExpr)
  aMax : Rat
  cfl : Rat
  limiter : SlopeLimiterKind
  deriving DecidableEq, Repr

namespace ConservationLawSpec
def numDims (s : ConservationLawSpec) : Nat := s.coords.length
def numVars (s : ConservationLawSpec) : Nat := s.vars.length
def paramEnv (s : ConservationLawSpec) : Nat → Rat := fun k => (getOr s.params k ("", 0)).2

def checkValid (s : ConservationLawSpec) : Bool :=
  !s.coords.isEmpty && !s.vars.isEmpty &&
  (s.coords.eraseDups.length == s.coords.length) &&
  (s.vars.eraseDups.length == s.vars.length) &&
  ((s.params.map Prod.fst).eraseDups.length == s.params.length) &&
  (s.fluxes.length == s.coords.length) &&
  s.fluxes.all (fun row => (row.length == s.vars.length) && row.all (checkExprDomainSafe s.domain)) &&
  decide (0 < s.aMax ∧ 0 ≤ s.cfl ∧ s.cfl * s.aMax ≤ 1)

theorem checkValid_flux_domainSafe (s : ConservationLawSpec) (hValid : s.checkValid = true)
    (d i : Nat) (hd : d < s.numDims) (hi : i < s.numVars) :
    checkExprDomainSafe s.domain (getOr (getOr s.fluxes d []) i (.const 0)) = true := by
  unfold checkValid at hValid
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hValid
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hFluxLen⟩, hRows⟩, _⟩ := hValid
  have hd' : d < s.fluxes.length := by unfold numDims at hd; omega
  obtain ⟨hRowLen, hRowSafe⟩ := hRows (getOr s.fluxes d []) (getOr_mem_of_lt s.fluxes d [] hd')
  have hi' : i < (getOr s.fluxes d []).length := by unfold numVars at hi; omega
  exact hRowSafe _ (getOr_mem_of_lt _ i (.const 0) hi')

end ConservationLawSpec

structure PdeRolloutTurn where
  courant : Rat
  useStrang : Bool
  deriving DecidableEq, Repr
structure PdeRolloutState where
  grid : MultiDGrid
  elapsedCourant : Rat
  acceptedSteps : Nat
def stepPdeRolloutTurn (spec : ConservationLawSpec) (dims : List Nat)
    (st : PdeRolloutState) (turn : PdeRolloutTurn) : Option PdeRolloutState :=
  if decide (0 ≤ turn.courant ∧ turn.courant * spec.aMax ≤ 1) then
    let axisFlux := fun d => rusanovNonlinearFlux (getOr spec.fluxes d []) spec.paramEnv spec.aMax
    let nextGrid := if turn.useStrang then evalStrangSweep dims turn.courant axisFlux st.grid
      else evalMultiDSweep dims turn.courant axisFlux st.grid
    some ⟨nextGrid, st.elapsedCourant + turn.courant, st.acceptedSteps + 1⟩
  else none
/-- Environment anti-narrowing completeness: a turn is refused iff it violates CFL. -/
theorem stepPdeRolloutTurn_none_iff_cfl_violation (spec : ConservationLawSpec) (dims : List Nat)
    (st : PdeRolloutState) (turn : PdeRolloutTurn) :
    stepPdeRolloutTurn spec dims st turn = none ↔ ¬ (0 ≤ turn.courant ∧ turn.courant * spec.aMax ≤ 1) := by
  unfold stepPdeRolloutTurn; split <;> simp_all
def runPdeRolloutTrace (spec : ConservationLawSpec) (dims : List Nat) :
    PdeRolloutState → List PdeRolloutTurn → Option PdeRolloutState
  | st, [] => some st
  | st, t :: ts => match stepPdeRolloutTurn spec dims st t with | none => none | some st' => runPdeRolloutTrace spec dims st' ts

/-- **Multi-Turn Rollout Integral & Monotone Time Invariant (`runPdeRolloutTrace_invariants`)**:
Across any accepted sequence of adaptive Lie/Strang turns, every conserved component's integral is
preserved identically, elapsed Courant time is non-decreasing, and step count increments by `turns.length`. -/
theorem runPdeRolloutTrace_invariants (spec : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (st0 stF : PdeRolloutState) (turns : List PdeRolloutTurn)
    (hRun : runPdeRolloutTrace spec dims st0 turns = some stF) :
    (∀ c, totalGridIntegral dims stF.grid c = totalGridIntegral dims st0.grid c) ∧
    st0.elapsedCourant ≤ stF.elapsedCourant ∧
    stF.acceptedSteps = st0.acceptedSteps + turns.length := by
  induction turns generalizing st0 with
  | nil =>
    simp only [runPdeRolloutTrace, Option.some.injEq] at hRun
    subst hRun; exact ⟨fun _ => rfl, Rat.le_refl, by simp⟩
  | cons t ts ih =>
    simp only [runPdeRolloutTrace] at hRun
    cases hStep : stepPdeRolloutTurn spec dims st0 t with
    | none => simp [hStep] at hRun
    | some st1 =>
      rw [hStep] at hRun
      unfold stepPdeRolloutTurn at hStep
      split at hStep
      · rename_i hCfl
        have hCfl' : 0 ≤ t.courant ∧ t.courant * spec.aMax ≤ 1 := of_decide_eq_true hCfl
        simp only [Option.some.injEq] at hStep
        obtain ⟨hConsRest, hTimeRest, hStepsRest⟩ := ih st1 hRun
        refine ⟨?_, ?_, ?_⟩
        · intro c
          rw [hConsRest c, ← hStep]
          have hBoth := multiDSweep_conserves_total_mass_momentum_energy dims hPos t.courant
            (fun d => rusanovNonlinearFlux (getOr spec.fluxes d []) spec.paramEnv spec.aMax) st0.grid c
          dsimp only; split
          · exact hBoth.2
          · exact hBoth.1
        · rw [← hStep] at hTimeRest; dsimp only at hTimeRest; grind
        · rw [← hStep] at hStepsRest; dsimp only at hStepsRest; simp only [List.length_cons]; omega
      · cases hStep

end Obend.Analysis.NonlinearMultiDPde
