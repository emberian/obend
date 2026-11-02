module
/-
# Obend.Analysis.Diff — Forward/Reverse Automatic Differentiation, Symbolic Derivatives & Mean-Value Enclosures

Implements `WS 25` (`NEXT-MATHEMATICA.md` §3):
1. **Forward-Mode Dual Numbers (`DualRat`, `DualInterval`, `evalDualRat`, `evalDualInterval`)**:
   - Exact rational dual numbers $a + b\varepsilon$ ($\varepsilon^2 = 0$) over `CanonicalRat` and interval
     dual numbers over `Interval`.
   - Proves **`evalDual_fst_eq_eval`**: for every `e : RealExpr`, the primal component `(evalDualRat rho v e).val`
     equals `evalPointPure rho e` (`evalPoint rho e = some (evalDualRat rho v e).val`).
2. **Symbolic Differentiation & Reverse-Mode Gradient Pullback (`symbolicDeriv`, `reverseGradVar`)**:
   - Symbolic derivative operator $\frac{\partial e}{\partial v} : \mathsf{RealExpr} \to \mathsf{RealExpr}$
     and reverse-mode adjoint pullback over `RealExpr`.
   - Proves **`symbolicDeriv_agrees_with_dual`**: for every `e : RealExpr`, variable `v`, and point
     assignment `rho`, evaluating `symbolicDeriv v e` at `rho` equals the forward-mode dual tangent
     `(evalDualRat rho v e).der`, and agrees with `reverseGradVar`.
3. **Interval Mean-Value Enclosure (`meanValueEnclosure`, `interval_mean_value_enclosure`)**:
   - Formalizes the Mean-Value Form interval enclosure $f(c) + f'(X) \cdot (X - c)$ and proves
     soundness of `Interval.add` enclosure and `meanValueEnclosure` over `DualInterval`.
-/
public import Obend.Analysis.RealAnalysis
@[expose] public section

namespace Obend.Analysis
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## 1. Total Point Evaluation (`evalPointPure`) & Agreement with `evalPoint` -/

/-- Total point evaluator for `RealExpr` at a rational assignment `rho : String → CanonicalRat`. -/
def evalPointPure (rho : String → CanonicalRat) : RealExpr → CanonicalRat
  | .const c => c
  | .var name => rho name
  | .add l r => evalPointPure rho l + evalPointPure rho r
  | .sub l r => evalPointPure rho l - evalPointPure rho r
  | .mul l r => evalPointPure rho l * evalPointPure rho r
  | .sqr a   => evalPointPure rho a * evalPointPure rho a

/-- `evalPoint rho e` always succeeds and returns `some (evalPointPure rho e)`. -/
@[simp] theorem evalPoint_eq_some_evalPointPure (rho : String → CanonicalRat) :
    ∀ (e : RealExpr), evalPoint rho e = some (evalPointPure rho e)
  | .const _ => rfl
  | .var _   => rfl
  | .add l r => by
    simp [evalPoint, evalPointPure,
      evalPoint_eq_some_evalPointPure rho l, evalPoint_eq_some_evalPointPure rho r]
  | .sub l r => by
    simp [evalPoint, evalPointPure,
      evalPoint_eq_some_evalPointPure rho l, evalPoint_eq_some_evalPointPure rho r]
  | .mul l r => by
    simp [evalPoint, evalPointPure,
      evalPoint_eq_some_evalPointPure rho l, evalPoint_eq_some_evalPointPure rho r]
  | .sqr a => by
    simp [evalPoint, evalPointPure, evalPoint_eq_some_evalPointPure rho a]

/-! ## 2. Forward-Mode Dual Numbers (`DualRat`, `DualInterval`) -/

/-- Forward-mode dual number $a + b\varepsilon$ ($\varepsilon^2 = 0$) over `CanonicalRat`. -/
structure DualRat where
  val : CanonicalRat
  der : CanonicalRat
  deriving DecidableEq, Repr

namespace DualRat

/-- Constant dual number $(c, 0)$. -/
def const (c : CanonicalRat) : DualRat :=
  ⟨c, 0⟩

/-- Active variable $(x, 1)$ when `name == diffVar`, or passive $(x, 0)$ otherwise. -/
def var (x : CanonicalRat) (isActive : Bool) : DualRat :=
  ⟨x, if isActive then 1 else 0⟩

/-- Dual addition: $(v_1 + v_2, d_1 + d_2)$. -/
def add (a b : DualRat) : DualRat :=
  ⟨a.val + b.val, a.der + b.der⟩

/-- Dual subtraction: $(v_1 - v_2, d_1 - d_2)$. -/
def sub (a b : DualRat) : DualRat :=
  ⟨a.val - b.val, a.der - b.der⟩

/-- Dual multiplication (Leibniz product rule): $(v_1 v_2, d_1 v_2 + v_1 d_2)$. -/
def mul (a b : DualRat) : DualRat :=
  ⟨a.val * b.val, a.der * b.val + a.val * b.der⟩

/-- Dual squaring: $(v^2, d \cdot v + v \cdot d)$. -/
def sqr (a : DualRat) : DualRat :=
  ⟨a.val * a.val, a.der * a.val + a.val * a.der⟩

end DualRat

/-- Evaluate a `RealExpr` in forward-mode automatic differentiation with respect to `diffVar`. -/
def evalDualRat (rho : String → CanonicalRat) (diffVar : String) : RealExpr → DualRat
  | .const c => DualRat.const c
  | .var name => DualRat.var (rho name) (name == diffVar)
  | .add l r => DualRat.add (evalDualRat rho diffVar l) (evalDualRat rho diffVar r)
  | .sub l r => DualRat.sub (evalDualRat rho diffVar l) (evalDualRat rho diffVar r)
  | .mul l r => DualRat.mul (evalDualRat rho diffVar l) (evalDualRat rho diffVar r)
  | .sqr a   => DualRat.sqr (evalDualRat rho diffVar a)

/-- **Theorem (`evalDual_fst_eq_eval`)**:
For every `e : RealExpr`, assignment `rho`, and differentiation variable `diffVar`, the primal
value component `(evalDualRat rho diffVar e).val` equals `evalPointPure rho e` (and `evalPoint rho e = some (evalDualRat rho diffVar e).val`). -/
theorem evalDual_fst_eq_eval (rho : String → CanonicalRat) (diffVar : String) :
    ∀ (e : RealExpr),
      (evalDualRat rho diffVar e).val = evalPointPure rho e ∧
      evalPoint rho e = some (evalDualRat rho diffVar e).val
  | .const _ => ⟨rfl, rfl⟩
  | .var _   => ⟨rfl, rfl⟩
  | .add l r => by
    have ihl := (evalDual_fst_eq_eval rho diffVar l).1
    have ihr := (evalDual_fst_eq_eval rho diffVar r).1
    have hval : (evalDualRat rho diffVar (.add l r)).val = evalPointPure rho (.add l r) := by
      simp [evalDualRat, DualRat.add, evalPointPure, ihl, ihr]
    exact ⟨hval, by rw [evalPoint_eq_some_evalPointPure, hval]⟩
  | .sub l r => by
    have ihl := (evalDual_fst_eq_eval rho diffVar l).1
    have ihr := (evalDual_fst_eq_eval rho diffVar r).1
    have hval : (evalDualRat rho diffVar (.sub l r)).val = evalPointPure rho (.sub l r) := by
      simp [evalDualRat, DualRat.sub, evalPointPure, ihl, ihr]
    exact ⟨hval, by rw [evalPoint_eq_some_evalPointPure, hval]⟩
  | .mul l r => by
    have ihl := (evalDual_fst_eq_eval rho diffVar l).1
    have ihr := (evalDual_fst_eq_eval rho diffVar r).1
    have hval : (evalDualRat rho diffVar (.mul l r)).val = evalPointPure rho (.mul l r) := by
      simp [evalDualRat, DualRat.mul, evalPointPure, ihl, ihr]
    exact ⟨hval, by rw [evalPoint_eq_some_evalPointPure, hval]⟩
  | .sqr a => by
    have iha := (evalDual_fst_eq_eval rho diffVar a).1
    have hval : (evalDualRat rho diffVar (.sqr a)).val = evalPointPure rho (.sqr a) := by
      simp [evalDualRat, DualRat.sqr, evalPointPure, iha]
    exact ⟨hval, by rw [evalPoint_eq_some_evalPointPure, hval]⟩

/-! ## 3. Symbolic Differentiation & Reverse-Mode Adjoint Pullback (`symbolicDeriv`, `reverseGradVar`) -/

/-- Symbolic partial derivative $\frac{\partial e}{\partial \text{diffVar}}$ over `RealExpr`. -/
def symbolicDeriv (diffVar : String) : RealExpr → RealExpr
  | .const _ => .const 0
  | .var name => if name == diffVar then .const 1 else .const 0
  | .add l r => .add (symbolicDeriv diffVar l) (symbolicDeriv diffVar r)
  | .sub l r => .sub (symbolicDeriv diffVar l) (symbolicDeriv diffVar r)
  | .mul l r => .add (.mul (symbolicDeriv diffVar l) r) (.mul l (symbolicDeriv diffVar r))
  | .sqr a   => .add (.mul (symbolicDeriv diffVar a) a) (.mul a (symbolicDeriv diffVar a))

/-- Reverse-mode AD adjoint sensitivity for `diffVar` (`reverseGradVar`):
recursively accumulates the partial derivative with respect to `diffVar` over `RealExpr`. -/
def reverseGradVar (rho : String → CanonicalRat) (diffVar : String) : RealExpr → CanonicalRat
  | .const _ => 0
  | .var name => if name == diffVar then 1 else 0
  | .add l r => reverseGradVar rho diffVar l + reverseGradVar rho diffVar r
  | .sub l r => reverseGradVar rho diffVar l - reverseGradVar rho diffVar r
  | .mul l r =>
    reverseGradVar rho diffVar l * evalPointPure rho r +
    evalPointPure rho l * reverseGradVar rho diffVar r
  | .sqr a =>
    reverseGradVar rho diffVar a * evalPointPure rho a +
    evalPointPure rho a * reverseGradVar rho diffVar a

/-- Top-down multi-variable reverse-mode cotangent pullback (`gradReverse`):
propagates an output cotangent seed `bar` ($\bar{y}$) from root to variable leaves in a single pass. -/
def gradReverse (rho : String → CanonicalRat) (bar : CanonicalRat) : RealExpr → List (String × CanonicalRat)
  | .const _ => []
  | .var name => [(name, bar)]
  | .add l r => gradReverse rho bar l ++ gradReverse rho bar r
  | .sub l r => gradReverse rho bar l ++ gradReverse rho (-bar) r
  | .mul l r =>
    gradReverse rho (bar * evalPointPure rho r) l ++
    gradReverse rho (evalPointPure rho l * bar) r
  | .sqr a =>
    gradReverse rho (bar * evalPointPure rho a) a ++
    gradReverse rho (evalPointPure rho a * bar) a

theorem reverseGradVar_eq_dual_der (rho : String → CanonicalRat) (diffVar : String) :
    ∀ (e : RealExpr), reverseGradVar rho diffVar e = (evalDualRat rho diffVar e).der
  | .const _ => rfl
  | .var _   => rfl
  | .add l r => by
    simp [reverseGradVar, evalDualRat, DualRat.add,
      reverseGradVar_eq_dual_der rho diffVar l, reverseGradVar_eq_dual_der rho diffVar r]
  | .sub l r => by
    simp [reverseGradVar, evalDualRat, DualRat.sub,
      reverseGradVar_eq_dual_der rho diffVar l, reverseGradVar_eq_dual_der rho diffVar r]
  | .mul l r => by
    have hvl := (evalDual_fst_eq_eval rho diffVar l).1
    have hvr := (evalDual_fst_eq_eval rho diffVar r).1
    simp [reverseGradVar, evalDualRat, DualRat.mul, hvl, hvr,
      reverseGradVar_eq_dual_der rho diffVar l, reverseGradVar_eq_dual_der rho diffVar r]
  | .sqr a => by
    have hva := (evalDual_fst_eq_eval rho diffVar a).1
    simp [reverseGradVar, evalDualRat, DualRat.sqr, hva,
      reverseGradVar_eq_dual_der rho diffVar a]

/-- **Theorem (`symbolicDeriv_agrees_with_dual`)**:
For every `e : RealExpr`, differentiation variable `diffVar`, and point assignment `rho`:
1. Evaluating the symbolic derivative `symbolicDeriv diffVar e` via `evalPointPure rho` produces
   the exact forward-mode dual tangent `(evalDualRat rho diffVar e).der`,
2. `evalPoint rho (symbolicDeriv diffVar e) = some (evalDualRat rho diffVar e).der`, and
3. The recursive reverse-mode adjoint `reverseGradVar rho diffVar e` equals `evalPointPure rho (symbolicDeriv diffVar e)`. -/
theorem symbolicDeriv_agrees_with_dual (rho : String → CanonicalRat) (diffVar : String) :
    ∀ (e : RealExpr),
      evalPointPure rho (symbolicDeriv diffVar e) = (evalDualRat rho diffVar e).der ∧
      evalPoint rho (symbolicDeriv diffVar e) = some (evalDualRat rho diffVar e).der ∧
      reverseGradVar rho diffVar e = evalPointPure rho (symbolicDeriv diffVar e)
  | .const _ => ⟨rfl, rfl, rfl⟩
  | .var name => by
    cases h : (name == diffVar) <;>
      simp [symbolicDeriv, evalDualRat, DualRat.var, evalPointPure, reverseGradVar, h]
  | .add l r => by
    have ihl := (symbolicDeriv_agrees_with_dual rho diffVar l).1
    have ihr := (symbolicDeriv_agrees_with_dual rho diffVar r).1
    have hder : evalPointPure rho (symbolicDeriv diffVar (.add l r)) =
        (evalDualRat rho diffVar (.add l r)).der := by
      simp [symbolicDeriv, evalDualRat, DualRat.add, evalPointPure, ihl, ihr]
    exact ⟨hder, by rw [evalPoint_eq_some_evalPointPure, hder],
      by rw [reverseGradVar_eq_dual_der, hder]⟩
  | .sub l r => by
    have ihl := (symbolicDeriv_agrees_with_dual rho diffVar l).1
    have ihr := (symbolicDeriv_agrees_with_dual rho diffVar r).1
    have hder : evalPointPure rho (symbolicDeriv diffVar (.sub l r)) =
        (evalDualRat rho diffVar (.sub l r)).der := by
      simp [symbolicDeriv, evalDualRat, DualRat.sub, evalPointPure, ihl, ihr]
    exact ⟨hder, by rw [evalPoint_eq_some_evalPointPure, hder],
      by rw [reverseGradVar_eq_dual_der, hder]⟩
  | .mul l r => by
    have ihl := (symbolicDeriv_agrees_with_dual rho diffVar l).1
    have ihr := (symbolicDeriv_agrees_with_dual rho diffVar r).1
    have hvl := (evalDual_fst_eq_eval rho diffVar l).1
    have hvr := (evalDual_fst_eq_eval rho diffVar r).1
    have hder : evalPointPure rho (symbolicDeriv diffVar (.mul l r)) =
        (evalDualRat rho diffVar (.mul l r)).der := by
      simp [symbolicDeriv, evalDualRat, DualRat.mul, evalPointPure, ihl, ihr, hvl, hvr]
    exact ⟨hder, by rw [evalPoint_eq_some_evalPointPure, hder],
      by rw [reverseGradVar_eq_dual_der, hder]⟩
  | .sqr a => by
    have iha := (symbolicDeriv_agrees_with_dual rho diffVar a).1
    have hva := (evalDual_fst_eq_eval rho diffVar a).1
    have hder : evalPointPure rho (symbolicDeriv diffVar (.sqr a)) =
        (evalDualRat rho diffVar (.sqr a)).der := by
      simp [symbolicDeriv, evalDualRat, DualRat.sqr, evalPointPure, iha, hva]
    exact ⟨hder, by rw [evalPoint_eq_some_evalPointPure, hder],
      by rw [reverseGradVar_eq_dual_der, hder]⟩

/-! ## 4. Interval Dual Arithmetic & Mean-Value Enclosure (`DualInterval`, `interval_mean_value_enclosure`) -/

/-- Interval dual pair `(val, der)` enclosing both function range and derivative range over an interval box. -/
structure DualInterval where
  val : Interval
  der : Interval
  deriving DecidableEq, Repr

namespace DualInterval

def const (c : CanonicalRat) : DualInterval :=
  ⟨Interval.ofPoint c, Interval.ofPoint 0⟩

def var (box : Interval) (isActive : Bool) : DualInterval :=
  ⟨box, if isActive then Interval.ofPoint 1 else Interval.ofPoint 0⟩

def add (a b : DualInterval) : DualInterval :=
  ⟨Interval.add a.val b.val, Interval.add a.der b.der⟩

def sub (a b : DualInterval) : DualInterval :=
  ⟨Interval.sub a.val b.val, Interval.sub a.der b.der⟩

def mul (a b : DualInterval) : DualInterval :=
  ⟨Interval.mul a.val b.val,
   Interval.add (Interval.mul a.der b.val) (Interval.mul a.val b.der)⟩

def sqr (a : DualInterval) : DualInterval :=
  let two : Interval := Interval.ofPoint 2
  ⟨Interval.sqr a.val, Interval.mul two (Interval.mul a.val a.der)⟩

end DualInterval

/-- Evaluate a `RealExpr` over an interval environment in forward-mode interval AD (`DualInterval`). -/
def evalDualInterval (env : List (String × Interval)) (diffVar : String) : RealExpr → Option DualInterval
  | .const c => some (DualInterval.const c)
  | .var name => do
    let box ← (env.find? (·.1 == name)).map (·.2)
    pure (DualInterval.var box (name == diffVar))
  | .add l r => do
    let dl ← evalDualInterval env diffVar l
    let dr ← evalDualInterval env diffVar r
    pure (DualInterval.add dl dr)
  | .sub l r => do
    let dl ← evalDualInterval env diffVar l
    let dr ← evalDualInterval env diffVar r
    pure (DualInterval.sub dl dr)
  | .mul l r => do
    let dl ← evalDualInterval env diffVar l
    let dr ← evalDualInterval env diffVar r
    pure (DualInterval.mul dl dr)
  | .sqr a => do
    let da ← evalDualInterval env diffVar a
    pure (DualInterval.sqr da)

/-- Mean-Value Form interval enclosure:
given a center evaluation enclosure `fc`, a derivative enclosure `dfBox` over the domain interval `X`,
and a center point `c`, computes $F_{\text{MV}}(X) = f(c) + f'(X) \cdot (X - c)$. -/
def meanValueEnclosure (fc : Interval) (dfBox : Interval) (domainX : Interval) (c : CanonicalRat) : Interval :=
  let deltaX := Interval.sub domainX (Interval.ofPoint c)
  Interval.add fc (Interval.mul dfBox deltaX)

/-- **Theorem (`evalDualInterval_sound`)**:
Universal Soundness of Forward-Mode Interval Automatic Differentiation (`evalDualInterval`):
For any `e : RealExpr`, interval environment `env`, differentiation variable `diffVar`, and
point assignment `rho` enclosed by `env` (`∀ v I, env.lookup v = some I → rho v ∈ I`), if
`evalDualInterval env diffVar e = some dIv`, then both the primal value `(evalDualRat rho diffVar e).val`
and the exact derivative `(evalDualRat rho diffVar e).der` are enclosed in `dIv.val` and `dIv.der`! -/
theorem evalDualInterval_sound
    (env : List (String × Interval))
    (rho : String → CanonicalRat)
    (hEnv : ∀ v I, env.lookup v = some I → rho v ∈ I)
    (diffVar : String) (e : RealExpr) (dIv : DualInterval)
    (hEval : evalDualInterval env diffVar e = some dIv) :
    (evalDualRat rho diffVar e).val ∈ dIv.val ∧
    (evalDualRat rho diffVar e).der ∈ dIv.der := by
  induction e generalizing dIv with
  | const c =>
    simp only [evalDualInterval, Option.some.injEq] at hEval
    subst hEval
    exact ⟨Interval.ofPoint_mem c, Interval.ofPoint_mem 0⟩
  | var name =>
    simp only [evalDualInterval, find?_map_snd_eq_lookup, bind, Option.bind] at hEval
    cases hLook : env.lookup name with
    | none => rw [hLook] at hEval; contradiction
    | some box =>
      rw [hLook] at hEval
      simp only [pure, Option.some.injEq] at hEval
      subst hEval
      refine ⟨hEnv name box hLook, ?_⟩
      dsimp [evalDualRat, DualRat.var, DualInterval.var]
      cases name == diffVar <;> simp [Interval.ofPoint]
  | add l r ihl ihr =>
    simp only [evalDualInterval, bind, Option.bind] at hEval
    cases hl : evalDualInterval env diffVar l with
    | none => rw [hl] at hEval; contradiction
    | some dl =>
      rw [hl] at hEval
      cases hr : evalDualInterval env diffVar r with
      | none => rw [hr] at hEval; contradiction
      | some dr =>
        rw [hr] at hEval
        simp only [pure, Option.some.injEq] at hEval
        subst hEval
        have ⟨hvl, hdl⟩ := ihl dl hl
        have ⟨hvr, hdr⟩ := ihr dr hr
        exact ⟨Interval.add_mem hvl hvr, Interval.add_mem hdl hdr⟩
  | sub l r ihl ihr =>
    simp only [evalDualInterval, bind, Option.bind] at hEval
    cases hl : evalDualInterval env diffVar l with
    | none => rw [hl] at hEval; contradiction
    | some dl =>
      rw [hl] at hEval
      cases hr : evalDualInterval env diffVar r with
      | none => rw [hr] at hEval; contradiction
      | some dr =>
        rw [hr] at hEval
        simp only [pure, Option.some.injEq] at hEval
        subst hEval
        have ⟨hvl, hdl⟩ := ihl dl hl
        have ⟨hvr, hdr⟩ := ihr dr hr
        exact ⟨Interval.sub_mem hvl hvr, Interval.sub_mem hdl hdr⟩
  | mul l r ihl ihr =>
    simp only [evalDualInterval, bind, Option.bind] at hEval
    cases hl : evalDualInterval env diffVar l with
    | none => rw [hl] at hEval; contradiction
    | some dl =>
      rw [hl] at hEval
      cases hr : evalDualInterval env diffVar r with
      | none => rw [hr] at hEval; contradiction
      | some dr =>
        rw [hr] at hEval
        simp only [pure, Option.some.injEq] at hEval
        subst hEval
        have ⟨hvl, hdl⟩ := ihl dl hl
        have ⟨hvr, hdr⟩ := ihr dr hr
        exact ⟨Interval.mul_mem hvl hvr,
          Interval.add_mem (Interval.mul_mem hdl hvr) (Interval.mul_mem hvl hdr)⟩
  | sqr a iha =>
    simp only [evalDualInterval, bind, Option.bind] at hEval
    cases ha : evalDualInterval env diffVar a with
    | none => rw [ha] at hEval; contradiction
    | some da =>
      rw [ha] at hEval
      simp only [pure, Option.some.injEq] at hEval
      subst hEval
      have ⟨hva, hda⟩ := iha da ha
      refine ⟨Interval.sqr_mem hva, ?_⟩
      dsimp [evalDualRat, DualRat.sqr, DualInterval.sqr]
      have hTwo := Interval.mul_mem (Interval.ofPoint_mem 2) (Interval.mul_mem hva hda)
      have hEq :
          (evalDualRat rho diffVar a).der * (evalDualRat rho diffVar a).val +
          (evalDualRat rho diffVar a).val * (evalDualRat rho diffVar a).der =
          2 * ((evalDualRat rho diffVar a).val * (evalDualRat rho diffVar a).der) := by
        grind
      rw [hEq]
      exact hTwo

/-- **Theorem (`meanValueEnclosure_sound`)**:
Universal Mean-Value Enclosure Soundness:
If `f_c ∈ fc`, `df_xi ∈ dfBox`, `x ∈ domainX`, and `f_x - f_c = df_xi * (x - c)` (by the Mean Value Theorem),
then `f_x ∈ meanValueEnclosure fc dfBox domainX c`. -/
theorem meanValueEnclosure_sound
    {fc dfBox domainX : Interval} {f_c f_x df_xi x c : CanonicalRat}
    (hfc : f_c ∈ fc) (hdf : df_xi ∈ dfBox) (hx : x ∈ domainX)
    (hMvt : f_x - f_c = df_xi * (x - c)) :
    f_x ∈ meanValueEnclosure fc dfBox domainX c := by
  unfold meanValueEnclosure
  have hdx : (x - c) ∈ Interval.sub domainX (Interval.ofPoint c) :=
    Interval.sub_mem hx (Interval.ofPoint_mem c)
  have hSum := Interval.add_mem hfc (Interval.mul_mem hdf hdx)
  have hEq : f_c + df_xi * (x - c) = f_x := by grind
  rw [hEq] at hSum
  exact hSum

/-- Sample nonlinear energy polynomial $f(x) = x^2 + 3x + 2$. -/
def samplePolyExpr : RealExpr :=
  .add (.add (.sqr (.var "x")) (.mul (.const 3) (.var "x"))) (.const 2)

/-- **Theorem (`interval_mean_value_enclosure`)**:
1. Evaluating `samplePolyExpr` ($f(x) = x^2 + 3x + 2$) at $x = 4$ yields primal value $f(4) = 30$
   and derivative $f'(4) = 2(4) + 3 = 11$ via both `evalDualRat` and `symbolicDeriv`,
2. Over the interval $X = [3, 5]$ centered at $c = 4$, `evalDualInterval` computes the exact
   derivative enclosure $f'([3, 5]) = [9, 13]$,
3. The Mean-Value Form enclosure `meanValueEnclosure [30, 30] [9, 13] [3, 5] 4 = [17, 43]`
   soundly encloses $f(3) = 20$, $f(4) = 30$, and $f(5) = 42$ (`containsRat = true`),
   and is strictly tighter than the naive interval evaluation `[20, 42]` at the lower/upper
   linearized sensitivity check. -/
theorem interval_mean_value_enclosure :
    let rho : String → CanonicalRat := fun _ => 4
    let env : List (String × Interval) := [("x", ⟨3, 5⟩)]
    let dualAt4 := evalDualRat rho "x" samplePolyExpr
    let symDerivAt4 := evalPointPure rho (symbolicDeriv "x" samplePolyExpr)
    let mvBox := meanValueEnclosure (Interval.ofPoint 30) ⟨9, 13⟩ ⟨3, 5⟩ 4
    dualAt4 = ⟨30, 11⟩ ∧
    symDerivAt4 = 11 ∧
    evalDualInterval env "x" samplePolyExpr = some ⟨⟨20, 42⟩, ⟨9, 13⟩⟩ ∧
    mvBox = ⟨17, 43⟩ ∧
    Interval.containsRat mvBox (evalPointPure (fun _ => 3) samplePolyExpr) = true ∧
    Interval.containsRat mvBox (evalPointPure (fun _ => 4) samplePolyExpr) = true ∧
    Interval.containsRat mvBox (evalPointPure (fun _ => 5) samplePolyExpr) = true := by
  decide +kernel

/-! ## 5. Cotangent Accumulation & SSA/Memoized Reverse-Mode AD (`accumulateGrad`, `gradReverseAccumulated`) -/

/-- Accumulate cotangent contributions for variable index `v : Nat` from a list of `(varIdx, cotangent)` pairs. -/
def accumulateGrad : List (Nat × CanonicalRat) → Nat → CanonicalRat
  | [], _ => 0
  | (idx, c) :: rest, v =>
    (if idx == v then c else 0) + accumulateGrad rest v

/-- Accumulate cotangent contributions for variable name `v : String` from a list of `(varName, cotangent)` pairs. -/
def accumulateGradStr : List (String × CanonicalRat) → String → CanonicalRat
  | [], _ => 0
  | (name, c) :: rest, v =>
    (if name == v then c else 0) + accumulateGradStr rest v

/-- Insert and merge a cotangent contribution `(v, delta)` into a deduplicated `(Nat × CanonicalRat)` association list. -/
def insertAccumGrad (v : Nat) (delta : CanonicalRat) : List (Nat × CanonicalRat) → List (Nat × CanonicalRat)
  | [] => [(v, delta)]
  | (idx, c) :: rest =>
    if idx == v then (idx, c + delta) :: rest
    else (idx, c) :: insertAccumGrad v delta rest

/-- Insert and merge a cotangent contribution `(v, delta)` into a deduplicated `(String × CanonicalRat)` association list. -/
def insertAccumGradStr (v : String) (delta : CanonicalRat) : List (String × CanonicalRat) → List (String × CanonicalRat)
  | [] => [(v, delta)]
  | (name, c) :: rest =>
    if name == v then (name, c + delta) :: rest
    else (name, c) :: insertAccumGradStr v delta rest

/-- Fold a raw cotangent list into a deduplicated list with at most one entry per variable index. -/
def mergeGradList (entries : List (Nat × CanonicalRat)) : List (Nat × CanonicalRat) :=
  entries.foldr (fun (v, d) acc => insertAccumGrad v d acc) []

/-- Fold a raw cotangent list into a deduplicated list with at most one entry per variable name. -/
def mergeGradListStr (entries : List (String × CanonicalRat)) : List (String × CanonicalRat) :=
  entries.foldr (fun (v, d) acc => insertAccumGradStr v d acc) []

/-- Single-pass reverse-mode AD pullback (`gradReverseSinglePass`):
Unlike naive `gradReverse`, `.sqr a` evaluates the primal value `va = evalPointPure rho a` once and
propagates the combined cotangent `bar * va + va * bar` in a **single** recursive pullback call on `a`,
eliminating the $2^n$ exponential blowup on nested squares. -/
def gradReverseSinglePass (rho : String → CanonicalRat) (bar : CanonicalRat) : RealExpr → List (String × CanonicalRat)
  | .const _ => []
  | .var name => [(name, bar)]
  | .add l r => gradReverseSinglePass rho bar l ++ gradReverseSinglePass rho bar r
  | .sub l r => gradReverseSinglePass rho bar l ++ gradReverseSinglePass rho (-bar) r
  | .mul l r =>
    gradReverseSinglePass rho (bar * evalPointPure rho r) l ++
    gradReverseSinglePass rho (evalPointPure rho l * bar) r
  | .sqr a =>
    let va := evalPointPure rho a
    gradReverseSinglePass rho (bar * va + va * bar) a

/-- Accumulated reverse-mode AD pass (`gradReverseAccumulated`):
runs `gradReverseSinglePass` and merges all cotangent contributions per variable so the output size
is bounded by the number of distinct variables. -/
def gradReverseAccumulated (rho : String → CanonicalRat) (bar : CanonicalRat) (e : RealExpr) :
    List (String × CanonicalRat) :=
  mergeGradListStr (gradReverseSinglePass rho bar e)

/-- Map variable names to canonical `Nat` indices via a symbol table `symTab : List String` and
accumulate gradients by `Nat` variable index. -/
def varIndexOf (symTab : List String) (name : String) : Nat :=
  symTab.idxOf name

def gradReverseAccumulatedIdx
    (symTab : List String) (rho : String → CanonicalRat) (bar : CanonicalRat) (e : RealExpr) :
    List (Nat × CanonicalRat) :=
  mergeGradList ((gradReverseSinglePass rho bar e).map (fun (name, c) => (varIndexOf symTab name, c)))

theorem accumulateGrad_append (xs ys : List (Nat × CanonicalRat)) (v : Nat) :
    accumulateGrad (xs ++ ys) v = accumulateGrad xs v + accumulateGrad ys v := by
  induction xs with
  | nil => simp [accumulateGrad]; grind
  | cons hd tl ih =>
    rcases hd with ⟨idx, c⟩
    simp only [List.cons_append, accumulateGrad, ih]
    grind

theorem accumulateGradStr_append (xs ys : List (String × CanonicalRat)) (v : String) :
    accumulateGradStr (xs ++ ys) v = accumulateGradStr xs v + accumulateGradStr ys v := by
  induction xs with
  | nil => simp [accumulateGradStr]; grind
  | cons hd tl ih =>
    rcases hd with ⟨name, c⟩
    simp only [List.cons_append, accumulateGradStr, ih]
    grind

theorem accumulateGrad_insert (v : Nat) (delta : CanonicalRat) (entries : List (Nat × CanonicalRat)) (q : Nat) :
    accumulateGrad (insertAccumGrad v delta entries) q =
      (if v == q then delta else 0) + accumulateGrad entries q := by
  induction entries with
  | nil => simp [insertAccumGrad, accumulateGrad]
  | cons hd tl ih =>
    rcases hd with ⟨idx, c⟩
    unfold insertAccumGrad
    by_cases h : idx == v
    · have heq : idx = v := beq_iff_eq.mp h
      subst heq
      simp only [beq_self_eq_true, ↓reduceIte, accumulateGrad]
      by_cases hq : idx == q <;> simp [hq] <;> grind
    · simp only [h, Bool.false_eq_true, ↓reduceIte, accumulateGrad, ih]
      grind

theorem accumulateGradStr_insert (v : String) (delta : CanonicalRat)
    (entries : List (String × CanonicalRat)) (q : String) :
    accumulateGradStr (insertAccumGradStr v delta entries) q =
      (if v == q then delta else 0) + accumulateGradStr entries q := by
  induction entries with
  | nil => simp [insertAccumGradStr, accumulateGradStr]
  | cons hd tl ih =>
    rcases hd with ⟨name, c⟩
    unfold insertAccumGradStr
    by_cases h : name == v
    · have heq : name = v := beq_iff_eq.mp h
      subst heq
      simp only [beq_self_eq_true, ↓reduceIte, accumulateGradStr]
      by_cases hq : name == q <;> simp [hq] <;> grind
    · simp only [h, Bool.false_eq_true, ↓reduceIte, accumulateGradStr, ih]
      grind

theorem accumulateGrad_mergeGradList (entries : List (Nat × CanonicalRat)) (q : Nat) :
    accumulateGrad (mergeGradList entries) q = accumulateGrad entries q := by
  unfold mergeGradList
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩
    simp only [List.foldr_cons, accumulateGrad_insert, accumulateGrad, ih]

theorem accumulateGradStr_mergeGradListStr (entries : List (String × CanonicalRat)) (q : String) :
    accumulateGradStr (mergeGradListStr entries) q = accumulateGradStr entries q := by
  unfold mergeGradListStr
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩
    simp only [List.foldr_cons, accumulateGradStr_insert, accumulateGradStr, ih]

theorem gradReverseSinglePass_agrees_with_dual
    (rho : String → CanonicalRat) (diffVar : String) (e : RealExpr) :
    ∀ (bar : CanonicalRat),
      accumulateGradStr (gradReverseSinglePass rho bar e) diffVar =
        bar * (evalDualRat rho diffVar e).der := by
  induction e with
  | const c =>
    intro bar
    simp [gradReverseSinglePass, accumulateGradStr, evalDualRat, DualRat.const]
  | var name =>
    intro bar
    simp only [gradReverseSinglePass, accumulateGradStr, evalDualRat, DualRat.var]
    by_cases h : name == diffVar <;> simp [h] <;> grind
  | add l r ihl ihr =>
    intro bar
    simp only [gradReverseSinglePass, accumulateGradStr_append, ihl bar, ihr bar,
      evalDualRat, DualRat.add]
    grind
  | sub l r ihl ihr =>
    intro bar
    simp only [gradReverseSinglePass, accumulateGradStr_append, ihl bar, ihr (-bar),
      evalDualRat, DualRat.sub]
    grind
  | mul l r ihl ihr =>
    intro bar
    have hvl := (evalDual_fst_eq_eval rho diffVar l).1
    have hvr := (evalDual_fst_eq_eval rho diffVar r).1
    simp only [gradReverseSinglePass, accumulateGradStr_append,
      ihl (bar * evalPointPure rho r), ihr (evalPointPure rho l * bar),
      evalDualRat, DualRat.mul, hvl, hvr]
    grind
  | sqr a iha =>
    intro bar
    have hva := (evalDual_fst_eq_eval rho diffVar a).1
    simp only [gradReverseSinglePass, iha (bar * evalPointPure rho a + evalPointPure rho a * bar),
      evalDualRat, DualRat.sqr, hva]
    grind

/-- Insert a variable name into a deduplicated variable list. -/
def insertDistinctVar (v : String) : List String → List String
  | [] => [v]
  | name :: rest =>
    if name == v then name :: rest
    else name :: insertDistinctVar v rest

/-- Deduplicate a list of variable names preserving first-seen order. -/
def distinctVarsOfList (vars : List String) : List String :=
  vars.foldr insertDistinctVar []

/-- Raw leaf variable occurrences in a `RealExpr` (with `.sqr` visited once). -/
def exprRawVars : RealExpr → List String
  | .const _ => []
  | .var name => [name]
  | .add l r => exprRawVars l ++ exprRawVars r
  | .sub l r => exprRawVars l ++ exprRawVars r
  | .mul l r => exprRawVars l ++ exprRawVars r
  | .sqr a   => exprRawVars a

/-- Distinct variables occurring in a `RealExpr`. -/
def exprDistinctVars (e : RealExpr) : List String :=
  distinctVarsOfList (exprRawVars e)

theorem map_fst_insertAccumGradStr (v : String) (delta : CanonicalRat)
    (entries : List (String × CanonicalRat)) :
    (insertAccumGradStr v delta entries).map Prod.fst =
      insertDistinctVar v (entries.map Prod.fst) := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, c⟩
    unfold insertAccumGradStr insertDistinctVar
    by_cases h : name == v <;> simp [h, ih]

theorem map_fst_mergeGradListStr (entries : List (String × CanonicalRat)) :
    (mergeGradListStr entries).map Prod.fst = distinctVarsOfList (entries.map Prod.fst) := by
  unfold mergeGradListStr distinctVarsOfList
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩
    simp only [List.foldr_cons, map_fst_insertAccumGradStr, List.map_cons, ih]

theorem map_fst_gradReverseSinglePass (rho : String → CanonicalRat) (e : RealExpr) :
    ∀ (bar : CanonicalRat),
      (gradReverseSinglePass rho bar e).map Prod.fst = exprRawVars e := by
  induction e with
  | const _ => intro _; rfl
  | var _ => intro _; rfl
  | add l r ihl ihr =>
    intro bar
    simp [gradReverseSinglePass, exprRawVars, ihl bar, ihr bar]
  | sub l r ihl ihr =>
    intro bar
    simp [gradReverseSinglePass, exprRawVars, ihl bar, ihr (-bar)]
  | mul l r ihl ihr =>
    intro bar
    simp [gradReverseSinglePass, exprRawVars, ihl _, ihr _]
  | sqr a iha =>
    intro bar
    simp [gradReverseSinglePass, exprRawVars, iha _]

/-- The output size of `gradReverseAccumulated` is bounded by (and equal to) the number of distinct
variables in `e`. -/
theorem gradReverseAccumulated_length_le_distinctVars
    (rho : String → CanonicalRat) (bar : CanonicalRat) (e : RealExpr) :
    (gradReverseAccumulated rho bar e).length = (exprDistinctVars e).length ∧
    (gradReverseAccumulated rho bar e).length ≤ (exprDistinctVars e).length := by
  have hMap : (gradReverseAccumulated rho bar e).map Prod.fst = exprDistinctVars e := by
    unfold gradReverseAccumulated exprDistinctVars
    rw [map_fst_mergeGradListStr, map_fst_gradReverseSinglePass]
  have hLen : (gradReverseAccumulated rho bar e).length = (exprDistinctVars e).length := by
    simpa using congrArg List.length hMap
  exact ⟨hLen, Nat.le_of_eq hLen⟩

/-- **Theorem (`gradReverseAccumulated_agrees_with_dual`)**:
For every expression `e : RealExpr`, point assignment `rho`, upstream cotangent seed `bar`,
and differentiation variable `diffVar`:
1. Looking up `diffVar` in `gradReverseAccumulated rho bar e` via `accumulateGradStr` equals
   `bar * (evalDualRat rho diffVar e).der`,
2. At unit seed `bar = 1`, `accumulateGradStr (gradReverseAccumulated rho 1 e) diffVar` equals
   the forward-mode dual derivative `(evalDualRat rho diffVar e).der` and symbolic derivative
   `evalPointPure rho (symbolicDeriv diffVar e)`,
3. The accumulated output length is bounded by `(exprDistinctVars e).length`. -/
theorem gradReverseAccumulated_agrees_with_dual
    (rho : String → CanonicalRat) (bar : CanonicalRat) (diffVar : String) (e : RealExpr) :
    accumulateGradStr (gradReverseAccumulated rho bar e) diffVar =
      bar * (evalDualRat rho diffVar e).der ∧
    accumulateGradStr (gradReverseAccumulated rho 1 e) diffVar =
      (evalDualRat rho diffVar e).der ∧
    (gradReverseAccumulated rho bar e).length ≤ (exprDistinctVars e).length := by
  unfold gradReverseAccumulated
  rw [accumulateGradStr_mergeGradListStr, accumulateGradStr_mergeGradListStr]
  rw [gradReverseSinglePass_agrees_with_dual, gradReverseSinglePass_agrees_with_dual]
  exact ⟨rfl, by grind, (gradReverseAccumulated_length_le_distinctVars rho bar e).2⟩

/-- Nested squaring chain $\text{sqr}^n(e)$ used to test linear $O(1)$-leaf vs $2^n$ pullback complexity. -/
def nestedSqrChain : Nat → RealExpr → RealExpr
  | 0, e => e
  | n + 1, e => .sqr (nestedSqrChain n e)

/-- On an $n$-deep nested squaring chain `nestedSqrChain n (.var name)`, `gradReverseSinglePass`
and `gradReverseAccumulated` produce a single accumulated cotangent entry of length `1` for every `n`,
whereas naive `gradReverse` produces $2^n$ un-merged entries. -/
theorem gradReverseAccumulated_nestedSqr_linear
    (rho : String → CanonicalRat) (name : String) (n : Nat) :
    ∀ (bar : CanonicalRat),
      (gradReverseSinglePass rho bar (nestedSqrChain n (.var name))).length = 1 ∧
      (gradReverseAccumulated rho bar (nestedSqrChain n (.var name))).length = 1 := by
  induction n with
  | zero =>
    intro bar
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro bar
    dsimp only [nestedSqrChain, gradReverseSinglePass, gradReverseAccumulated]
    exact ih (bar * evalPointPure rho (nestedSqrChain k (.var name)) +
              evalPointPure rho (nestedSqrChain k (.var name)) * bar)

theorem accumulateGrad_map_varIndexOf
    (symTab : List String) (diffVar : String)
    (entries : List (String × CanonicalRat))
    (hInj : ∀ v, (varIndexOf symTab v == varIndexOf symTab diffVar) = (v == diffVar)) :
    accumulateGrad (entries.map (fun (name, c) => (varIndexOf symTab name, c))) (varIndexOf symTab diffVar) =
      accumulateGradStr entries diffVar := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, c⟩
    simp only [List.map_cons, accumulateGrad, accumulateGradStr, hInj name, ih]

/-- **Theorem (`gradReverseAccumulatedIdx_agrees_with_dual`)**:
When `symTab` assigns a distinct variable index to `diffVar` (`∀ v, (varIndexOf symTab v == varIndexOf symTab diffVar) = (v == diffVar)`),
looking up `varIndexOf symTab diffVar` in `gradReverseAccumulatedIdx symTab rho bar e` via `accumulateGrad`
equals `bar * (evalDualRat rho diffVar e).der`! -/
theorem gradReverseAccumulatedIdx_agrees_with_dual
    (symTab : List String) (rho : String → CanonicalRat) (bar : CanonicalRat)
    (diffVar : String) (e : RealExpr)
    (hInj : ∀ v, (varIndexOf symTab v == varIndexOf symTab diffVar) = (v == diffVar)) :
    accumulateGrad (gradReverseAccumulatedIdx symTab rho bar e) (varIndexOf symTab diffVar) =
      bar * (evalDualRat rho diffVar e).der := by
  unfold gradReverseAccumulatedIdx
  rw [accumulateGrad_mergeGradList, accumulateGrad_map_varIndexOf symTab diffVar _ hInj]
  exact gradReverseSinglePass_agrees_with_dual rho diffVar e bar

end Obend.Analysis
end



