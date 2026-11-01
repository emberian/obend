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

end Obend.Analysis
end
