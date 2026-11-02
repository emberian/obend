module
/-
# Obend.Analysis.RealAnalysis — canonical rationals, interval arithmetic and real expressions

Provides:
- `CanonicalRat`: Canonical exact rational arithmetic embedding into `Core.Data`.
- `Interval`: Closed intervals `[lo, hi]` over `CanonicalRat` with exact interval arithmetic.
- `RealExpr`: Arithmetic expressions over real/rational variables and constants.
- `evalInterval` & `evalPoint`: Verified interval enclosure and point evaluation.
-/
public import Obend.Core.Data
public import Obend.Tactic.Tooth

@[expose] public section
namespace Obend.Analysis
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## Canonical Rationals -/

/-- Exact canonical rational number. Lean 4's `Rat` guarantees reduced coprime terms and positive denominator. -/
abbrev CanonicalRat := Rat

namespace CanonicalRat

/-- Smart canonicalizing constructor reducing numerator and denominator to lowest terms. -/
def mk (n : Int) (d : Nat) : CanonicalRat :=
  mkRat n d

def ofInt (n : Int) : CanonicalRat :=
  Rat.ofInt n

def ofNat (n : Nat) : CanonicalRat :=
  Rat.ofInt (Int.ofNat n)

def zero : CanonicalRat := 0
def one : CanonicalRat := 1

def add (a b : CanonicalRat) : CanonicalRat := a + b
def sub (a b : CanonicalRat) : CanonicalRat := a - b
def mul (a b : CanonicalRat) : CanonicalRat := a * b
def div (a b : CanonicalRat) : CanonicalRat := a / b
def neg (a : CanonicalRat) : CanonicalRat := -a
def inv (a : CanonicalRat) : CanonicalRat := a⁻¹

def le (a b : CanonicalRat) : Prop := a ≤ b
def lt (a b : CanonicalRat) : Prop := a < b

def ble (a b : CanonicalRat) : Bool := decide (a ≤ b)
def blt (a b : CanonicalRat) : Bool := decide (a < b)

/-- Wire encoding of CanonicalRat into Core.Data. -/
def toData (r : CanonicalRat) : Data :=
  .variant "rat" (.record [
    ("num", .natural r.num.natAbs),
    ("neg", .boolean (r.num < 0)),
    ("den", .natural r.den)
  ])

/-- Wire decoding of Core.Data into CanonicalRat. -/
def ofData? : Data → Option CanonicalRat
  | .variant "rat" (.record [("num", .natural n), ("neg", .boolean isNeg), ("den", .natural d)]) =>
    if d == 0 then none
    else
      let s : Int := if isNeg then -(n : Int) else (n : Int)
      some (mkRat s d)
  | _ => none

end CanonicalRat

/-! ## Interval Arithmetic -/

/-- Certified closed interval `[lo, hi]`. -/
structure Interval where
  lo : CanonicalRat
  hi : CanonicalRat
  deriving DecidableEq, Repr

namespace Interval

/-- Propositional membership of a rational number `x` in closed interval `I = [I.lo, I.hi]`. -/
def Mem (x : CanonicalRat) (I : Interval) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

instance : Membership CanonicalRat Interval where
  mem I x := Interval.Mem x I

instance (x : CanonicalRat) (I : Interval) : Decidable (Interval.Mem x I) :=
  inferInstanceAs (Decidable (I.lo ≤ x ∧ x ≤ I.hi))

instance (x : CanonicalRat) (I : Interval) : Decidable (x ∈ I) :=
  inferInstanceAs (Decidable (I.lo ≤ x ∧ x ≤ I.hi))

@[simp] theorem mem_iff (x : CanonicalRat) (I : Interval) :
    (x ∈ I) ↔ (I.lo ≤ x ∧ x ≤ I.hi) := Iff.rfl

@[simp] theorem Mem_iff_mem (x : CanonicalRat) (I : Interval) :
    Interval.Mem x I ↔ x ∈ I := Iff.rfl

/-- Well-formedness of an interval: `I.lo ≤ I.hi`. -/
def Wf (I : Interval) : Prop :=
  I.lo ≤ I.hi

/-- Smart constructor verifying that `lo ≤ hi`. -/
def make (lo hi : CanonicalRat) : Option Interval :=
  if decide (lo ≤ hi) then some ⟨lo, hi⟩ else none

/-- Degenerate point interval `[q, q]`. -/
def ofPoint (q : CanonicalRat) : Interval :=
  ⟨q, q⟩

/-- Membership test for a rational point inside the closed interval. -/
def containsRat (i : Interval) (q : CanonicalRat) : Bool :=
  decide (i.lo ≤ q ∧ q ≤ i.hi)

/-- Boolean sub-interval inclusion test (`outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi`). -/
def subset (inner outer : Interval) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

@[simp] theorem containsRat_iff_mem (I : Interval) (x : CanonicalRat) :
    I.containsRat x = true ↔ x ∈ I := by
  simp [containsRat, mem_iff]

theorem subset_iff (inner outer : Interval) :
    Interval.subset inner outer = true ↔ (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi) := by
  simp [subset]

theorem subset_sound {inner outer : Interval} {x : CanonicalRat}
    (hSub : Interval.subset inner outer = true) (hx : x ∈ inner) :
    x ∈ outer := by
  rw [subset_iff] at hSub
  rw [mem_iff] at hx ⊢
  grind

theorem mem_imp_wf {x : CanonicalRat} {I : Interval} (hx : x ∈ I) : I.Wf := by
  rw [mem_iff] at hx
  unfold Wf
  grind

theorem ofPoint_mem (q : CanonicalRat) : q ∈ Interval.ofPoint q := by
  simp [ofPoint]

theorem ofPoint_wf (q : CanonicalRat) : (Interval.ofPoint q).Wf :=
  mem_imp_wf (ofPoint_mem q)

/-- Interval addition: `[a.lo + b.lo, a.hi + b.hi]`. -/
def add (a b : Interval) : Interval :=
  ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Interval negation: `[-a.hi, -a.lo]`. -/
def neg (a : Interval) : Interval :=
  ⟨-a.hi, -a.lo⟩

/-- Interval subtraction: `[a.lo - b.hi, a.hi - b.lo]`. -/
def sub (a b : Interval) : Interval :=
  ⟨a.lo - b.hi, a.hi - b.lo⟩

def min4 (a b c d : CanonicalRat) : CanonicalRat :=
  min (min a b) (min c d)

def max4 (a b c d : CanonicalRat) : CanonicalRat :=
  max (max a b) (max c d)

/-- Interval multiplication: enclosure over all 4 endpoint products. -/
def mul (a b : Interval) : Interval :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨min4 p1 p2 p3 p4, max4 p1 p2 p3 p4⟩

/-- Interval squaring: handles intervals spanning zero. -/
def sqr (a : Interval) : Interval :=
  if decide (a.lo ≤ 0 ∧ 0 ≤ a.hi) then
    ⟨0, max (a.lo * a.lo) (a.hi * a.hi)⟩
  else
    let s1 := a.lo * a.lo
    let s2 := a.hi * a.hi
    ⟨min s1 s2, max s1 s2⟩

/-! ### Universal Interval Soundness Theorems over `Rat` -/

/-- **Theorem (`Interval.add_mem`)**: Interval addition encloses `x + y` for all `x ∈ A, y ∈ B`. -/
theorem add_mem {x y : CanonicalRat} {A B : Interval}
    (hx : x ∈ A) (hy : y ∈ B) :
    (x + y) ∈ Interval.add A B := by
  rw [mem_iff] at hx hy ⊢
  dsimp [Interval.add]
  grind

theorem add_wf {A B : Interval} (hA : A.Wf) (hB : B.Wf) : (Interval.add A B).Wf := by
  unfold Wf at hA hB ⊢
  dsimp [Interval.add]
  grind

/-- **Theorem (`Interval.neg_mem`)**: Interval negation encloses `-x` for all `x ∈ A`. -/
theorem neg_mem {x : CanonicalRat} {A : Interval}
    (hx : x ∈ A) :
    (-x) ∈ Interval.neg A := by
  rw [mem_iff] at hx ⊢
  dsimp [Interval.neg]
  grind

theorem neg_wf {A : Interval} (hA : A.Wf) : (Interval.neg A).Wf := by
  unfold Wf at hA ⊢
  dsimp [Interval.neg]
  grind

/-- **Theorem (`Interval.sub_mem`)**: Interval subtraction encloses `x - y` for all `x ∈ A, y ∈ B`. -/
theorem sub_mem {x y : CanonicalRat} {A B : Interval}
    (hx : x ∈ A) (hy : y ∈ B) :
    (x - y) ∈ Interval.sub A B := by
  rw [mem_iff] at hx hy ⊢
  dsimp [Interval.sub]
  grind

theorem sub_wf {A B : Interval} (hA : A.Wf) (hB : B.Wf) : (Interval.sub A B).Wf := by
  unfold Wf at hA hB ⊢
  dsimp [Interval.sub]
  grind

theorem mul_le_mul_of_nonpos_left {a b c : CanonicalRat} (h : a ≤ b) (hc : c ≤ 0) :
    c * b ≤ c * a := by
  have hc' : 0 ≤ -c := by grind
  have h1 := Rat.mul_le_mul_of_nonneg_left h hc'
  grind

theorem mul_le_mul_of_nonpos_right {a b c : CanonicalRat} (h : a ≤ b) (hc : c ≤ 0) :
    b * c ≤ a * c := by
  have hc' : 0 ≤ -c := by grind
  have h1 := Rat.mul_le_mul_of_nonneg_right h hc'
  grind

theorem mul_bounds_left (x blo bhi y : CanonicalRat) (hy1 : blo ≤ y) (hy2 : y ≤ bhi) :
    min (x * blo) (x * bhi) ≤ x * y ∧ x * y ≤ max (x * blo) (x * bhi) := by
  rcases @Rat.le_total 0 x with hx | hx
  · have h1 := Rat.mul_le_mul_of_nonneg_left hy1 hx
    have h2 := Rat.mul_le_mul_of_nonneg_left hy2 hx
    grind
  · have h1 := mul_le_mul_of_nonpos_left hy1 hx
    have h2 := mul_le_mul_of_nonpos_left hy2 hx
    grind

theorem mul_bounds_right (alo ahi x c : CanonicalRat) (hx1 : alo ≤ x) (hx2 : x ≤ ahi) :
    min (alo * c) (ahi * c) ≤ x * c ∧ x * c ≤ max (alo * c) (ahi * c) := by
  rcases @Rat.le_total 0 c with hc | hc
  · have h1 := Rat.mul_le_mul_of_nonneg_right hx1 hc
    have h2 := Rat.mul_le_mul_of_nonneg_right hx2 hc
    grind
  · have h1 := mul_le_mul_of_nonpos_right hx1 hc
    have h2 := mul_le_mul_of_nonpos_right hx2 hc
    grind

/-- **Theorem (`Interval.mul_mem`)**: 4-corner interval multiplication encloses `x * y` for all `x ∈ A, y ∈ B`. -/
theorem mul_mem {x y : CanonicalRat} {A B : Interval}
    (hx : x ∈ A) (hy : y ∈ B) :
    (x * y) ∈ Interval.mul A B := by
  rw [mem_iff] at hx hy ⊢
  dsimp [Interval.mul, min4, max4]
  have hxy := mul_bounds_left x B.lo B.hi y hy.1 hy.2
  have hlo := mul_bounds_right A.lo A.hi x B.lo hx.1 hx.2
  have hhi := mul_bounds_right A.lo A.hi x B.hi hx.1 hx.2
  grind

theorem mul_wf {A B : Interval} (hA : A.Wf) (hB : B.Wf) : (Interval.mul A B).Wf :=
  mem_imp_wf (mul_mem (x := A.lo) (y := B.lo) ⟨by grind, hA⟩ ⟨by grind, hB⟩)

theorem rat_sq_nonneg (x : CanonicalRat) : 0 ≤ x * x := by
  rcases @Rat.le_total 0 x with hx | hx
  · have h := Rat.mul_le_mul_of_nonneg_left hx hx
    grind
  · have h := mul_le_mul_of_nonpos_left hx hx
    grind

/-- **Theorem (`Interval.sqr_mem`)**: Interval squaring encloses `x * x` for all `x ∈ A`. -/
theorem sqr_mem {x : CanonicalRat} {A : Interval}
    (hx : x ∈ A) :
    (x * x) ∈ Interval.sqr A := by
  rw [mem_iff] at hx ⊢
  unfold Interval.sqr
  have h0 := rat_sq_nonneg x
  rcases @Rat.le_total 0 x with hx0 | hx0
  · have hhi : 0 ≤ A.hi := by grind
    have h1 := Rat.mul_le_mul_of_nonneg_left hx.2 hx0
    have h2 := Rat.mul_le_mul_of_nonneg_right hx.2 hhi
    by_cases hcond : A.lo ≤ 0 ∧ 0 ≤ A.hi
    · simp only [hcond]
      grind
    · simp only [hcond, decide_false, Bool.false_eq_true, ↓reduceIte]
      have halo : 0 ≤ A.lo := by grind
      have h3 := Rat.mul_le_mul_of_nonneg_left hx.1 halo
      have h4 := Rat.mul_le_mul_of_nonneg_right hx.1 hx0
      grind
  · have hlo : A.lo ≤ 0 := by grind
    have h1 := mul_le_mul_of_nonpos_left hx.1 hx0
    have h2 := mul_le_mul_of_nonpos_right hx.1 hlo
    by_cases hcond : A.lo ≤ 0 ∧ 0 ≤ A.hi
    · simp only [hcond]
      grind
    · simp only [hcond, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hahi : A.hi ≤ 0 := by grind
      have h3 := mul_le_mul_of_nonpos_left hx.2 hahi
      have h4 := mul_le_mul_of_nonpos_right hx.2 hx0
      grind

theorem sqr_wf {A : Interval} (hA : A.Wf) : (Interval.sqr A).Wf :=
  mem_imp_wf (sqr_mem (x := A.lo) ⟨by grind, hA⟩)

end Interval

/-! ## Real Expression Syntax & Evaluation -/

/-- Real and rational arithmetic expression. -/
inductive RealExpr where
  | const (val : CanonicalRat)
  | var (name : String)
  | add (l r : RealExpr)
  | sub (l r : RealExpr)
  | mul (l r : RealExpr)
  | sqr (a : RealExpr)
  deriving DecidableEq, Repr

/-- Evaluate a RealExpr over an interval environment. -/
def evalInterval (env : List (String × Interval)) : RealExpr → Option Interval
  | .const c => some (Interval.ofPoint c)
  | .var name => (env.find? (·.1 == name)).map (·.2)
  | .add l r => do
      let il ← evalInterval env l
      let ir ← evalInterval env r
      pure (Interval.add il ir)
  | .sub l r => do
      let il ← evalInterval env l
      let ir ← evalInterval env r
      pure (Interval.sub il ir)
  | .mul l r => do
      let il ← evalInterval env l
      let ir ← evalInterval env r
      pure (Interval.mul il ir)
  | .sqr a => do
      let ia ← evalInterval env a
      pure (Interval.sqr ia)

/-- Total point evaluator for a `RealExpr` at a rational assignment `rho : String → CanonicalRat`. -/
def evalExpr (rho : String → CanonicalRat) : RealExpr → CanonicalRat
  | .const c => c
  | .var name => rho name
  | .add l r => evalExpr rho l + evalExpr rho r
  | .sub l r => evalExpr rho l - evalExpr rho r
  | .mul l r => evalExpr rho l * evalExpr rho r
  | .sqr a   => evalExpr rho a * evalExpr rho a

/-- Evaluate a RealExpr at a concrete rational point assignment. -/
def evalPoint (rho : String → CanonicalRat) : RealExpr → Option CanonicalRat
  | .const c => some c
  | .var name => some (rho name)
  | .add l r => do
      let vl ← evalPoint rho l
      let vr ← evalPoint rho r
      pure (vl + vr)
  | .sub l r => do
      let vl ← evalPoint rho l
      let vr ← evalPoint rho r
      pure (vl - vr)
  | .mul l r => do
      let vl ← evalPoint rho l
      let vr ← evalPoint rho r
      pure (vl * vr)
  | .sqr a => do
      let va ← evalPoint rho a
      pure (va * va)

theorem evalPoint_eq_some_evalExpr (rho : String → CanonicalRat) :
    ∀ (e : RealExpr), evalPoint rho e = some (evalExpr rho e)
  | .const _ => rfl
  | .var _   => rfl
  | .add l r => by
    simp [evalPoint, evalExpr, evalPoint_eq_some_evalExpr rho l, evalPoint_eq_some_evalExpr rho r]
  | .sub l r => by
    simp [evalPoint, evalExpr, evalPoint_eq_some_evalExpr rho l, evalPoint_eq_some_evalExpr rho r]
  | .mul l r => by
    simp [evalPoint, evalExpr, evalPoint_eq_some_evalExpr rho l, evalPoint_eq_some_evalExpr rho r]
  | .sqr a => by
    simp [evalPoint, evalExpr, evalPoint_eq_some_evalExpr rho a]

@[simp] theorem find?_map_snd_eq_lookup (env : List (String × Interval)) (v : String) :
    (env.find? (·.1 == v)).map (·.2) = env.lookup v := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, val⟩
    simp only [List.find?_cons, List.lookup]
    have h : (k == v) = (v == k) := by
      cases hkv : k == v <;> cases hvk : v == k <;> simp_all [beq_iff_eq]
    rw [h]
    cases v == k <;> simp [ih]

/-- **Theorem (`evalInterval_sound`)**:
Fundamental Theorem of Interval Arithmetic for `RealExpr`:
For any expression `e : RealExpr`, interval environment `env`, and point assignment `rho`
enclosed by `env` (`∀ v I, env.lookup v = some I → rho v ∈ I`), if `evalInterval env e = some I`,
then `evalExpr rho e ∈ I`. -/
theorem evalInterval_sound
    (env : List (String × Interval))
    (rho : String → CanonicalRat)
    (hEnv : ∀ v I, env.lookup v = some I → rho v ∈ I)
    (e : RealExpr) (I : Interval)
    (hEval : evalInterval env e = some I) :
    evalExpr rho e ∈ I := by
  induction e generalizing I with
  | const c =>
    simp only [evalInterval, Option.some.injEq] at hEval
    subst hEval
    exact Interval.ofPoint_mem c
  | var name =>
    simp only [evalInterval, find?_map_snd_eq_lookup] at hEval
    exact hEnv name I hEval
  | add l r ihl ihr =>
    simp only [evalInterval, bind, Option.bind] at hEval
    cases hl : evalInterval env l with
    | none => rw [hl] at hEval; contradiction
    | some il =>
      rw [hl] at hEval
      cases hr : evalInterval env r with
      | none => rw [hr] at hEval; contradiction
      | some ir =>
        rw [hr] at hEval
        simp only [pure, Option.some.injEq] at hEval
        subst hEval
        exact Interval.add_mem (ihl il hl) (ihr ir hr)
  | sub l r ihl ihr =>
    simp only [evalInterval, bind, Option.bind] at hEval
    cases hl : evalInterval env l with
    | none => rw [hl] at hEval; contradiction
    | some il =>
      rw [hl] at hEval
      cases hr : evalInterval env r with
      | none => rw [hr] at hEval; contradiction
      | some ir =>
        rw [hr] at hEval
        simp only [pure, Option.some.injEq] at hEval
        subst hEval
        exact Interval.sub_mem (ihl il hl) (ihr ir hr)
  | mul l r ihl ihr =>
    simp only [evalInterval, bind, Option.bind] at hEval
    cases hl : evalInterval env l with
    | none => rw [hl] at hEval; contradiction
    | some il =>
      rw [hl] at hEval
      cases hr : evalInterval env r with
      | none => rw [hr] at hEval; contradiction
      | some ir =>
        rw [hr] at hEval
        simp only [pure, Option.some.injEq] at hEval
        subst hEval
        exact Interval.mul_mem (ihl il hl) (ihr ir hr)
  | sqr a iha =>
    simp only [evalInterval, bind, Option.bind] at hEval
    cases ha : evalInterval env a with
    | none => rw [ha] at hEval; contradiction
    | some ia =>
      rw [ha] at hEval
      simp only [pure, Option.some.injEq] at hEval
      subst hEval
      exact Interval.sqr_mem (iha ia ha)

/-! ## `#tooth` Mutation Probes for `Interval.add`, `Interval.mul`, and `evalInterval_sound` -/

/-- Broken `Interval.add` that drops `b` and returns `a`. -/
def intervalAddDropB (a _b : Interval) : Interval := a

#tooth Interval.add_mem by mutation Interval.add := intervalAddDropB

/-- Broken `Interval.mul` that only multiplies endpoints `(a.lo * b.lo, a.hi * b.hi)` instead of 4-corner min/max. -/
def intervalMulNaiveEndpoints (a b : Interval) : Interval :=
  ⟨a.lo * b.lo, a.hi * b.hi⟩

#tooth Interval.mul_mem by mutation Interval.mul := intervalMulNaiveEndpoints

/-- Broken `evalInterval` that maps `.sub` to `Interval.add` instead of `Interval.sub`. -/
def evalIntervalSubAsAdd (env : List (String × Interval)) : RealExpr → Option Interval
  | .const c => some (Interval.ofPoint c)
  | .var name => (env.find? (·.1 == name)).map (·.2)
  | .add l r => do
      let il ← evalIntervalSubAsAdd env l
      let ir ← evalIntervalSubAsAdd env r
      pure (Interval.add il ir)
  | .sub l r => do
      let il ← evalIntervalSubAsAdd env l
      let ir ← evalIntervalSubAsAdd env r
      pure (Interval.add il ir)
  | .mul l r => do
      let il ← evalIntervalSubAsAdd env l
      let ir ← evalIntervalSubAsAdd env r
      pure (Interval.mul il ir)
  | .sqr a => do
      let ia ← evalIntervalSubAsAdd env a
      pure (Interval.sqr ia)

#tooth evalInterval_sound by mutation evalInterval := evalIntervalSubAsAdd

end Obend.Analysis
end

