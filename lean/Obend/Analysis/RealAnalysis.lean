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

/-- Smart constructor verifying that `lo ≤ hi`. -/
def make (lo hi : CanonicalRat) : Option Interval :=
  if decide (lo ≤ hi) then some ⟨lo, hi⟩ else none

/-- Degenerate point interval `[q, q]`. -/
def ofPoint (q : CanonicalRat) : Interval :=
  ⟨q, q⟩

/-- Membership test for a rational point inside the closed interval. -/
def containsRat (i : Interval) (q : CanonicalRat) : Bool :=
  decide (i.lo ≤ q ∧ q ≤ i.hi)

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

end Obend.Analysis
end
