module
/-
# Obend.Judge.RealAnalysis — certified interval arithmetic and polynomial SOS judges

Provides:
- `intervalJudge`: Verifies exact numerical interval bounds against `RealExpr` evaluations.
- `sosJudge`: Verifies polynomial Sum-of-Squares (SOS) non-negativity certificates and Putinar/Gröbner constraints.
-/
public import Obend.Judge.Class
public import Obend.Analysis.RealAnalysis

@[expose] public section
namespace Obend.Judge
open Obend.Analysis
open Obend.Analysis.CanonicalRat
set_option autoImplicit false

/-! ## Certified Interval Judge (`interval@1`) -/

/-- Query specifying an arithmetic expression, domain bounds for variables, and the claimed enclosure. -/
structure IntervalQuery where
  expr : RealExpr
  env : List (String × Interval)
  claimedBound : Interval
  deriving DecidableEq, Repr

/-- Certificate for an interval query: direct evaluation or counterexample refutation point. -/
inductive IntervalCert where
  | direct
  | counterexample (point : List (String × CanonicalRat))
  deriving DecidableEq, Repr

/-- Refusal clauses for interval verification. -/
inductive IntervalClause where
  | boundViolated (computed claimed : Interval)
  | domainUndefined
  | refutationWitness (point : List (String × CanonicalRat))
  deriving DecidableEq, Repr

/-- Checker for IntervalJudge. -/
def intervalCheck (_fuel : Nat) (q : IntervalQuery) (c : IntervalCert) : Judge.Verdict IntervalClause :=
  match c with
  | .direct =>
    match evalInterval q.env q.expr with
    | some comp =>
      if decide (q.claimedBound.lo ≤ comp.lo ∧ comp.hi ≤ q.claimedBound.hi) then .ok
      else .refused (.boundViolated comp q.claimedBound) []
    | none => .refused .domainUndefined []
  | .counterexample pt =>
    let rho (s : String) : CanonicalRat :=
      match pt.find? (·.1 == s) with
      | some (_, v) => v
      | none => 0
    match evalPoint rho q.expr with
    | some v =>
      if decide (v < q.claimedBound.lo ∨ q.claimedBound.hi < v) then
        .refused (.refutationWitness pt) []
      else .uncovered
    | none => .refused .domainUndefined []

instance intervalJudge : Judge IntervalQuery IntervalCert where
  Clause := IntervalClause
  Meaning q c := intervalCheck 0 q c = .ok
  check := intervalCheck
  sound := by intro r q c h; exact h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c r, intervalCheck r q c = .ok
  complete := by rintro q ⟨c, r, h⟩ _; exact ⟨c, r, h⟩
  mono := by intro r r' o c le hne; rfl

/-! ## Polynomial Sum-of-Squares (SOS) Judge (`sos@1`) -/

namespace SOS

abbrev Monomial := List (Nat × Nat)

def Monomial.lt : Monomial → Monomial → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | (v1, d1) :: r1, (v2, d2) :: r2 =>
    if v1 < v2 then true
    else if v2 < v1 then false
    else if d1 < d2 then true
    else if d2 < d1 then false
    else Monomial.lt r1 r2

def Monomial.mul : Monomial → Monomial → Monomial
  | [], m2 => m2
  | m1, [] => m1
  | (v1, d1) :: r1, (v2, d2) :: r2 =>
    if v1 < v2 then (v1, d1) :: Monomial.mul r1 ((v2, d2) :: r2)
    else if v2 < v1 then (v2, d2) :: Monomial.mul ((v1, d1) :: r1) r2
    else (v1, d1 + d2) :: Monomial.mul r1 r2

def insertTerm (m : Monomial) (c : CanonicalRat) : List (Monomial × CanonicalRat) → List (Monomial × CanonicalRat)
  | [] => if c == 0 then [] else [(m, c)]
  | (m', c') :: rest =>
    if m == m' then
      let c_new := c + c'
      if c_new == 0 then rest else (m, c_new) :: rest
    else if Monomial.lt m m' then
      if c == 0 then (m', c') :: rest else (m, c) :: (m', c') :: rest
    else
      (m', c') :: insertTerm m c rest

structure Poly where
  terms : List (Monomial × CanonicalRat)
  deriving DecidableEq, Repr

namespace Poly

def zero : Poly := ⟨[]⟩

def one : Poly := ⟨[([], 1)]⟩

def isZero (p : Poly) : Bool :=
  p.terms.isEmpty

def add (p1 p2 : Poly) : Poly :=
  ⟨p2.terms.foldl (fun acc (m, c) => insertTerm m c acc) p1.terms⟩

def neg (p : Poly) : Poly :=
  ⟨p.terms.map fun (m, c) => (m, -c)⟩

def sub (p1 p2 : Poly) : Poly :=
  add p1 (neg p2)

def scale (c : CanonicalRat) (p : Poly) : Poly :=
  if c == 0 then zero
  else ⟨p.terms.map fun (m, k) => (m, c * k)⟩

def mulTerm (t : Monomial × CanonicalRat) (p : Poly) : Poly :=
  if t.2 == 0 then zero
  else ⟨p.terms.map fun (m, c) => (Monomial.mul t.1 m, t.2 * c)⟩

def mul (p1 p2 : Poly) : Poly :=
  p1.terms.foldl (fun acc t => add acc (mulTerm t p2)) zero

def sqr (p : Poly) : Poly :=
  mul p p

end Poly

structure SOSPoly where
  terms : List (CanonicalRat × Poly)
  deriving DecidableEq, Repr

namespace SOSPoly

def expand (sos : SOSPoly) : Poly :=
  sos.terms.foldl (fun acc (c, p) => Poly.add acc (Poly.scale c (Poly.sqr p))) Poly.zero

def allCoeffsPos (sos : SOSPoly) : Bool :=
  sos.terms.all fun (c, _) => decide (0 < c)

end SOSPoly

structure SOSQuery where
  goal : Poly
  ineqs : List Poly
  eqs : List Poly
  deriving DecidableEq, Repr

structure SOSCert where
  sigma0 : SOSPoly
  sigmas : List (SOSPoly × Nat)
  lambdas : List (Poly × Nat)
  deriving DecidableEq, Repr

inductive SOSClause where
  | invalidSOSWeights
  | identityMismatch (residual : Poly)
  deriving DecidableEq, Repr

def sosCheck (_fuel : Nat) (q : SOSQuery) (c : SOSCert) : Judge.Verdict SOSClause :=
  if !c.sigma0.allCoeffsPos then
    .refused .invalidSOSWeights []
  else if !c.sigmas.all (fun (s, _) => s.allCoeffsPos) then
    .refused .invalidSOSWeights []
  else
    let term0 := c.sigma0.expand
    let termIneq := c.sigmas.foldl (fun acc (sig, idx) =>
      match q.ineqs[idx]? with
      | some gi => Poly.add acc (Poly.mul sig.expand gi)
      | none => acc) Poly.zero
    let termEq := c.lambdas.foldl (fun acc (lam, idx) =>
      match q.eqs[idx]? with
      | some hj => Poly.add acc (Poly.mul lam hj)
      | none => acc) Poly.zero
    let certPoly := Poly.add term0 (Poly.add termIneq termEq)
    let diff := Poly.sub q.goal certPoly
    if diff.isZero then .ok
    else .refused (.identityMismatch diff) []

instance sosJudge : Judge SOSQuery SOSCert where
  Clause := SOSClause
  Meaning q c := sosCheck 0 q c = .ok
  check := sosCheck
  sound := by intro r q c h; exact h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c r, sosCheck r q c = .ok
  complete := by rintro q ⟨c, r, h⟩ _; exact ⟨c, r, h⟩
  mono := by intro r r' o c le hne; rfl

end SOS

end Obend.Judge
end
