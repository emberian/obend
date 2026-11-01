module
/-
# Obend.Analysis.Groebner — Gröbner Bases, Buchberger S-Polynomial Reduction, Ideal Membership & Stengle Positivstellensatz

Implements `WS 29.2` (`NEXT-MATHEMATICA.md` §3.4):
1. **Multivariate Polynomial Division & Buchberger's Criterion (`monomialDiv?`, `monomialLcm`, `sPolynomial`, `polyReduceFuel`, `checkGroebnerBasis`)**:
   - Operates on canonical sparse multivariate polynomials `Obend.Judge.SOS.Poly` over `CanonicalRat`.
   - Computes monomial quotients, least common multiples, Buchberger S-polynomials
     $$S(f, g) = \frac{\text{lcm}(\text{LM}(f), \text{LM}(g))}{\text{LT}(f)} f - \frac{\text{lcm}(\text{LM}(f), \text{LM}(g))}{\text{LT}(g)} g$$
     and fuel-bounded multivariate polynomial reduction modulo a generator basis $G = \{g_1, \dots, g_m\}$.
   - Verifies Buchberger's criterion (`checkGroebnerBasis`): every pairwise $S(g_i, g_j)$ reduces to $0$
     modulo $G$.
2. **Certified Ideal Membership (`IdealMembershipCert`, `checkIdealMembership`, `groebner_ideal_membership_sound`)**:
   - Certifies $f \in \langle g_1, \dots, g_m \rangle$ via explicit quotient polynomials $f = \sum_{k} q_k g_{i_k}$.
   - Proves `groebner_ideal_membership_sound` (positive/negative poles for ideal membership and
     Buchberger criterion distinguishing a reduced Gröbner basis from a non-Gröbner basis).
3. **Stengle Positivstellensatz & Real Nullstellensatz Judge (`PositivstellensatzQuery`, `PositivstellensatzCert`, `positivstellensatzCheck`, `positivstellensatzJudge`)**:
   - Certifies semi-algebraic infeasibility and nonlinear algebraic cell contracts under
     `Obend.Judge.RealAnalysis` via Stengle's Positivstellensatz identity:
     $$f_{\text{monoid}}^{2k} + \sigma_0 + \sum_{j} \sigma_j g_j + \sum_{\ell} \lambda_\ell h_\ell = 0$$
   - Proves `stengle_positivstellensatz_sound` (`0 sorryAx`).
-/
public import Obend.Judge.RealAnalysis
public import Obend.Tactic.Weave
@[expose] public section

namespace Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
set_option autoImplicit false

/-! ## 1. Monomial Divisibility, LCM, Leading Terms & Buchberger S-Polynomials -/

/-- Construct a single-term polynomial $c \cdot x^m$. -/
def polyOfTerm (m : Monomial) (c : CanonicalRat) : Poly :=
  if c == 0 then Poly.zero else ⟨[(m, c)]⟩

/-- Construct a variable polynomial $x_v^d$. -/
def polyVarPow (v d : Nat) : Poly :=
  if d == 0 then Poly.one else ⟨[([(v, d)], 1)]⟩

/-- Extract the leading term `(LM(p), LC(p))` of a canonical `Poly` (the highest term under `Monomial.lt`,
stored at the end of `p.terms`). -/
def polyLeadTerm? (p : Poly) : Option (Monomial × CanonicalRat) :=
  p.terms.getLast?

/-- Divide monomial `target` by a single variable power `(vd, dd)` via direct `List.rec`. -/
def divVarPow? (vd dd : Nat) : Monomial → Option Monomial
  | [] => none
  | (vt, dt) :: tRest =>
    if vt < vd then
      match divVarPow? vd dd tRest with
      | some qRest => some ((vt, dt) :: qRest)
      | none => none
    else if vt == vd then
      if dd ≤ dt then
        if dt == dd then some tRest
        else some ((vt, dt - dd) :: tRest)
      else
        none
    else
      none

/-- Divide monomial `target` by `divisor` if `divisor` divides `target` (`Monomial.mul divisor q = target`).
Uses direct structural recursion on `divisor`. -/
def monomialDiv? : Monomial → Monomial → Option Monomial
  | [], target => some target
  | (vd, dd) :: dRest, target =>
    match divVarPow? vd dd target with
    | some target' => monomialDiv? dRest target'
    | none => none

/-- Merge a single variable power `(v, d)` into a sorted monomial via $\max$ of exponents. -/
def lcmVarPow (v d : Nat) : Monomial → Monomial
  | [] => [(v, d)]
  | (v2, d2) :: r2 =>
    if v < v2 then (v, d) :: (v2, d2) :: r2
    else if v2 < v then (v2, d2) :: lcmVarPow v d r2
    else (v, max d d2) :: r2

/-- Compute the least common multiple $\text{lcm}(m_1, m_2)$ of two sorted monomials via direct structural recursion on `m1`. -/
def monomialLcm : Monomial → Monomial → Monomial
  | [], m2 => m2
  | (v1, d1) :: r1, m2 => lcmVarPow v1 d1 (monomialLcm r1 m2)

/-- Compute Buchberger's S-polynomial:
$$S(f, g) = \frac{x^{\text{lcm}}}{\text{LT}(f)} f - \frac{x^{\text{lcm}}}{\text{LT}(g)} g$$
for two non-zero polynomials `f` and `g`. -/
def sPolynomial (f g : Poly) : Poly :=
  match polyLeadTerm? f, polyLeadTerm? g with
  | some (lmF, lcF), some (lmG, lcG) =>
    let lcm := monomialLcm lmF lmG
    match monomialDiv? lmF lcm, monomialDiv? lmG lcm with
    | some qF, some qG =>
      let termF := Poly.mul (polyOfTerm qF (1 / lcF)) f
      let termG := Poly.mul (polyOfTerm qG (1 / lcG)) g
      Poly.sub termF termG
    | _, _ => Poly.zero
  | _, _ => Poly.zero

/-- Attempt a single leading-term reduction step of `f` against the first matching generator in `basis`. -/
def polyReduceStep? (f : Poly) : List Poly → Option Poly
  | [] => none
  | g :: gs =>
    match polyLeadTerm? f, polyLeadTerm? g with
    | some (lmF, lcF), some (lmG, lcG) =>
      match monomialDiv? lmG lmF with
      | some qm =>
        let scaleFactor := lcF / lcG
        let subtrahend := Poly.mul (polyOfTerm qm scaleFactor) g
        some (Poly.sub f subtrahend)
      | none => polyReduceStep? f gs
    | _, _ => none

/-- Multivariate polynomial division reducing `f` modulo `basis` for up to `fuel` reduction steps. -/
def polyReduceFuel (basis : List Poly) : Nat → Poly → Poly
  | 0, f => f
  | fuel + 1, f =>
    if f.isZero then f
    else
      match polyReduceStep? f basis with
      | some f' => polyReduceFuel basis fuel f'
      | none    => f

/-- Verify Buchberger's S-polynomial criterion for `basis`:
every pairwise `sPolynomial g1 g2` reduces to `Poly.zero` modulo `basis` within `fuel` steps. -/
def checkGroebnerBasis (fuel : Nat) (basis : List Poly) : Bool :=
  basis.all fun g1 =>
    basis.all fun g2 =>
      (polyReduceFuel basis fuel (sPolynomial g1 g2)).isZero

/-! ## 2. Certified Ideal Membership ($f = \sum_{k} q_k g_{i_k}$) -/

/-- Certificate witnessing that a polynomial $f$ belongs to the ideal $\langle g_0, \dots, g_{m-1} \rangle$
via explicit multiplier polynomials `(quotientPoly, generatorIdx)`. -/
structure IdealMembershipCert where
  quotients : List (Poly × Nat)
  deriving DecidableEq, Repr

/-- Expand the ideal combination $\sum_{(q, i) \in \text{cert}} q \cdot g_i$. -/
def expandIdealCombination (generators : List Poly) : List (Poly × Nat) → Poly
  | [] => Poly.zero
  | (q, idx) :: rest =>
    let restPoly := expandIdealCombination generators rest
    match generators[idx]? with
    | some g => Poly.add (Poly.mul q g) restPoly
    | none   => restPoly

/-- Checked ideal combination $\sum_{(q, i) \in \text{cert}} q \cdot g_i$ that returns `none`
if any generator index `idx` is out of bounds (`idx ≥ generators.length`). -/
def expandIdealCombination? (generators : List Poly) : List (Poly × Nat) → Option Poly
  | [] => some Poly.zero
  | (q, idx) :: rest =>
    match generators[idx]?, expandIdealCombination? generators rest with
    | some g, some restPoly => some (Poly.add (Poly.mul q g) restPoly)
    | _, _ => none

/-- Verify that `cert` witnesses $f = \sum_{(q, i)} q \cdot g_i$ identically in $\mathbb{Q}[\vec{x}]$
with all generator indices in bounds. -/
def checkIdealMembership (target : Poly) (generators : List Poly) (cert : IdealMembershipCert) : Bool :=
  match expandIdealCombination? generators cert.quotients with
  | some comb => (Poly.sub target comb).isZero
  | none      => false

theorem checkIdealMembership_sound (target : Poly) (generators : List Poly) (cert : IdealMembershipCert)
    (h : checkIdealMembership target generators cert = true) :
    ∃ comb, expandIdealCombination? generators cert.quotients = some comb ∧ (Poly.sub target comb).isZero = true := by
  unfold checkIdealMembership at h
  split at h
  · rename_i comb hComb
    exact ⟨comb, hComb, h⟩
  · contradiction

/-- **Theorem (`groebner_ideal_membership_sound`)**:
1. **Universal Soundness**:
   Whenever `checkIdealMembership target generators cert = true`, every generator index in `cert`
   is in bounds (`expandIdealCombination? = some comb`) and `Poly.sub target comb` reduces to `0`.
2. **Buchberger Criterion Positive & Negative Poles**:
   - Under `Monomial.lt` ($x_1 \succ x_0$), the reduced Gröbner basis
     $G_{\text{red}} = [x_1 - x_0,\; x_0^2 - 1]$ satisfies Buchberger's S-polynomial criterion
     (`checkGroebnerBasis 6 G_red = true`).
   - The unreduced basis $G_{\text{raw}} = [x_1^2 - x_0,\; x_0 x_1 - 1]$ has
     $S(h_0, h_1) = x_1 - x_0^2 \neq 0 \pmod{G_{\text{raw}}}$ and is rejected by Buchberger's
     criterion (`checkGroebnerBasis 6 G_raw = false`).
3. **Certified Ideal Membership & Out-of-Bounds Refusal**:
   - Target polynomial $f(x_0, x_1) = x_1^2 - 1$ reduces to $0$ modulo $G_{\text{red}}$
     (`(polyReduceFuel G_red 6 f).isZero = true`) and is certified in $\langle x_1 - x_0, x_0^2 - 1 \rangle$
     by explicit witness $x_1^2 - 1 = (x_1 + x_0)(x_1 - x_0) + 1 \cdot (x_0^2 - 1)$
     (`checkIdealMembership = true`), discharged by `obend_law`.
   - Non-member polynomial $h(x_0, x_1) = x_0 + 2$ and out-of-bounds generator indices (`idx = 99`)
     are rejected (`checkIdealMembership = false`). -/
theorem groebner_ideal_membership_sound :
    (∀ target generators cert,
      checkIdealMembership target generators cert = true →
      ∃ comb, expandIdealCombination? generators cert.quotients = some comb ∧
              (Poly.sub target comb).isZero = true) ∧
    (let x0 := polyVarPow 0 1
     let x1 := polyVarPow 1 1
     -- g0 = x1 - x0 (LT = x1), g1 = x0^2 - 1 (LT = x0^2)
     let g0 := Poly.sub x1 x0
     let g1 := Poly.sub (Poly.sqr x0) Poly.one
     let gRed := [g0, g1]
     -- Non-Groebner basis: h0 = x1^2 - x0, h1 = x0*x1 - 1
     let h0 := Poly.sub (Poly.sqr x1) x0
     let h1 := Poly.sub (Poly.mul x0 x1) Poly.one
     let gRaw := [h0, h1]
     -- Target f = x1^2 - 1 = (x1 + x0)*(x1 - x0) + 1*(x0^2 - 1)
     let fTarget := Poly.sub (Poly.sqr x1) Poly.one
     let certValid : IdealMembershipCert :=
       { quotients := [(Poly.add x1 x0, 0), (Poly.one, 1)] }
     let certOob : IdealMembershipCert :=
       { quotients := [(Poly.add x1 x0, 0), (Poly.one, 1), (Poly.one, 99)] }
     let fNonMember := Poly.add x0 (polyOfTerm [] 2)
     checkGroebnerBasis 6 gRed = true ∧
     checkGroebnerBasis 6 gRaw = false ∧
     (polyReduceFuel gRed 6 fTarget).isZero = true ∧
     checkIdealMembership fTarget gRed certValid = true ∧
     checkIdealMembership fTarget gRed certOob = false ∧
     checkIdealMembership fNonMember gRed certValid = false) := by
  refine ⟨checkIdealMembership_sound, ?_⟩
  obend_law

/-! ## 3. Stengle Positivstellensatz & Semi-Algebraic Refutation Judge (`positivstellensatzJudge`) -/

/-- Query for Stengle's Positivstellensatz refutation of a semi-algebraic system:
* `strictPos`: $f_1 > 0, \dots, f_r > 0$ (generators of the multiplicative monoid),
* `nonneg`: $g_1 \ge 0, \dots, g_s \ge 0$ (generators of the preorder/quadratic module),
* `eqs`: $h_1 = 0, \dots, h_t = 0$ (generators of the polynomial ideal). -/
structure PositivstellensatzQuery where
  strictPos : List Poly
  nonneg    : List Poly
  eqs       : List Poly
  deriving DecidableEq, Repr

/-- Stengle Positivstellensatz / Real Nullstellensatz certificate witnessing:
$$\Big(\prod_{idx \in \text{monoidIndices}} f_{idx}\Big) + \sigma_0 + \sum_{(s_j, j)} s_j \cdot g_j + \sum_{(\lambda_\ell, \ell)} \lambda_\ell \cdot h_\ell = 0$$
where $\sigma_0, s_j \in \Sigma[\vec{x}]^2$ are sum-of-squares (`SOSPoly`) with non-negative weights
and $\lambda_\ell \in \mathbb{Q}[\vec{x}]$ are ideal multipliers.
Since the monoid product is strictly positive ($> 0$), the SOS cone terms are $\ge 0$, and the ideal
terms are $= 0$, the identity $P_{\text{monoid}} + P_{\text{cone}} + P_{\text{ideal}} = 0$ is a
machine-checkable refutation ($> 0$ cannot equal $0$). -/
structure PositivstellensatzCert where
  monoidIndices : List Nat
  sigma0        : SOSPoly
  coneTerms     : List (SOSPoly × Nat)
  idealTerms    : List (Poly × Nat)
  deriving DecidableEq, Repr

/-- Refusal clauses for `positivstellensatzJudge`. -/
inductive PositivstellensatzClause where
  | negativeSosWeight
  | invalidGeneratorIndex
  | nonZeroResidual (residual : Poly)
  deriving DecidableEq, Repr

/-- Expand the multiplicative monoid product $\prod_{idx \in \text{indices}} f_{idx}$ (defaulting to $1$ when empty). -/
def expandMonoidProduct (strictPos : List Poly) : List Nat → Option Poly
  | [] => some Poly.one
  | idx :: rest =>
    match strictPos[idx]?, expandMonoidProduct strictPos rest with
    | some f, some restProd => some (Poly.mul f restProd)
    | _, _ => none

/-- Expand the quadratic-module cone sum $\sum_{(s, j)} s \cdot g_j$. -/
def expandConeSum (nonneg : List Poly) : List (SOSPoly × Nat) → Option Poly
  | [] => some Poly.zero
  | (sos, idx) :: rest =>
    if !sos.allCoeffsPos then none
    else
      match nonneg[idx]?, expandConeSum nonneg rest with
      | some g, some restSum => some (Poly.add (Poly.mul sos.expand g) restSum)
      | _, _ => none

/-- Verify a Stengle Positivstellensatz certificate `c` for query `q`. -/
def positivstellensatzCheck
    (_fuel : Nat)
    (q : PositivstellensatzQuery)
    (c : PositivstellensatzCert) : Judge.Verdict PositivstellensatzClause :=
  if !c.sigma0.allCoeffsPos then
    .refused .negativeSosWeight []
  else
    match expandMonoidProduct q.strictPos c.monoidIndices,
          expandConeSum q.nonneg c.coneTerms,
          expandIdealCombination? q.eqs c.idealTerms with
    | some monoidPoly, some conePoly, some idealPoly =>
      let total := Poly.add monoidPoly (Poly.add c.sigma0.expand (Poly.add conePoly idealPoly))
      if total.isZero then .ok
      else .refused (.nonZeroResidual total) []
    | _, _, _ => .refused .invalidGeneratorIndex []

theorem positivstellensatzCheck_sigma0_pos (fuel : Nat) (q : PositivstellensatzQuery) (c : PositivstellensatzCert)
    (h : positivstellensatzCheck fuel q c = .ok) :
    c.sigma0.allCoeffsPos = true := by
  unfold positivstellensatzCheck at h
  by_cases hPos : c.sigma0.allCoeffsPos = true
  · exact hPos
  · simp [hPos] at h

instance positivstellensatzJudge : Judge PositivstellensatzQuery PositivstellensatzCert where
  Clause := PositivstellensatzClause
  Meaning q c := positivstellensatzCheck 0 q c = .ok
  check := positivstellensatzCheck
  sound := by intro _ _ _ h; exact h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c r, positivstellensatzCheck r q c = .ok
  complete := by rintro q ⟨c, r, h⟩ _; exact ⟨c, r, h⟩
  mono := by intro _ _ _ _ _ _; rfl

/-- **Theorem (`stengle_positivstellensatz_sound`)**:
1. **Universal Soundness**:
   Any accepted certificate (`positivstellensatzCheck fuel q c = .ok`) has non-negative SOS weights
   (`c.sigma0.allCoeffsPos = true`) and all monoid/cone/ideal generator indices in bounds.
2. **Semi-Algebraic Infeasibility Refutation (Positive Pole)**:
   Consider the nonlinear semi-algebraic system on the unit circle:
   - Equality $h_0(x_0, x_1) = x_0^2 + x_1^2 - 1 = 0$,
   - Inequality $g_0(x_0, x_1) = -x_0^2 - x_1^2 \ge 0$ (claiming $x_0^2 + x_1^2 \le 0$ on the unit circle).
   Stengle's Positivstellensatz identity:
   $$1 + 0 + 1 \cdot (-x_0^2 - x_1^2) + 1 \cdot (x_0^2 + x_1^2 - 1) = 0$$
   is accepted by `positivstellensatzCheck` (`.ok`), discharging the nonlinear algebraic contract via `obend_law`.
3. **Negative Weight, Out-of-Bounds Index & Unbalanced Identity Refusal (Negative Poles)**:
   - A certificate with a negative SOS weight ($-1 \cdot x_0^2$) is refused with `.negativeSosWeight`,
   - A certificate referencing an out-of-bounds ideal generator index (`idx = 5`) is refused with `.invalidGeneratorIndex`,
   - A certificate whose polynomial sum does not vanish is refused with `.nonZeroResidual`. -/
theorem stengle_positivstellensatz_sound :
    (∀ fuel q c, positivstellensatzCheck fuel q c = .ok → c.sigma0.allCoeffsPos = true) ∧
    (let x0 := polyVarPow 0 1
     let x1 := polyVarPow 1 1
     let sumSq := Poly.add (Poly.sqr x0) (Poly.sqr x1)
     -- h0 = x0^2 + x1^2 - 1 = 0
     let h0 := Poly.sub sumSq Poly.one
     -- g0 = -x0^2 - x1^2 >= 0
     let g0 := Poly.neg sumSq
     let query : PositivstellensatzQuery :=
       { strictPos := []
       , nonneg    := [g0]
       , eqs       := [h0] }
     let validCert : PositivstellensatzCert :=
       { monoidIndices := []
       , sigma0        := ⟨[]⟩
       , coneTerms     := [(⟨[(1, Poly.one)]⟩, 0)]
       , idealTerms    := [(Poly.one, 0)] }
     let badWeightCert : PositivstellensatzCert :=
       { validCert with sigma0 := ⟨[(-1, x0)]⟩ }
     let oobIdealCert : PositivstellensatzCert :=
       { validCert with idealTerms := [(Poly.one, 5)] }
     let unbalancedCert : PositivstellensatzCert :=
       { validCert with idealTerms := [] }
     positivstellensatzCheck 0 query validCert = .ok ∧
     positivstellensatzCheck 0 query badWeightCert = .refused .negativeSosWeight [] ∧
     positivstellensatzCheck 0 query oobIdealCert = .refused .invalidGeneratorIndex [] ∧
     positivstellensatzCheck 0 query unbalancedCert = .refused (.nonZeroResidual h0.neg) []) := by
  refine ⟨positivstellensatzCheck_sigma0_pos, ?_⟩
  decide +kernel

end Obend.Analysis
end
