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
2. **Certified Ideal Membership (`IdealMembershipCert`, `checkIdealMembership`, `checkIdealMembership_eval_sound`, `groebner_ideal_membership_sound`)**:
   - Certifies $f \in \langle g_1, \dots, g_m \rangle$ via explicit quotient polynomials $f = \sum_{k} q_k g_{i_k}$.
   - Proves `checkIdealMembership_eval_sound`: if `checkIdealMembership target gens cert = true`, then for
     every assignment $\rho : \mathbb{N} \to \mathbb{Q}$, $(\forall g \in \text{gens},\; g.\text{eval}\,\rho = 0) \to \text{target}.\text{eval}\,\rho = 0$.
   - Proves `groebner_ideal_membership_sound` (positive/negative poles for ideal membership and
     Buchberger criterion distinguishing a reduced Gröbner basis from a non-Gröbner basis).
3. **Stengle Positivstellensatz & Real Nullstellensatz Judge (`PositivstellensatzQuery`, `PositivstellensatzCert`, `positivstellensatzCheck`, `positivstellensatz_eval_infeasible`, `positivstellensatzJudge`)**:
   - Certifies semi-algebraic infeasibility and nonlinear algebraic cell contracts under
     `Obend.Judge.RealAnalysis` via Stengle's Positivstellensatz identity:
     $$\prod_{i \in I} f_i + \sigma_0 + \sum_{j} \sigma_j g_j + \sum_{\ell} \lambda_\ell h_\ell = 0$$
     where the strict-generator index list $I$ may repeat indices.
   - Proves `positivstellensatz_eval_infeasible` and `stengle_positivstellensatz_sound`.
   - States the certificate as algebra (`PolyAtIdx`, `MonoidProdRel`, `ConeSumRel`, `IdealCombRel`,
     `StenglePositivstellensatzRefutable`) and proves `stenglePositivstellensatzRefutable_iff_check_ok`:
     the judge's `Fragment` is the set of queries with a Stengle identity, and that is exactly the
     set the checker accepts a certificate for.
-/
public import Obend.Judge.RealAnalysis
import Obend.Tactic.Tooth
import all Obend.Judge.RealAnalysis
import all Obend.Analysis.RealAnalysis
public section

namespace Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
set_option autoImplicit false

/-! ## 1. Monomial Divisibility, LCM, Leading Terms & Buchberger S-Polynomials -/

/-- Construct a single-term polynomial $c \cdot x^m$. -/
@[expose] def polyOfTerm (m : Monomial) (c : CanonicalRat) : Poly :=
  if c == 0 then Poly.zero else ⟨[(m, c)]⟩

/-- Construct a variable polynomial $x_v^d$. -/
@[expose] def polyVarPow (v d : Nat) : Poly :=
  if d == 0 then Poly.one else ⟨[([(v, d)], 1)]⟩

/-- Extract the leading term `(LM(p), LC(p))` of a canonical `Poly` (the highest term under `Monomial.lt`,
stored at the end of `p.terms`). -/
@[expose] def polyLeadTerm? (p : Poly) : Option (Monomial × CanonicalRat) :=
  p.terms.getLast?

/-- Divide monomial `target` by a single variable power `(vd, dd)` via direct `List.rec`. -/
@[expose] def divVarPow? (vd dd : Nat) : Monomial → Option Monomial
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
@[expose] def monomialDiv? : Monomial → Monomial → Option Monomial
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
@[expose] def polyReduceStep? (f : Poly) : List Poly → Option Poly
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
@[expose] def polyReduceFuel (basis : List Poly) : Nat → Poly → Poly
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
  deriving @[expose] DecidableEq, Repr

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
@[expose] def expandIdealCombination? (generators : List Poly) : List (Poly × Nat) → Option Poly
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

/-- `checkIdealMembership` accepts a non-zero target: $x_1^2 - 1 = (x_1 + x_0)(x_1 - x_0) + 1 \cdot (x_0^2 - 1)$
lies in $\langle x_1 - x_0,\; x_0^2 - 1 \rangle$. -/
theorem checkIdealMembership_inhabited :
    ∃ target gens cert, checkIdealMembership target gens cert = true ∧ 0 < target.terms.length := by
  refine ⟨Poly.sub (Poly.sqr (polyVarPow 1 1)) Poly.one,
    [Poly.sub (polyVarPow 1 1) (polyVarPow 0 1), Poly.sub (Poly.sqr (polyVarPow 0 1)) Poly.one],
    { quotients := [(Poly.add (polyVarPow 1 1) (polyVarPow 0 1), 0), (Poly.one, 1)] }, ?_⟩
  decide +kernel

/-- Any checked ideal combination $\sum_{(q, i)} q \cdot g_i$ evaluates to $0$ at every assignment
$\rho$ where all generators $g \in \text{generators}$ vanish. -/
theorem expandIdealCombination?_eval_eq_zero
    (ρ : Nat → CanonicalRat) (generators : List Poly)
    (hGens : ∀ g ∈ generators, g.eval ρ = 0)
    (quotients : List (Poly × Nat)) (comb : Poly)
    (hComb : expandIdealCombination? generators quotients = some comb) :
    comb.eval ρ = 0 := by
  induction quotients generalizing comb with
  | nil =>
    simp only [expandIdealCombination?, Option.some.injEq] at hComb
    subst hComb
    rfl
  | cons hd tl ih =>
    rcases hd with ⟨q, idx⟩
    simp only [expandIdealCombination?] at hComb
    cases hg : generators[idx]? with
    | none => rw [hg] at hComb; contradiction
    | some g =>
      rw [hg] at hComb
      cases hRest : expandIdealCombination? generators tl with
      | none => rw [hRest] at hComb; contradiction
      | some restPoly =>
        rw [hRest] at hComb
        simp only [Option.some.injEq] at hComb
        subst hComb
        rw [Poly.eval_add, Poly.eval_mul, ih restPoly hRest]
        have hmem : g ∈ generators := List.mem_of_getElem? hg
        rw [hGens g hmem]
        grind

/-- **Theorem (`checkIdealMembership_eval_sound`)**:
True semantic soundness of `checkIdealMembership` over `Poly.eval`:
If `checkIdealMembership target gens cert = true`, then for every variable assignment
`ρ : Nat → CanonicalRat`, if every generator `g ∈ gens` evaluates to `0`, then `target.eval ρ = 0`! -/
theorem checkIdealMembership_eval_sound
    (target : Poly) (gens : List Poly) (cert : IdealMembershipCert)
    (h : checkIdealMembership target gens cert = true)
    (ρ : Nat → CanonicalRat)
    (hGens : ∀ g ∈ gens, g.eval ρ = 0) :
    target.eval ρ = 0 := by
  obtain ⟨comb, hComb, hZero⟩ := checkIdealMembership_sound target gens cert h
  have hSub := Poly.eval_isZero ρ (Poly.sub target comb) hZero
  rw [Poly.eval_sub] at hSub
  have hCombZero := expandIdealCombination?_eval_eq_zero ρ gens hGens cert.quotients comb hComb
  grind

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
  decide +kernel

/-! ## 3. Stengle Positivstellensatz & Semi-Algebraic Refutation Judge (`positivstellensatzJudge`) -/

/-- Query for Stengle's Positivstellensatz refutation of a semi-algebraic system:
* `strictPos`: $f_1 > 0, \dots, f_r > 0$ (generators of the multiplicative monoid),
* `nonneg`: $g_1 \ge 0, \dots, g_s \ge 0$ (generators of the preorder/quadratic module),
* `eqs`: $h_1 = 0, \dots, h_t = 0$ (generators of the polynomial ideal). -/
structure PositivstellensatzQuery where
  strictPos : List Poly
  nonneg    : List Poly
  eqs       : List Poly
  deriving @[expose] DecidableEq, Repr

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
  deriving @[expose] DecidableEq, Repr

/-- Refusal clauses for `positivstellensatzJudge`. -/
inductive PositivstellensatzClause where
  | feasibleAtOrigin
  | negativeSosWeight
  | invalidGeneratorIndex
  | nonZeroResidual (residual : Poly)
  deriving @[expose] DecidableEq, Repr

/-- Check whether the origin `ρ₀ := fun _ => 0` simultaneously satisfies all strict-positivity,
non-negativity, and equality constraints of `q`, directly refuting `PositivstellensatzQuery.Infeasible q`. -/
def queryFeasibleAtOrigin (q : PositivstellensatzQuery) : Bool :=
  (q.strictPos.all fun f => decide (0 < f.eval (fun _ => 0))) &&
  (q.nonneg.all fun g => decide (0 ≤ g.eval (fun _ => 0))) &&
  (q.eqs.all fun h => decide (h.eval (fun _ => 0) = 0))

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
  if queryFeasibleAtOrigin q then
    .refused .feasibleAtOrigin []
  else if !c.sigma0.allCoeffsPos then
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

/-- What an acceptance of `positivstellensatzCheck` consists of: the origin is not a feasible point,
the free SOS term has positive weights, the three expansions are in bounds, and their sum with the
SOS term cancels identically. -/
theorem positivstellensatzCheck_ok_elim (fuel : Nat) (q : PositivstellensatzQuery) (c : PositivstellensatzCert)
    (hOk : positivstellensatzCheck fuel q c = .ok) :
    queryFeasibleAtOrigin q = false ∧
    c.sigma0.allCoeffsPos = true ∧
    ∃ monoidPoly conePoly idealPoly,
      expandMonoidProduct q.strictPos c.monoidIndices = some monoidPoly ∧
      expandConeSum q.nonneg c.coneTerms = some conePoly ∧
      expandIdealCombination? q.eqs c.idealTerms = some idealPoly ∧
      (Poly.add monoidPoly (Poly.add c.sigma0.expand (Poly.add conePoly idealPoly))).isZero = true := by
  unfold positivstellensatzCheck at hOk
  by_cases hFeas : queryFeasibleAtOrigin q = true
  · simp [hFeas] at hOk
  · simp only [hFeas, Bool.false_eq_true, ↓reduceIte] at hOk
    by_cases hPos0 : c.sigma0.allCoeffsPos = true
    · simp only [hPos0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      rcases Option.eq_none_or_eq_some (expandMonoidProduct q.strictPos c.monoidIndices) with hMon | ⟨monoidPoly, hMon⟩
      · rw [hMon] at hOk; contradiction
      · rw [hMon] at hOk
        rcases Option.eq_none_or_eq_some (expandConeSum q.nonneg c.coneTerms) with hCone | ⟨conePoly, hCone⟩
        · rw [hCone] at hOk; contradiction
        · rw [hCone] at hOk
          rcases Option.eq_none_or_eq_some (expandIdealCombination? q.eqs c.idealTerms) with hIdeal | ⟨idealPoly, hIdeal⟩
          · rw [hIdeal] at hOk; contradiction
          · rw [hIdeal] at hOk
            dsimp only at hOk
            split at hOk
            · rename_i hTotalZero
              exact ⟨Bool.eq_false_of_ne_true hFeas, hPos0, monoidPoly, conePoly, idealPoly,
                hMon, hCone, hIdeal, hTotalZero⟩
            · contradiction
    · simp [hPos0] at hOk

/-- The converse of `positivstellensatzCheck_ok_elim`: those four facts make the checker accept. -/
theorem positivstellensatzCheck_ok_intro (fuel : Nat) (q : PositivstellensatzQuery) (c : PositivstellensatzCert)
    (monoidPoly conePoly idealPoly : Poly)
    (hFeas : queryFeasibleAtOrigin q = false)
    (hPos0 : c.sigma0.allCoeffsPos = true)
    (hMon : expandMonoidProduct q.strictPos c.monoidIndices = some monoidPoly)
    (hCone : expandConeSum q.nonneg c.coneTerms = some conePoly)
    (hIdeal : expandIdealCombination? q.eqs c.idealTerms = some idealPoly)
    (hZero : (Poly.add monoidPoly (Poly.add c.sigma0.expand (Poly.add conePoly idealPoly))).isZero = true) :
    positivstellensatzCheck fuel q c = .ok := by
  unfold positivstellensatzCheck
  simp only [hFeas, hPos0, hMon, hCone, hIdeal, hZero, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- The grade is not consulted: the checker decides every certificate at grade `0`. -/
theorem positivstellensatzCheck_fuel_irrelevant (r r' : Nat) (q : PositivstellensatzQuery)
    (c : PositivstellensatzCert) :
    positivstellensatzCheck r q c = positivstellensatzCheck r' q c := by
  rfl

theorem positivstellensatzCheck_sigma0_pos (fuel : Nat) (q : PositivstellensatzQuery) (c : PositivstellensatzCert)
    (h : positivstellensatzCheck fuel q c = .ok) :
    c.sigma0.allCoeffsPos = true :=
  (positivstellensatzCheck_ok_elim fuel q c h).2.1

theorem expandMonoidProduct_eval_pos
    (ρ : Nat → CanonicalRat) (strictPos : List Poly)
    (hPos : ∀ f ∈ strictPos, 0 < f.eval ρ)
    (indices : List Nat) (monoidPoly : Poly)
    (hProd : expandMonoidProduct strictPos indices = some monoidPoly) :
    0 < monoidPoly.eval ρ := by
  induction indices generalizing monoidPoly with
  | nil =>
    simp only [expandMonoidProduct, Option.some.injEq] at hProd
    subst hProd
    simp [Poly.eval_one]
    decide
  | cons idx rest ih =>
    simp only [expandMonoidProduct] at hProd
    cases hf : strictPos[idx]? with
    | none => rw [hf] at hProd; contradiction
    | some f =>
      rw [hf] at hProd
      cases hRest : expandMonoidProduct strictPos rest with
      | none => rw [hRest] at hProd; contradiction
      | some restProd =>
        rw [hRest] at hProd
        simp only [Option.some.injEq] at hProd
        subst hProd
        rw [Poly.eval_mul]
        have hf_pos : 0 < f.eval ρ := hPos f (List.mem_of_getElem? hf)
        have hrest_pos : 0 < restProd.eval ρ := ih restProd hRest
        have hle : 0 ≤ f.eval ρ := by grind
        have hle2 : 0 ≤ restProd.eval ρ := by grind
        have hne1 : f.eval ρ ≠ 0 := by grind
        have hne2 : restProd.eval ρ ≠ 0 := by grind
        have hmul_nonneg := Rat.mul_le_mul_of_nonneg_left hle2 hle
        by_cases hzero : f.eval ρ * restProd.eval ρ = 0
        · grind
        · grind

theorem expandConeSum_eval_nonneg
    (ρ : Nat → CanonicalRat) (nonneg : List Poly)
    (hNonneg : ∀ g ∈ nonneg, 0 ≤ g.eval ρ)
    (coneTerms : List (SOSPoly × Nat)) (conePoly : Poly)
    (hCone : expandConeSum nonneg coneTerms = some conePoly) :
    0 ≤ conePoly.eval ρ := by
  induction coneTerms generalizing conePoly with
  | nil =>
    simp only [expandConeSum, Option.some.injEq] at hCone
    subst hCone
    simp [Poly.eval_zero]
  | cons hd tl ih =>
    rcases hd with ⟨sos, idx⟩
    simp only [expandConeSum] at hCone
    by_cases hSos : sos.allCoeffsPos = true
    · simp only [hSos, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCone
      cases hg : nonneg[idx]? with
      | none => rw [hg] at hCone; contradiction
      | some g =>
        rw [hg] at hCone
        cases hRest : expandConeSum nonneg tl with
        | none => rw [hRest] at hCone; contradiction
        | some restSum =>
          rw [hRest] at hCone
          simp only [Option.some.injEq] at hCone
          subst hCone
          rw [Poly.eval_add, Poly.eval_mul]
          have hsos_nonneg := SOSPoly.eval_expand_nonneg ρ sos hSos
          have hg_nonneg := hNonneg g (List.mem_of_getElem? hg)
          have hmul := Rat.mul_le_mul_of_nonneg_left hg_nonneg hsos_nonneg
          have hrest_nonneg := ih restSum hRest
          grind
    · simp [hSos] at hCone

/-- Independent semantic meaning of `PositivstellensatzQuery`:
no rational assignment `ρ : Nat → CanonicalRat` can simultaneously satisfy all strict-positivity
constraints `f ∈ q.strictPos`, non-negativity constraints `g ∈ q.nonneg`, and equality constraints
`h ∈ q.eqs`. -/
def PositivstellensatzQuery.Infeasible (q : PositivstellensatzQuery) : Prop :=
  ∀ (ρ : Nat → CanonicalRat),
    (∀ f ∈ q.strictPos, 0 < f.eval ρ) →
    (∀ g ∈ q.nonneg, 0 ≤ g.eval ρ) →
    (∀ h ∈ q.eqs, h.eval ρ = 0) →
    False

/-- The unfolding of `PositivstellensatzQuery.Infeasible`, for modules that see only this one's
public part. -/
theorem PositivstellensatzQuery.infeasible_iff (q : PositivstellensatzQuery) :
    q.Infeasible ↔
      ∀ (ρ : Nat → CanonicalRat),
        (∀ f ∈ q.strictPos, 0 < f.eval ρ) →
        (∀ g ∈ q.nonneg, 0 ≤ g.eval ρ) →
        (∀ h ∈ q.eqs, h.eval ρ = 0) →
        False :=
  ⟨fun h => h, fun h => h⟩

/-- **Stengle's identity refutes the system.** A monoid product `monoidPoly` of the strict
generators, an SOS term `sigma0`, a cone sum `conePoly` over the non-negative generators and an
ideal combination `idealPoly` of the equations whose sum cancels identically leave no rational
point: there the first is `> 0`, the next two are `≥ 0` and the last is `= 0`. -/
theorem stengle_identity_infeasible
    (q : PositivstellensatzQuery) (sigma0 : SOSPoly) (monoidIndices : List Nat)
    (coneTerms : List (SOSPoly × Nat)) (idealTerms : List (Poly × Nat))
    (monoidPoly conePoly idealPoly : Poly)
    (hPos0 : sigma0.allCoeffsPos = true)
    (hMon : expandMonoidProduct q.strictPos monoidIndices = some monoidPoly)
    (hCone : expandConeSum q.nonneg coneTerms = some conePoly)
    (hIdeal : expandIdealCombination? q.eqs idealTerms = some idealPoly)
    (hZero : (Poly.add monoidPoly (Poly.add sigma0.expand (Poly.add conePoly idealPoly))).isZero = true) :
    PositivstellensatzQuery.Infeasible q := by
  intro ρ hStrict hNonneg hEqs
  have hEvalTotal := Poly.eval_isZero ρ _ hZero
  rw [Poly.eval_add, Poly.eval_add, Poly.eval_add] at hEvalTotal
  have hMonPos := expandMonoidProduct_eval_pos ρ q.strictPos hStrict monoidIndices monoidPoly hMon
  have hSig0 := SOSPoly.eval_expand_nonneg ρ sigma0 hPos0
  have hConeNonneg := expandConeSum_eval_nonneg ρ q.nonneg hNonneg coneTerms conePoly hCone
  have hIdealZero := expandIdealCombination?_eval_eq_zero ρ q.eqs hEqs idealTerms idealPoly hIdeal
  grind

/-- **Theorem (`positivstellensatz_general_eval_infeasible`)**:
Whenever `positivstellensatzCheck fuel q c = .ok`, the semi-algebraic system `q` is semantically
infeasible over `CanonicalRat` (`PositivstellensatzQuery.Infeasible q`). -/
theorem positivstellensatz_general_eval_infeasible
    (fuel : Nat) (q : PositivstellensatzQuery) (c : PositivstellensatzCert)
    (hOk : positivstellensatzCheck fuel q c = .ok) :
    PositivstellensatzQuery.Infeasible q := by
  obtain ⟨_, hPos0, monoidPoly, conePoly, idealPoly, hMon, hCone, hIdeal, hZero⟩ :=
    positivstellensatzCheck_ok_elim fuel q c hOk
  exact stengle_identity_infeasible q c.sigma0 c.monoidIndices c.coneTerms c.idealTerms
    monoidPoly conePoly idealPoly hPos0 hMon hCone hIdeal hZero

/-- **Theorem (`positivstellensatz_eval_infeasible`)**:
If a Positivstellensatz SOS certificate is valid (`positivstellensatzCheck fuel q c = .ok` with
`c.monoidIndices = []`, so the monoid term is $1$ and $1 + \sigma_0 + \sum s_j g_j + \sum \lambda_\ell h_\ell = 0$),
then **no assignment `ρ : Nat → CanonicalRat` can simultaneously satisfy `∀ g ∈ q.nonneg, 0 ≤ g.eval ρ`
and `∀ h ∈ q.eqs, h.eval ρ = 0`**! -/
theorem positivstellensatz_eval_infeasible
    (fuel : Nat) (q : PositivstellensatzQuery) (c : PositivstellensatzCert)
    (hOk : positivstellensatzCheck fuel q c = .ok)
    (hMonoidOne : c.monoidIndices = [])
    (ρ : Nat → CanonicalRat)
    (hNonneg : ∀ g ∈ q.nonneg, 0 ≤ g.eval ρ)
    (hEqs : ∀ h ∈ q.eqs, h.eval ρ = 0) :
    False := by
  unfold positivstellensatzCheck at hOk
  by_cases hFeas : queryFeasibleAtOrigin q = true
  · simp [hFeas] at hOk
  · simp only [hFeas, Bool.false_eq_true, ↓reduceIte] at hOk
    by_cases hPos0 : c.sigma0.allCoeffsPos = true
    · simp only [hPos0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hMonoidOne,
        expandMonoidProduct] at hOk
      cases hCone : expandConeSum q.nonneg c.coneTerms with
      | none => rw [hCone] at hOk; contradiction
      | some conePoly =>
        rw [hCone] at hOk
        cases hIdeal : expandIdealCombination? q.eqs c.idealTerms with
        | none => rw [hIdeal] at hOk; contradiction
        | some idealPoly =>
          rw [hIdeal] at hOk
          dsimp only at hOk
          split at hOk
          · rename_i hTotalZero
            have hEvalTotal := Poly.eval_isZero ρ _ hTotalZero
            rw [Poly.eval_add, Poly.eval_add, Poly.eval_add, Poly.eval_one] at hEvalTotal
            have hSig0 := SOSPoly.eval_expand_nonneg ρ c.sigma0 hPos0
            have hConeNonneg := expandConeSum_eval_nonneg ρ q.nonneg hNonneg c.coneTerms conePoly hCone
            have hIdealZero := expandIdealCombination?_eval_eq_zero ρ q.eqs hEqs c.idealTerms idealPoly hIdeal
            grind
          · contradiction
    · simp [hPos0] at hOk

/-- Refuting clauses of `positivstellensatzJudge`: `.feasibleAtOrigin` constructively exhibits
the feasible point `ρ₀ = fun _ => 0`, refuting `PositivstellensatzQuery.Infeasible q`. -/
def positivstellensatzRefutes : PositivstellensatzClause → Bool
  | .feasibleAtOrigin => true
  | _ => false

theorem queryFeasibleAtOrigin_refutes (q : PositivstellensatzQuery)
    (hFeas : queryFeasibleAtOrigin q = true) :
    ¬ PositivstellensatzQuery.Infeasible q := by
  intro hInfeas
  unfold queryFeasibleAtOrigin at hFeas
  rcases (Bool.and_eq_true _ _).mp hFeas with ⟨hStrictNonneg, hEqsB⟩
  rcases (Bool.and_eq_true _ _).mp hStrictNonneg with ⟨hStrictB, hNonnegB⟩
  apply hInfeas (fun _ => 0)
  · intro f hf
    exact of_decide_eq_true (List.all_eq_true.mp hStrictB f hf)
  · intro g hg
    exact of_decide_eq_true (List.all_eq_true.mp hNonnegB g hg)
  · intro h hh
    exact of_decide_eq_true (List.all_eq_true.mp hEqsB h hh)

theorem positivstellensatzCheck_refuted
    {r : Nat} {q : PositivstellensatzQuery} {c : PositivstellensatzCert}
    {k : PositivstellensatzClause} {p : List Nat}
    (hRef : positivstellensatzCheck r q c = .refused k p)
    (hRefutes : positivstellensatzRefutes k = true) :
    ¬ PositivstellensatzQuery.Infeasible q := by
  have hk : k = .feasibleAtOrigin := by
    cases k <;> simp [positivstellensatzRefutes] at hRefutes ⊢
  subst hk
  unfold positivstellensatzCheck at hRef
  by_cases hFeas : queryFeasibleAtOrigin q = true
  · exact queryFeasibleAtOrigin_refutes q hFeas
  · simp only [hFeas, Bool.false_eq_true, ↓reduceIte] at hRef
    by_cases hPos0 : c.sigma0.allCoeffsPos = true
    · simp only [hPos0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
      cases hMon : expandMonoidProduct q.strictPos c.monoidIndices <;>
        cases hCone : expandConeSum q.nonneg c.coneTerms <;>
        cases hIdeal : expandIdealCombination? q.eqs c.idealTerms <;>
        simp [hMon, hCone, hIdeal] at hRef
      split at hRef <;> simp at hRef
    · simp [hPos0] at hRef

/-! ### The certificate as algebra: Stengle's identity stated over the polynomial ring

The relations below say what a Positivstellensatz certificate is without running anything: a
generator picked by position, a product of strict generators, a sum of SOS multiples of
non-negative generators, an ideal combination of the equations, and the identity that their sum
with a free SOS term is the zero polynomial. Each is proved equal to the corresponding expansion
of the checker, and `stenglePositivstellensatzRefutable_iff_check_ok` is the resulting
characterization of the queries the checker can accept. -/

/-- Every weight of the SOS combination is strictly positive. -/
def PosSosWeights (sos : SOSPoly) : Prop :=
  ∀ t ∈ sos.terms, 0 < t.1

theorem posSosWeights_iff (sos : SOSPoly) :
    PosSosWeights sos ↔ sos.allCoeffsPos = true := by
  unfold PosSosWeights SOSPoly.allCoeffsPos
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    obtain ⟨c, p⟩ := t
    exact decide_eq_true (h (c, p) ht)
  · intro h t ht
    obtain ⟨c, p⟩ := t
    exact of_decide_eq_true (h (c, p) ht)

/-- A polynomial with no terms is the one `Poly.isZero` accepts. -/
theorem polyTermsNil_iff_isZero (p : Poly) : p.terms = [] ↔ p.isZero = true := by
  obtain ⟨ts⟩ := p
  cases ts <;> simp [Poly.isZero]

/-- `p` is the generator at position `i` of the list. -/
inductive PolyAtIdx : List Poly → Nat → Poly → Prop where
  | zero (p : Poly) (ps : List Poly) : PolyAtIdx (p :: ps) 0 p
  | succ (q : Poly) (ps : List Poly) (i : Nat) (p : Poly) :
      PolyAtIdx ps i p → PolyAtIdx (q :: ps) (i + 1) p

theorem polyAtIdx_iff (ps : List Poly) (i : Nat) (p : Poly) :
    PolyAtIdx ps i p ↔ ps[i]? = some p := by
  constructor
  · intro h
    induction h with
    | zero p ps => exact List.getElem?_cons_zero
    | succ q ps i p _ ih =>
      rw [List.getElem?_cons_succ]
      exact ih
  · intro h
    induction ps generalizing i with
    | nil => rw [List.getElem?_nil] at h; exact nomatch h
    | cons q ps ih =>
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at h
        cases h
        exact PolyAtIdx.zero _ _
      | succ i =>
        rw [List.getElem?_cons_succ] at h
        exact PolyAtIdx.succ q ps i p (ih i h)

/-- `p` is the product of the strict generators at the listed positions (`1` for none). -/
inductive MonoidProdRel (strictPos : List Poly) : List Nat → Poly → Prop where
  | nil : MonoidProdRel strictPos [] Poly.one
  | cons (idx : Nat) (rest : List Nat) (f p : Poly) :
      PolyAtIdx strictPos idx f → MonoidProdRel strictPos rest p →
      MonoidProdRel strictPos (idx :: rest) (Poly.mul f p)

theorem monoidProdRel_iff (strictPos : List Poly) (indices : List Nat) (p : Poly) :
    MonoidProdRel strictPos indices p ↔ expandMonoidProduct strictPos indices = some p := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons idx rest f p hf _ ih =>
      have hf' := (polyAtIdx_iff strictPos idx f).mp hf
      simp only [expandMonoidProduct, hf', ih]
  · intro h
    induction indices generalizing p with
    | nil =>
      simp only [expandMonoidProduct, Option.some.injEq] at h
      subst h
      exact MonoidProdRel.nil
    | cons idx rest ih =>
      simp only [expandMonoidProduct] at h
      rcases Option.eq_none_or_eq_some (strictPos[idx]?) with hf | ⟨f, hf⟩
      · rw [hf] at h; contradiction
      · rw [hf] at h
        rcases Option.eq_none_or_eq_some (expandMonoidProduct strictPos rest) with hRest | ⟨restProd, hRest⟩
        · rw [hRest] at h; contradiction
        · rw [hRest] at h
          simp only [Option.some.injEq] at h
          subst h
          exact MonoidProdRel.cons idx rest f restProd
            ((polyAtIdx_iff strictPos idx f).mpr hf) (ih restProd hRest)

/-- `s` is the sum of the listed positive-weight SOS multiples of non-negative generators. -/
inductive ConeSumRel (nonneg : List Poly) : List (SOSPoly × Nat) → Poly → Prop where
  | nil : ConeSumRel nonneg [] Poly.zero
  | cons (sos : SOSPoly) (idx : Nat) (rest : List (SOSPoly × Nat)) (g s : Poly) :
      PosSosWeights sos → PolyAtIdx nonneg idx g → ConeSumRel nonneg rest s →
      ConeSumRel nonneg ((sos, idx) :: rest) (Poly.add (Poly.mul sos.expand g) s)

theorem coneSumRel_iff (nonneg : List Poly) (coneTerms : List (SOSPoly × Nat)) (s : Poly) :
    ConeSumRel nonneg coneTerms s ↔ expandConeSum nonneg coneTerms = some s := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons sos idx rest g s hw hg _ ih =>
      have hw' := (posSosWeights_iff sos).mp hw
      have hg' := (polyAtIdx_iff nonneg idx g).mp hg
      simp only [expandConeSum, hw', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hg', ih]
  · intro h
    induction coneTerms generalizing s with
    | nil =>
      simp only [expandConeSum, Option.some.injEq] at h
      subst h
      exact ConeSumRel.nil
    | cons hd tl ih =>
      rcases hd with ⟨sos, idx⟩
      simp only [expandConeSum] at h
      by_cases hSos : sos.allCoeffsPos = true
      · simp only [hSos, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        rcases Option.eq_none_or_eq_some (nonneg[idx]?) with hg | ⟨g, hg⟩
        · rw [hg] at h; contradiction
        · rw [hg] at h
          rcases Option.eq_none_or_eq_some (expandConeSum nonneg tl) with hRest | ⟨restSum, hRest⟩
          · rw [hRest] at h; contradiction
          · rw [hRest] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ConeSumRel.cons sos idx tl g restSum ((posSosWeights_iff sos).mpr hSos)
              ((polyAtIdx_iff nonneg idx g).mpr hg) (ih restSum hRest)
      · simp [hSos] at h

/-- `s` is the listed combination of the equation generators with polynomial multipliers. -/
inductive IdealCombRel (eqs : List Poly) : List (Poly × Nat) → Poly → Prop where
  | nil : IdealCombRel eqs [] Poly.zero
  | cons (q : Poly) (idx : Nat) (rest : List (Poly × Nat)) (h s : Poly) :
      PolyAtIdx eqs idx h → IdealCombRel eqs rest s →
      IdealCombRel eqs ((q, idx) :: rest) (Poly.add (Poly.mul q h) s)

theorem idealCombRel_iff (eqs : List Poly) (idealTerms : List (Poly × Nat)) (s : Poly) :
    IdealCombRel eqs idealTerms s ↔ expandIdealCombination? eqs idealTerms = some s := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons q idx rest g s hg _ ih =>
      have hg' := (polyAtIdx_iff eqs idx g).mp hg
      simp only [expandIdealCombination?, hg', ih]
  · intro h
    induction idealTerms generalizing s with
    | nil =>
      simp only [expandIdealCombination?, Option.some.injEq] at h
      subst h
      exact IdealCombRel.nil
    | cons hd tl ih =>
      rcases hd with ⟨q, idx⟩
      simp only [expandIdealCombination?] at h
      rcases Option.eq_none_or_eq_some (eqs[idx]?) with hg | ⟨g, hg⟩
      · rw [hg] at h; contradiction
      · rw [hg] at h
        rcases Option.eq_none_or_eq_some (expandIdealCombination? eqs tl) with hRest | ⟨restPoly, hRest⟩
        · rw [hRest] at h; contradiction
        · rw [hRest] at h
          simp only [Option.some.injEq] at h
          subst h
          exact IdealCombRel.cons q idx tl g restPoly
            ((polyAtIdx_iff eqs idx g).mpr hg) (ih restPoly hRest)

/-- `checkIdealMembership` accepts exactly the certificates whose quotients combine the generators
into the target. -/
theorem checkIdealMembership_true_iff (target : Poly) (generators : List Poly) (cert : IdealMembershipCert) :
    checkIdealMembership target generators cert = true ↔
      ∃ comb, IdealCombRel generators cert.quotients comb ∧ (Poly.sub target comb).terms = [] := by
  constructor
  · intro h
    obtain ⟨comb, hComb, hZero⟩ := checkIdealMembership_sound target generators cert h
    exact ⟨comb, (idealCombRel_iff generators cert.quotients comb).mpr hComb,
      (polyTermsNil_iff_isZero _).mpr hZero⟩
  · rintro ⟨comb, hComb, hZero⟩
    unfold checkIdealMembership
    rw [(idealCombRel_iff generators cert.quotients comb).mp hComb]
    exact (polyTermsNil_iff_isZero _).mp hZero

/-- **The queries Stengle's Positivstellensatz refutes over `ℚ[x]`**: some product of the strict
generators, plus a positive-weight SOS term, plus a cone sum over the non-negative generators,
plus an ideal combination of the equations, is the zero polynomial. -/
def StenglePositivstellensatzRefutable (q : PositivstellensatzQuery) : Prop :=
  ∃ (monoidIndices : List Nat) (sigma0 : SOSPoly) (coneTerms : List (SOSPoly × Nat))
    (idealTerms : List (Poly × Nat)) (monoidPoly conePoly idealPoly : Poly),
    PosSosWeights sigma0 ∧
    MonoidProdRel q.strictPos monoidIndices monoidPoly ∧
    ConeSumRel q.nonneg coneTerms conePoly ∧
    IdealCombRel q.eqs idealTerms idealPoly ∧
    (Poly.add monoidPoly (Poly.add sigma0.expand (Poly.add conePoly idealPoly))).terms = []

/-- A Stengle identity leaves no rational point, the origin included. -/
theorem stenglePositivstellensatzRefutable_infeasible (q : PositivstellensatzQuery)
    (hRef : StenglePositivstellensatzRefutable q) : PositivstellensatzQuery.Infeasible q := by
  obtain ⟨monoidIndices, sigma0, coneTerms, idealTerms, monoidPoly, conePoly, idealPoly,
    hPos, hMon, hCone, hIdeal, hZero⟩ := hRef
  exact stengle_identity_infeasible q sigma0 monoidIndices coneTerms idealTerms
    monoidPoly conePoly idealPoly
    ((posSosWeights_iff sigma0).mp hPos)
    ((monoidProdRel_iff q.strictPos monoidIndices monoidPoly).mp hMon)
    ((coneSumRel_iff q.nonneg coneTerms conePoly).mp hCone)
    ((idealCombRel_iff q.eqs idealTerms idealPoly).mp hIdeal)
    ((polyTermsNil_iff_isZero _).mp hZero)

/-- **Theorem (`stenglePositivstellensatzRefutable_iff_check_ok`)**: the checker accepts some
certificate for `q` exactly when `q` has a Stengle identity. The origin test of the checker costs
nothing here: an identity already rules the origin out (`stenglePositivstellensatzRefutable_infeasible`). -/
theorem stenglePositivstellensatzRefutable_iff_check_ok (q : PositivstellensatzQuery) :
    StenglePositivstellensatzRefutable q ↔ ∃ c r, positivstellensatzCheck r q c = .ok := by
  constructor
  · intro hRef
    have hInfeas := stenglePositivstellensatzRefutable_infeasible q hRef
    have hFeas : queryFeasibleAtOrigin q = false :=
      Bool.eq_false_of_ne_true (fun hF => queryFeasibleAtOrigin_refutes q hF hInfeas)
    obtain ⟨monoidIndices, sigma0, coneTerms, idealTerms, monoidPoly, conePoly, idealPoly,
      hPos, hMon, hCone, hIdeal, hZero⟩ := hRef
    exact ⟨⟨monoidIndices, sigma0, coneTerms, idealTerms⟩, 0,
      positivstellensatzCheck_ok_intro 0 q ⟨monoidIndices, sigma0, coneTerms, idealTerms⟩
        monoidPoly conePoly idealPoly hFeas
        ((posSosWeights_iff sigma0).mp hPos)
        ((monoidProdRel_iff q.strictPos monoidIndices monoidPoly).mp hMon)
        ((coneSumRel_iff q.nonneg coneTerms conePoly).mp hCone)
        ((idealCombRel_iff q.eqs idealTerms idealPoly).mp hIdeal)
        ((polyTermsNil_iff_isZero _).mp hZero)⟩
  · rintro ⟨c, r, hOk⟩
    obtain ⟨_, hPos0, monoidPoly, conePoly, idealPoly, hMon, hCone, hIdeal, hZero⟩ :=
      positivstellensatzCheck_ok_elim r q c hOk
    exact ⟨c.monoidIndices, c.sigma0, c.coneTerms, c.idealTerms, monoidPoly, conePoly, idealPoly,
      (posSosWeights_iff c.sigma0).mpr hPos0,
      (monoidProdRel_iff q.strictPos c.monoidIndices monoidPoly).mpr hMon,
      (coneSumRel_iff q.nonneg c.coneTerms conePoly).mpr hCone,
      (idealCombRel_iff q.eqs c.idealTerms idealPoly).mpr hIdeal,
      (polyTermsNil_iff_isZero _).mpr hZero⟩

-- Omitting the positive monoid term lets the empty sum refute even a feasible query.
#tooth stenglePositivstellensatzRefutable_infeasible by mutation StenglePositivstellensatzRefutable :=
  fun q => ∃ sigma0 coneTerms idealTerms conePoly idealPoly,
    PosSosWeights sigma0 ∧ ConeSumRel q.nonneg coneTerms conePoly ∧
    IdealCombRel q.eqs idealTerms idealPoly ∧
    (Poly.add sigma0.expand (Poly.add conePoly idealPoly)).terms = []

-- Ignoring the selected strict generators loses identities that need a vanishing factor.
#tooth stenglePositivstellensatzRefutable_iff_check_ok by mutation expandMonoidProduct :=
  fun _ _ => some Poly.one

-- An invalid generator index disqualifies this certificate only.
#tooth positivstellensatzCheck_refuted by mutation positivstellensatzRefutes :=
  fun k => k == .feasibleAtOrigin || k == .invalidGeneratorIndex

instance positivstellensatzJudge : Judge PositivstellensatzQuery PositivstellensatzCert where
  Clause := PositivstellensatzClause
  Meaning q _c := PositivstellensatzQuery.Infeasible q
  check := positivstellensatzCheck
  sound := by intro r q c h; exact positivstellensatz_general_eval_infeasible r q c h
  refutes := positivstellensatzRefutes
  refuted := by intro r q c k p hRef hRefutes _c'; exact positivstellensatzCheck_refuted hRef hRefutes
  Fragment := StenglePositivstellensatzRefutable
  complete := by
    intro q hFrag _
    exact (stenglePositivstellensatzRefutable_iff_check_ok q).mp hFrag
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
