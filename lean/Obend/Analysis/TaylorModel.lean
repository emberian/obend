module
/-
# Obend.Analysis.TaylorModel — High-Order Taylor Models, Transcendental Enclosures & Picard–Lindelöf ODE Integration

Implements `WS 29.1` (`NEXT-MATHEMATICA.md` §3.2–3.3):
1. **High-Order Taylor Models (`TaylorModel`)**:
   - Represents a smooth function over $x \in \text{domain} = [a, b]$ centered at $c$ as a pair
     $(p(x - c), I_{\text{rem}})$ where $p(\delta) = \sum_{j=0}^k c_j \delta^j$ is a degree-$k$ polynomial
     over `CanonicalRat` and $I_{\text{rem}}$ is a rigorous `Interval` remainder bound.
   - Eliminates the interval dependency and wrapping effect: `tmSub tm tm` cancels all polynomial
     coefficients to zero (`evalTaylorModelRange (tmSub x x) = [0, 0]`), whereas naive interval
     subtraction `Interval.sub dom dom` doubles the interval width.
   - Supports truncated polynomial multiplication `tmMul order a b` that folds degree $> \text{order}$
     monomials and cross-remainder terms rigorously into `rem`.
2. **Certified Transcendental Taylor Models & Convergent Cauchy-Remainder `AnalyticModel`
   (`tmExp`, `tmSin`, `tmCos`, `tmLn1p`, `tmSqrt1p`, `convergentSeriesAnalyticModel`, `certifiedAnalyticModel`)**:
   - Constructs convergent arbitrary-order rational Maclaurin and Newton-binomial series families
     (`expSeries`, `sinSeries`, `cosSeries`, `ln1pSeries`, `sqrt1pSeries`) together with outward
     Cauchy-remainder rational enclosures (`expCauchyEnclosure`, `sqrtRationalEnclosure`, …).
   - Proves constructively by Horner majorant induction (`horner_factorial_majorant`,
     `horner_half_domain_majorant`) that `SeriesOrder extra` forms a certified `AnalyticModel`
     for **every** truncation depth `extra : Nat`, with `certifiedAnalyticModel` (`extra = 6`)
     providing genuine non-zero alternating higher-order residuals over `CanonicalRat`.
3. **Picard–Lindelöf Operator & Long-Horizon ODE Integration (`polyIntegrate`, `picardLinearOdeModel`, `stepPicardTaylor1D`)**:
   - Formal polynomial integration $\int_0^t \sum_{j=0}^k c_j s^j \, ds = \sum_{j=0}^k \frac{c_j}{j+1} t^{j+1}$
     and contractive Picard–Lindelöf iteration $\Phi(x)(t) = x_0 + \int_0^t f(x(s)) \, ds$, proving
     `taylorModel_picard_sound` (`0 sorryAx`).
-/
public import Obend.Analysis.Flowpipe
public section

namespace Obend.Analysis
set_option autoImplicit false

/-! ## 1. Univariate Polynomials in $(x - c)$ & High-Order Taylor Models -/

/-- Add two coefficient lists $\sum a_j \delta^j$ and $\sum b_j \delta^j$ via direct structural recursion on `as`. -/
@[expose] def polyAdd : List CanonicalRat → List CanonicalRat → List CanonicalRat
  | [], bs => bs
  | a :: as, bs =>
    match bs with
    | [] => a :: as
    | b :: bs' => (a + b) :: polyAdd as bs'

/-- Negate a coefficient list. -/
@[expose] def polyNeg (cs : List CanonicalRat) : List CanonicalRat :=
  cs.map (fun c => -c)

/-- Subtract two coefficient lists (`polyAdd as (polyNeg bs)`). -/
@[expose] def polySub (as bs : List CanonicalRat) : List CanonicalRat :=
  polyAdd as (polyNeg bs)

/-- Scale a coefficient list by a rational scalar `s`. -/
@[expose] def polyScale (s : CanonicalRat) (cs : List CanonicalRat) : List CanonicalRat :=
  cs.map (fun c => s * c)

/-- Full Cauchy product of two coefficient lists. -/
@[expose] def polyMulFull : List CanonicalRat → List CanonicalRat → List CanonicalRat
  | [], _ => []
  | a :: as, bs => polyAdd (polyScale a bs) (0 :: polyMulFull as bs)

/-- Evaluate $\sum_{j=0}^k c_j \delta^j$ at a concrete rational offset $\delta = x - c$ via Horner's rule. -/
@[expose] def evalTaylorPolyAt : List CanonicalRat → CanonicalRat → CanonicalRat
  | [], _ => 0
  | c :: cs, dx => c + dx * evalTaylorPolyAt cs dx

/-- Compute $\delta^n$ as an `Interval` enclosure via direct `Nat.rec`. -/
@[expose] def intervalPow (dxIv : Interval) : Nat → Interval
  | 0 => Interval.ofPoint 1
  | n + 1 => Interval.mul dxIv (intervalPow dxIv n)

/-- Evaluate $\sum_{j=0}^k c_j \delta^j$ over an offset interval $\delta \in \text{dxIv}$ via structural recursion on `cs`. -/
@[expose] def evalPolyTermsInterval (dxIv : Interval) : List CanonicalRat → Nat → Interval
  | [], _ => Interval.ofPoint 0
  | c :: cs, deg =>
    let rest := evalPolyTermsInterval dxIv cs (deg + 1)
    if c == 0 then
      rest
    else
      let termIv := Interval.mul (Interval.ofPoint c) (intervalPow dxIv deg)
      Interval.add termIv rest

/-- Evaluate a polynomial coefficient list over an offset interval `dxIv`. -/
@[expose] def evalTaylorPolyInterval (coeffs : List CanonicalRat) (dxIv : Interval) : Interval :=
  evalPolyTermsInterval dxIv coeffs 0

/-- High-order Taylor model $(p(x - c), I_{\text{rem}})$ over $x \in \text{domain}$ centered at `center`. -/
structure TaylorModel where
  coeffs : List CanonicalRat
  center : CanonicalRat
  domain : Interval
  rem    : Interval
  deriving @[expose] DecidableEq, Repr

/-- Offset interval $\text{domain} - \text{center}$. -/
@[expose] def TaylorModel.deltaDomain (tm : TaylorModel) : Interval :=
  Interval.sub tm.domain (Interval.ofPoint tm.center)

/-- Evaluate a `TaylorModel` at a concrete point $x \in \text{domain}$, returning $p(x - c) \oplus I_{\text{rem}}$. -/
@[expose] def evalTaylorModelPoint (tm : TaylorModel) (x : CanonicalRat) : Interval :=
  let pVal := evalTaylorPolyAt tm.coeffs (x - tm.center)
  Interval.add (Interval.ofPoint pVal) tm.rem

/-- Compute the certified range enclosure $p(\text{domain} - c) \oplus I_{\text{rem}}$ of a `TaylorModel`. -/
@[expose] def evalTaylorModelRange (tm : TaylorModel) : Interval :=
  Interval.add (evalTaylorPolyInterval tm.coeffs tm.deltaDomain) tm.rem

/-- Constant Taylor model $(q, c, \text{dom}, [0, 0])$. -/
@[expose] def tmConst (q center : CanonicalRat) (dom : Interval) : TaylorModel where
  coeffs := [q]
  center := center
  domain := dom
  rem    := Interval.ofPoint 0

/-- Identity variable Taylor model $x = c + 1 \cdot (x - c)$ over `dom` centered at `center`. -/
@[expose] def tmVar (center : CanonicalRat) (dom : Interval) : TaylorModel where
  coeffs := [center, 1]
  center := center
  domain := dom
  rem    := Interval.ofPoint 0

/-- Add two Taylor models sharing `(center, domain)`. -/
@[expose] def tmAdd (a b : TaylorModel) : TaylorModel where
  coeffs := polyAdd a.coeffs b.coeffs
  center := a.center
  domain := a.domain
  rem    := Interval.add a.rem b.rem

/-- Subtract two Taylor models sharing `(center, domain)`. -/
@[expose] def tmSub (a b : TaylorModel) : TaylorModel where
  coeffs := polySub a.coeffs b.coeffs
  center := a.center
  domain := a.domain
  rem    := Interval.sub a.rem b.rem

/-- Scale a Taylor model by a rational constant `s`. -/
@[expose] def tmScale (s : CanonicalRat) (tm : TaylorModel) : TaylorModel where
  coeffs := polyScale s tm.coeffs
  center := tm.center
  domain := tm.domain
  rem    := Interval.mul (Interval.ofPoint s) tm.rem

/-- Multiply two Taylor models truncated at polynomial degree `order`, folding all terms of
degree $> \text{order}$ and cross-remainder terms into the certified remainder interval `rem`. -/
@[expose] def tmMul (order : Nat) (a b : TaylorModel) : TaylorModel :=
  let fullCoeffs := polyMulFull a.coeffs b.coeffs
  let keptCoeffs := fullCoeffs.take (order + 1)
  let highCoeffs := fullCoeffs.drop (order + 1)
  let dxIv := a.deltaDomain
  let highRem := evalPolyTermsInterval dxIv highCoeffs (order + 1)
  let polyARange := evalTaylorPolyInterval a.coeffs dxIv
  let polyBRange := evalTaylorPolyInterval b.coeffs dxIv
  let crossRem :=
    Interval.add
      (Interval.add (Interval.mul polyARange b.rem) (Interval.mul a.rem polyBRange))
      (Interval.mul a.rem b.rem)
  { coeffs := keptCoeffs
  , center := a.center
  , domain := a.domain
  , rem    := Interval.add highRem crossRem }

/-! ## 2. Taylor Models with the Lagrange Remainder Constants of $\exp, \sin, \cos, \ln(1+x), \sqrt{1+x}$ (relative to `AnalyticModel`, §5) -/

/-- Degree-4 Taylor model for $\exp(x) \approx 1 + x + \frac{1}{2}x^2 + \frac{1}{6}x^3 + \frac{1}{24}x^4$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
@[expose] def tmExp (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [1, 1, CanonicalRat.mk 1 2, CanonicalRat.mk 1 6, CanonicalRat.mk 1 24]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-5 Taylor model for $\sin(x) \approx x - \frac{1}{6}x^3 + \frac{1}{120}x^5$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
@[expose] def tmSin (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [0, 1, 0, CanonicalRat.mk (-1) 6, 0, CanonicalRat.mk 1 120]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-4 Taylor model for $\cos(x) \approx 1 - \frac{1}{2}x^2 + \frac{1}{24}x^4$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
@[expose] def tmCos (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [1, 0, CanonicalRat.mk (-1) 2, 0, CanonicalRat.mk 1 24]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-4 Taylor model for $\ln(1 + x) \approx x - \frac{1}{2}x^2 + \frac{1}{3}x^3 - \frac{1}{4}x^4$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
@[expose] def tmLn1p (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [0, 1, CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 3, CanonicalRat.mk (-1) 4]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-3 Taylor model for $\sqrt{1 + x} \approx 1 + \frac{1}{2}x - \frac{1}{8}x^2 + \frac{1}{16}x^3$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
@[expose] def tmSqrt1p (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [1, CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 8, CanonicalRat.mk 1 16]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Certified Lagrange remainder bound for degree-4 $\exp(x)$ over `dom` ($\subseteq [-1, 1]$, where $|(\exp)^{(5)}(\xi)| \le 3$):
$R_4(\exp, \text{dom}) = \left[-\frac{3}{120}, \frac{3}{120}\right] \cdot \text{dom}^5 = \left[-\frac{1}{40}, \frac{1}{40}\right] \cdot \text{dom}^5$. -/
@[expose] def lagrangeRemExp4 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-1) 40) (CanonicalRat.mk 1 40)) (intervalPow dom 5)

/-- Certified Lagrange remainder bound for degree-5 $\sin(x)$ over `dom` ($|\sin^{(6)}(\xi)| \le 1$):
$R_5(\sin, \text{dom}) = \left[-\frac{1}{720}, \frac{1}{720}\right] \cdot \text{dom}^6$. -/
@[expose] def lagrangeRemSin5 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-1) 720) (CanonicalRat.mk 1 720)) (intervalPow dom 6)

/-- Certified Lagrange remainder bound for degree-4 $\cos(x)$ over `dom` ($|\cos^{(5)}(\xi)| \le 1$):
$R_4(\cos, \text{dom}) = \left[-\frac{1}{120}, \frac{1}{120}\right] \cdot \text{dom}^5$. -/
@[expose] def lagrangeRemCos4 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-1) 120) (CanonicalRat.mk 1 120)) (intervalPow dom 5)

/-- Certified Lagrange remainder bound for degree-4 $\ln(1 + x)$ over `dom` ($\subseteq [-1/2, 1/2]$, where $|(1+\xi)^{-5}| \le 32$):
$R_4(\ln(1+\cdot), \text{dom}) = \left[-\frac{32}{5}, \frac{32}{5}\right] \cdot \text{dom}^5$. -/
@[expose] def lagrangeRemLn1p4 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-32) 5) (CanonicalRat.mk 32 5)) (intervalPow dom 5)

/-- Certified Lagrange remainder bound for degree-3 $\sqrt{1 + x}$ over `dom` ($\subseteq [-1/2, 1/2]$):
$R_3(\sqrt{1+\cdot}, \text{dom}) = \left[-\frac{15}{24}, \frac{15}{24}\right] \cdot \text{dom}^4 = \left[-\frac{5}{8}, \frac{5}{8}\right] \cdot \text{dom}^4$. -/
@[expose] def lagrangeRemSqrt1p3 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-5) 8) (CanonicalRat.mk 5 8)) (intervalPow dom 4)

@[expose] abbrev lagrangeRemSqrt3 := lagrangeRemSqrt1p3

/-- Canonical invalid/rejected `TaylorModel` (`rem = ⟨1, -1⟩` with `lo > hi`) returned when
`dom` violates the certified validity domain guard. -/
@[expose] def invalidTaylorModel (dom : Interval) : TaylorModel where
  coeffs := []
  center := 0
  domain := dom
  rem    := ⟨1, -1⟩

/-- Certified single-argument Taylor models enforcing explicit domain checks (`dom ⊆ [-1, 1]` for
`exp/sin/cos`, and `dom ⊆ [-1/2, 1/2]` for `ln1p/sqrt1p` so `tmLn1pCertified` can never evaluate
across the $\ln(0) = -\infty$ pole at $x = -1$) and computing Lagrange remainder intervals directly from `dom`. -/
@[expose] def tmExpCertified (dom : Interval) : TaylorModel :=
  if Interval.subset dom (Interval.mk (-1) 1) then
    tmExp dom (lagrangeRemExp4 dom)
  else
    invalidTaylorModel dom

@[expose] def tmSinCertified (dom : Interval) : TaylorModel :=
  if Interval.subset dom (Interval.mk (-1) 1) then
    tmSin dom (lagrangeRemSin5 dom)
  else
    invalidTaylorModel dom

@[expose] def tmCosCertified (dom : Interval) : TaylorModel :=
  if Interval.subset dom (Interval.mk (-1) 1) then
    tmCos dom (lagrangeRemCos4 dom)
  else
    invalidTaylorModel dom

@[expose] def tmLn1pCertified (dom : Interval) : TaylorModel :=
  if Interval.subset dom (Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)) then
    tmLn1p dom (lagrangeRemLn1p4 dom)
  else
    invalidTaylorModel dom

@[expose] def tmSqrt1pCertified (dom : Interval) : TaylorModel :=
  if Interval.subset dom (Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)) then
    tmSqrt1p dom (lagrangeRemSqrt1p3 dom)
  else
    invalidTaylorModel dom

/-- **Theorem (`taylorModel_transcendental_enclosure_sound`)**:
1. **Dependency Cancellation (`tmSub x x = [0, 0]`)**:
   For $x \in [-1/10, 1/10]$, naive interval subtraction `Interval.sub dom dom` yields
   $[-1/5, 1/5]$, whereas `evalTaylorModelRange (tmSub (tmVar 0 dom) (tmVar 0 dom))` cancels
   the linear coefficients and yields the exact point interval $[0, 0]$.
2. **Certified Domain-Derived Lagrange Remainders & Transcendental Enclosures**:
   - Over $x \in [-1/10, 1/10]$, `lagrangeRemExp4 dom`, `lagrangeRemSin5 dom`, and `lagrangeRemCos4 dom`
     compute rigorous remainder intervals directly from `dom` that are strict subintervals of $[-10^{-5}, 10^{-5}]$.
   - Even on a positive singleton domain $X = [1/10, 1/10]$, `lagrangeRemSin5 ⟨1/10, 1/10⟩` encloses
     negative remainders such as $-\frac{1}{720 \cdot 10^6}$.
   - At $x = 0$, $\exp(0) \in [1 - 10^{-5}, 1 + 10^{-5}]$, $\sin(0) \in [-10^{-6}, 10^{-6}]$,
     $\cos(0) \in [1 - 10^{-5}, 1 + 10^{-5}]$, $\ln(1+0) \in [-10^{-4}, 10^{-4}]$, and
     $\sqrt{1+0} \in [1 - 10^{-4}, 1 + 10^{-4}]$.
   - At $x = 1/10$, `evalTaylorModelPoint (tmExpCertified dom) (1/10)` encloses the degree-4 rational
     approximation $265241 / 240000$.
   - Over $x \in [-1/10, 1/10]$, the degree-4 Taylor model for $\sin^2(x) + \cos^2(x)$
     (`tmAdd (tmMul 4 sinTM sinTM) (tmMul 4 cosTM cosTM)`) cancels the $-x^2 + x^2$ quadratic
     and $\pm \frac{1}{3} x^4$ quartic drift and encloses $1$ across the entire domain. -/
-- fixture kept (2026-11-04): consumed by Obend/Tactic/SiliconElab.lean
theorem taylorModel_transcendental_enclosure_sound :
    let dom : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    let posPtDom : Interval := ⟨CanonicalRat.mk 1 10, CanonicalRat.mk 1 10⟩
    let xTM := tmVar 0 dom
    let rem5 : Interval := ⟨CanonicalRat.mk (-1) 100000, CanonicalRat.mk 1 100000⟩
    let expTM := tmExpCertified dom
    let sinTM := tmSinCertified dom
    let cosTM := tmCosCertified dom
    let lnTM := tmLn1pCertified dom
    let sqrtTM := tmSqrt1pCertified dom
    let pythagTM := tmAdd (tmMul 4 sinTM sinTM) (tmMul 4 cosTM cosTM)
    -- 1. Dependency cancellation vs. naive interval subtraction
    evalTaylorModelRange (tmSub xTM xTM) = ⟨0, 0⟩ ∧
    Interval.sub dom dom = ⟨CanonicalRat.mk (-1) 5, CanonicalRat.mk 1 5⟩ ∧
    -- 2. Certified Lagrange remainders derived from dom (including signed singleton domain)
    Interval.isSubintervalOf expTM.rem rem5 = true ∧
    Interval.isSubintervalOf sinTM.rem rem5 = true ∧
    Interval.isSubintervalOf cosTM.rem rem5 = true ∧
    Interval.containsRat (lagrangeRemSin5 posPtDom) (CanonicalRat.mk (-1) 720000000) = true ∧
    -- 3. Verified transcendental enclosures at x = 0 and x = 1/10
    Interval.containsRat (evalTaylorModelPoint expTM 0) 1 = true ∧
    Interval.containsRat (evalTaylorModelPoint sinTM 0) 0 = true ∧
    Interval.containsRat (evalTaylorModelPoint cosTM 0) 1 = true ∧
    Interval.containsRat (evalTaylorModelPoint lnTM 0) 0 = true ∧
    Interval.containsRat (evalTaylorModelPoint sqrtTM 0) 1 = true ∧
    Interval.containsRat (evalTaylorModelPoint expTM (CanonicalRat.mk 1 10)) (CanonicalRat.mk 265241 240000) = true ∧
    -- 4. Pythagorean identity sin^2(x) + cos^2(x) cancels degree-2 and degree-4 terms and encloses 1
    pythagTM.coeffs = [1, 0, 0, 0, 0] ∧
    Interval.containsRat (evalTaylorModelRange pythagTM) 1 = true := by
  decide +kernel

/-! ## 3. Picard–Lindelöf Taylor-Model ODE Operator & Wrapping-Effect Elimination -/

/-- Formal integration helper $\sum_{j} \frac{c_j}{\text{deg}+1} t^{\text{deg}+1}$ via structural recursion on `cs`. -/
@[expose] def polyIntegrateAux : List CanonicalRat → Nat → List CanonicalRat
  | [], _ => []
  | c :: cs, deg => (c / CanonicalRat.ofNat (deg + 1)) :: polyIntegrateAux cs (deg + 1)

/-- Formal integration $\int_0^t p(s) \, ds$ prepending constant $0$. -/
@[expose] def polyIntegrate (cs : List CanonicalRat) : List CanonicalRat :=
  0 :: polyIntegrateAux cs 0

/-- One Picard–Lindelöf operator step $\Phi(p)(t) = x_0 + \int_0^t (\lambda \cdot p(s) + b) \, ds$
for an affine/linearized mode $\dot{x} = \lambda x + b$, truncated to degree `order`. -/
@[expose] def picardLinearStep (order : Nat) (x0 lam b : CanonicalRat) (coeffs : List CanonicalRat) : List CanonicalRat :=
  let rhs := polyAdd [b] (polyScale lam coeffs)
  let integrated := (polyIntegrate rhs).take (order + 1)
  polyAdd [x0] integrated

/-- Iterate the contractive Picard–Lindelöf operator `order` times from constant seed `[x0]`
to obtain the degree-`order` Taylor flow polynomial in $t$. -/
@[expose] def picardLinearCoeffs (order : Nat) (x0 lam b : CanonicalRat) : Nat → List CanonicalRat
  | 0 => [x0]
  | k + 1 => picardLinearStep order x0 lam b (picardLinearCoeffs order x0 lam b k)

/-- Validated degree-4 Picard–Lindelöf Taylor-model step for $\dot{x} = -x$ over $[0, \Delta t]$
starting from initial interval $X_0$:
Contracts the symbolic Taylor propagator $1 - \Delta t + \frac{\Delta t^2}{2} - \frac{\Delta t^3}{6} + \frac{\Delta t^4}{24}$
before multiplying by $X_0$, eliminating the interval dependency/wrapping effect. -/
@[expose] def stepPicardDecay1D (initBox : Interval) (dt : CanonicalRat) (remPad : Interval) : Interval :=
  let unitPicard := picardLinearCoeffs 4 1 (-1) 0 4
  let factor := evalTaylorPolyAt unitPicard dt
  Interval.add (Interval.mul (Interval.ofPoint factor) initBox) remPad

/-- Naive uncontracted degree-4 interval Taylor step that evaluates each power term
$c_j \Delta t^j X_0$ as an independent interval and sums them, suffering the interval wrapping effect. -/
@[expose] def stepNaiveIntervalPicardTerms (initBox : Interval) (dt : CanonicalRat) : List CanonicalRat → Nat → Interval
  | [], _ => Interval.ofPoint 0
  | c :: cs, deg =>
    let coeffDt := Interval.mul (Interval.ofPoint c) (intervalPow (Interval.ofPoint dt) deg)
    let termBox := Interval.mul coeffDt initBox
    Interval.add termBox (stepNaiveIntervalPicardTerms initBox dt cs (deg + 1))

@[expose] def stepNaiveIntervalPicard1D (initBox : Interval) (dt : CanonicalRat) (remPad : Interval) : Interval :=
  let unitPicard := picardLinearCoeffs 4 1 (-1) 0 4
  Interval.add (stepNaiveIntervalPicardTerms initBox dt unitPicard 0) remPad

/-- **Theorem (`taylorModel_picard_sound`)**:
1. **Contractive Picard–Lindelöf Polynomial Generation**:
   Iterating `picardLinearCoeffs 4 1 (-1) 0 4` on $\dot{x} = -x, x(0) = 1$ produces the exact
   degree-4 Taylor expansion `[1, -1, 1/2, -1/6, 1/24]`.
2. **Elimination of the Interval Wrapping Effect**:
   For $\dot{x} = -x$ over step $\Delta t = 1/2$ starting from $X_0 = [9/10, 11/10]$ with
   remainder $R = [-1/1000, 1/1000]$:
   - The degree-4 Picard Taylor-model step (`stepPicardDecay1D X0 (1/2) R`) contracts the symbolic
     propagator $1 - \Delta t + \frac{\Delta t^2}{2} - \frac{\Delta t^3}{6} + \frac{\Delta t^4}{24} = \frac{233}{384}$
     before applying $X_0$, producing a **strict subinterval** (`Interval.isSubintervalOf = true`
     with strictly smaller width `picardBox.hi - picardBox.lo < naiveBox.hi - naiveBox.lo`) of the
     naive interval Taylor evaluation (`stepNaiveIntervalPicard1D X0 (1/2) R`). -/
-- fixture kept (2026-11-04): consumed by Obend/Tactic/SiliconElab.lean
theorem taylorModel_picard_sound :
    let X0 : Interval := ⟨CanonicalRat.mk 9 10, CanonicalRat.mk 11 10⟩
    let dt : CanonicalRat := CanonicalRat.mk 1 2
    let rem : Interval := ⟨CanonicalRat.mk (-1) 1000, CanonicalRat.mk 1 1000⟩
    let naiveBox := stepNaiveIntervalPicard1D X0 dt rem
    let picardBox := stepPicardDecay1D X0 dt rem
    picardLinearCoeffs 4 1 (-1) 0 4 =
      [1, -1, CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 6, CanonicalRat.mk 1 24] ∧
    evalTaylorPolyAt (picardLinearCoeffs 4 1 (-1) 0 4) dt = CanonicalRat.mk 233 384 ∧
    Interval.isSubintervalOf picardBox naiveBox = true ∧
    decide (picardBox.hi - picardBox.lo < naiveBox.hi - naiveBox.lo) = true := by
  decide +kernel

/-! ## 4. Semantic Function Enclosure (`TaylorModel.Models`) & `AnalyticModel` Soundness -/

namespace TaylorModel

/-- Alias for `tm.rem` matching `TaylorModel.Models` specification. -/
@[expose] abbrev remainder (tm : TaylorModel) : Interval := tm.rem

@[expose] abbrev add := tmAdd
@[expose] abbrev sub := tmSub
@[expose] abbrev scale := tmScale
@[expose] abbrev mul := tmMul

/-- Semantic function-enclosure relation `TaylorModel.Models f tm`:
For every point `x` in `tm.domain`, the approximation residual
`f x - evalTaylorPolyAt tm.coeffs (x - tm.center)` lies in `tm.remainder`. -/
@[expose] def Models (f : CanonicalRat → CanonicalRat) (tm : TaylorModel) : Prop :=
  ∀ x, Interval.Mem x tm.domain →
    Interval.Mem (f x - evalTaylorPolyAt tm.coeffs (x - tm.center)) tm.remainder

end TaylorModel

theorem evalTaylorPolyAt_polyAdd (as bs : List CanonicalRat) (dx : CanonicalRat) :
    evalTaylorPolyAt (polyAdd as bs) dx = evalTaylorPolyAt as dx + evalTaylorPolyAt bs dx := by
  induction as generalizing bs with
  | nil =>
    simp [polyAdd, evalTaylorPolyAt]
    grind
  | cons a as ih =>
    cases bs with
    | nil =>
      simp [polyAdd, evalTaylorPolyAt]
      grind
    | cons b bs' =>
      simp only [polyAdd, evalTaylorPolyAt, ih bs']
      grind

theorem evalTaylorPolyAt_polyNeg (cs : List CanonicalRat) (dx : CanonicalRat) :
    evalTaylorPolyAt (polyNeg cs) dx = - evalTaylorPolyAt cs dx := by
  unfold polyNeg
  induction cs with
  | nil =>
    simp [evalTaylorPolyAt]
  | cons c cs ih =>
    simp only [List.map_cons, evalTaylorPolyAt, ih]
    grind

theorem evalTaylorPolyAt_polySub (as bs : List CanonicalRat) (dx : CanonicalRat) :
    evalTaylorPolyAt (polySub as bs) dx = evalTaylorPolyAt as dx - evalTaylorPolyAt bs dx := by
  unfold polySub
  rw [evalTaylorPolyAt_polyAdd, evalTaylorPolyAt_polyNeg]
  grind

theorem evalTaylorPolyAt_polyScale (s : CanonicalRat) (cs : List CanonicalRat) (dx : CanonicalRat) :
    evalTaylorPolyAt (polyScale s cs) dx = s * evalTaylorPolyAt cs dx := by
  unfold polyScale
  induction cs with
  | nil =>
    simp [evalTaylorPolyAt]
  | cons c cs ih =>
    simp only [List.map_cons, evalTaylorPolyAt, ih]
    grind

/-- **Theorem (`TaylorModel.add_models`)**:
If `tmA` models `f` and `tmB` models `g` over the same `(center, domain)`, then `tmAdd tmA tmB`
models `fun x => f x + g x`. -/
theorem TaylorModel.add_models
    {f g : CanonicalRat → CanonicalRat} {tmA tmB : TaylorModel}
    (hCenter : tmA.center = tmB.center)
    (hDom : tmA.domain = tmB.domain)
    (hA : TaylorModel.Models f tmA)
    (hB : TaylorModel.Models g tmB) :
    TaylorModel.Models (fun x => f x + g x) (tmAdd tmA tmB) := by
  intro x hx
  dsimp [tmAdd, TaylorModel.remainder] at hx ⊢
  have hxB : Interval.Mem x tmB.domain := hDom ▸ hx
  have hRemA := hA x hx
  have hRemB := hB x hxB
  rw [hCenter] at hRemA
  have hSum := Interval.add_mem hRemA hRemB
  rw [hCenter, evalTaylorPolyAt_polyAdd]
  have hEq :
      (f x + g x) - (evalTaylorPolyAt tmA.coeffs (x - tmB.center) + evalTaylorPolyAt tmB.coeffs (x - tmB.center)) =
      (f x - evalTaylorPolyAt tmA.coeffs (x - tmB.center)) +
      (g x - evalTaylorPolyAt tmB.coeffs (x - tmB.center)) := by
    grind
  rw [hEq]
  exact hSum

/-- **Theorem (`TaylorModel.sub_models`)**:
If `tmA` models `f` and `tmB` models `g` over the same `(center, domain)`, then `tmSub tmA tmB`
models `fun x => f x - g x`. -/
theorem TaylorModel.sub_models
    {f g : CanonicalRat → CanonicalRat} {tmA tmB : TaylorModel}
    (hCenter : tmA.center = tmB.center)
    (hDom : tmA.domain = tmB.domain)
    (hA : TaylorModel.Models f tmA)
    (hB : TaylorModel.Models g tmB) :
    TaylorModel.Models (fun x => f x - g x) (tmSub tmA tmB) := by
  intro x hx
  dsimp [tmSub, TaylorModel.remainder] at hx ⊢
  have hxB : Interval.Mem x tmB.domain := hDom ▸ hx
  have hRemA := hA x hx
  have hRemB := hB x hxB
  rw [hCenter] at hRemA
  have hDiff := Interval.sub_mem hRemA hRemB
  rw [hCenter, evalTaylorPolyAt_polySub]
  have hEq :
      (f x - g x) - (evalTaylorPolyAt tmA.coeffs (x - tmB.center) - evalTaylorPolyAt tmB.coeffs (x - tmB.center)) =
      (f x - evalTaylorPolyAt tmA.coeffs (x - tmB.center)) -
      (g x - evalTaylorPolyAt tmB.coeffs (x - tmB.center)) := by
    grind
  rw [hEq]
  exact hDiff

/-- **Theorem (`TaylorModel.scale_models`)**:
If `tm` models `f`, then for any rational scalar `s`, `tmScale s tm` models `fun x => s * f x`. -/
theorem TaylorModel.scale_models
    (s : CanonicalRat) {f : CanonicalRat → CanonicalRat} {tm : TaylorModel}
    (h : TaylorModel.Models f tm) :
    TaylorModel.Models (fun x => s * f x) (tmScale s tm) := by
  intro x hx
  dsimp [tmScale, TaylorModel.remainder] at hx ⊢
  have hRem := h x hx
  have hScaled := Interval.mul_mem (Interval.ofPoint_mem s) hRem
  rw [evalTaylorPolyAt_polyScale]
  have hEq :
      s * f x - s * evalTaylorPolyAt tm.coeffs (x - tm.center) =
      s * (f x - evalTaylorPolyAt tm.coeffs (x - tm.center)) := by
    grind
  rw [hEq]
  exact hScaled

/-- Point evaluation enclosure: if `tm` models `f` and `x ∈ tm.domain`, then `f x ∈ evalTaylorModelPoint tm x`. -/
theorem evalTaylorModelPoint_encloses
    {f : CanonicalRat → CanonicalRat} {tm : TaylorModel}
    (h : TaylorModel.Models f tm) {x : CanonicalRat} (hx : x ∈ tm.domain) :
    f x ∈ evalTaylorModelPoint tm x := by
  unfold evalTaylorModelPoint
  have hRem := h x hx
  have hSum := Interval.add_mem (Interval.ofPoint_mem (evalTaylorPolyAt tm.coeffs (x - tm.center))) hRem
  have hEq :
      evalTaylorPolyAt tm.coeffs (x - tm.center) + (f x - evalTaylorPolyAt tm.coeffs (x - tm.center)) = f x := by
    grind
  rw [hEq] at hSum
  exact hSum

/-- Rational power $x^n$ matching `intervalPow`. -/
@[expose] def powRat (x : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | n + 1 => x * powRat x n

theorem intervalPow_mem (dom : Interval) (x : CanonicalRat) (hx : x ∈ dom) :
    ∀ (n : Nat), powRat x n ∈ intervalPow dom n
  | 0 => Interval.ofPoint_mem 1
  | n + 1 => Interval.mul_mem hx (intervalPow_mem dom x hx n)

/-- Constant Taylor model `tmConst` soundly models the constant function `fun _ => q`. -/
theorem TaylorModel.const_models (q center : CanonicalRat) (dom : Interval) :
    TaylorModel.Models (fun _ => q) (tmConst q center dom) := by
  intro x _
  dsimp [tmConst, evalTaylorPolyAt, TaylorModel.remainder]
  have h0 : q - (q + (x - center) * 0) = 0 := by grind
  rw [h0]
  exact Interval.ofPoint_mem 0

/-- Identity variable Taylor model `tmVar` soundly models the identity function `fun x => x`. -/
theorem TaylorModel.var_models (center : CanonicalRat) (dom : Interval) :
    TaylorModel.Models (fun x => x) (tmVar center dom) := by
  intro x _
  dsimp [tmVar, evalTaylorPolyAt, TaylorModel.remainder]
  have h0 : x - (center + (x - center) * (1 + (x - center) * 0)) = 0 := by grind
  rw [h0]
  exact Interval.ofPoint_mem 0

/-- If `x ∈ tm.domain`, then the offset `x - tm.center` belongs to `tm.deltaDomain`. -/
theorem TaylorModel.deltaDomain_mem (tm : TaylorModel) {x : CanonicalRat} (hx : x ∈ tm.domain) :
    (x - tm.center) ∈ tm.deltaDomain :=
  Interval.sub_mem hx (Interval.ofPoint_mem tm.center)

/-- Universal enclosure of `evalPolyTermsInterval`: for any offset `dx ∈ dxIv`, coefficient list `cs`,
and starting degree `deg`, `powRat dx deg * evalTaylorPolyAt cs dx ∈ evalPolyTermsInterval dxIv cs deg`. -/
theorem evalPolyTermsInterval_mem
    (dxIv : Interval) {dx : CanonicalRat} (hdx : dx ∈ dxIv) :
    ∀ (cs : List CanonicalRat) (deg : Nat),
      (powRat dx deg * evalTaylorPolyAt cs dx) ∈ evalPolyTermsInterval dxIv cs deg
  | [], deg => by
    dsimp [evalTaylorPolyAt, evalPolyTermsInterval]
    have h0 : powRat dx deg * 0 = 0 := by grind
    rw [h0]
    exact Interval.ofPoint_mem 0
  | c :: cs, deg => by
    dsimp only [evalTaylorPolyAt, evalPolyTermsInterval]
    have ih := evalPolyTermsInterval_mem dxIv hdx cs (deg + 1)
    by_cases hc : c == 0
    · have hc0 : c = 0 := beq_iff_eq.mp hc
      subst hc0
      simp only [beq_self_eq_true, ↓reduceIte]
      have hEq : powRat dx deg * (0 + dx * evalTaylorPolyAt cs dx) =
          powRat dx (deg + 1) * evalTaylorPolyAt cs dx := by
        dsimp [powRat]
        grind
      rw [hEq]
      exact ih
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hTerm : (c * powRat dx deg) ∈ Interval.mul (Interval.ofPoint c) (intervalPow dxIv deg) :=
        Interval.mul_mem (Interval.ofPoint_mem c) (intervalPow_mem dxIv dx hdx deg)
      have hSum := Interval.add_mem hTerm ih
      have hEq : powRat dx deg * (c + dx * evalTaylorPolyAt cs dx) =
          c * powRat dx deg + powRat dx (deg + 1) * evalTaylorPolyAt cs dx := by
        dsimp [powRat]
        grind
      rw [hEq]
      exact hSum

/-- Universal enclosure of `evalTaylorPolyInterval`: for any offset `dx ∈ dxIv`,
`evalTaylorPolyAt coeffs dx ∈ evalTaylorPolyInterval coeffs dxIv`. -/
theorem evalTaylorPolyInterval_mem
    (coeffs : List CanonicalRat) (dxIv : Interval) {dx : CanonicalRat} (hdx : dx ∈ dxIv) :
    evalTaylorPolyAt coeffs dx ∈ evalTaylorPolyInterval coeffs dxIv := by
  unfold evalTaylorPolyInterval
  have h := evalPolyTermsInterval_mem dxIv hdx coeffs 0
  have h1 : powRat dx 0 * evalTaylorPolyAt coeffs dx = evalTaylorPolyAt coeffs dx := by
    dsimp [powRat]
    grind
  rw [h1] at h
  exact h

/-- **Theorem (`evalTaylorModelRange_encloses`)**:
Full-domain range enclosure: if `tm` models `f` (`TaylorModel.Models f tm`), then for every
point `x ∈ tm.domain`, `f x ∈ evalTaylorModelRange tm`. -/
theorem evalTaylorModelRange_encloses
    {f : CanonicalRat → CanonicalRat} {tm : TaylorModel}
    (h : TaylorModel.Models f tm) {x : CanonicalRat} (hx : x ∈ tm.domain) :
    f x ∈ evalTaylorModelRange tm := by
  unfold evalTaylorModelRange
  have hdx := TaylorModel.deltaDomain_mem tm hx
  have hPoly := evalTaylorPolyInterval_mem tm.coeffs tm.deltaDomain hdx
  have hRem := h x hx
  have hSum := Interval.add_mem hPoly hRem
  have hEq :
      evalTaylorPolyAt tm.coeffs (x - tm.center) + (f x - evalTaylorPolyAt tm.coeffs (x - tm.center)) = f x := by
    grind
  rw [hEq] at hSum
  exact hSum

theorem evalTaylorPolyAt_polyMulFull (as bs : List CanonicalRat) (dx : CanonicalRat) :
    evalTaylorPolyAt (polyMulFull as bs) dx = evalTaylorPolyAt as dx * evalTaylorPolyAt bs dx := by
  induction as with
  | nil =>
    simp [polyMulFull, evalTaylorPolyAt]
  | cons a as ih =>
    simp only [polyMulFull, evalTaylorPolyAt_polyAdd, evalTaylorPolyAt_polyScale, evalTaylorPolyAt, ih]
    grind

theorem evalTaylorPolyAt_take_add_drop (cs : List CanonicalRat) (dx : CanonicalRat) :
    ∀ (k : Nat),
      evalTaylorPolyAt cs dx =
        evalTaylorPolyAt (cs.take k) dx + powRat dx k * evalTaylorPolyAt (cs.drop k) dx
  | 0 => by
    simp [evalTaylorPolyAt, powRat]
    grind
  | k + 1 => by
    cases cs with
    | nil =>
      simp [evalTaylorPolyAt]
      grind
    | cons c rest =>
      simp only [List.take_succ_cons, List.drop_succ_cons, evalTaylorPolyAt, powRat]
      have ih := evalTaylorPolyAt_take_add_drop rest dx k
      grind

/-- **Theorem (`TaylorModel.mul_models`)**:
If `tmA` models `f` and `tmB` models `g` over the same `(center, domain)`, then for any
truncation degree `order : Nat`, `tmMul order tmA tmB` soundly models `fun x => f x * g x`
(folding both the truncated high-degree polynomial terms `> order` and the 3 cross-remainder
terms into the certified remainder interval). -/
theorem TaylorModel.mul_models
    (order : Nat) {f g : CanonicalRat → CanonicalRat} {tmA tmB : TaylorModel}
    (hCenter : tmA.center = tmB.center)
    (hDom : tmA.domain = tmB.domain)
    (hA : TaylorModel.Models f tmA)
    (hB : TaylorModel.Models g tmB) :
    TaylorModel.Models (fun x => f x * g x) (tmMul order tmA tmB) := by
  intro x hx
  let dx := x - tmA.center
  have hdx : dx ∈ tmA.deltaDomain := TaylorModel.deltaDomain_mem tmA hx
  have hxB : x ∈ tmB.domain := hDom ▸ hx
  have hRemA : (f x - evalTaylorPolyAt tmA.coeffs dx) ∈ tmA.rem := hA x hx
  have hRemB : (g x - evalTaylorPolyAt tmB.coeffs dx) ∈ tmB.rem := by
    have hB0 := hB x hxB
    rw [← hCenter] at hB0
    exact hB0
  have hPolyA : evalTaylorPolyAt tmA.coeffs dx ∈ evalTaylorPolyInterval tmA.coeffs tmA.deltaDomain :=
    evalTaylorPolyInterval_mem tmA.coeffs tmA.deltaDomain hdx
  have hPolyB : evalTaylorPolyAt tmB.coeffs dx ∈ evalTaylorPolyInterval tmB.coeffs tmA.deltaDomain :=
    evalTaylorPolyInterval_mem tmB.coeffs tmA.deltaDomain hdx
  have hHigh :
      (powRat dx (order + 1) * evalTaylorPolyAt ((polyMulFull tmA.coeffs tmB.coeffs).drop (order + 1)) dx) ∈
        evalPolyTermsInterval tmA.deltaDomain ((polyMulFull tmA.coeffs tmB.coeffs).drop (order + 1)) (order + 1) :=
    evalPolyTermsInterval_mem tmA.deltaDomain hdx ((polyMulFull tmA.coeffs tmB.coeffs).drop (order + 1)) (order + 1)
  have hCross :
      ((evalTaylorPolyAt tmA.coeffs dx * (g x - evalTaylorPolyAt tmB.coeffs dx) +
        (f x - evalTaylorPolyAt tmA.coeffs dx) * evalTaylorPolyAt tmB.coeffs dx) +
       (f x - evalTaylorPolyAt tmA.coeffs dx) * (g x - evalTaylorPolyAt tmB.coeffs dx)) ∈
      Interval.add
        (Interval.add
          (Interval.mul (evalTaylorPolyInterval tmA.coeffs tmA.deltaDomain) tmB.rem)
          (Interval.mul tmA.rem (evalTaylorPolyInterval tmB.coeffs tmA.deltaDomain)))
        (Interval.mul tmA.rem tmB.rem) :=
    Interval.add_mem
      (Interval.add_mem (Interval.mul_mem hPolyA hRemB) (Interval.mul_mem hRemA hPolyB))
      (Interval.mul_mem hRemA hRemB)
  have hTotal := Interval.add_mem hHigh hCross
  have hSplit := evalTaylorPolyAt_take_add_drop (polyMulFull tmA.coeffs tmB.coeffs) dx (order + 1)
  have hFull := evalTaylorPolyAt_polyMulFull tmA.coeffs tmB.coeffs dx
  have hAlg :
      f x * g x - evalTaylorPolyAt ((polyMulFull tmA.coeffs tmB.coeffs).take (order + 1)) dx =
      (powRat dx (order + 1) * evalTaylorPolyAt ((polyMulFull tmA.coeffs tmB.coeffs).drop (order + 1)) dx) +
      ((evalTaylorPolyAt tmA.coeffs dx * (g x - evalTaylorPolyAt tmB.coeffs dx) +
        (f x - evalTaylorPolyAt tmA.coeffs dx) * evalTaylorPolyAt tmB.coeffs dx) +
       (f x - evalTaylorPolyAt tmA.coeffs dx) * (g x - evalTaylorPolyAt tmB.coeffs dx)) := by
    grind
  show (f x * g x - evalTaylorPolyAt ((polyMulFull tmA.coeffs tmB.coeffs).take (order + 1)) dx) ∈
    (tmMul order tmA tmB).rem
  unfold tmMul
  dsimp only
  rw [hAlg]
  exact hTotal

/-- Canonical validity domain $[-1, 1]$ for degree-4 $\exp(x)$ Taylor–Lagrange remainder bound
(where $|\exp^{(5)}(\xi)| \le e < 3$, so $\frac{3}{5!} = \frac{1}{40}$). -/
@[expose] def expValidDomain : Interval :=
  Interval.mk (-1) 1

/-- Canonical validity domain $[-1, 1]$ for degree-5 $\sin(x)$ and degree-4 $\cos(x)$ Taylor–Lagrange
remainder bounds (`dom.lo ≥ -1 ∧ dom.hi ≤ 1`). -/
@[expose] def trigValidDomain : Interval :=
  Interval.mk (-1) 1

/-- Canonical validity domain $[-\frac{1}{2}, \frac{1}{2}]$ for degree-4 $\ln(1 + x)$ Taylor–Lagrange
remainder bound (where $|(1 + \xi)^{-5}| \le 2^5 = 32$ on $\xi \in [-1/2, 1/2]$, strictly avoiding the
branch singularity at $x = -1$). -/
@[expose] def ln1pValidDomain : Interval :=
  Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)

/-- Canonical validity domain $[-\frac{1}{2}, \frac{1}{2}]$ for degree-3 $\sqrt{1 + x}$ Taylor–Lagrange
remainder bound (where $\left|\frac{-15}{16}(1+\xi)^{-7/2}\right| \cdot \frac{1}{4!} \le \frac{5}{8}$ on $\xi \in [-1/2, 1/2]$). -/
@[expose] def sqrt1pValidDomain : Interval :=
  Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)

/-! ## 5. Convergent Rational Power-Series & Cauchy-Remainder `AnalyticModel`

We construct arbitrary-order convergent rational power-series families for $\exp(x)$, $\sin(x)$,
$\cos(x)$, $\ln(1 + x)$, and $\sqrt{1 + x}$, together with outward rational Cauchy-remainder
enclosures and a constructive proof by Horner majorant induction (`horner_factorial_majorant`,
`horner_half_domain_majorant`) that `SeriesOrder extra` satisfies the exact Taylor–Lagrange
remainder envelopes of `AnalyticModel` for **every** higher-order truncation depth `extra : Nat`. -/

/-- Type tag indexing the convergent rational `AnalyticModel` at extra series truncation depth `extra`. -/
structure SeriesOrder (extra : Nat) : Type where
  mk ::

/-- Exact natural factorial $n!$. -/
@[expose] def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

theorem natFact_pos (n : Nat) : 0 < natFact n := by
  induction n with
  | zero => decide
  | succ k ih =>
    unfold natFact
    exact Nat.mul_pos (Nat.succ_pos k) ih

theorem natFact_succ_ge_two_mul {d : Nat} (hd : 1 ≤ d) :
    2 * natFact d ≤ natFact (d + 1) := by
  show 2 * natFact d ≤ (d + 1) * natFact d
  have h2 : 2 ≤ d + 1 := by omega
  exact Nat.mul_le_mul_right (natFact d) h2

theorem rat_div_nonneg {a b : CanonicalRat} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a / b := by
  by_cases hlt : a / b < 0
  · have hPosDiff : 0 < -(a / b) := by grind
    have hProdPos : 0 < (-(a / b)) * b := Rat.mul_pos hPosDiff hb
    have hNe : b ≠ 0 := by grind
    have hCancel : a / b * b = a := Rat.div_mul_cancel hNe
    grind
  · grind

theorem rat_div_le_of_mul_le {a b c : CanonicalRat} (hb : 0 < b) (h : a ≤ c * b) :
    a / b ≤ c := by
  by_cases hlt : c < a / b
  · have hPosDiff : 0 < a / b - c := by grind
    have hProdPos : 0 < (a / b - c) * b := Rat.mul_pos hPosDiff hb
    have hNe : b ≠ 0 := by grind
    have hCancel : a / b * b = a := Rat.div_mul_cancel hNe
    grind
  · grind

theorem rat_le_div_of_mul_le {a b c : CanonicalRat} (hb : 0 < b) (h : a * b ≤ c) :
    a ≤ c / b := by
  by_cases hlt : c / b < a
  · have hPosDiff : 0 < a - c / b := by grind
    have hProdPos : 0 < (a - c / b) * b := Rat.mul_pos hPosDiff hb
    have hNe : b ≠ 0 := by grind
    have hCancel : c / b * b = c := Rat.div_mul_cancel hNe
    grind
  · grind

/-- Append decomposition for `evalTaylorPolyAt`:
`evalTaylorPolyAt (as ++ bs) dx = evalTaylorPolyAt as dx + powRat dx as.length * evalTaylorPolyAt bs dx`. -/
theorem evalTaylorPolyAt_append (as bs : List CanonicalRat) (dx : CanonicalRat) :
    evalTaylorPolyAt (as ++ bs) dx =
      evalTaylorPolyAt as dx + powRat dx as.length * evalTaylorPolyAt bs dx := by
  induction as with
  | nil =>
    dsimp [evalTaylorPolyAt, powRat]
    grind
  | cons a rest ih =>
    simp only [List.cons_append, List.length_cons, evalTaylorPolyAt, ih]
    have hPow : powRat dx (rest.length + 1) = dx * powRat dx rest.length := rfl
    rw [hPow]
    grind

/-- Coefficient-wise factorial bound $|a_j| \le \frac{1}{(d + j)!}$ starting at degree `d`. -/
@[expose] def FactorialBounded : Nat → List CanonicalRat → Prop
  | _, [] => True
  | d, a :: rest =>
    a ∈ Interval.mk (CanonicalRat.mk (-1) (natFact d)) (CanonicalRat.mk 1 (natFact d)) ∧
      FactorialBounded (d + 1) rest

theorem two_div_succ_fact_le_inv_fact {d : Nat} (hd : 1 ≤ d) :
    CanonicalRat.mk 2 (natFact (d + 1)) ≤ CanonicalRat.mk 1 (natFact d) := by
  have hPosD : 0 < natFact d := natFact_pos d
  have hPosS : 0 < natFact (d + 1) := natFact_pos (d + 1)
  have hGrow : 2 * natFact d ≤ natFact (d + 1) := natFact_succ_ge_two_mul hd
  have hRatD : (0 : CanonicalRat) < (natFact d : CanonicalRat) := by exact_mod_cast hPosD
  have hRatS : (0 : CanonicalRat) < (natFact (d + 1) : CanonicalRat) := by exact_mod_cast hPosS
  have hRatGrow : 2 * (natFact d : CanonicalRat) ≤ (natFact (d + 1) : CanonicalRat) := by
    exact_mod_cast hGrow
  have hMk2 : CanonicalRat.mk 2 (natFact (d + 1)) = (2 : CanonicalRat) / (natFact (d + 1) : CanonicalRat) := by
    simp [CanonicalRat.mk, Rat.mkRat_eq_div]
  have hMk1 : CanonicalRat.mk 1 (natFact d) = (1 : CanonicalRat) / (natFact d : CanonicalRat) := by
    simp [CanonicalRat.mk, Rat.mkRat_eq_div]
  rw [hMk2, hMk1]
  apply rat_div_le_of_mul_le hRatS
  have hInvNonneg : (0 : CanonicalRat) ≤ (1 : CanonicalRat) / (natFact d : CanonicalRat) :=
    rat_div_nonneg (by decide) hRatD
  have hRhs := Rat.mul_le_mul_of_nonneg_left hRatGrow hInvNonneg
  have hNe : (natFact d : CanonicalRat) ≠ 0 := by grind
  grind

/-- **Lemma (`horner_factorial_majorant`)**:
For any starting degree $d \ge 1$, any tail coefficient list `cs` obeying `FactorialBounded d cs`,
and any $x \in [-1, 1]$, Horner evaluation satisfies
`evalTaylorPolyAt cs x ∈ [-2 / d!, 2 / d!]`. -/
theorem horner_factorial_majorant {d : Nat} {cs : List CanonicalRat} {x : CanonicalRat}
    (hd : 1 ≤ d)
    (hBnd : FactorialBounded d cs)
    (hx : x ∈ expValidDomain) :
    evalTaylorPolyAt cs x ∈
      Interval.mk (CanonicalRat.mk (-2) (natFact d)) (CanonicalRat.mk 2 (natFact d)) := by
  induction cs generalizing d with
  | nil =>
    simp only [evalTaylorPolyAt, Interval.mem_iff]
    have hPos : (0 : CanonicalRat) < (natFact d : CanonicalRat) := by exact_mod_cast natFact_pos d
    have hNonneg : (0 : CanonicalRat) ≤ CanonicalRat.mk 2 (natFact d) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]
      exact rat_div_nonneg (by decide) hPos
    have hNeg : CanonicalRat.mk (-2) (natFact d) = -CanonicalRat.mk 2 (natFact d) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]
      grind
    rw [hNeg]
    grind
  | cons a rest ih =>
    rcases hBnd with ⟨ha, hRest⟩
    have hd1 : 1 ≤ d + 1 := by omega
    have hRec := ih hd1 hRest
    have hStepLe : CanonicalRat.mk 2 (natFact (d + 1)) ≤ CanonicalRat.mk 1 (natFact d) :=
      two_div_succ_fact_le_inv_fact hd
    have hNegEq1 : CanonicalRat.mk (-1) (natFact d) = -CanonicalRat.mk 1 (natFact d) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
    have hNegEq2 : CanonicalRat.mk (-2) (natFact (d + 1)) = -CanonicalRat.mk 2 (natFact (d + 1)) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
    have hNegEq2d : CanonicalRat.mk (-2) (natFact d) = -CanonicalRat.mk 2 (natFact d) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
    have hDouble : CanonicalRat.mk 1 (natFact d) + CanonicalRat.mk 1 (natFact d) =
        CanonicalRat.mk 2 (natFact d) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
    have hYSub : evalTaylorPolyAt rest x ∈
        Interval.mk (CanonicalRat.mk (-1) (natFact d)) (CanonicalRat.mk 1 (natFact d)) := by
      rw [Interval.mem_iff] at hRec ⊢
      grind
    have hMul := Interval.mul_mem hx hYSub
    have hMulSub : (x * evalTaylorPolyAt rest x) ∈
        Interval.mk (CanonicalRat.mk (-1) (natFact d)) (CanonicalRat.mk 1 (natFact d)) := by
      unfold expValidDomain Interval.mul Interval.min4 Interval.max4 at hMul
      rw [Interval.mem_iff] at hMul ⊢
      rw [hNegEq1] at hMul ⊢
      have hRatD : (0 : CanonicalRat) < (natFact d : CanonicalRat) := by exact_mod_cast natFact_pos d
      have hPos1 : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 (natFact d) := by
        simp [CanonicalRat.mk, Rat.mkRat_eq_div]
        exact rat_div_nonneg (by decide) hRatD
      grind
    have hAdd := Interval.add_mem ha hMulSub
    unfold evalTaylorPolyAt
    rw [Interval.mem_iff] at hAdd ⊢
    unfold Interval.add at hAdd
    grind

/-- Uniform coefficient bound $|a| \le M$ across a polynomial tail list. -/
@[expose] def UniformBounded (M : CanonicalRat) : List CanonicalRat → Prop
  | [] => True
  | a :: rest => a ∈ Interval.mk (-M) M ∧ UniformBounded M rest

/-- **Lemma (`horner_half_domain_majorant`)**:
For any $M \ge 0$, any coefficient list `cs` obeying `UniformBounded M cs`, and any
$x \in [-\frac{1}{2}, \frac{1}{2}]$, Horner evaluation satisfies
`evalTaylorPolyAt cs x ∈ [-2 * M, 2 * M]`. -/
theorem horner_half_domain_majorant {M : CanonicalRat} {cs : List CanonicalRat} {x : CanonicalRat}
    (hM : 0 ≤ M)
    (hBnd : UniformBounded M cs)
    (hx : x ∈ Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)) :
    evalTaylorPolyAt cs x ∈ Interval.mk (-(2 * M)) (2 * M) := by
  induction cs with
  | nil =>
    simp only [evalTaylorPolyAt, Interval.mem_iff]
    grind
  | cons a rest ih =>
    rcases hBnd with ⟨ha, hRest⟩
    have hRec := ih hRest
    have hMul := Interval.mul_mem hx hRec
    have hHalfEq : CanonicalRat.mk 1 2 * (2 * M) = M := by
      have : CanonicalRat.mk 1 2 = (1 : CanonicalRat) / 2 := by decide +kernel
      rw [this]; grind
    have hNegHalfEq : CanonicalRat.mk (-1) 2 = -CanonicalRat.mk 1 2 := by decide +kernel
    have hMulSub : (x * evalTaylorPolyAt rest x) ∈ Interval.mk (-M) M := by
      unfold Interval.mul Interval.min4 Interval.max4 at hMul
      rw [Interval.mem_iff] at hMul ⊢
      rw [hNegHalfEq] at hMul
      grind
    have hAdd := Interval.add_mem ha hMulSub
    unfold evalTaylorPolyAt
    unfold Interval.add at hAdd
    rw [Interval.mem_iff] at hAdd ⊢
    grind

/-! ### 5.1 Convergent Maclaurin & Newton-Binomial Rational Series -/

/-- Exponential Maclaurin tail $\sum_{j=0}^{\text{len}-1} \frac{x^j}{(d + j)!}$ starting at degree `d`. -/
@[expose] def expTailFrom (d : Nat) : Nat → List CanonicalRat
  | 0 => []
  | len + 1 => CanonicalRat.mk 1 (natFact d) :: expTailFrom (d + 1) len

theorem expTailFrom_factorialBounded (d len : Nat) :
    FactorialBounded d (expTailFrom d len) := by
  induction len generalizing d with
  | zero => trivial
  | succ k ih =>
    refine ⟨?_, ih (d + 1)⟩
    rw [Interval.mem_iff]
    have hRatD : (0 : CanonicalRat) < (natFact d : CanonicalRat) := by exact_mod_cast natFact_pos d
    have hPos : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 (natFact d) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]
      exact rat_div_nonneg (by decide) hRatD
    have hNeg : CanonicalRat.mk (-1) (natFact d) = -CanonicalRat.mk 1 (natFact d) := by
      simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
    grind

/-- Convergent exponential Maclaurin series coefficients up to degree `4 + extra`. -/
@[expose] def expSeriesCoeffs (extra : Nat) : List CanonicalRat :=
  [1, 1, CanonicalRat.mk 1 2, CanonicalRat.mk 1 6, CanonicalRat.mk 1 24] ++ expTailFrom 5 extra

/-- Convergent rational exponential series $\sum_{k=0}^{4 + \text{extra}} \frac{x^k}{k!}$. -/
@[expose] def expSeries (extra : Nat) (x : CanonicalRat) : CanonicalRat :=
  evalTaylorPolyAt (expSeriesCoeffs extra) x

/-- Sine Maclaurin coefficient at degree `d`:
$0$ for even $d$, $\frac{1}{d!}$ for $d \equiv 1 \pmod 4$, $-\frac{1}{d!}$ for $d \equiv 3 \pmod 4$. -/
@[expose] def sinCoeffAt (d : Nat) : CanonicalRat :=
  if d % 2 == 0 then 0
  else if d % 4 == 1 then CanonicalRat.mk 1 (natFact d)
  else CanonicalRat.mk (-1) (natFact d)

/-- Sine Maclaurin tail starting at degree `d`. -/
@[expose] def sinTailFrom (d : Nat) : Nat → List CanonicalRat
  | 0 => []
  | len + 1 => sinCoeffAt d :: sinTailFrom (d + 1) len

theorem sinCoeffAt_mem_fact (d : Nat) :
    sinCoeffAt d ∈ Interval.mk (CanonicalRat.mk (-1) (natFact d)) (CanonicalRat.mk 1 (natFact d)) := by
  unfold sinCoeffAt
  have hRatD : (0 : CanonicalRat) < (natFact d : CanonicalRat) := by exact_mod_cast natFact_pos d
  have hPos : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 (natFact d) := by
    simp [CanonicalRat.mk, Rat.mkRat_eq_div]
    exact rat_div_nonneg (by decide) hRatD
  have hNeg : CanonicalRat.mk (-1) (natFact d) = -CanonicalRat.mk 1 (natFact d) := by
    simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
  split
  · rw [Interval.mem_iff]; grind
  · split <;> (rw [Interval.mem_iff]; grind)

theorem sinTailFrom_factorialBounded (d len : Nat) :
    FactorialBounded d (sinTailFrom d len) := by
  induction len generalizing d with
  | zero => trivial
  | succ k ih => exact ⟨sinCoeffAt_mem_fact d, ih (d + 1)⟩

/-- Convergent sine Maclaurin series coefficients up to degree `6 + extra`. -/
@[expose] def sinSeriesCoeffs (extra : Nat) : List CanonicalRat :=
  [0, 1, 0, CanonicalRat.mk (-1) 6, 0, CanonicalRat.mk 1 120] ++ (0 :: sinTailFrom 7 extra)

/-- Convergent rational sine series $\sum_{k=0}^{6 + \text{extra}} c_k x^k$. -/
@[expose] def sinSeries (extra : Nat) (x : CanonicalRat) : CanonicalRat :=
  evalTaylorPolyAt (sinSeriesCoeffs extra) x

/-- Cosine Maclaurin coefficient at degree `d`:
$0$ for odd $d$, $\frac{1}{d!}$ for $d \equiv 0 \pmod 4$, $-\frac{1}{d!}$ for $d \equiv 2 \pmod 4$. -/
@[expose] def cosCoeffAt (d : Nat) : CanonicalRat :=
  if d % 2 == 1 then 0
  else if d % 4 == 0 then CanonicalRat.mk 1 (natFact d)
  else CanonicalRat.mk (-1) (natFact d)

/-- Cosine Maclaurin tail starting at degree `d`. -/
@[expose] def cosTailFrom (d : Nat) : Nat → List CanonicalRat
  | 0 => []
  | len + 1 => cosCoeffAt d :: cosTailFrom (d + 1) len

theorem cosCoeffAt_mem_fact (d : Nat) :
    cosCoeffAt d ∈ Interval.mk (CanonicalRat.mk (-1) (natFact d)) (CanonicalRat.mk 1 (natFact d)) := by
  unfold cosCoeffAt
  have hRatD : (0 : CanonicalRat) < (natFact d : CanonicalRat) := by exact_mod_cast natFact_pos d
  have hPos : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 (natFact d) := by
    simp [CanonicalRat.mk, Rat.mkRat_eq_div]
    exact rat_div_nonneg (by decide) hRatD
  have hNeg : CanonicalRat.mk (-1) (natFact d) = -CanonicalRat.mk 1 (natFact d) := by
    simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
  split
  · rw [Interval.mem_iff]; grind
  · split <;> (rw [Interval.mem_iff]; grind)

theorem cosTailFrom_factorialBounded (d len : Nat) :
    FactorialBounded d (cosTailFrom d len) := by
  induction len generalizing d with
  | zero => trivial
  | succ k ih => exact ⟨cosCoeffAt_mem_fact d, ih (d + 1)⟩

/-- Convergent cosine Maclaurin series coefficients up to degree `5 + extra`. -/
@[expose] def cosSeriesCoeffs (extra : Nat) : List CanonicalRat :=
  [1, 0, CanonicalRat.mk (-1) 2, 0, CanonicalRat.mk 1 24] ++ (0 :: cosTailFrom 6 extra)

/-- Convergent rational cosine series $\sum_{k=0}^{5 + \text{extra}} c_k x^k$. -/
@[expose] def cosSeries (extra : Nat) (x : CanonicalRat) : CanonicalRat :=
  evalTaylorPolyAt (cosSeriesCoeffs extra) x

/-- Alternating Mercator series tail for $\ln(1 + x)$ starting at degree `d ≥ 1` with `sign ∈ {-1, 1}`. -/
@[expose] def ln1pTailFrom (d : Nat) (sign : Int) : Nat → List CanonicalRat
  | 0 => []
  | len + 1 => CanonicalRat.mk sign d :: ln1pTailFrom (d + 1) (-sign) len

theorem ln1pTailFrom_uniformBounded {d : Nat} {sign : Int} (hd : 5 ≤ d)
    (hSign : sign = 1 ∨ sign = -1) (len : Nat) :
    UniformBounded (CanonicalRat.mk 1 5) (ln1pTailFrom d sign len) := by
  induction len generalizing d sign with
  | zero => trivial
  | succ k ih =>
    have hdPos : 0 < d := by omega
    have hRatD : (0 : CanonicalRat) < (d : CanonicalRat) := by exact_mod_cast hdPos
    have hRat5 : (5 : CanonicalRat) ≤ (d : CanonicalRat) := by exact_mod_cast hd
    have hBound1 : (1 : CanonicalRat) / (d : CanonicalRat) ≤ CanonicalRat.mk 1 5 := by
      have h5 : CanonicalRat.mk 1 5 = (1 : CanonicalRat) / 5 := by decide +kernel
      rw [h5]
      apply rat_div_le_of_mul_le hRatD
      grind
    refine ⟨?_, ih (by omega) (by rcases hSign with rfl | rfl <;> simp)⟩
    rcases hSign with rfl | rfl
    · rw [Interval.mem_iff]
      have hEq : CanonicalRat.mk 1 d = (1 : CanonicalRat) / (d : CanonicalRat) := by
        simp [CanonicalRat.mk, Rat.mkRat_eq_div]
      have hNonneg : (0 : CanonicalRat) ≤ (1 : CanonicalRat) / (d : CanonicalRat) :=
        rat_div_nonneg (by decide) hRatD
      rw [hEq]
      grind
    · rw [Interval.mem_iff]
      have hEq : CanonicalRat.mk (-1) d = -((1 : CanonicalRat) / (d : CanonicalRat)) := by
        simp [CanonicalRat.mk, Rat.mkRat_eq_div]; grind
      have hNonneg : (0 : CanonicalRat) ≤ (1 : CanonicalRat) / (d : CanonicalRat) :=
        rat_div_nonneg (by decide) hRatD
      rw [hEq]
      grind

/-- Convergent Mercator series coefficients for $\ln(1 + x)$ up to degree `4 + extra`. -/
@[expose] def ln1pSeriesCoeffs (extra : Nat) : List CanonicalRat :=
  [0, 1, CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 3, CanonicalRat.mk (-1) 4] ++
    ln1pTailFrom 5 1 extra

/-- Convergent rational Mercator series $\sum_{k=1}^{4 + \text{extra}} \frac{(-1)^{k-1}}{k} x^k$. -/
@[expose] def ln1pSeries (extra : Nat) (x : CanonicalRat) : CanonicalRat :=
  evalTaylorPolyAt (ln1pSeriesCoeffs extra) x

/-- Newton generalized binomial tail for $\sqrt{1 + x} = \sum_{k=0}^\infty \binom{1/2}{k} x^k$,
where $b_{d+1} = -b_d \cdot \frac{2d - 1}{2d + 2}$. -/
@[expose] def sqrt1pTailFrom (d : Nat) (curCoeff : CanonicalRat) : Nat → List CanonicalRat
  | 0 => []
  | len + 1 =>
    let nextCoeff := -curCoeff * CanonicalRat.mk (Int.ofNat (2 * d - 1)) (2 * d + 2)
    curCoeff :: sqrt1pTailFrom (d + 1) nextCoeff len

theorem sqrt1p_ratio_mem_unit {d : Nat} (hd : 1 ≤ d) :
    CanonicalRat.mk (Int.ofNat (2 * d - 1)) (2 * d + 2) ∈ Interval.mk (0 : CanonicalRat) 1 := by
  rw [Interval.mem_iff]
  let numNat : Nat := 2 * d - 1
  let denNat : Nat := 2 * d + 2
  have hDenPos : 0 < denNat := by omega
  have hNumLe : numNat ≤ denNat := by omega
  have hEq : CanonicalRat.mk (Int.ofNat numNat) denNat =
      (numNat : CanonicalRat) / (denNat : CanonicalRat) := by
    simp only [CanonicalRat.mk, Rat.mkRat_eq_div]
    exact_mod_cast rfl
  change (0 : CanonicalRat) ≤ CanonicalRat.mk (Int.ofNat numNat) denNat ∧
    CanonicalRat.mk (Int.ofNat numNat) denNat ≤ 1
  rw [hEq]
  have hRatDen : (0 : CanonicalRat) < (denNat : CanonicalRat) := by exact_mod_cast hDenPos
  have hRatNumNonneg : (0 : CanonicalRat) ≤ (numNat : CanonicalRat) := by
    exact_mod_cast Nat.zero_le numNat
  refine ⟨rat_div_nonneg hRatNumNonneg hRatDen, ?_⟩
  apply rat_div_le_of_mul_le hRatDen
  have hRatLe : (numNat : CanonicalRat) ≤ (denNat : CanonicalRat) := by
    exact_mod_cast hNumLe
  grind

theorem sqrt1pTailFrom_uniformBounded {d : Nat} {cur : CanonicalRat} {M : CanonicalRat}
    (hd : 1 ≤ d) (hM : 0 ≤ M) (hCur : cur ∈ Interval.mk (-M) M) (len : Nat) :
    UniformBounded M (sqrt1pTailFrom d cur len) := by
  induction len generalizing d cur with
  | zero => trivial
  | succ k ih =>
    refine ⟨hCur, ?_⟩
    have hRat := sqrt1p_ratio_mem_unit hd
    have hNegCur : (-cur) ∈ Interval.mk (-M) M := by
      rw [Interval.mem_iff] at hCur ⊢; grind
    have hMul := Interval.mul_mem hNegCur hRat
    have hNext : (-cur * CanonicalRat.mk (Int.ofNat (2 * d - 1)) (2 * d + 2)) ∈ Interval.mk (-M) M := by
      unfold Interval.mul Interval.min4 Interval.max4 at hMul
      rw [Interval.mem_iff] at hMul ⊢
      grind
    exact ih (by omega) hNext

/-- Convergent Newton-binomial coefficients for $\sqrt{1 + x}$ up to degree `3 + extra`. -/
@[expose] def sqrt1pSeriesCoeffs (extra : Nat) : List CanonicalRat :=
  [1, CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 8, CanonicalRat.mk 1 16] ++
    sqrt1pTailFrom 4 (CanonicalRat.mk (-5) 128) extra

/-- Convergent rational Newton-binomial series for $\sqrt{1 + x}$. -/
@[expose] def sqrt1pSeries (extra : Nat) (x : CanonicalRat) : CanonicalRat :=
  evalTaylorPolyAt (sqrt1pSeriesCoeffs extra) x

/-! ### 5.2 Outward Cauchy-Remainder Enclosures & Certified Rational Square-Root Enclosure -/

/-- Outward rational Cauchy-remainder interval enclosure for $\exp(x)$ at arbitrary truncation order `order ≥ 1`:
evaluates $\sum_{k=0}^{\text{order}} \frac{x^k}{k!} \oplus \left[-\frac{2}{(\text{order}+1)!}, \frac{2}{(\text{order}+1)!}\right] \cdot x^{\text{order}+1}$. -/
@[expose] def expCauchyEnclosure (order : Nat) (x : CanonicalRat) : Interval :=
  let headVal := evalTaylorPolyAt (expTailFrom 0 (order + 1)) x
  let d := order + 1
  let tailFactor := Interval.mk (CanonicalRat.mk (-2) (natFact d)) (CanonicalRat.mk 2 (natFact d))
  let remIv := Interval.mul tailFactor (Interval.ofPoint (powRat x d))
  Interval.add (Interval.ofPoint headVal) remIv

theorem expTailFrom_split (d a b : Nat) :
    expTailFrom d (a + b) = expTailFrom d a ++ expTailFrom (d + a) b := by
  induction a generalizing d with
  | zero => simp [expTailFrom]
  | succ k ih =>
    simp only [Nat.succ_add, expTailFrom, List.cons_append]
    rw [ih (d + 1)]
    have hEq : d + 1 + k = d + (k + 1) := by omega
    rw [hEq]

theorem expTailFrom_length (d len : Nat) :
    (expTailFrom d len).length = len := by
  induction len generalizing d with
  | zero => rfl
  | succ k ih => simp [expTailFrom, ih]

/-- **Theorem (`expCauchyEnclosure_encloses_higher_orders`)**:
For EVERY truncation order `order : Nat`, EVERY extra degree count `more : Nat`, and EVERY
$x \in [-1, 1]$, the higher-degree Maclaurin sum $\sum_{k=0}^{\text{order} + \text{more}} \frac{x^k}{k!}$
is rigorously enclosed inside `expCauchyEnclosure order x`. -/
theorem expCauchyEnclosure_encloses_higher_orders
    (order more : Nat) (x : CanonicalRat) (hx : x ∈ expValidDomain) :
    evalTaylorPolyAt (expTailFrom 0 (order + 1 + more)) x ∈ expCauchyEnclosure order x := by
  rw [expTailFrom_split 0 (order + 1) more, evalTaylorPolyAt_append, expTailFrom_length]
  have h0 : 0 + (order + 1) = order + 1 := by omega
  rw [h0]
  have hd : 1 ≤ order + 1 := by omega
  have hTail := horner_factorial_majorant hd (expTailFrom_factorialBounded (order + 1) more) hx
  have hMul := Interval.mul_mem hTail (Interval.ofPoint_mem (powRat x (order + 1)))
  have hComm : powRat x (order + 1) * evalTaylorPolyAt (expTailFrom (order + 1) more) x =
      evalTaylorPolyAt (expTailFrom (order + 1) more) x * powRat x (order + 1) := by grind
  rw [hComm]
  exact Interval.add_mem (Interval.ofPoint_mem _) hMul

/-- Outward rational square-root interval enclosure via scaled `Nat.sqrt` bracketing
(following `Soundcalc.Common.Sqrt`): scales nonnegative $q = \frac{n}{d}$ by $2^{2 \cdot \text{prec}}$
and returns $\left[\frac{\lfloor \sqrt{n \cdot d \cdot 4^{\text{prec}}} \rfloor}{d \cdot 2^{\text{prec}}},
\frac{\lfloor \sqrt{n \cdot d \cdot 4^{\text{prec}}} \rfloor + 1}{d \cdot 2^{\text{prec}}}\right]$. -/
@[expose] def sqrtRationalEnclosure (prec : Nat) (q : CanonicalRat) : Interval :=
  if decide (q < 0) then
    ⟨1, -1⟩
  else
    let n : Nat := q.num.toNat
    let d : Nat := q.den
    let scale : Nat := 2 ^ prec
    let rad : Nat := n * d * (scale * scale)
    let s : Nat := Nat.sqrt rad
    let denom : Nat := d * scale
    ⟨CanonicalRat.mk (Int.ofNat s) denom, CanonicalRat.mk (Int.ofNat (s + 1)) denom⟩

/-- **Theorem (`sqrtRationalEnclosure_brackets_square`)**:
For every precision `prec : Nat` and nonnegative rational `0 ≤ q`, `I := sqrtRationalEnclosure prec q`
satisfies `0 ≤ I.lo`, `I.lo ≤ I.hi`, and `I.lo * I.lo ≤ q ∧ q ≤ I.hi * I.hi`. -/
theorem sqrtRationalEnclosure_brackets_square
    (prec : Nat) (q : CanonicalRat) (hq : 0 ≤ q) :
    let I := sqrtRationalEnclosure prec q
    0 ≤ I.lo ∧ I.lo ≤ I.hi ∧ I.lo * I.lo ≤ q ∧ q ≤ I.hi * I.hi := by
  dsimp only [sqrtRationalEnclosure]
  have hDecFalse : decide (q < 0) = false := by
    rw [decide_eq_false_iff_not]
    grind
  rw [hDecFalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  let n : Nat := q.num.toNat
  let d : Nat := q.den
  let scale : Nat := 2 ^ prec
  let rad : Nat := n * d * (scale * scale)
  let s : Nat := Nat.sqrt rad
  let denom : Nat := d * scale
  have hdPos : 0 < d := q.den_pos
  have hScalePos : 0 < scale := Nat.two_pow_pos prec
  have hDenomPos : 0 < denom := Nat.mul_pos hdPos hScalePos
  have hLoSq : s * s ≤ rad := Nat.sqrt_le rad
  have hHiSq : rad ≤ (s + 1) * (s + 1) := Nat.le_of_lt (Nat.lt_succ_sqrt rad)
  have hNumNonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hNumEq : (n : Int) = q.num := Int.toNat_of_nonneg hNumNonneg
  have hqEq : q = (n : CanonicalRat) / (d : CanonicalRat) := by
    have h1 : mkRat q.num d = q := Rat.mkRat_self q
    rw [Rat.mkRat_eq_div] at h1
    have hCast : (q.num : CanonicalRat) = (n : CanonicalRat) := by exact_mod_cast hNumEq.symm
    rw [← h1, hCast]
  have hLoEq : CanonicalRat.mk (Int.ofNat s) denom = (s : CanonicalRat) / (denom : CanonicalRat) := by
    simp only [CanonicalRat.mk, Rat.mkRat_eq_div]
    exact_mod_cast rfl
  have hHiEq : CanonicalRat.mk (Int.ofNat (s + 1)) denom = ((s + 1 : Nat) : CanonicalRat) / (denom : CanonicalRat) := by
    simp only [CanonicalRat.mk, Rat.mkRat_eq_div]
    exact_mod_cast rfl
  change 0 ≤ CanonicalRat.mk (Int.ofNat s) denom ∧
    CanonicalRat.mk (Int.ofNat s) denom ≤ CanonicalRat.mk (Int.ofNat (s + 1)) denom ∧
    CanonicalRat.mk (Int.ofNat s) denom * CanonicalRat.mk (Int.ofNat s) denom ≤ q ∧
    q ≤ CanonicalRat.mk (Int.ofNat (s + 1)) denom * CanonicalRat.mk (Int.ofNat (s + 1)) denom
  rw [hLoEq, hHiEq]
  have hRatDenom : (0 : CanonicalRat) < (denom : CanonicalRat) := by exact_mod_cast hDenomPos
  have hRatDenomSq : (0 : CanonicalRat) < (denom : CanonicalRat) * (denom : CanonicalRat) :=
    Rat.mul_pos hRatDenom hRatDenom
  have hLoNonneg : (0 : CanonicalRat) ≤ (s : CanonicalRat) / (denom : CanonicalRat) :=
    rat_div_nonneg (by exact_mod_cast Nat.zero_le s) hRatDenom
  have hLoLeHi : (s : CanonicalRat) / (denom : CanonicalRat) ≤ ((s + 1 : Nat) : CanonicalRat) / (denom : CanonicalRat) := by
    apply rat_div_le_of_mul_le hRatDenom
    have hNe : (denom : CanonicalRat) ≠ 0 := by grind
    have hCancel : ((s + 1 : Nat) : CanonicalRat) / (denom : CanonicalRat) * (denom : CanonicalRat) =
        ((s + 1 : Nat) : CanonicalRat) := by grind
    rw [hCancel]
    exact_mod_cast Nat.le_succ s
  have hRadRat : (rad : CanonicalRat) = q * ((denom : CanonicalRat) * (denom : CanonicalRat)) := by
    have hRadExpand : (rad : CanonicalRat) = (n : CanonicalRat) * (d : CanonicalRat) * ((scale : CanonicalRat) * (scale : CanonicalRat)) := by
      exact_mod_cast (rfl : rad = n * d * (scale * scale))
    have hDenomExpand : (denom : CanonicalRat) = (d : CanonicalRat) * (scale : CanonicalRat) := by
      exact_mod_cast (rfl : denom = d * scale)
    have hdNe : (d : CanonicalRat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdPos)
    rw [hRadExpand, hDenomExpand, hqEq]
    grind
  have hSqLo : ((s : CanonicalRat) / (denom : CanonicalRat)) * ((s : CanonicalRat) / (denom : CanonicalRat)) ≤ q := by
    have hCastLo : (s : CanonicalRat) * (s : CanonicalRat) ≤ (rad : CanonicalRat) := by exact_mod_cast hLoSq
    rw [hRadRat] at hCastLo
    have hNe : (denom : CanonicalRat) ≠ 0 := by grind
    have hDivProd : ((s : CanonicalRat) / (denom : CanonicalRat)) * ((s : CanonicalRat) / (denom : CanonicalRat)) =
        ((s : CanonicalRat) * (s : CanonicalRat)) / ((denom : CanonicalRat) * (denom : CanonicalRat)) := by grind
    rw [hDivProd]
    exact rat_div_le_of_mul_le hRatDenomSq hCastLo
  have hSqHi : q ≤ (((s + 1 : Nat) : CanonicalRat) / (denom : CanonicalRat)) *
      (((s + 1 : Nat) : CanonicalRat) / (denom : CanonicalRat)) := by
    have hCastHi : (rad : CanonicalRat) ≤ ((s + 1 : Nat) : CanonicalRat) * ((s + 1 : Nat) : CanonicalRat) := by
      exact_mod_cast hHiSq
    rw [hRadRat] at hCastHi
    have hNe : (denom : CanonicalRat) ≠ 0 := by grind
    have hDivProd : (((s + 1 : Nat) : CanonicalRat) / (denom : CanonicalRat)) *
        (((s + 1 : Nat) : CanonicalRat) / (denom : CanonicalRat)) =
        (((s + 1 : Nat) : CanonicalRat) * ((s + 1 : Nat) : CanonicalRat)) /
          ((denom : CanonicalRat) * (denom : CanonicalRat)) := by grind
    rw [hDivProd]
    exact rat_le_div_of_mul_le hRatDenomSq hCastHi
  exact ⟨hLoNonneg, hLoLeHi, hSqLo, hSqHi⟩

/-! ### 5.3 Certified `AnalyticModel` Typeclass & Arbitrary-Order Convergent Instances -/

/-- A certified rational model of the five elementary transcendental/algebraic functions
(`expFn`, `sinFn`, `cosFn`, `ln1pFn`, `sqrt1pFn`) satisfying the degree-4/5/4/4/3 Taylor–Lagrange
remainder identities with exact real remainder constants over their convergence domains. -/
class AnalyticModel (R : Type) where
  expFn    : CanonicalRat → CanonicalRat
  sinFn    : CanonicalRat → CanonicalRat
  cosFn    : CanonicalRat → CanonicalRat
  ln1pFn   : CanonicalRat → CanonicalRat
  sqrt1pFn : CanonicalRat → CanonicalRat
  exp_lagrange4 :
    ∀ (D : Interval), Interval.subset D expValidDomain = true →
      ∀ (x : CanonicalRat), Interval.Mem x D →
        ∃ c ∈ Interval.mk (CanonicalRat.mk (-1) 40) (CanonicalRat.mk 1 40),
          expFn x - evalTaylorPolyAt [1, 1, CanonicalRat.mk 1 2, CanonicalRat.mk 1 6, CanonicalRat.mk 1 24] x =
            c * powRat x 5
  sin_lagrange5 :
    ∀ (D : Interval), Interval.subset D trigValidDomain = true →
      ∀ (x : CanonicalRat), Interval.Mem x D →
        ∃ c ∈ Interval.mk (CanonicalRat.mk (-1) 720) (CanonicalRat.mk 1 720),
          sinFn x - evalTaylorPolyAt [0, 1, 0, CanonicalRat.mk (-1) 6, 0, CanonicalRat.mk 1 120] x =
            c * powRat x 6
  cos_lagrange4 :
    ∀ (D : Interval), Interval.subset D trigValidDomain = true →
      ∀ (x : CanonicalRat), Interval.Mem x D →
        ∃ c ∈ Interval.mk (CanonicalRat.mk (-1) 120) (CanonicalRat.mk 1 120),
          cosFn x - evalTaylorPolyAt [1, 0, CanonicalRat.mk (-1) 2, 0, CanonicalRat.mk 1 24] x =
            c * powRat x 5
  ln1p_lagrange4 :
    ∀ (D : Interval), Interval.subset D ln1pValidDomain = true →
      ∀ (x : CanonicalRat), Interval.Mem x D →
        ∃ c ∈ Interval.mk (CanonicalRat.mk (-32) 5) (CanonicalRat.mk 32 5),
          ln1pFn x - evalTaylorPolyAt [0, 1, CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 3, CanonicalRat.mk (-1) 4] x =
            c * powRat x 5
  sqrt1p_lagrange3 :
    ∀ (D : Interval), Interval.subset D sqrt1pValidDomain = true →
      ∀ (x : CanonicalRat), Interval.Mem x D →
        ∃ c ∈ Interval.mk (CanonicalRat.mk (-5) 8) (CanonicalRat.mk 5 8),
          sqrt1pFn x - evalTaylorPolyAt [1, CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 8, CanonicalRat.mk 1 16] x =
            c * powRat x 4

/-- **Theorem / Instance (`convergentSeriesAnalyticModel`)**:
For **every** extra series truncation depth `extra : Nat`, the convergent rational Maclaurin and
Newton-binomial series (`expSeries extra`, `sinSeries extra`, `cosSeries extra`, `ln1pSeries extra`,
`sqrt1pSeries extra`) constructively satisfy all five Taylor–Lagrange remainder envelopes of `AnalyticModel`. -/
instance convergentSeriesAnalyticModel (extra : Nat) : AnalyticModel (SeriesOrder extra) where
  expFn    := expSeries extra
  sinFn    := sinSeries extra
  cosFn    := cosSeries extra
  ln1pFn   := ln1pSeries extra
  sqrt1pFn := sqrt1pSeries extra
  exp_lagrange4 D hDom x hx := by
    have hxDom : x ∈ expValidDomain := Interval.subset_sound hDom hx
    let c := evalTaylorPolyAt (expTailFrom 5 extra) x
    have hcTight := horner_factorial_majorant (d := 5) (by decide) (expTailFrom_factorialBounded 5 extra) hxDom
    have hSub : Interval.subset
        (Interval.mk (CanonicalRat.mk (-2) (natFact 5)) (CanonicalRat.mk 2 (natFact 5)))
        (Interval.mk (CanonicalRat.mk (-1) 40) (CanonicalRat.mk 1 40)) = true := by decide +kernel
    refine ⟨c, Interval.subset_sound hSub hcTight, ?_⟩
    unfold expSeries expSeriesCoeffs
    rw [evalTaylorPolyAt_append]
    dsimp [c]
    grind
  sin_lagrange5 D hDom x hx := by
    have hxDom : x ∈ expValidDomain := Interval.subset_sound hDom hx
    let y := evalTaylorPolyAt (sinTailFrom 7 extra) x
    let c := x * y
    have hyTight := horner_factorial_majorant (d := 7) (by decide) (sinTailFrom_factorialBounded 7 extra) hxDom
    have hcMul := Interval.mul_mem hxDom hyTight
    have hSub : Interval.subset
        (Interval.mul expValidDomain (Interval.mk (CanonicalRat.mk (-2) (natFact 7)) (CanonicalRat.mk 2 (natFact 7))))
        (Interval.mk (CanonicalRat.mk (-1) 720) (CanonicalRat.mk 1 720)) = true := by decide +kernel
    refine ⟨c, Interval.subset_sound hSub hcMul, ?_⟩
    unfold sinSeries sinSeriesCoeffs
    rw [evalTaylorPolyAt_append]
    dsimp [evalTaylorPolyAt, c, y]
    grind
  cos_lagrange4 D hDom x hx := by
    have hxDom : x ∈ expValidDomain := Interval.subset_sound hDom hx
    let y := evalTaylorPolyAt (cosTailFrom 6 extra) x
    let c := x * y
    have hyTight := horner_factorial_majorant (d := 6) (by decide) (cosTailFrom_factorialBounded 6 extra) hxDom
    have hcMul := Interval.mul_mem hxDom hyTight
    have hSub : Interval.subset
        (Interval.mul expValidDomain (Interval.mk (CanonicalRat.mk (-2) (natFact 6)) (CanonicalRat.mk 2 (natFact 6))))
        (Interval.mk (CanonicalRat.mk (-1) 120) (CanonicalRat.mk 1 120)) = true := by decide +kernel
    refine ⟨c, Interval.subset_sound hSub hcMul, ?_⟩
    unfold cosSeries cosSeriesCoeffs
    rw [evalTaylorPolyAt_append]
    dsimp [evalTaylorPolyAt, c, y]
    grind
  ln1p_lagrange4 D hDom x hx := by
    have hxDom : x ∈ Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2) :=
      Interval.subset_sound hDom hx
    let c := evalTaylorPolyAt (ln1pTailFrom 5 1 extra) x
    have hcTight := horner_half_domain_majorant
      (M := CanonicalRat.mk 1 5) (by decide +kernel)
      (ln1pTailFrom_uniformBounded (d := 5) (sign := 1) (by decide) (Or.inl rfl) extra) hxDom
    have hSub : Interval.subset
        (Interval.mk (-(2 * CanonicalRat.mk 1 5)) (2 * CanonicalRat.mk 1 5))
        (Interval.mk (CanonicalRat.mk (-32) 5) (CanonicalRat.mk 32 5)) = true := by decide +kernel
    refine ⟨c, Interval.subset_sound hSub hcTight, ?_⟩
    unfold ln1pSeries ln1pSeriesCoeffs
    rw [evalTaylorPolyAt_append]
    dsimp [c]
    grind
  sqrt1p_lagrange3 D hDom x hx := by
    have hxDom : x ∈ Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2) :=
      Interval.subset_sound hDom hx
    let c := evalTaylorPolyAt (sqrt1pTailFrom 4 (CanonicalRat.mk (-5) 128) extra) x
    have hcTight := horner_half_domain_majorant
      (M := CanonicalRat.mk 5 128) (by decide +kernel)
      (sqrt1pTailFrom_uniformBounded (d := 4) (cur := CanonicalRat.mk (-5) 128) (M := CanonicalRat.mk 5 128)
        (by decide) (by decide +kernel) (by decide +kernel) extra) hxDom
    have hSub : Interval.subset
        (Interval.mk (-(2 * CanonicalRat.mk 5 128)) (2 * CanonicalRat.mk 5 128))
        (Interval.mk (CanonicalRat.mk (-5) 8) (CanonicalRat.mk 5 8)) = true := by decide +kernel
    refine ⟨c, Interval.subset_sound hSub hcTight, ?_⟩
    unfold sqrt1pSeries sqrt1pSeriesCoeffs
    rw [evalTaylorPolyAt_append]
    dsimp [c]
    grind

/-- Canonical high-order certified `AnalyticModel CanonicalRat` (`extra = 6`: degree-10 `exp`,
degree-12 `sin`, degree-11 `cos`, degree-10 `ln1p`, and degree-9 `sqrt1p`), where all five modelled
functions carry non-zero alternating higher-degree series tails enclosed constructively by `AnalyticModel`. -/
instance certifiedAnalyticModel : AnalyticModel CanonicalRat :=
  let M := convergentSeriesAnalyticModel 6
  { expFn          := M.expFn
    sinFn          := M.sinFn
    cosFn          := M.cosFn
    ln1pFn         := M.ln1pFn
    sqrt1pFn       := M.sqrt1pFn
    exp_lagrange4  := M.exp_lagrange4
    sin_lagrange5  := M.sin_lagrange5
    cos_lagrange4  := M.cos_lagrange4
    ln1p_lagrange4 := M.ln1p_lagrange4
    sqrt1p_lagrange3 := M.sqrt1p_lagrange3 }

/-- **Theorem (`tmExpCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ expValidDomain` (`[-1, 1]`), `tmExpCertified dom`
soundly models `AnalyticModel.expFn`. -/
theorem tmExpCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom expValidDomain = true := by decide) :
    TaylorModel.Models (M.expFn) (tmExpCertified dom) := by
  intro x hx
  unfold tmExpCertified at hx ⊢
  have hSub : Interval.subset dom (Interval.mk (-1) 1) = true := hDom
  rw [if_pos hSub] at hx ⊢
  dsimp [tmExp, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.exp_lagrange4 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 5)

/-- **Theorem (`tmSinCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ trigValidDomain` (`[-1, 1]`), `tmSinCertified dom`
soundly models `AnalyticModel.sinFn` (including on positive singleton domains $X = [1/10, 1/10]$
where $\sin(x) - p_5(x) < 0$). -/
theorem tmSinCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom trigValidDomain = true := by decide) :
    TaylorModel.Models (M.sinFn) (tmSinCertified dom) := by
  intro x hx
  unfold tmSinCertified at hx ⊢
  have hSub : Interval.subset dom (Interval.mk (-1) 1) = true := hDom
  rw [if_pos hSub] at hx ⊢
  dsimp [tmSin, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.sin_lagrange5 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 6)

/-- **Theorem (`tmCosCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ trigValidDomain` (`[-1, 1]`), `tmCosCertified dom`
soundly models `AnalyticModel.cosFn`. -/
theorem tmCosCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom trigValidDomain = true := by decide) :
    TaylorModel.Models (M.cosFn) (tmCosCertified dom) := by
  intro x hx
  unfold tmCosCertified at hx ⊢
  have hSub : Interval.subset dom (Interval.mk (-1) 1) = true := hDom
  rw [if_pos hSub] at hx ⊢
  dsimp [tmCos, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.cos_lagrange4 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 5)

/-- **Theorem (`tmLn1pCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ ln1pValidDomain` (`[-1/2, 1/2]`), `tmLn1pCertified dom`
soundly models `AnalyticModel.ln1pFn`. -/
theorem tmLn1pCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom ln1pValidDomain = true := by decide) :
    TaylorModel.Models (M.ln1pFn) (tmLn1pCertified dom) := by
  intro x hx
  unfold tmLn1pCertified at hx ⊢
  have hSub : Interval.subset dom (Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)) = true := hDom
  rw [if_pos hSub] at hx ⊢
  dsimp [tmLn1p, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.ln1p_lagrange4 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 5)

/-- **Theorem (`tmSqrt1pCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ sqrt1pValidDomain` (`[-1/2, 1/2]`), `tmSqrt1pCertified dom`
soundly models `AnalyticModel.sqrt1pFn`. -/
theorem tmSqrt1pCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom sqrt1pValidDomain = true := by decide) :
    TaylorModel.Models (M.sqrt1pFn) (tmSqrt1pCertified dom) := by
  intro x hx
  unfold tmSqrt1pCertified at hx ⊢
  have hSub : Interval.subset dom (Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)) = true := hDom
  rw [if_pos hSub] at hx ⊢
  dsimp [tmSqrt1p, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.sqrt1p_lagrange3 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 4)

/-- **Theorem (`analyticModel_domain_guard_rejects_out_of_domain`)**:
Out-of-domain intervals (such as $x = 10$ outside `expValidDomain = [-1, 1]`, $x = 5$ outside
`trigValidDomain = [-1, 1]`, or the branch singularity $x = -1$ outside `ln1pValidDomain = [-1/2, 1/2]`
and `sqrt1pValidDomain = [-1/2, 1/2]`) are rejected by the validity domain guards (`Interval.subset = false`),
while in-domain intervals such as $[-1/10, 1/10]$ are accepted (`Interval.subset = true`). -/
-- fixture kept (2026-11-04): target of #tooth at Obend/Analysis/TaylorModel.lean:943
theorem analyticModel_domain_guard_rejects_out_of_domain :
    let tenthDom := Interval.mk (CanonicalRat.mk (-1) 10) (CanonicalRat.mk 1 10)
    Interval.subset tenthDom expValidDomain = true ∧
    Interval.subset tenthDom trigValidDomain = true ∧
    Interval.subset tenthDom ln1pValidDomain = true ∧
    Interval.subset tenthDom sqrt1pValidDomain = true ∧
    Interval.subset (Interval.ofPoint 10) expValidDomain = false ∧
    Interval.subset (Interval.ofPoint 5) trigValidDomain = false ∧
    Interval.subset (Interval.ofPoint (-1)) ln1pValidDomain = false ∧
    Interval.subset (Interval.ofPoint (-1)) sqrt1pValidDomain = false := by
  decide +kernel

/-- Concrete verification of `certifiedAnalyticModel` non-zero alternating higher-degree tails,
`expCauchyEnclosure`, `sqrtRationalEnclosure`, and fail-closed pole guards (`tmLn1pCertified ⟨-1, 0⟩`). -/
example :
    let unitDom : Interval := ⟨-1, 1⟩
    let expAt1 := evalTaylorModelPoint (tmExpCertified unitDom) 1
    let cauchy8At1 := expCauchyEnclosure 8 1
    let eRatApprox : CanonicalRat := CanonicalRat.mk 27182818 10000000
    let tenth : CanonicalRat := CanonicalRat.mk 1 10
    Interval.containsRat expAt1 (certifiedAnalyticModel.expFn 1) = true ∧
    Interval.containsRat cauchy8At1 (expSeries 8 1) = true ∧
    Interval.containsRat expAt1 eRatApprox = true ∧
    decide (certifiedAnalyticModel.sinFn tenth <
      evalTaylorPolyAt [0, 1, 0, CanonicalRat.mk (-1) 6, 0, CanonicalRat.mk 1 120] tenth) = true ∧
    decide (certifiedAnalyticModel.cosFn tenth <
      evalTaylorPolyAt [1, 0, CanonicalRat.mk (-1) 2, 0, CanonicalRat.mk 1 24] tenth) = true ∧
    decide (certifiedAnalyticModel.ln1pFn tenth >
      evalTaylorPolyAt [0, 1, CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 3, CanonicalRat.mk (-1) 4] tenth) = true ∧
    decide (certifiedAnalyticModel.sqrt1pFn tenth <
      evalTaylorPolyAt [1, CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 8, CanonicalRat.mk 1 16] tenth) = true ∧
    (tmLn1pCertified ⟨-1, 0⟩).rem = ⟨1, -1⟩ ∧
    (tmExpCertified ⟨-2, 2⟩).rem = ⟨1, -1⟩ ∧
    Interval.containsRat (evalTaylorModelRange (tmLn1pCertified ⟨-1, 0⟩)) 0 = false := by
  decide +kernel

end Obend.Analysis
end

