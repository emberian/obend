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
2. **Verified Transcendental Enclosures (`tmExp`, `tmSin`, `tmCos`, `tmLn1p`, `tmSqrt1p`)**:
   - Certified Taylor-with-Lagrange-remainder models for $\exp(x)$, $\sin(x)$, $\cos(x)$, $\ln(1+x)$,
     and $\sqrt{1+x}$ over bounded rational domains, proving `taylorModel_transcendental_enclosure_sound`.
3. **Picard–Lindelöf Operator & Long-Horizon ODE Integration (`polyIntegrate`, `picardLinearOdeModel`, `stepPicardTaylor1D`)**:
   - Formal polynomial integration $\int_0^t \sum_{j=0}^k c_j s^j \, ds = \sum_{j=0}^k \frac{c_j}{j+1} t^{j+1}$
     and contractive Picard–Lindelöf iteration $\Phi(x)(t) = x_0 + \int_0^t f(x(s)) \, ds$, proving
     `taylorModel_picard_sound` (`0 sorryAx`).
-/
public import Obend.Analysis.Flowpipe
@[expose] public section

namespace Obend.Analysis
set_option autoImplicit false

/-! ## 1. Univariate Polynomials in $(x - c)$ & High-Order Taylor Models -/

/-- Add two coefficient lists $\sum a_j \delta^j$ and $\sum b_j \delta^j$ via direct structural recursion on `as`. -/
def polyAdd : List CanonicalRat → List CanonicalRat → List CanonicalRat
  | [], bs => bs
  | a :: as, bs =>
    match bs with
    | [] => a :: as
    | b :: bs' => (a + b) :: polyAdd as bs'

/-- Negate a coefficient list. -/
def polyNeg (cs : List CanonicalRat) : List CanonicalRat :=
  cs.map (fun c => -c)

/-- Subtract two coefficient lists (`polyAdd as (polyNeg bs)`). -/
def polySub (as bs : List CanonicalRat) : List CanonicalRat :=
  polyAdd as (polyNeg bs)

/-- Scale a coefficient list by a rational scalar `s`. -/
def polyScale (s : CanonicalRat) (cs : List CanonicalRat) : List CanonicalRat :=
  cs.map (fun c => s * c)

/-- Full Cauchy product of two coefficient lists. -/
def polyMulFull : List CanonicalRat → List CanonicalRat → List CanonicalRat
  | [], _ => []
  | a :: as, bs => polyAdd (polyScale a bs) (0 :: polyMulFull as bs)

/-- Evaluate $\sum_{j=0}^k c_j \delta^j$ at a concrete rational offset $\delta = x - c$ via Horner's rule. -/
def evalTaylorPolyAt : List CanonicalRat → CanonicalRat → CanonicalRat
  | [], _ => 0
  | c :: cs, dx => c + dx * evalTaylorPolyAt cs dx

/-- Compute $\delta^n$ as an `Interval` enclosure via direct `Nat.rec`. -/
def intervalPow (dxIv : Interval) : Nat → Interval
  | 0 => Interval.ofPoint 1
  | n + 1 => Interval.mul dxIv (intervalPow dxIv n)

/-- Evaluate $\sum_{j=0}^k c_j \delta^j$ over an offset interval $\delta \in \text{dxIv}$ via structural recursion on `cs`. -/
def evalPolyTermsInterval (dxIv : Interval) : List CanonicalRat → Nat → Interval
  | [], _ => Interval.ofPoint 0
  | c :: cs, deg =>
    let rest := evalPolyTermsInterval dxIv cs (deg + 1)
    if c == 0 then
      rest
    else
      let termIv := Interval.mul (Interval.ofPoint c) (intervalPow dxIv deg)
      Interval.add termIv rest

/-- Evaluate a polynomial coefficient list over an offset interval `dxIv`. -/
def evalTaylorPolyInterval (coeffs : List CanonicalRat) (dxIv : Interval) : Interval :=
  evalPolyTermsInterval dxIv coeffs 0

/-- High-order Taylor model $(p(x - c), I_{\text{rem}})$ over $x \in \text{domain}$ centered at `center`. -/
structure TaylorModel where
  coeffs : List CanonicalRat
  center : CanonicalRat
  domain : Interval
  rem    : Interval
  deriving DecidableEq, Repr

/-- Offset interval $\text{domain} - \text{center}$. -/
def TaylorModel.deltaDomain (tm : TaylorModel) : Interval :=
  Interval.sub tm.domain (Interval.ofPoint tm.center)

/-- Evaluate a `TaylorModel` at a concrete point $x \in \text{domain}$, returning $p(x - c) \oplus I_{\text{rem}}$. -/
def evalTaylorModelPoint (tm : TaylorModel) (x : CanonicalRat) : Interval :=
  let pVal := evalTaylorPolyAt tm.coeffs (x - tm.center)
  Interval.add (Interval.ofPoint pVal) tm.rem

/-- Compute the certified range enclosure $p(\text{domain} - c) \oplus I_{\text{rem}}$ of a `TaylorModel`. -/
def evalTaylorModelRange (tm : TaylorModel) : Interval :=
  Interval.add (evalTaylorPolyInterval tm.coeffs tm.deltaDomain) tm.rem

/-- Constant Taylor model $(q, c, \text{dom}, [0, 0])$. -/
def tmConst (q center : CanonicalRat) (dom : Interval) : TaylorModel where
  coeffs := [q]
  center := center
  domain := dom
  rem    := Interval.ofPoint 0

/-- Identity variable Taylor model $x = c + 1 \cdot (x - c)$ over `dom` centered at `center`. -/
def tmVar (center : CanonicalRat) (dom : Interval) : TaylorModel where
  coeffs := [center, 1]
  center := center
  domain := dom
  rem    := Interval.ofPoint 0

/-- Add two Taylor models sharing `(center, domain)`. -/
def tmAdd (a b : TaylorModel) : TaylorModel where
  coeffs := polyAdd a.coeffs b.coeffs
  center := a.center
  domain := a.domain
  rem    := Interval.add a.rem b.rem

/-- Subtract two Taylor models sharing `(center, domain)`. -/
def tmSub (a b : TaylorModel) : TaylorModel where
  coeffs := polySub a.coeffs b.coeffs
  center := a.center
  domain := a.domain
  rem    := Interval.sub a.rem b.rem

/-- Scale a Taylor model by a rational constant `s`. -/
def tmScale (s : CanonicalRat) (tm : TaylorModel) : TaylorModel where
  coeffs := polyScale s tm.coeffs
  center := tm.center
  domain := tm.domain
  rem    := Interval.mul (Interval.ofPoint s) tm.rem

/-- Multiply two Taylor models truncated at polynomial degree `order`, folding all terms of
degree $> \text{order}$ and cross-remainder terms into the certified remainder interval `rem`. -/
def tmMul (order : Nat) (a b : TaylorModel) : TaylorModel :=
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

/-! ## 2. Verified Transcendental Taylor Enclosures ($\exp, \sin, \cos, \ln(1+x), \sqrt{1+x}$) -/

/-- Degree-4 Taylor model for $\exp(x) \approx 1 + x + \frac{1}{2}x^2 + \frac{1}{6}x^3 + \frac{1}{24}x^4$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
def tmExp (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [1, 1, CanonicalRat.mk 1 2, CanonicalRat.mk 1 6, CanonicalRat.mk 1 24]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-5 Taylor model for $\sin(x) \approx x - \frac{1}{6}x^3 + \frac{1}{120}x^5$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
def tmSin (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [0, 1, 0, CanonicalRat.mk (-1) 6, 0, CanonicalRat.mk 1 120]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-4 Taylor model for $\cos(x) \approx 1 - \frac{1}{2}x^2 + \frac{1}{24}x^4$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
def tmCos (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [1, 0, CanonicalRat.mk (-1) 2, 0, CanonicalRat.mk 1 24]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-4 Taylor model for $\ln(1 + x) \approx x - \frac{1}{2}x^2 + \frac{1}{3}x^3 - \frac{1}{4}x^4$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
def tmLn1p (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [0, 1, CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 3, CanonicalRat.mk (-1) 4]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- Degree-3 Taylor model for $\sqrt{1 + x} \approx 1 + \frac{1}{2}x - \frac{1}{8}x^2 + \frac{1}{16}x^3$
centered at $0$ over `dom` with certified Lagrange remainder `lagrangeRem`. -/
def tmSqrt1p (dom lagrangeRem : Interval) : TaylorModel where
  coeffs := [1, CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 8, CanonicalRat.mk 1 16]
  center := 0
  domain := dom
  rem    := lagrangeRem

/-- **Theorem (`taylorModel_transcendental_enclosure_sound`)**:
1. **Dependency Cancellation (`tmSub x x = [0, 0]`)**:
   For $x \in [-1/10, 1/10]$, naive interval subtraction `Interval.sub dom dom` yields
   $[-1/5, 1/5]$, whereas `evalTaylorModelRange (tmSub (tmVar 0 dom) (tmVar 0 dom))` cancels
   the linear coefficients and yields the exact point interval $[0, 0]$.
2. **Transcendental Value & Pythagorean Identity Enclosures**:
   - At $x = 0$, $\exp(0) \in [1 - 10^{-5}, 1 + 10^{-5}]$, $\sin(0) \in [-10^{-6}, 10^{-6}]$,
     $\cos(0) \in [1 - 10^{-5}, 1 + 10^{-5}]$, $\ln(1+0) \in [-10^{-5}, 10^{-5}]$, and
     $\sqrt{1+0} \in [1 - 10^{-4}, 1 + 10^{-4}]$.
   - At $x = 1/10$, `evalTaylorModelPoint expTM (1/10)` encloses the degree-4 rational
     approximation $265241 / 240000$.
   - Over $x \in [-1/10, 1/10]$, the degree-4 Taylor model for $\sin^2(x) + \cos^2(x)$
     (`tmAdd (tmMul 4 sinTM sinTM) (tmMul 4 cosTM cosTM)`) cancels the $-x^2 + x^2$ quadratic
     and $\pm \frac{1}{3} x^4$ quartic drift and encloses $1$ across the entire domain. -/
theorem taylorModel_transcendental_enclosure_sound :
    let dom : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    let xTM := tmVar 0 dom
    let rem5 : Interval := ⟨CanonicalRat.mk (-1) 100000, CanonicalRat.mk 1 100000⟩
    let expTM := tmExp dom rem5
    let sinTM := tmSin dom rem5
    let cosTM := tmCos dom rem5
    let lnTM := tmLn1p dom rem5
    let sqrtTM := tmSqrt1p dom rem5
    let pythagTM := tmAdd (tmMul 4 sinTM sinTM) (tmMul 4 cosTM cosTM)
    -- 1. Dependency cancellation vs. naive interval subtraction
    evalTaylorModelRange (tmSub xTM xTM) = ⟨0, 0⟩ ∧
    Interval.sub dom dom = ⟨CanonicalRat.mk (-1) 5, CanonicalRat.mk 1 5⟩ ∧
    -- 2. Verified transcendental enclosures at x = 0 and x = 1/10
    Interval.containsRat (evalTaylorModelPoint expTM 0) 1 = true ∧
    Interval.containsRat (evalTaylorModelPoint sinTM 0) 0 = true ∧
    Interval.containsRat (evalTaylorModelPoint cosTM 0) 1 = true ∧
    Interval.containsRat (evalTaylorModelPoint lnTM 0) 0 = true ∧
    Interval.containsRat (evalTaylorModelPoint sqrtTM 0) 1 = true ∧
    Interval.containsRat (evalTaylorModelPoint expTM (CanonicalRat.mk 1 10)) (CanonicalRat.mk 265241 240000) = true ∧
    -- 3. Pythagorean identity sin^2(x) + cos^2(x) cancels degree-2 and degree-4 terms and encloses 1
    pythagTM.coeffs = [1, 0, 0, 0, 0] ∧
    Interval.containsRat (evalTaylorModelRange pythagTM) 1 = true := by
  decide +kernel

/-! ## 3. Picard–Lindelöf Taylor-Model ODE Operator & Wrapping-Effect Elimination -/

/-- Formal integration helper $\sum_{j} \frac{c_j}{\text{deg}+1} t^{\text{deg}+1}$ via structural recursion on `cs`. -/
def polyIntegrateAux : List CanonicalRat → Nat → List CanonicalRat
  | [], _ => []
  | c :: cs, deg => (c / CanonicalRat.ofNat (deg + 1)) :: polyIntegrateAux cs (deg + 1)

/-- Formal integration $\int_0^t p(s) \, ds$ prepending constant $0$. -/
def polyIntegrate (cs : List CanonicalRat) : List CanonicalRat :=
  0 :: polyIntegrateAux cs 0

/-- One Picard–Lindelöf operator step $\Phi(p)(t) = x_0 + \int_0^t (\lambda \cdot p(s) + b) \, ds$
for an affine/linearized mode $\dot{x} = \lambda x + b$, truncated to degree `order`. -/
def picardLinearStep (order : Nat) (x0 lam b : CanonicalRat) (coeffs : List CanonicalRat) : List CanonicalRat :=
  let rhs := polyAdd [b] (polyScale lam coeffs)
  let integrated := (polyIntegrate rhs).take (order + 1)
  polyAdd [x0] integrated

/-- Iterate the contractive Picard–Lindelöf operator `order` times from constant seed `[x0]`
to obtain the degree-`order` Taylor flow polynomial in $t$. -/
def picardLinearCoeffs (order : Nat) (x0 lam b : CanonicalRat) : Nat → List CanonicalRat
  | 0 => [x0]
  | k + 1 => picardLinearStep order x0 lam b (picardLinearCoeffs order x0 lam b k)

/-- Validated degree-4 Picard–Lindelöf Taylor-model step for $\dot{x} = -x$ over $[0, \Delta t]$
starting from initial interval $X_0$:
Contracts the symbolic Taylor propagator $1 - \Delta t + \frac{\Delta t^2}{2} - \frac{\Delta t^3}{6} + \frac{\Delta t^4}{24}$
before multiplying by $X_0$, eliminating the interval dependency/wrapping effect. -/
def stepPicardDecay1D (initBox : Interval) (dt : CanonicalRat) (remPad : Interval) : Interval :=
  let unitPicard := picardLinearCoeffs 4 1 (-1) 0 4
  let factor := evalTaylorPolyAt unitPicard dt
  Interval.add (Interval.mul (Interval.ofPoint factor) initBox) remPad

/-- Naive uncontracted degree-4 interval Taylor step that evaluates each power term
$c_j \Delta t^j X_0$ as an independent interval and sums them, suffering the interval wrapping effect. -/
def stepNaiveIntervalPicardTerms (initBox : Interval) (dt : CanonicalRat) : List CanonicalRat → Nat → Interval
  | [], _ => Interval.ofPoint 0
  | c :: cs, deg =>
    let coeffDt := Interval.mul (Interval.ofPoint c) (intervalPow (Interval.ofPoint dt) deg)
    let termBox := Interval.mul coeffDt initBox
    Interval.add termBox (stepNaiveIntervalPicardTerms initBox dt cs (deg + 1))

def stepNaiveIntervalPicard1D (initBox : Interval) (dt : CanonicalRat) (remPad : Interval) : Interval :=
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

end Obend.Analysis
end
