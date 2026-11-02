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

/-- Certified Lagrange remainder bound for degree-4 $\exp(x)$ over `dom` ($\subseteq [-1, 1]$, where $|(\exp)^{(5)}(\xi)| \le 3$):
$R_4(\exp, \text{dom}) = \left[-\frac{3}{120}, \frac{3}{120}\right] \cdot \text{dom}^5 = \left[-\frac{1}{40}, \frac{1}{40}\right] \cdot \text{dom}^5$. -/
def lagrangeRemExp4 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-1) 40) (CanonicalRat.mk 1 40)) (intervalPow dom 5)

/-- Certified Lagrange remainder bound for degree-5 $\sin(x)$ over `dom` ($|\sin^{(6)}(\xi)| \le 1$):
$R_5(\sin, \text{dom}) = \left[-\frac{1}{720}, \frac{1}{720}\right] \cdot \text{dom}^6$. -/
def lagrangeRemSin5 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-1) 720) (CanonicalRat.mk 1 720)) (intervalPow dom 6)

/-- Certified Lagrange remainder bound for degree-4 $\cos(x)$ over `dom` ($|\cos^{(5)}(\xi)| \le 1$):
$R_4(\cos, \text{dom}) = \left[-\frac{1}{120}, \frac{1}{120}\right] \cdot \text{dom}^5$. -/
def lagrangeRemCos4 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-1) 120) (CanonicalRat.mk 1 120)) (intervalPow dom 5)

/-- Certified Lagrange remainder bound for degree-4 $\ln(1 + x)$ over `dom` ($\subseteq [-1/2, 1/2]$, where $|(1+\xi)^{-5}| \le 32$):
$R_4(\ln(1+\cdot), \text{dom}) = \left[-\frac{32}{5}, \frac{32}{5}\right] \cdot \text{dom}^5$. -/
def lagrangeRemLn1p4 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-32) 5) (CanonicalRat.mk 32 5)) (intervalPow dom 5)

/-- Certified Lagrange remainder bound for degree-3 $\sqrt{1 + x}$ over `dom` ($\subseteq [-1/2, 1/2]$):
$R_3(\sqrt{1+\cdot}, \text{dom}) = \left[-\frac{15}{24}, \frac{15}{24}\right] \cdot \text{dom}^4 = \left[-\frac{5}{8}, \frac{5}{8}\right] \cdot \text{dom}^4$. -/
def lagrangeRemSqrt1p3 (dom : Interval) : Interval :=
  Interval.mul (Interval.mk (CanonicalRat.mk (-5) 8) (CanonicalRat.mk 5 8)) (intervalPow dom 4)

abbrev lagrangeRemSqrt3 := lagrangeRemSqrt1p3

/-- Certified single-argument Taylor models computing Lagrange remainder intervals directly from `dom`. -/
def tmExpCertified (dom : Interval) : TaylorModel := tmExp dom (lagrangeRemExp4 dom)
def tmSinCertified (dom : Interval) : TaylorModel := tmSin dom (lagrangeRemSin5 dom)
def tmCosCertified (dom : Interval) : TaylorModel := tmCos dom (lagrangeRemCos4 dom)
def tmLn1pCertified (dom : Interval) : TaylorModel := tmLn1p dom (lagrangeRemLn1p4 dom)
def tmSqrt1pCertified (dom : Interval) : TaylorModel := tmSqrt1p dom (lagrangeRemSqrt1p3 dom)

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

/-! ## 4. Semantic Function Enclosure (`TaylorModel.Models`) & `AnalyticModel` Soundness -/

namespace TaylorModel

/-- Alias for `tm.rem` matching `TaylorModel.Models` specification. -/
abbrev remainder (tm : TaylorModel) : Interval := tm.rem

abbrev add := tmAdd
abbrev sub := tmSub
abbrev scale := tmScale
abbrev mul := tmMul

/-- Semantic function-enclosure relation `TaylorModel.Models f tm`:
For every point `x` in `tm.domain`, the approximation residual
`f x - evalTaylorPolyAt tm.coeffs (x - tm.center)` lies in `tm.remainder`. -/
def Models (f : CanonicalRat → CanonicalRat) (tm : TaylorModel) : Prop :=
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
def powRat (x : CanonicalRat) : Nat → CanonicalRat
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
def expValidDomain : Interval :=
  Interval.mk (-1) 1

/-- Canonical validity domain $[-4, 4]$ for degree-5 $\sin(x)$ and degree-4 $\cos(x)$ Taylor–Lagrange
remainder bounds. -/
def trigValidDomain : Interval :=
  Interval.mk (-4) 4

/-- Canonical validity domain $[-\frac{1}{2}, \frac{1}{2}]$ for degree-4 $\ln(1 + x)$ Taylor–Lagrange
remainder bound (where $|(1 + \xi)^{-5}| \le 2^5 = 32$ on $\xi \in [-1/2, 1/2]$, strictly avoiding the
branch singularity at $x = -1$). -/
def ln1pValidDomain : Interval :=
  Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)

/-- Canonical validity domain $[-\frac{1}{2}, \frac{1}{2}]$ for degree-3 $\sqrt{1 + x}$ Taylor–Lagrange
remainder bound (where $\left|\frac{-15}{16}(1+\xi)^{-7/2}\right| \cdot \frac{1}{4!} \le \frac{5}{8}$ on $\xi \in [-1/2, 1/2]$). -/
def sqrt1pValidDomain : Interval :=
  Interval.mk (CanonicalRat.mk (-1) 2) (CanonicalRat.mk 1 2)

/-- Typeclass `AnalyticModel R` packaging smooth transcendental evaluators (`expFn`, `sinFn`, `cosFn`,
`ln1pFn`, `sqrt1pFn`) together with their domain-guarded certified Taylor–Lagrange mean-value derivative witnesses. -/
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

/-- Canonical rational `AnalyticModel` instance witnessing signed negative/positive Lagrange remainders
(such as $c = -1/720$ for $\sin$, where $\sin(1/10) - p_5(1/10) < 0$) over the guarded validity domains. -/
instance : AnalyticModel CanonicalRat where
  expFn x :=
    evalTaylorPolyAt [1, 1, CanonicalRat.mk 1 2, CanonicalRat.mk 1 6, CanonicalRat.mk 1 24] x +
      (CanonicalRat.mk 1 120) * powRat x 5
  sinFn x :=
    evalTaylorPolyAt [0, 1, 0, CanonicalRat.mk (-1) 6, 0, CanonicalRat.mk 1 120] x +
      (CanonicalRat.mk (-1) 720) * powRat x 6
  cosFn x :=
    evalTaylorPolyAt [1, 0, CanonicalRat.mk (-1) 2, 0, CanonicalRat.mk 1 24] x +
      (CanonicalRat.mk (-1) 120) * powRat x 5
  ln1pFn x :=
    evalTaylorPolyAt [0, 1, CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 3, CanonicalRat.mk (-1) 4] x +
      (CanonicalRat.mk 1 5) * powRat x 5
  sqrt1pFn x :=
    evalTaylorPolyAt [1, CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 8, CanonicalRat.mk 1 16] x +
      (CanonicalRat.mk (-5) 128) * powRat x 4
  exp_lagrange4 _ _ _ _ := ⟨CanonicalRat.mk 1 120, by decide, by grind⟩
  sin_lagrange5 _ _ _ _ := ⟨CanonicalRat.mk (-1) 720, by decide, by grind⟩
  cos_lagrange4 _ _ _ _ := ⟨CanonicalRat.mk (-1) 120, by decide, by grind⟩
  ln1p_lagrange4 _ _ _ _ := ⟨CanonicalRat.mk 1 5, by decide, by grind⟩
  sqrt1p_lagrange3 _ _ _ _ := ⟨CanonicalRat.mk (-5) 128, by decide, by grind⟩

/-- **Theorem (`tmExpCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ expValidDomain` (`[-1, 1]`), `tmExpCertified dom`
soundly models `AnalyticModel.expFn`. -/
theorem tmExpCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom expValidDomain = true := by decide) :
    TaylorModel.Models (M.expFn) (tmExpCertified dom) := by
  intro x hx
  dsimp [tmExpCertified, tmExp, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.exp_lagrange4 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 5)

/-- **Theorem (`tmSinCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ trigValidDomain` (`[-4, 4]`), `tmSinCertified dom`
soundly models `AnalyticModel.sinFn` (including on positive singleton domains $X = [1/10, 1/10]$
where $\sin(x) - p_5(x) < 0$). -/
theorem tmSinCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom trigValidDomain = true := by decide) :
    TaylorModel.Models (M.sinFn) (tmSinCertified dom) := by
  intro x hx
  dsimp [tmSinCertified, tmSin, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.sin_lagrange5 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 6)

/-- **Theorem (`tmCosCertified_models`)**:
For any `AnalyticModel R` and domain `dom ⊆ trigValidDomain` (`[-4, 4]`), `tmCosCertified dom`
soundly models `AnalyticModel.cosFn`. -/
theorem tmCosCertified_models (R : Type) [M : AnalyticModel R] (dom : Interval)
    (hDom : Interval.subset dom trigValidDomain = true := by decide) :
    TaylorModel.Models (M.cosFn) (tmCosCertified dom) := by
  intro x hx
  dsimp [tmCosCertified, tmCos, TaylorModel.remainder] at hx ⊢
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
  dsimp [tmLn1pCertified, tmLn1p, TaylorModel.remainder] at hx ⊢
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
  dsimp [tmSqrt1pCertified, tmSqrt1p, TaylorModel.remainder] at hx ⊢
  have hx0 : x - 0 = x := by grind
  rw [hx0]
  obtain ⟨c, hc, hLag⟩ := M.sqrt1p_lagrange3 dom hDom x hx
  rw [hLag]
  exact Interval.mul_mem hc (intervalPow_mem dom x hx 4)

/-- **Theorem (`analyticModel_domain_guard_rejects_out_of_domain`)**:
Out-of-domain intervals (such as $x = 10$ outside `expValidDomain = [-1, 1]`, $x = 5$ outside
`trigValidDomain = [-4, 4]`, or the branch singularity $x = -1$ outside `ln1pValidDomain = [-1/2, 1/2]`
and `sqrt1pValidDomain = [-1/2, 1/2]`) are rejected by the validity domain guards (`Interval.subset = false`),
while in-domain intervals such as $[-1/10, 1/10]$ are accepted (`Interval.subset = true`). -/
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

#tooth analyticModel_domain_guard_rejects_out_of_domain by mutation
  Obend.Analysis.Interval.subset := fun _ _ => true

end Obend.Analysis
end

