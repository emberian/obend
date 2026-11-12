module
/-
# Obend.Hardware.Photonics — Coherent Gaussian-Integer ($\mathbb{Z}[i]$) $2 \times 2$ Optical Transfer Matrices, Cascaded MZIs & Two-Boson Hong–Ou–Mandel Interference

Formalizes coherent complex optical field transfer matrices over $\mathbb{Z}[i]$:

1. **Complex Gaussian-Integer ($\mathbb{Z}[i]$) Optical Field Phasors & $2 \times 2$ Unitary Directional Coupler**:
   - `ComplexField`, `complexField_normSq_nonneg`, `brahmagupta_cancel`,
   - `evalDirectionalCoupler2x2`, `directional_coupler_2x2_power_conservation`:
     $|E_{\text{out},1}|^2 + |E_{\text{out},2}|^2 = (t^2 + \kappa^2)(|E_1|^2 + |E_2|^2)$.
2. **Cascaded $2 \times 2$ Complex Mach–Zehnder Interferometer (MZI) Transfer Matrix**:
   - `evalPhaseShifter2x2`, `evalCascadedMzi2x2`,
   - `cascaded_mzi_zero_phase_pure_cross` ($\Delta\phi = 0 \implies \text{bar} = 0$),
   - `cascaded_mzi_pi_phase_pure_bar` ($\Delta\phi = \pi \implies \text{cross} = 0$).
3. **Thermo-Optic Crosstalk Pre-Distortion & 2-Boson Hong–Ou–Mandel Photonics Exports (`Obend.Analysis`)**.
-/
public import Obend.Analysis.Equitable
@[expose] public section

namespace Obend.Hardware.Photonics
open Obend.Analysis
set_option autoImplicit false

private theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have hNeg : 0 ≤ -a := by omega
    have hProd := Int.mul_nonneg hNeg hNeg
    grind

/-! ## 1. Complex Gaussian-Integer ($\mathbb{Z}[i]$) Optical Field Phasors & $2 \times 2$ Unitary Directional Coupler -/

/-- Exact Gaussian-integer ($\mathbb{Z}[i]$) complex optical electric field phasor $E = E_{\text{re}} + i E_{\text{im}}$:
* `re`: in-phase ($I$) optical field amplitude component,
* `im`: quadrature ($Q$) optical field amplitude component. -/
structure ComplexField where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace ComplexField

/-- Zero optical electric field phasor $0 + 0i$. -/
def zero : ComplexField := ⟨0, 0⟩

/-- Coherent superposition (complex addition) of two optical field phasors. -/
def add (z w : ComplexField) : ComplexField :=
  ⟨z.re + w.re, z.im + w.im⟩

/-- Coherent subtraction of two optical field phasors. -/
def sub (z w : ComplexField) : ComplexField :=
  ⟨z.re - w.re, z.im - w.im⟩

/-- Complex multiplication $(a + ib)(c + id) = (ac - bd) + i(ad + bc)$ of two optical phasors. -/
def mul (z w : ComplexField) : ComplexField :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- Real scalar field attenuation or gain $c \cdot (E_{\text{re}} + i E_{\text{im}})$. -/
def scale (c : Int) (z : ComplexField) : ComplexField :=
  ⟨c * z.re, c * z.im⟩

/-- Quarter-wave ($+\pi/2$ radian, factor of $i$) optical phase rotation $i \cdot (E_{\text{re}} + i E_{\text{im}}) = -E_{\text{im}} + i E_{\text{re}}$. -/
def mulI (z : ComplexField) : ComplexField :=
  ⟨-z.im, z.re⟩

/-- Optical intensity / power $|E|^2 = E_{\text{re}}^2 + E_{\text{im}}^2$ of a complex field phasor. -/
def normSq (z : ComplexField) : Int :=
  z.re * z.re + z.im * z.im

end ComplexField

/-- Theorem (`complexField_normSq_nonneg`):
Optical power $|E|^2 = \text{re}^2 + \text{im}^2$ is universally non-negative for all `z : ComplexField`. -/
theorem complexField_normSq_nonneg (z : ComplexField) :
    0 ≤ z.normSq := by
  dsimp only [ComplexField.normSq]
  have hRe : 0 ≤ z.re * z.re := int_sq_nonneg z.re
  have hIm : 0 ≤ z.im * z.im := int_sq_nonneg z.im
  omega

/-- Helper algebraic identities on `Int` for ring normalization without external algebra tactics. -/
theorem int_one_mul (a : Int) : 1 * a = a := by omega

theorem int_neg_one_mul (a : Int) : (-1) * a = -a := by omega

theorem int_neg_neg (a : Int) : -(-a) = a := by omega

theorem int_add_neg_self (a : Int) : a + (-a) = 0 := by omega

theorem int_neg_add_self (a : Int) : (-a) + a = 0 := by omega

theorem int_neg_mul_left (a b : Int) : (-a) * b = -(a * b) := by
  grind

theorem int_mul_neg_right (a b : Int) : a * (-b) = -(a * b) := by
  grind

/-- Four-factor integer multiplication swap $(p q)(r s) = (p r)(q s)$. -/
theorem int_mul_four_swap (p q r s : Int) :
    (p * q) * (r * s) = (p * r) * (q * s) := by
  grind

/-- **Brahmagupta–Fibonacci Two-Square Identity** (`brahmagupta_cancel`):
$$(t a - k b)^2 + (k a + t b)^2 = (t^2 + k^2)(a^2 + b^2),$$
where the opposite-sign evanescent cross-interference terms $-2 t k a b$ and $+2 t k a b$
cancel identically across all `t, k, a, b : Int`. -/
theorem brahmagupta_cancel (t k a b : Int) :
    (t * a - k * b) * (t * a - k * b) + (k * a + t * b) * (k * a + t * b) =
      (t * t + k * k) * (a * a + b * b) := by
  grind

/-- Coherent $2 \times 2$ evanescent directional coupler transfer matrix over $\mathbb{Z}[i]$:
$$\begin{pmatrix} E_{\text{out},1} \\ E_{\text{out},2} \end{pmatrix}
  = \begin{pmatrix} t & i \kappa \\ i \kappa & t \end{pmatrix}
    \begin{pmatrix} E_1 \\ E_2 \end{pmatrix}
  = \begin{pmatrix} t E_1 + i \kappa E_2 \\ i \kappa E_1 + t E_2 \end{pmatrix}.$$ -/
def evalDirectionalCoupler2x2
    (t kappa : Int) (e1 e2 : ComplexField) : ComplexField × ComplexField :=
  let out1 : ComplexField := ⟨t * e1.re - kappa * e2.im, t * e1.im + kappa * e2.re⟩
  let out2 : ComplexField := ⟨-kappa * e1.im + t * e2.re, kappa * e1.re + t * e2.im⟩
  (out1, out2)

/-- Theorem (`directional_coupler_2x2_power_conservation`):
For ALL straight-through and cross-coupling field coefficients `t, kappa : Int` and ALL complex
input optical field phasors `e1, e2 : ComplexField` (arbitrary relative phase and amplitude), the
$2 \times 2$ directional coupler transfer matrix $\begin{pmatrix} t & i\kappa \\ i\kappa & t \end{pmatrix}$
strictly conserves total optical power up to the unitary scale factor $t^2 + \kappa^2$:
$$|E_{\text{out},1}|^2 + |E_{\text{out},2}|^2 = (t^2 + \kappa^2)\left(|E_1|^2 + |E_2|^2\right).$$ -/
theorem directional_coupler_2x2_power_conservation
    (t kappa : Int) (e1 e2 : ComplexField) :
    let (out1, out2) := evalDirectionalCoupler2x2 t kappa e1 e2
    out1.normSq + out2.normSq = (t * t + kappa * kappa) * (e1.normSq + e2.normSq) := by
  dsimp only [evalDirectionalCoupler2x2, ComplexField.normSq]
  grind

/-! ## 2. Cascaded $2 \times 2$ Complex MZI Transfer Matrix -/

/-- Upper-arm optical phase shifter transfer matrix $\begin{pmatrix} e^{i\Delta\phi} & 0 \\ 0 & 1 \end{pmatrix}$
represented by a complex phase phasor `phasePhasor : ComplexField` ($1 + 0i$ for $\Delta\phi = 0$,
$-1 + 0i$ for $\Delta\phi = \pi$, $0 + 1i$ for $\Delta\phi = \pi/2$). -/
def evalPhaseShifter2x2
    (phasePhasor : ComplexField) (e1 e2 : ComplexField) : ComplexField × ComplexField :=
  (ComplexField.mul phasePhasor e1, e2)

/-- Complete cascaded $2 \times 2$ Mach–Zehnder Interferometer (MZI) complex field transfer matrix
$$T_{\text{MZI}} = U_{\text{DC}}(t, \kappa) \cdot \Phi(\Delta\phi) \cdot U_{\text{DC}}(t, \kappa)$$
formed by composing the input $2 \times 2$ directional coupler, the upper-arm thermo-optic phase
shifter `phasePhasor`, and the output $2 \times 2$ directional coupler. -/
def evalCascadedMzi2x2
    (t kappa : Int) (phasePhasor : ComplexField) (eIn1 eIn2 : ComplexField) :
    ComplexField × ComplexField :=
  let (m1, m2) := evalDirectionalCoupler2x2 t kappa eIn1 eIn2
  let (p1, p2) := evalPhaseShifter2x2 phasePhasor m1 m2
  evalDirectionalCoupler2x2 t kappa p1 p2

/-- Theorem (`cascaded_mzi_zero_phase_pure_cross`):
For ANY symmetric 50:50 directional coupler (`t = kappa`) and ANY complex input optical field
`eIn : ComplexField` injected into Port 1 (`eIn2 = ⟨0, 0⟩`), when the phase shifter is unshifted
($\Delta\phi = 0$, `phasePhasor = ⟨1, 0⟩`), the two cascaded $i\kappa$ cross-couplings interfere
destructively at the bar port (`out1 = ⟨0, 0⟩`), routing 100% of the optical field to the cross port! -/
theorem cascaded_mzi_zero_phase_pure_cross
    (t : Int) (eIn : ComplexField) :
    (evalCascadedMzi2x2 t t ⟨1, 0⟩ eIn ⟨0, 0⟩).1 = ⟨0, 0⟩ := by
  cases eIn
  simp only [evalCascadedMzi2x2, evalDirectionalCoupler2x2, evalPhaseShifter2x2,
    ComplexField.mul, ComplexField.mk.injEq]
  constructor <;> grind

/-- Theorem (`cascaded_mzi_pi_phase_pure_bar`):
For ANY symmetric 50:50 directional coupler (`t = kappa`) and ANY complex input optical field
`eIn : ComplexField` injected into Port 1 (`eIn2 = ⟨0, 0⟩`), when the upper-arm phase shifter induces
a half-wave shift ($\Delta\phi = \pi$, `phasePhasor = ⟨-1, 0⟩`), destructive interference completely
extinguishes the cross port (`out2 = ⟨0, 0⟩`), routing 100% of the optical field to the bar port! -/
theorem cascaded_mzi_pi_phase_pure_bar
    (t : Int) (eIn : ComplexField) :
    (evalCascadedMzi2x2 t t ⟨-1, 0⟩ eIn ⟨0, 0⟩).2 = ⟨0, 0⟩ := by
  cases eIn
  simp only [evalCascadedMzi2x2, evalDirectionalCoupler2x2, evalPhaseShifter2x2,
    ComplexField.mul, ComplexField.mk.injEq]
  constructor <;> grind

/-! ## 3. Thermo-Optic Crosstalk Pre-Distortion & 2-Boson Hong–Ou–Mandel Photonics Exports -/

export Obend.Analysis (
  faddeevAdjugateAndDet
  ThermoOpticPhaseShifter
  compensateThermalCrosstalk
  goldenThermalCrosstalk4x4
  faddeevAdjugate_cancels_crosstalk_4x4
  compensateThermalCrosstalk_exact_4x4
  twoBosonPermanent
  beamSplitter5050
  hong_ou_mandel_bunching_exact
  twoBosonPermanent_bose_symmetry
  twoBosonHamiltonian
  twoBosonPart
  twoBosonQuotient
  twoBoson_equitable_intertwining_poly
)

end Obend.Hardware.Photonics
end
