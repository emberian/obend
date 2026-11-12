module
/-
# Obend.Hardware.Analog — Common-Centroid 1D/2D Gradient & Hessian Cancellation and Parametric $N$-Bit SAR ADC Verification

Formalizes mixed-signal silicon layout symmetry and charge-redistribution quantization laws:

1. **1D `ABBA` & 8-Cell Prouhet–Thue–Morse (`ABBABAAB`) Common-Centroid Cancellation**:
   - `commonCentroid_cancels_linear_gradient`, `aabb_suffers_linear_gradient_mismatch`,
   - `abba1D_quadratic_bow_residual` ($4 c_{xx} d^2$ residual on 4-cell `ABBA`),
   - `prouhetThueMorse_cancels_linear_and_quadratic_bow`: cancels both linear slope $g_x$ and
     parabolic curvature $c_{xx}$ identically to `0`.
2. **2D Planar Quad & 8-Cell $(\pm 1, \pm 3), (\pm 3, \pm 1)$ Octuple Hessian Cancellation**:
   - `commonCentroid2D_cancels_planar_gradient`, `crossCoupledQuad2D_cancels_gradients_and_axial_bow`,
   - `chiralityBalanced2D_cancels_full_hessian`: real 8-cell 2D octuple coordinates
     $A = \{(+1,+3), (-1,-3), (+3,-1), (-3,+1)\}$, $B = \{(+1,-3), (-1,+3), (+3,+1), (-3,-1)\}$
     on distinct silicon grid sites canceling $P_0$, $(g_x, g_y)$, axial bow $(c_{xx}, c_{yy})$,
     and mixed saddle twist $c_{xy} x y$ identically to `0`!
3. **Parametric $N$-Bit Successive Approximation Register (SAR) ADC**:
   - `sarBitTrial`, `runSarAdc4`, `runSarAdcN`, `runSarAdcN_exact_quantization_bounds`.
-/
@[expose] public section

namespace Obend.Hardware.Analog
set_option autoImplicit false

/-! ## 1. ABBA Common-Centroid Linear-Gradient Cancellation Theorem -/

/-- Spatially varying process parameter $P(x) = P_0 + g \cdot x$ across a 1D silicon layout axis
(modeling threshold voltage $V_{\text{th}}(x)$, oxide thickness $t_{\text{ox}}(x)$, or unit capacitance
$C_{\square}(x)$ with nominal value `p0` and linear gradient slope `gradPerUm`). -/
def evalLinearGradient (p0 gradPerUm x : Int) : Int :=
  p0 + gradPerUm * x

/-- Mismatch $\Delta P_{\text{ABBA}} = (P(x_0) + P(x_0 + 3d)) - (P(x_0 + d) + P(x_0 + 2d))$ of a
common-centroid `ABBA` differential layout where device $A = \{x_0, x_0 + 3d\}$ and
device $B = \{x_0 + d, x_0 + 2d\}$ share the common centroid $x_c = x_0 + 1.5 d$. -/
def abbaCentroidMismatch (p0 gradPerUm x0 pitch : Int) : Int :=
  let aTotal := evalLinearGradient p0 gradPerUm x0 + evalLinearGradient p0 gradPerUm (x0 + 3 * pitch)
  let bTotal := evalLinearGradient p0 gradPerUm (x0 + pitch) + evalLinearGradient p0 gradPerUm (x0 + 2 * pitch)
  aTotal - bTotal

/-- Mismatch $\Delta P_{\text{AABB}} = (P(x_0) + P(x_0 + d)) - (P(x_0 + 2d) + P(x_0 + 3d))$ of an
unmatched `AABB` layout where device $A = \{x_0, x_0 + d\}$ and device $B = \{x_0 + 2d, x_0 + 3d\}$. -/
def aabbUnmatchedMismatch (p0 gradPerUm x0 pitch : Int) : Int :=
  let aTotal := evalLinearGradient p0 gradPerUm x0 + evalLinearGradient p0 gradPerUm (x0 + pitch)
  let bTotal := evalLinearGradient p0 gradPerUm (x0 + 2 * pitch) + evalLinearGradient p0 gradPerUm (x0 + 3 * pitch)
  aTotal - bTotal

/-- Theorem (`commonCentroid_cancels_linear_gradient`):
For ANY base process parameter `p0 : Int`, ANY linear gradient slope `gradPerUm : Int`,
ANY placement origin `x0 : Int`, and ANY unit cell pitch `pitch : Int`, the `ABBA` common-centroid
layout cancels the first-order die gradient identically to zero! -/
theorem commonCentroid_cancels_linear_gradient
    (p0 gradPerUm x0 pitch : Int) :
    abbaCentroidMismatch p0 gradPerUm x0 pitch = 0 := by
  dsimp only [abbaCentroidMismatch, evalLinearGradient]
  grind

/-- Theorem (`aabb_suffers_linear_gradient_mismatch`):
In contrast, an unmatched `AABB` placement suffers a systematic mismatch equal to `-4 * (gradPerUm * pitch)`. -/
theorem aabb_suffers_linear_gradient_mismatch
    (p0 gradPerUm x0 pitch : Int) :
    aabbUnmatchedMismatch p0 gradPerUm x0 pitch = -4 * (gradPerUm * pitch) := by
  dsimp only [aabbUnmatchedMismatch, evalLinearGradient]
  grind

/-! ## 2. Mixed-Signal 4-Bit SAR ADC + Capacitive DAC Binary-Search Convergence Proof -/

/-- Evaluate one bit-trial step of a Successive Approximation Register (SAR) ADC with unit step `vLsbMv`:
Tries adding `bitWeight` (`8, 4, 2, 1`) to `currentCode`; if the capacitive DAC output
`(currentCode + bitWeight) * vLsbMv ≤ vInMv`, the comparator outputs `1` and keeps the bit;
otherwise the comparator outputs `0` and clears the bit. -/
def sarBitTrial (vInMv vLsbMv currentCode bitWeight : Nat) : Nat :=
  let trialCode := currentCode + bitWeight
  if trialCode * vLsbMv ≤ vInMv then
    trialCode
  else
    currentCode

/-- Execute the complete 4-cycle MSB-to-LSB binary search (`weights = [8, 4, 2, 1]`) of a 4-bit SAR ADC. -/
def runSarAdc4 (vInMv vLsbMv : Nat) : Nat :=
  let s3 := sarBitTrial vInMv vLsbMv 0  8
  let s2 := sarBitTrial vInMv vLsbMv s3 4
  let s1 := sarBitTrial vInMv vLsbMv s2 2
  let s0 := sarBitTrial vInMv vLsbMv s1 1
  s0

/-- Helper lemma: All 16 quantization codes `q ∈ [0, 15]` evaluate to `q` at offsets `{0, 50, 99} mV`. -/
theorem sarAdc4_all_bins_check :
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat).all
      (fun q =>
        decide (runSarAdc4 (q * 100) 100 = q ∧
                runSarAdc4 (q * 100 + 50) 100 = q ∧
                runSarAdc4 (q * 100 + 99) 100 = q)) = true :=
  rfl

/-- Theorem (`sarAdc4_exact_quantization`):
For every 4-bit quantization code $q \in [0, 15]$ (at standard 100 mV LSB step `vLsbMv = 100`
and mid-bin sample offset `offsetMv ∈ {0, 50, 99}`), the 4-cycle SAR ADC + capacitive DAC converges
to the exact digital code `q`. -/
theorem sarAdc4_exact_quantization :
    ∀ q ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat),
      runSarAdc4 (q * 100) 100 = q ∧
      runSarAdc4 (q * 100 + 50) 100 = q ∧
      runSarAdc4 (q * 100 + 99) 100 = q := by
  intro q hMem
  have hAll := sarAdc4_all_bins_check
  simp only [List.all_eq_true, decide_eq_true_eq] at hAll
  exact hAll q hMem

/-- 1-step invariant for `sarBitTrial`: if `currentCode + bitWeight ≤ maxCode` and
`currentCode * vLsbMv ≤ vInMv`, then `sarBitTrial` remains `≤ maxCode` and never overshoots `vInMv`. -/
theorem sarBitTrial_invariant
    (vInMv vLsbMv currentCode bitWeight maxCode : Nat)
    (hBound : currentCode + bitWeight ≤ maxCode)
    (hNoOver : currentCode * vLsbMv ≤ vInMv) :
    sarBitTrial vInMv vLsbMv currentCode bitWeight ≤ maxCode ∧
    (sarBitTrial vInMv vLsbMv currentCode bitWeight) * vLsbMv ≤ vInMv := by
  simp only [sarBitTrial]
  split
  · next h => exact ⟨hBound, h⟩
  · exact ⟨by omega, hNoOver⟩

/-- General symbolic theorem: For ANY `vLsbMv` and ANY analog input `vInMv`,
the 4-bit SAR ADC code `q = runSarAdc4 vInMv vLsbMv` satisfies:
1. $0 \le q \le 15$, and
2. The DAC output voltage never overshoots the input ($q \cdot V_{\text{LSB}} \le V_{\text{in}}$)! -/
theorem sarAdc4_no_overshoot (vInMv vLsbMv : Nat) :
    runSarAdc4 vInMv vLsbMv ≤ 15 ∧
    (runSarAdc4 vInMv vLsbMv) * vLsbMv ≤ vInMv := by
  unfold runSarAdc4
  have h0 : 0 * vLsbMv ≤ vInMv := by simp
  have h3 := sarBitTrial_invariant vInMv vLsbMv 0 8 8 (by omega) h0
  have h2 := sarBitTrial_invariant vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4 12
    (by have := h3.1; omega) h3.2
  have h1 := sarBitTrial_invariant vInMv vLsbMv
    (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4) 2 14
    (by have := h2.1; omega) h2.2
  exact sarBitTrial_invariant vInMv vLsbMv
    (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4) 2) 1 15
    (by have := h1.1; omega) h1.2

/-! ## 3. 2D Oxide Curvature ($\nabla^2 P$), Prouhet–Thue–Morse & 8-Cell Octuple Hessian Cancellation -/

/-- Full 2D second-order spatial process profile at unit-cell grid coordinates `(kx, ky)` with
unit-cell pitches `(px, py)` around the layout origin:
$$P(k_x p_x, k_y p_y) = P_0 + k_x (g_x p_x) + k_y (g_y p_y) + k_x^2 (c_{xx} p_x^2) + (k_x k_y) (c_{xy} p_x p_y) + k_y^2 (c_{yy} p_y^2)$$
where $(g_x, g_y)$ is the first-order wafer gradient vector and
$\nabla^2 P = \begin{pmatrix} 2 c_{xx} & c_{xy} \\ c_{xy} & 2 c_{yy} \end{pmatrix}$ is the 2D Hessian
oxide/threshold curvature tensor (parabolic bow $c_{xx}, c_{yy}$ and saddle twist $c_{xy}$). -/
def evalQuadratic2D (p0 gx gy cxx cxy cyy px py kx ky : Int) : Int :=
  p0 +
  kx * (gx * px) +
  ky * (gy * py) +
  (kx * kx) * (cxx * (px * px)) +
  (kx * ky) * (cxy * (px * py)) +
  (ky * ky) * (cyy * (py * py))

/-- 1D restriction of the second-order spatial profile at unit-cell grid index `k` and pitch `pitch`:
$P(k \cdot d) = P_0 + k (g_x d) + k^2 (c_{xx} d^2)$. -/
def evalQuadratic1D (p0 gx cxx pitch k : Int) : Int :=
  p0 + k * (gx * pitch) + (k * k) * (cxx * (pitch * pitch))

/-- 1D `ABBA` mismatch under a second-order quadratic oxide profile $P(k \cdot d)$,
with $A$ at $k \in \{0, 3\}$ and $B$ at $k \in \{1, 2\}$. -/
def abbaQuadraticMismatch1D (p0 gx cxx pitch : Int) : Int :=
  let aTotal := evalQuadratic1D p0 gx cxx pitch 0 + evalQuadratic1D p0 gx cxx pitch 3
  let bTotal := evalQuadratic1D p0 gx cxx pitch 1 + evalQuadratic1D p0 gx cxx pitch 2
  aTotal - bTotal

/-- Theorem (`abba1D_quadratic_bow_residual`):
While the 4-cell 1D `ABBA` common-centroid layout cancels $P_0$ and the linear gradient $g_x$
identically, under a non-zero parabolic curvature $c_{xx}$ it leaves an exact quantitative
second-order bow residual equal to $4 c_{xx} d^2$! -/
theorem abba1D_quadratic_bow_residual (p0 gx cxx pitch : Int) :
    abbaQuadraticMismatch1D p0 gx cxx pitch = 4 * (cxx * (pitch * pitch)) := by
  dsimp only [abbaQuadraticMismatch1D, evalQuadratic1D]
  grind

/-- 8-element **Prouhet–Thue–Morse (`ABBABAAB`)** 1D common-centroid layout under a second-order
quadratic profile:
* Device $A$ occupies the 4 even-popcount cells $k \in \{0, 3, 5, 6\}$,
* Device $B$ occupies the 4 odd-popcount cells $k \in \{1, 2, 4, 7\}$. -/
def prouhetThueMorseMismatch1D (p0 gx cxx pitch : Int) : Int :=
  let aTotal :=
    evalQuadratic1D p0 gx cxx pitch 0 +
    evalQuadratic1D p0 gx cxx pitch 3 +
    evalQuadratic1D p0 gx cxx pitch 5 +
    evalQuadratic1D p0 gx cxx pitch 6
  let bTotal :=
    evalQuadratic1D p0 gx cxx pitch 1 +
    evalQuadratic1D p0 gx cxx pitch 2 +
    evalQuadratic1D p0 gx cxx pitch 4 +
    evalQuadratic1D p0 gx cxx pitch 7
  aTotal - bTotal

/-- Theorem (`prouhetThueMorse_cancels_linear_and_quadratic_bow`):
For ANY nominal value `p0`, ANY linear gradient `gx`, ANY parabolic oxide curvature `cxx`, and
ANY unit cell pitch `pitch`, the 8-cell **Prouhet–Thue–Morse (`ABBABAAB`)** layout cancels BOTH
the first-order linear gradient ($0 + 3 + 5 + 6 = 1 + 2 + 4 + 7 = 14$) AND the second-order
quadratic curvature bow ($0^2 + 3^2 + 5^2 + 6^2 = 1^2 + 2^2 + 4^2 + 7^2 = 70$) identically to ZERO! -/
theorem prouhetThueMorse_cancels_linear_and_quadratic_bow (p0 gx cxx pitch : Int) :
    prouhetThueMorseMismatch1D p0 gx cxx pitch = 0 := by
  dsimp only [prouhetThueMorseMismatch1D, evalQuadratic1D]
  grind

/-- 2D Cross-Coupled Common-Centroid Quad (`[[A, B], [B, A]]`) placed at $(\pm d_x, \pm d_y)$:
* Device $A$ occupies $\{(-1, -1), (+1, +1)\}$,
* Device $B$ occupies $\{(-1, +1), (+1, -1)\}$. -/
def crossCoupledQuad2DMismatch (p0 gx gy cxx cxy cyy px py : Int) : Int :=
  let aTotal :=
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) (-1) +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 1
  let bTotal :=
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) 1 +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 (-1)
  aTotal - bTotal

/-- Theorem (`crossCoupledQuad2D_cancels_gradients_and_axial_bow`):
A 2D cross-coupled quad `[[A, B], [B, A]]` cancels the nominal offset $P_0$, both 2D linear
gradients $(g_x, g_y)$, AND both axial parabolic bow terms $(c_{xx}, c_{yy})$ identically to zero,
leaving only the mixed saddle twist residual $4 c_{xy} d_x d_y$! -/
theorem crossCoupledQuad2D_cancels_gradients_and_axial_bow
    (p0 gx gy cxx cxy cyy px py : Int) :
    crossCoupledQuad2DMismatch p0 gx gy cxx cxy cyy px py = 4 * (cxy * (px * py)) := by
  dsimp only [crossCoupledQuad2DMismatch, evalQuadratic2D]
  grind

/-- Explicit 2D grid coordinates `(kx, ky)` of Device $A$ in the 8-cell chirality-balanced octuple
array on the $(\pm 1, \pm 3), (\pm 3, \pm 1)$ ring:
$A = \{(+1, +3), (-1, -3), (+3, -1), (-3, +1)\}$. -/
def octuple2DCellsA : List (Int × Int) :=
  [(1, 3), (-1, -3), (3, -1), (-3, 1)]

/-- Explicit 2D grid coordinates `(kx, ky)` of Device $B$ in the 8-cell chirality-balanced octuple
array on the $(\pm 1, \pm 3), (\pm 3, \pm 1)$ ring:
$B = \{(+1, -3), (-1, +3), (+3, +1), (-3, -1)\}$. -/
def octuple2DCellsB : List (Int × Int) :=
  [(1, -3), (-1, 3), (3, 1), (-3, -1)]

/-- All 8 unit-cell coordinates in `octuple2DCellsA ++ octuple2DCellsB` are pairwise distinct
physical silicon sites (`Nodup`). -/
theorem octuple2DCells_nodup :
    (octuple2DCellsA ++ octuple2DCellsB).Nodup := by
  decide

/-- Real 8-cell 2D Octuple Common-Centroid Array mismatch evaluating `evalQuadratic2D` across the
8 distinct $(\pm 1, \pm 3), (\pm 3, \pm 1)$ unit-cell coordinates:
* Device $A$: $(+1, +3), (-1, -3), (+3, -1), (-3, +1)$ ($\sum k_x k_y = 3 + 3 - 3 - 3 = 0$),
* Device $B$: $(+1, -3), (-1, +3), (+3, +1), (-3, -1)$ ($\sum k_x k_y = -3 - 3 + 3 + 3 = 0$). -/
def chiralityBalanced2DMismatch (p0 gx gy cxx cxy cyy px py : Int) : Int :=
  let aTotal :=
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 3 +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) (-3) +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 3 (-1) +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-3) 1
  let bTotal :=
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 (-3) +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) 3 +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 3 1 +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-3) (-1)
  aTotal - bTotal

/-- Theorem (`chiralityBalanced2D_cancels_full_hessian`):
Evaluating `evalQuadratic2D` over the 8 distinct $(\pm 1, \pm 3), (\pm 3, \pm 1)$ octuple silicon
sites cancels the nominal offset $P_0$, both 2D first-order gradients $(g_x, g_y)$, both axial
parabolic bow terms $(c_{xx}, c_{yy})$ ($\sum k_x^2 = \sum k_y^2 = 20$ on both $A$ and $B$), AND
the mixed 2D saddle twist $c_{xy} x y$ ($\sum k_x k_y = 0$ on both $A$ and $B$) identically to zero! -/
theorem chiralityBalanced2D_cancels_full_hessian
    (p0 gx gy cxx cxy cyy px py : Int) :
    chiralityBalanced2DMismatch p0 gx gy cxx cxy cyy px py = 0 := by
  dsimp only [chiralityBalanced2DMismatch, evalQuadratic2D]
  grind

/-! ## 4. Parametric $N$-Bit Charge-Redistribution SAR ADC & 2D Planar Common-Centroid Array -/

/-- Parametric $N$-bit recursive Successive Approximation Register (SAR) ADC binary search:
Given remaining bit count `bits : Nat`, current binary search accumulator `accCode : Nat`,
analog input `vInMv : Nat`, and LSB step size `vLsbMv : Nat` (where $V_{\text{DAC}}(\text{code}) = \text{code} \cdot V_{\text{LSB}}$),
at step $b$ (from $N - 1$ down to $0$), tests trial code `trial = accCode + 2^b`:
if `trial * vLsbMv ≤ vInMv`, keeps `trial`, else keeps `accCode`. -/
def runSarAdcN : Nat → Nat → Nat → Nat → Nat
  | 0, accCode, _, _ => accCode
  | b + 1, accCode, vInMv, vLsbMv =>
    let nextAcc := sarBitTrial vInMv vLsbMv accCode (2 ^ b)
    runSarAdcN b nextAcc vInMv vLsbMv

/-- Top-level $N$-bit SAR ADC conversion starting from accumulator `accCode = 0`. -/
def evalSarAdcN (bits vInMv vLsbMv : Nat) : Nat :=
  runSarAdcN bits 0 vInMv vLsbMv

/-- Theorem (`runSarAdcN_eq_runSarAdc4`):
At $N = 4$ and initial accumulator `accCode = 0`, the parametric recursive `runSarAdcN` reduces
definitionally to the 4-cycle unrolled `runSarAdc4` for all `vInMv` and `vLsbMv`. -/
theorem runSarAdcN_eq_runSarAdc4 (vInMv vLsbMv : Nat) :
    runSarAdcN 4 0 vInMv vLsbMv = runSarAdc4 vInMv vLsbMv :=
  rfl

/-- Theorem (`runSarAdcN_matches_runSarAdc4`):
At $N = 4$ and $V_{\text{LSB}} = 100\,\text{mV}$, `runSarAdcN 4 0` agrees identically with `runSarAdc4`
for every input `vInMv` and quantizes all 16 bins $q \in [0, 15]$ at offsets $\{0, 50, 99\}\,\text{mV}$
to the exact digital code `q`. -/
theorem runSarAdcN_matches_runSarAdc4 :
    (∀ vInMv vLsbMv : Nat, runSarAdcN 4 0 vInMv vLsbMv = runSarAdc4 vInMv vLsbMv) ∧
    (∀ q ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat),
      runSarAdcN 4 0 (q * 100) 100 = runSarAdc4 (q * 100) 100 ∧
      runSarAdcN 4 0 (q * 100) 100 = q ∧
      runSarAdcN 4 0 (q * 100 + 50) 100 = q ∧
      runSarAdcN 4 0 (q * 100 + 99) 100 = q) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro q hMem
  have h4 := sarAdc4_exact_quantization q hMem
  exact ⟨rfl, h4.1, h4.2.1, h4.2.2⟩

/-- Inductive accumulator invariant for `runSarAdcN`: if `accCode * vLsbMv ≤ vInMv`, then after
`bits` successive binary-search trials, `(runSarAdcN bits accCode vInMv vLsbMv) * vLsbMv ≤ vInMv`
and the output code is bounded above by `accCode + 2^bits - 1`. -/
theorem runSarAdcN_acc_invariant
    (bits accCode vInMv vLsbMv : Nat)
    (hAcc : accCode * vLsbMv ≤ vInMv) :
    (runSarAdcN bits accCode vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    accCode ≤ runSarAdcN bits accCode vInMv vLsbMv ∧
    runSarAdcN bits accCode vInMv vLsbMv + 1 ≤ accCode + 2 ^ bits := by
  induction bits generalizing accCode with
  | zero =>
    dsimp only [runSarAdcN]
    have hPow : 2 ^ 0 = 1 := rfl
    exact ⟨hAcc, Nat.le_refl accCode, by omega⟩
  | succ b ih =>
    dsimp only [runSarAdcN]
    have hStep := sarBitTrial_invariant vInMv vLsbMv accCode (2 ^ b) (accCode + 2 ^ b) (Nat.le_refl _) hAcc
    have hSub := ih (sarBitTrial vInMv vLsbMv accCode (2 ^ b)) hStep.2
    have hGeAcc : accCode ≤ sarBitTrial vInMv vLsbMv accCode (2 ^ b) := by
      dsimp only [sarBitTrial]
      split <;> omega
    have hPowSucc : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by
      rw [Nat.pow_succ]
      omega
    refine ⟨hSub.1, by omega, ?_⟩
    have hBound := hStep.1
    have hUpper := hSub.2.2
    omega

/-- Theorem (`runSarAdcN_lower_bound`):
For any bit resolution `bits : Nat`, analog input `vInMv : Nat`, and positive LSB step `0 < vLsbMv`,
the quantized SAR ADC output code `code = runSarAdcN bits 0 vInMv vLsbMv` never overshoots the
analog input (`code * vLsbMv ≤ vInMv`) and lies strictly within the $N$-bit range `[0, 2^bits)`. -/
theorem runSarAdcN_lower_bound
    (bits vInMv vLsbMv : Nat)
    (_hPos : 0 < vLsbMv) :
    (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits := by
  have h0 : 0 * vLsbMv ≤ vInMv := by simp
  have hInv := runSarAdcN_acc_invariant bits 0 vInMv vLsbMv h0
  exact ⟨hInv.1, by omega⟩

/-- Inductive upper quantization-bin invariant for `runSarAdcN`:
Whenever `vInMv < (accCode + 2^bits) * vLsbMv`, the binary search maintains
`vInMv < (runSarAdcN bits accCode vInMv vLsbMv + 1) * vLsbMv`, bounding quantization error
strictly within $1\,\text{LSB}$ (`vLsbMv`). -/
theorem runSarAdcN_acc_upper_bound
    (bits accCode vInMv vLsbMv : Nat)
    (hUpper : vInMv < (accCode + 2 ^ bits) * vLsbMv) :
    vInMv < (runSarAdcN bits accCode vInMv vLsbMv + 1) * vLsbMv := by
  induction bits generalizing accCode with
  | zero =>
    dsimp only [runSarAdcN]
    have hPow : 2 ^ 0 = 1 := rfl
    rw [hPow] at hUpper
    exact hUpper
  | succ b ih =>
    dsimp only [runSarAdcN, sarBitTrial]
    have hPowSucc : accCode + 2 ^ b + 2 ^ b = accCode + 2 ^ (b + 1) := by
      rw [Nat.pow_succ]
      omega
    split
    · apply ih (accCode + 2 ^ b)
      rw [hPowSucc]
      exact hUpper
    · next hNotLe =>
      apply ih accCode
      omega

/-- Theorem (`runSarAdcN_exact_quantization_bounds`):
For any resolution `bits : Nat`, analog input `vInMv : Nat`, and positive step `0 < vLsbMv`,
`code = runSarAdcN bits 0 vInMv vLsbMv` satisfies both the lower DAC bound `code * vLsbMv ≤ vInMv`
and, whenever `vInMv < 2^bits * vLsbMv` (non-saturating range), the tight upper bin bound
`vInMv < (code + 1) * vLsbMv` ($0\,\text{LSB}$ ideal DNL). -/
theorem runSarAdcN_exact_quantization_bounds
    (bits vInMv vLsbMv : Nat)
    (hPos : 0 < vLsbMv) :
    (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits ∧
    (vInMv < 2 ^ bits * vLsbMv →
      vInMv < (runSarAdcN bits 0 vInMv vLsbMv + 1) * vLsbMv) := by
  have hLow := runSarAdcN_lower_bound bits vInMv vLsbMv hPos
  refine ⟨hLow.1, hLow.2, ?_⟩
  intro hInRange
  have hZeroAdd : 0 + 2 ^ bits = 2 ^ bits := Nat.zero_add (2 ^ bits)
  apply runSarAdcN_acc_upper_bound bits 0 vInMv vLsbMv
  rw [hZeroAdd]
  exact hInRange

/-- 2D planar linear process profile $P(x, y) = P_0 + g_x \cdot x + g_y \cdot y$ across a silicon die
(modeling MIM unit capacitance $C_{\square}(x, y)$ or threshold voltage $V_{\text{th}}(x, y)$). -/
def evalPlanarGradient2D (p0 gx gy x y : Int) : Int :=
  p0 + gx * x + gy * y

/-- 2D Planar Common-Centroid Capacitor Array mismatch (`eval2DCommonCentroidMismatch`) for a
cross-coupled $2 \times 2$ quad `[[A, B], [B, A]]` at arbitrary die origin `(x0, y0)` with cell
pitches `(dx, dy)`:
* Capacitor $A$ sums unit cells at `(x0, y0)` and `(x0 + dx, y0 + dy)`,
* Capacitor $B$ sums unit cells at `(x0 + dx, y0)` and `(x0, y0 + dy)`. -/
def eval2DCommonCentroidMismatch (p0 gx gy x0 y0 dx dy : Int) : Int :=
  let capA :=
    evalPlanarGradient2D p0 gx gy x0 y0 +
    evalPlanarGradient2D p0 gx gy (x0 + dx) (y0 + dy)
  let capB :=
    evalPlanarGradient2D p0 gx gy (x0 + dx) y0 +
    evalPlanarGradient2D p0 gx gy x0 (y0 + dy)
  capA - capB

/-- Unmatched 2D Side-by-Side Capacitor Array mismatch (`[[A, A], [B, B]]` split along the $y$-axis):
* Capacitor $A$ occupies `(x0, y0)` and `(x0 + dx, y0)`,
* Capacitor $B$ occupies `(x0, y0 + dy)` and `(x0 + dx, y0 + dy)`. -/
def eval2DUnmatchedMismatch (p0 gx gy x0 y0 dx dy : Int) : Int :=
  let capA :=
    evalPlanarGradient2D p0 gx gy x0 y0 +
    evalPlanarGradient2D p0 gx gy (x0 + dx) y0
  let capB :=
    evalPlanarGradient2D p0 gx gy x0 (y0 + dy) +
    evalPlanarGradient2D p0 gx gy (x0 + dx) (y0 + dy)
  capA - capB

/-- Theorem (`commonCentroid2D_cancels_planar_gradient`):
For ANY nominal process parameter `p0 : Int`, ANY 2D planar wafer gradient slopes `gx gy : Int`,
ANY placement origin `x0 y0 : Int`, and ANY unit cell pitches `dx dy : Int`, the 2D common-centroid
capacitor array cancels both $x$-axis and $y$-axis linear die gradients identically to `0`! -/
theorem commonCentroid2D_cancels_planar_gradient
    (p0 gx gy x0 y0 dx dy : Int) :
    eval2DCommonCentroidMismatch p0 gx gy x0 y0 dx dy = 0 := by
  dsimp only [eval2DCommonCentroidMismatch, evalPlanarGradient2D]
  grind

/-- Theorem (`unmatched2D_suffers_planar_gradient`):
In contrast, an unmatched side-by-side 2D capacitor array `[[A, A], [B, B]]` suffers a systematic
$y$-axis gradient mismatch equal to `-2 * (gy * dy)`. -/
theorem unmatched2D_suffers_planar_gradient
    (p0 gx gy x0 y0 dx dy : Int) :
    eval2DUnmatchedMismatch p0 gx gy x0 y0 dx dy = -2 * (gy * dy) := by
  dsimp only [eval2DUnmatchedMismatch, evalPlanarGradient2D]
  grind

end Obend.Hardware.Analog
end
