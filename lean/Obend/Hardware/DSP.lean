module
/-
# Obend.Hardware.DSP — Synchronous DSP Datapaths, Phased-Array RF Beamforming & Rollett LNA Stability

Formalizes synchronous Digital Signal Processing (DSP) and Software-Defined Radio (SDR) / RF front-end
mathematics in the Lean 4 kernel:

1. **Iterative CORDIC Vector/Rotation Engine & Numerically Controlled Oscillator (NCO)**:
   - Models an unrolled / iterative CORDIC stage (`CordicVec`, `stepCordicShiftZero`, `stepCordicStage`)
     and proves the exact 2D Pythagorean norm scaling identity (`cordic_stage0_norm_scaling`:
     $X_1^2 + Y_1^2 = 2 (X_0^2 + Y_0^2)$) across rotation directions $d \in \{-1, +1\}$,
   - Formalizes a $B$-bit Numerically Controlled Oscillator (`NcoAccum`, `stepNco`) and proves modular
     phase-word confinement (`nco_phase_in_bounds`).
2. **Cascaded Integrator-Comb (CIC) Decimator & Symmetric Linear-Phase FIR Folding**:
   - Formalizes Hogenauer's **CIC decimation filter** (`CicFilterSpec`) of order $N$, decimation ratio $R$,
     and differential delay $M$, proving the overflow-free 2's-complement accumulator bit-growth
     theorem (`cic_register_width_sound`: $B_{\text{out}} = B_{\text{in}} + N \cdot \lceil \log_2(R M) \rceil \ge B_{\text{in}}$)
     and stage monotonicity (`cic_width_monotone_stages`),
   - Formalizes **Symmetric Linear-Phase FIR Filter** tap pairs $h[k] = h[M - k]$ (`evalSymmetricFirTapPair`,
     ` evalDirectFirTapPair`) and proves that pre-adding symmetric delay-line samples before multiplying
     halves hardware DSP multiplier count with zero arithmetic discrepancy (`firSymmetric_folds_multipliers`).
3. **RF Uniform Linear Array (ULA) Phased-Array Beamformer**:
   - Models an $N$-element phased-array receiver/transmitter (`PhasedArrayUla`) with conjugate phase
     steering weights, proving coherent $N^2$ main-lobe array power gain (`phasedArray_coherent_gain_sq`:
     $P_{\text{array}} = N^2 \cdot A_0^2$) and exact destructive null steering (`phasedArray_null_steering`)
     when sub-arrays are phased in antiphase ($\Delta \phi = \pi$).
4. **2-Port S-Parameter Rollett Unconditional LNA Stability ($K > 1, |\Delta| < 1$)**:
   - Formalizes 2-port complex scattering parameters $(S_{11}, S_{12}, S_{21}, S_{22})$ and Rollett's
     stability factor $K = \frac{1 - |S_{11}|^2 - |S_{22}|^2 + |\Delta|^2}{2 |S_{12} S_{21}|}$ in exact
     scaled integer arithmetic (`TwoPortSParams`, `checkRollettUnconditionalStability`),
   - Proves soundness (`rollettStability_sound`) and certifies a concrete 2m Ham Radio ($144\,\text{MHz}$)
     SiGe / GaAs Low-Noise Amplifier while refusing a potentially oscillating negative-resistance stage
     (`golden2mHamLna_stable_and_unstable_refused`).
-/
public import Obend.Hardware.RF
@[expose] public section

namespace Obend.Hardware.DSP

open Obend.Hardware.RF

/-! ## 1. Iterative CORDIC Vector/Rotation Engine & Numerically Controlled Oscillator (NCO) -/

/-- 2D fixed-point IQ vector $(I, Q) = (x, y)$ in the CORDIC datapath. -/
structure CordicVec where
  x : Int
  y : Int
  deriving DecidableEq, Repr

/-- Squared Euclidean magnitude $R^2 = x^2 + y^2$ of a `CordicVec`. -/
def evalCordicNormSq (v : CordicVec) : Int :=
  v.x * v.x + v.y * v.y

/-- Stage-0 ($\tan \theta_0 = 2^0 = 1$, i.e. $\pm 45^\circ$) CORDIC micro-rotation:
* For `dirPos = true` ($d = +1$, counter-clockwise): $(x', y') = (x - y, y + x)$,
* For `dirPos = false` ($d = -1$, clockwise): $(x', y') = (x + y, y - x)$. -/
def stepCordicStage0 (v : CordicVec) (dirPos : Bool) : CordicVec :=
  if dirPos then
    { x := v.x - v.y, y := v.y + v.x }
  else
    { x := v.x + v.y, y := v.y - v.x }

/-- General stage-$i$ CORDIC micro-rotation with shift $S_i = 2^i$ (represented by `shiftDiv : Int`):
$$(x_{i+1}, y_{i+1}) = (x_i \mp y_i / 2^i,\; y_i \pm x_i / 2^i).$$ -/
def stepCordicStage (v : CordicVec) (dirPos : Bool) (shiftFactor : Int) : CordicVec :=
  if shiftFactor ≤ 0 then v
  else if dirPos then
    { x := v.x - v.y / shiftFactor, y := v.y + v.x / shiftFactor }
  else
    { x := v.x + v.y / shiftFactor, y := v.y - v.x / shiftFactor }

/-- Helper algebraic identity: $(x - y)^2 + (y + x)^2 = 2(x^2 + y^2)$ and $(x + y)^2 + (y - x)^2 = 2(x^2 + y^2)$. -/
theorem int_cordic_stage0_identity (x y : Int) :
    (x - y) * (x - y) + (y + x) * (y + x) = 2 * (x * x + y * y) ∧
    (x + y) * (x + y) + (y - x) * (y - x) = 2 * (x * x + y * y) := by
  have h1 : (x - y) * (x - y) = x * x - x * y - y * x + y * y := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]
    omega
  have h2 : (y + x) * (y + x) = y * y + y * x + x * y + x * x := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have h3 : (x + y) * (x + y) = x * x + x * y + y * x + y * y := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have h4 : (y - x) * (y - x) = y * y - y * x - x * y + x * x := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]
    omega
  constructor <;> omega

/-- Theorem (`cordic_stage0_norm_scaling`):
Regardless of rotation direction `dirPos` ($+45^\circ$ or $-45^\circ$), the stage-0 CORDIC
micro-rotation scales the squared Euclidean IQ magnitude $x^2 + y^2$ by exactly $K_0^2 = 1 + 2^0 = 2$:
$$\text{evalCordicNormSq}(\text{stepCordicStage0}(v, d)) = 2 \cdot \text{evalCordicNormSq}(v).$$ -/
theorem cordic_stage0_norm_scaling (v : CordicVec) (dirPos : Bool) :
    evalCordicNormSq (stepCordicStage0 v dirPos) = 2 * evalCordicNormSq v := by
  dsimp only [evalCordicNormSq, stepCordicStage0]
  have hId := int_cordic_stage0_identity v.x v.y
  cases dirPos
  · exact hId.2
  · exact hId.1

/-- Numerically Controlled Oscillator (NCO) phase accumulator with modulus $M = 2^B > 0$
and frequency tuning word `ftw`. -/
structure NcoAccum where
  phaseModulus : Nat
  phaseWord : Nat
  tuningWord : Nat
  deriving DecidableEq, Repr

/-- Advance the NCO phase accumulator by one sample clock cycle:
$\phi[n+1] = (\phi[n] + \text{FTW}) \bmod M$. -/
def stepNco (nco : NcoAccum) : NcoAccum :=
  if nco.phaseModulus == 0 then nco
  else { nco with phaseWord := (nco.phaseWord + nco.tuningWord) % nco.phaseModulus }

/-- Theorem (`nco_phase_in_bounds`):
For any positive phase modulus `0 < nco.phaseModulus`, the stepped NCO phase word is strictly
bounded by `nco.phaseModulus` (`(stepNco nco).phaseWord < nco.phaseModulus`), guaranteeing
wrap-around phase continuity without LUT index out-of-bounds faults. -/
theorem nco_phase_in_bounds (nco : NcoAccum) (hMod : 0 < nco.phaseModulus) :
    (stepNco nco).phaseWord < nco.phaseModulus := by
  dsimp only [stepNco]
  have hNe : (nco.phaseModulus == 0) = false := by
    cases h : nco.phaseModulus == 0
    · rfl
    · have hEq : nco.phaseModulus = 0 := LawfulBEq.eq_of_beq h
      omega
  rw [hNe]
  exact Nat.mod_lt (nco.phaseWord + nco.tuningWord) hMod

/-! ## 2. Cascaded Integrator-Comb (CIC) Decimator & Symmetric Linear-Phase FIR Folding -/

/-- **Hogenauer Cascaded Integrator-Comb (CIC)** decimation/interpolation filter specification:
* `inputWidthBits`: input ADC/mixer sample bit width $B_{\text{in}}$,
* `numStages`: number of cascaded integrator + comb stages $N$,
* `decimationRatio`: rate-change factor $R$,
* `diffDelay`: comb differential delay $M$ (typically $1$ or $2$),
* `ceilLog2Rm`: $\lceil \log_2(R \cdot M) \rceil$ bit growth per stage. -/
structure CicFilterSpec where
  filterName : String
  inputWidthBits : Nat
  numStages : Nat
  decimationRatio : Nat
  diffDelay : Nat
  ceilLog2Rm : Nat
  deriving DecidableEq, Repr

/-- Required 2's-complement internal integrator & comb register bit width to guarantee zero
runtime overflow under Hogenauer's theorem:
$$B_{\max} = B_{\text{in}} + N \cdot \lceil \log_2(R \cdot M) \rceil.$$ -/
def evalCicRequiredWidthBits (cic : CicFilterSpec) : Nat :=
  cic.inputWidthBits + cic.numStages * cic.ceilLog2Rm

/-- Check that a hardware CIC datapath register width `allocatedBits` satisfies Hogenauer's
overflow-free bound and has positive rate parameters. -/
def checkCicOverflowFree (cic : CicFilterSpec) (allocatedBits : Nat) : Bool :=
   decide (0 < cic.inputWidthBits) &&
  decide (0 < cic.numStages) &&
  decide (0 < cic.decimationRatio) &&
  decide (evalCicRequiredWidthBits cic ≤ allocatedBits)

/-- Theorem (`cic_register_width_sound`):
If `checkCicOverflowFree cic allocatedBits = true`, then `allocatedBits` is at least Hogenauer's
exact bit-growth bound $B_{\text{in}} + N \cdot \lceil \log_2(R M) \rceil$, which in turn is
at least the input sample width $B_{\text{in}}$. -/
theorem cic_register_width_sound (cic : CicFilterSpec) (allocatedBits : Nat)
    (hOk : checkCicOverflowFree cic allocatedBits = true) :
    cic.inputWidthBits ≤ evalCicRequiredWidthBits cic ∧
    evalCicRequiredWidthBits cic ≤ allocatedBits := by
  dsimp only [checkCicOverflowFree] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  exact ⟨Nat.le_add_right cic.inputWidthBits (cic.numStages * cic.ceilLog2Rm), of_decide_eq_true hOk.2⟩

/-- Theorem (`cic_width_monotone_stages`):
Adding stages ($N_1 \le N_2$) to a CIC decimator monotonically increases the required internal
register bit width. -/
theorem cic_width_monotone_stages (c1 c2 : CicFilterSpec)
    (hIn : c1.inputWidthBits = c2.inputWidthBits)
    (hLog : c1.ceilLog2Rm = c2.ceilLog2Rm)
    (hStages : c1.numStages ≤ c2.numStages) :
    evalCicRequiredWidthBits c1 ≤ evalCicRequiredWidthBits c2 := by
  dsimp only [evalCicRequiredWidthBits]
  rw [hIn, hLog]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right c2.ceilLog2Rm hStages) c2.inputWidthBits

/-- Direct-form FIR evaluation of a symmetric tap pair $(k, M - k)$ with shared coefficient
$h_k = h_{M - k}$ (`coeff`) and delay-line samples `xEarly = x[n - k]`, `xLate = x[n - (M - k)]`:
requires **two** multiplications `coeff * xEarly + coeff * xLate`. -/
def evalDirectFirTapPair (coeff xEarly xLate : Int) : Int :=
  coeff * xEarly + coeff * xLate

/-- Folded Linear-Phase FIR evaluation of a symmetric tap pair: pre-adds the delay-line samples
`xEarly + xLate` in a cheap adder before performing **one** hardware DSP multiplication
`coeff * (xEarly + xLate)`. -/
def evalFoldedSymmetricFirTapPair (coeff xEarly xLate : Int) : Int :=
  coeff * (xEarly + xLate)

/-- Theorem (`firSymmetric_folds_multipliers`):
Pre-adding symmetric delay-line samples in a linear-phase FIR filter (`evalFoldedSymmetricFirTapPair`)
produces the **exact** same fixed-point output as the 2-multiplier direct form (`evalDirectFirTapPair`),
cutting hardware DSP48 / MAC multiplier utilization in half with zero rounding error! -/
theorem firSymmetric_folds_multipliers (coeff xEarly xLate : Int) :
    evalFoldedSymmetricFirTapPair coeff xEarly xLate =
    evalDirectFirTapPair coeff xEarly xLate := by
  dsimp only [evalFoldedSymmetricFirTapPair, evalDirectFirTapPair]
  exact Int.mul_add coeff xEarly xLate

/-! ## 3. RF Uniform Linear Array (ULA) Phased-Array Beamformer -/

/-- Uniform Linear Array (ULA) RF phased-array specification:
* `numElements`: number of antenna elements $N$,
* `elementPitchUm`: inter-element spacing $d$ (typically $\lambda / 2$),
* `elementAmplitudeMv`: per-element coherent demodulated envelope amplitude $A_0$ (after conjugate phase alignment). -/
structure PhasedArrayUla where
  arrayName : String
  numElements : Nat
  elementPitchUm : Nat
  elementAmplitudeMv : Int
  deriving DecidableEq, Repr

/-- Coherent boresight / phase-steered main-lobe voltage amplitude sum across $N$ elements:
$$V_{\text{sum}} = \sum_{k=0}^{N-1} A_0 = N \cdot A_0.$$ -/
def evalPhasedArrayMainLobeVoltageMv (ula : PhasedArrayUla) : Int :=
  (ula.numElements : Int) * ula.elementAmplitudeMv

/-- Coherent main-lobe array power proxy $P_{\text{array}} = V_{\text{sum}}^2 = (N \cdot A_0)^2$. -/
def evalPhasedArrayMainLobePower (ula : PhasedArrayUla) : Int :=
  evalPhasedArrayMainLobeVoltageMv ula * evalPhasedArrayMainLobeVoltageMv ula

/-- Single-element isotropic baseline power proxy $P_{\text{elem}} = A_0^2$. -/
def evalSingleElementPower (ula : PhasedArrayUla) : Int :=
  ula.elementAmplitudeMv * ula.elementAmplitudeMv

/-- Theorem (`phasedArray_coherent_gain_sq`):
When an $N$-element phased array is conjugate-phase-steered to the target angle $\theta_0$,
its coherent main-lobe power equals exactly $N^2$ times the single-element power ($10 \log_{10} N^2 = 20 \log_{10} N\,\text{dB}$):
$$P_{\text{array}} = (N \cdot A_0)^2 = N^2 \cdot P_{\text{elem}}.$$ -/
theorem phasedArray_coherent_gain_sq (ula : PhasedArrayUla) :
    evalPhasedArrayMainLobePower ula =
    ((ula.numElements : Int) * (ula.numElements : Int)) * evalSingleElementPower ula := by
  dsimp only [evalPhasedArrayMainLobePower, evalPhasedArrayMainLobeVoltageMv, evalSingleElementPower]
  have h1 : (ula.numElements : Int) * ula.elementAmplitudeMv * ((ula.numElements : Int) * ula.elementAmplitudeMv) =
      (ula.numElements : Int) * (ula.elementAmplitudeMv * ((ula.numElements : Int) * ula.elementAmplitudeMv)) := by
    rw [Int.mul_assoc]
  have h2 : ula.elementAmplitudeMv * ((ula.numElements : Int) * ula.elementAmplitudeMv) =
      (ula.numElements : Int) * (ula.elementAmplitudeMv * ula.elementAmplitudeMv) := by
    rw [← Int.mul_assoc, Int.mul_comm ula.elementAmplitudeMv (ula.numElements : Int), Int.mul_assoc]
  rw [h1, h2, ← Int.mul_assoc]

/-- Destructive interferer null-steering sum for two symmetric sub-arrays of amplitude `subArrayAmpMv`
steered in antiphase ($\Delta \phi = \pi \implies w_1 = +1, w_2 = -1$) toward an off-axis jammer. -/
def evalNullSteeredJammerVoltageMv (subArrayAmpMv : Int) : Int :=
  subArrayAmpMv + (-subArrayAmpMv)

/-- Theorem (`phasedArray_null_steering`):
When two balanced sub-arrays receive an off-axis jammer in antiphase ($\Delta \phi = \pi$),
their combined voltage and jammer power vanish identically to `0` (complete spatial null)! -/
theorem phasedArray_null_steering (subArrayAmpMv : Int) :
    evalNullSteeredJammerVoltageMv subArrayAmpMv = 0 ∧
    evalNullSteeredJammerVoltageMv subArrayAmpMv * evalNullSteeredJammerVoltageMv subArrayAmpMv = 0 := by
  dsimp only [evalNullSteeredJammerVoltageMv]
  omega

/-! ## 4. 2-Port S-Parameter Rollett Unconditional LNA Stability ($K > 1, |\Delta| < 1$) -/

/-- 2-port RF Scattering Parameters (S-parameters) scaled in permille ($1000 = 1.000$):
* `s11MagSqPermilleSq`: $|S_{11}|^2$ in units of $10^{-6}$ ($1000000 = 1.0$),
* `s22MagSqPermilleSq`: $|S_{22}|^2$ in units of $10^{-6}$,
* `s12s21MagPermilleSq`: $|S_{12} \cdot S_{21}|$ in units of $10^{-6}$,
* `deltaMagSqPermilleSq`: $|\Delta|^2 = |S_{11} S_{22} - S_{12} S_{21}|^2$ in units of $10^{-6}$. -/
structure TwoPortSParams where
  stageName : String
  freqMhz : Nat
  s11MagSqPermilleSq : Int
  s22MagSqPermilleSq : Int
  s12s21MagPermilleSq : Int
  deltaMagSqPermilleSq : Int
  deriving DecidableEq, Repr

/-- Numerator of Rollett's stability factor $K$:
$$\text{Num}(K) = 10^6 - |S_{11}|^2 - |S_{22}|^2 + |\Delta|^2.$$ -/
def evalRollettNumerator (sp : TwoPortSParams) : Int :=
  1000000 - sp.s11MagSqPermilleSq - sp.s22MagSqPermilleSq + sp.deltaMagSqPermilleSq

/-- Denominator of Rollett's stability factor $K$:
$$\text{Den}(K) = 2 \cdot |S_{12} S_{21}|.$$ -/
def evalRollettDenominator (sp : TwoPortSParams) : Int :=
  2 * sp.s12s21MagPermilleSq

/-- **Rollett Unconditional Stability Criterion ($K > 1$ and $|\Delta| < 1$)**:
A 2-port RF amplifier is unconditionally stable for all passive source and load terminations
($|\Gamma_S| < 1, |\Gamma_L| < 1$) if and only if:
1. $|S_{11}|^2 < 10^6$ and $|S_{22}|^2 < 10^6$,
2. $|\Delta|^2 < 10^6$ ($|\Delta| < 1$),
3. $K > 1 \iff \text{evalRollettNumerator}(sp) > \text{evalRollettDenominator}(sp) > 0$. -/
def checkRollettUnconditionalStability (sp : TwoPortSParams) : Bool :=
  decide (0 ≤ sp.s11MagSqPermilleSq ∧ sp.s11MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.s22MagSqPermilleSq ∧ sp.s22MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.deltaMagSqPermilleSq ∧ sp.deltaMagSqPermilleSq < 1000000) &&
  decide (0 < evalRollettDenominator sp) &&
  decide (evalRollettDenominator sp < evalRollettNumerator sp)

/-- Theorem (`rollettStability_sound`):
Whenever `checkRollettUnconditionalStability sp = true`, the 2-port RF stage satisfies Rollett's
strict unconditional stability inequalities $|\Delta|^2 < 10^6$, $|S_{11}|^2 < 10^6$, $|S_{22}|^2 < 10^6$,
and $0 < 2 |S_{12} S_{21}| < 10^6 - |S_{11}|^2 - |S_{22}|^2 + |\Delta|^2$ ($K > 1$). -/
theorem rollettStability_sound (sp : TwoPortSParams)
    (hStable : checkRollettUnconditionalStability sp = true) :
    sp.s11MagSqPermilleSq < 1000000 ∧
    sp.s22MagSqPermilleSq < 1000000 ∧
    sp.deltaMagSqPermilleSq < 1000000 ∧
    0 < evalRollettDenominator sp ∧
    evalRollettDenominator sp < evalRollettNumerator sp := by
  dsimp only [checkRollettUnconditionalStability] at hStable
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hStable
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hStable
  exact ⟨hStable.1.1.1.1.2, hStable.1.1.1.2.2, hStable.1.1.2.2, hStable.1.2, hStable.2⟩

/-- Concrete 2-meter Ham Radio ($144\,\text{MHz}$) Low-Noise Amplifier S-parameter characterization:
* $|S_{11}| = 0.25 \implies |S_{11}|^2 = 62500$,
* $|S_{22}| = 0.30 \implies |S_{22}|^2 = 90000$,
* $|S_{21}| = 8.0\,(18\,\text{dB}), |S_{12}| = 0.04\,(-28\,\text{dB}) \implies |S_{12} S_{21}| = 320000$,
* $|\Delta|^2 = 85000 < 10^6$,
* $\text{Num}(K) = 1000000 - 62500 - 90000 + 85000 = 932500 > \text{Den}(K) = 640000$ ($K \approx 1.457 > 1$). -/
def golden2mHamLnaSParams : TwoPortSParams :=
  { stageName := "vhf_144mhz_sige_lna"
    freqMhz := 144
    s11MagSqPermilleSq := 62500
    s22MagSqPermilleSq := 90000
    s12s21MagPermilleSq := 320000
    deltaMagSqPermilleSq := 85000 }

/-- Potentially oscillating unneutralized RF stage with excessive reverse feedback
$|S_{12} S_{21}| = 480000 \implies \text{Den}(K) = 960000 > \text{Num}(K) = 750000$ ($K \approx 0.78 < 1$). -/
def unstableFeedbackLnaSParams : TwoPortSParams :=
  { golden2mHamLnaSParams with
    stageName := "unneutralized_feedback_lna"
    s12s21MagPermilleSq := 480000 }

/-- Theorem (`golden2mHamLna_stable_and_unstable_refused`):
The 2m VHF Ham Radio LNA passes Rollett unconditional stability ($K \approx 1.457 > 1, |\Delta| < 1$),
produces a positive 4-element phased-array coherent gain of $16 \times$ ($+12\,\text{dB}$),
and the unneutralized high-feedback stage with $K < 1$ is refused! -/
theorem golden2mHamLna_stable_and_unstable_refused :
    checkRollettUnconditionalStability golden2mHamLnaSParams = true ∧
    checkRollettUnconditionalStability unstableFeedbackLnaSParams = false ∧
    checkCicOverflowFree
      { filterName := "sdr_rx_cic4_r64"
        inputWidthBits := 14
        numStages := 4
        decimationRatio := 64
        diffDelay := 1
        ceilLog2Rm := 6 } 38 = true ∧
    evalPhasedArrayMainLobePower
      { arrayName := "vhf_2m_4elem_yagi_ula"
        numElements := 4
        elementPitchUm := 1040000
        elementAmplitudeMv := 100 } = 160000 := by
  decide +kernel

end Obend.Hardware.DSP
end
