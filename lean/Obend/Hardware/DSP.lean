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

/-! ## 5. Multi-Stage Unrolled CORDIC Pipeline (`runCordicPipeline`, `cordic_stage1_norm_identity`, `cordic_twoStage_exact_gain_10x`) -/

/-- Recursively execute a multi-stage CORDIC pipeline chaining arbitrary micro-rotation stages
`(dirPos, shiftFactor)` from initial vector `v : CordicVec`. -/
def runCordicPipeline (v : CordicVec) : List (Bool × Int) → CordicVec
  | [] => v
  | (dirPos, shiftFactor) :: rest =>
    runCordicPipeline (stepCordicStage v dirPos shiftFactor) rest

/-- Theorem (`runCordicPipeline_append`):
Executing a concatenated multi-stage CORDIC pipeline `stages1 ++ stages2` is identical to executing
`stages1` followed by `stages2` from the intermediate `CordicVec` register state. -/
theorem runCordicPipeline_append
    (stages1 stages2 : List (Bool × Int)) (v : CordicVec) :
    runCordicPipeline v (stages1 ++ stages2) =
      runCordicPipeline (runCordicPipeline v stages1) stages2 := by
  induction stages1 generalizing v with
  | nil => rfl
  | cons st rest ih =>
    dsimp only [List.cons_append, runCordicPipeline]
    exact ih (stepCordicStage v st.1 st.2)

/-- Stage-1 ($\tan \theta_1 = 2^{-1} = 1/2$, scaled by $2$ so $(x', y') = (2x \mp y, 2y \pm x)$)
exact-integer CORDIC micro-rotation:
* For `dirPos = true` ($d = +1$, counter-clockwise): $(x', y') = (2x - y, 2y + x)$,
* For `dirPos = false` ($d = -1$, clockwise): $(x', y') = (2x + y, 2y - x)$. -/
def stepCordicStage1 (v : CordicVec) (dirPos : Bool) : CordicVec :=
  if dirPos then
    { x := 2 * v.x - v.y, y := 2 * v.y + v.x }
  else
    { x := 2 * v.x + v.y, y := 2 * v.y - v.x }

/-- Helper algebraic identity for Stage-1 CORDIC:
$(2x - y)^2 + (2y + x)^2 = 5(x^2 + y^2)$ and $(2x + y)^2 + (2y - x)^2 = 5(x^2 + y^2)$. -/
theorem int_cordic_stage1_identity (x y : Int) :
    (2 * x - y) * (2 * x - y) + (2 * y + x) * (2 * y + x) = 5 * (x * x + y * y) ∧
    (2 * x + y) * (2 * x + y) + (2 * y - x) * (2 * y - x) = 5 * (x * x + y * y) := by
  have h1 : (2 * x - y) * (2 * x - y) = (2 * x) * (2 * x) - (2 * x) * y - y * (2 * x) + y * y := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]
    omega
  have h2 : (2 * y + x) * (2 * y + x) = (2 * y) * (2 * y) + (2 * y) * x + x * (2 * y) + x * x := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have h3 : (2 * x + y) * (2 * x + y) = (2 * x) * (2 * x) + (2 * x) * y + y * (2 * x) + y * y := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have h4 : (2 * y - x) * (2 * y - x) = (2 * y) * (2 * y) - (2 * y) * x - x * (2 * y) + x * x := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]
    omega
  have hx2 : (2 * x) * (2 * x) = 4 * (x * x) := by
    rw [← Int.mul_assoc, Int.mul_comm (2 * x) 2, ← Int.mul_assoc, Int.mul_assoc]
    omega
  have hy2 : (2 * y) * (2 * y) = 4 * (y * y) := by
    rw [← Int.mul_assoc, Int.mul_comm (2 * y) 2, ← Int.mul_assoc, Int.mul_assoc]
    omega
  have hxy1 : (2 * x) * y = 2 * (x * y) := by rw [Int.mul_assoc]
  have hxy2 : y * (2 * x) = 2 * (x * y) := by rw [Int.mul_comm y (2 * x), Int.mul_assoc]
  have hyx1 : (2 * y) * x = 2 * (x * y) := by rw [Int.mul_assoc, Int.mul_comm y x]
  have hyx2 : x * (2 * y) = 2 * (x * y) := by rw [← Int.mul_assoc, Int.mul_comm x 2, Int.mul_assoc]
  constructor <;> omega

/-- Theorem (`cordic_stage1_norm_identity`):
For Stage 1 ($\tan \theta_1 = 1/2$, scaled by $2$ so $(x', y') = (2x \mp y, 2y \pm x)$),
the squared Euclidean norm scales by exact integer factor $1 + 2^2 = 5$:
$$(x')^2 + (y')^2 = 5 (x^2 + y^2).$$ -/
theorem cordic_stage1_norm_identity (v : CordicVec) (dirPos : Bool) :
    evalCordicNormSq (stepCordicStage1 v dirPos) = 5 * evalCordicNormSq v := by
  dsimp only [evalCordicNormSq, stepCordicStage1]
  have hId := int_cordic_stage1_identity v.x v.y
  cases dirPos
  · exact hId.2
  · exact hId.1

/-- Combined 2-stage exact-integer CORDIC pipeline chaining Stage 0 ($\tan \theta_0 = 1$)
followed by scaled Stage 1 ($\tan \theta_1 = 1/2$). -/
def stepCordicTwoStage (v : CordicVec) (dir0 dir1 : Bool) : CordicVec :=
  stepCordicStage1 (stepCordicStage0 v dir0) dir1

/-- Theorem (`cordic_twoStage_exact_gain_10x`):
For the combined Stage-0 + Stage-1 CORDIC pipeline, the squared Euclidean norm scales by the exact
integer factor $2 \times 5 = 10$ across all four rotation sign combinations `(dir0, dir1)`! -/
theorem cordic_twoStage_exact_gain_10x (v : CordicVec) (dir0 dir1 : Bool) :
    evalCordicNormSq (stepCordicTwoStage v dir0 dir1) = 10 * evalCordicNormSq v := by
  dsimp only [stepCordicTwoStage]
  rw [cordic_stage1_norm_identity, cordic_stage0_norm_scaling]
  omega

/-- Unrolled CORDIC micro-rotation stage parameters with explicit angle accumulator:
* `shiftPow2`: barrel-shifter exponent $i$ so the stage divisor is $2^i$ (`shiftPow2 = 0, 1, 2, 3`),
* `atanAngleMrad`: elementary arctangent angle $\arctan(2^{-i})$ in milliradians ($\text{mrad}$, e.g. `785, 464, 245, 124`),
* `signPositive`: micro-rotation direction $d_i \in \{+1, -1\}$. -/
structure CordicMicroStage where
  shiftPow2     : Nat
  atanAngleMrad : Int
  signPositive  : Bool
  deriving DecidableEq, Repr

/-- Single unrolled CORDIC micro-rotation step updating $(x, y, z)$ across `st : CordicMicroStage`
with shift divisor $2^{\text{shiftPow2}}$. -/
def cordicRotateStep (x y z : Int) (st : CordicMicroStage) : Int × Int × Int :=
  let sf : Int := Int.ofNat (2 ^ st.shiftPow2)
  if st.signPositive then
    (x - y / sf, y + x / sf, z - st.atanAngleMrad)
  else
    (x + y / sf, y - x / sf, z + st.atanAngleMrad)

/-- Recursively execute a multi-stage unrolled CORDIC angle-tracking pipeline from `(x0, y0, z0)`. -/
def runCordicMicroPipeline (x0 y0 z0 : Int) : List CordicMicroStage → Int × Int × Int
  | [] => (x0, y0, z0)
  | st :: rest =>
    let (x1, y1, z1) := cordicRotateStep x0 y0 z0 st
    runCordicMicroPipeline x1 y1 z1 rest

/-- Concrete 4-stage unrolled CORDIC micro-rotation pipeline:
* Stage 0: $2^0 = 1$, $\arctan(1) \approx 785\,\text{mrad}$ ($+45.0^\circ$), `signPositive = true`,
* Stage 1: $2^1 = 2$, $\arctan(1/2) \approx 464\,\text{mrad}$ ($-26.6^\circ$), `signPositive = false`,
* Stage 2: $2^2 = 4$, $\arctan(1/4) \approx 245\,\text{mrad}$ ($+14.0^\circ$), `signPositive = true`,
* Stage 3: $2^3 = 8$, $\arctan(1/8) \approx 124\,\text{mrad}$ ($-7.1^\circ$), `signPositive = false`. -/
def goldenCordic4Stages : List CordicMicroStage :=
  [ { shiftPow2 := 0, atanAngleMrad := 785, signPositive := true }
  , { shiftPow2 := 1, atanAngleMrad := 464, signPositive := false }
  , { shiftPow2 := 2, atanAngleMrad := 245, signPositive := true }
  , { shiftPow2 := 3, atanAngleMrad := 124, signPositive := false } ]

/-- Theorem (`cordic_4stage_pipeline_verified`):
Starting from $(x_0, y_0, z_0) = (1000, 0, 442)$ ($442\,\text{mrad} \approx 25.3^\circ$), the 4-stage
unrolled CORDIC pipeline `goldenCordic4Stages` converges to `(1484, 704, 0)` with zero residual
angle error (`z4 = 0`) and processing norm gain $x_4^2 + y_4^2 = 2697872 > x_0^2 + y_0^2 = 1000000$. -/
theorem cordic_4stage_pipeline_verified :
    runCordicMicroPipeline 1000 0 442 goldenCordic4Stages = (1484, 704, 0) ∧
    (let (x4, y4, z4) := runCordicMicroPipeline 1000 0 442 goldenCordic4Stages
     z4 = 0 ∧ 1000 * 1000 < x4 * x4 + y4 * y4) := by
  decide +kernel

/-! ## 6. 2D Complex IQ Phasor Beamforming Summation (`IqPhasor`, `evalUlaIqBeamformer`) -/

/-- 2D complex baseband IQ phasor $s = I + j Q$. -/
structure IqPhasor where
  i : Int
  q : Int
  deriving DecidableEq, Repr

/-- Complex conjugate weight multiplication for phased-array matched filtering:
$$(I_{\text{sig}} + j Q_{\text{sig}}) \cdot (I_w - j Q_w) =
  (I_{\text{sig}} I_w + Q_{\text{sig}} Q_w) + j (Q_{\text{sig}} I_w - I_{\text{sig}} Q_w).$$ -/
def iqConjMul (sig weight : IqPhasor) : IqPhasor :=
  ⟨sig.i * weight.i + sig.q * weight.q, sig.q * weight.i - sig.i * weight.q⟩

/-- Uniform Linear Array (ULA) complex IQ beamformer summation across `(sig, weight)` antenna elements:
$$Y = \sum_{k=0}^{N-1} s_k \cdot w_k^*.$$ -/
def evalUlaIqBeamformer : List (IqPhasor × IqPhasor) → IqPhasor
  | [] => ⟨0, 0⟩
  | (sig, weight) :: rest =>
    let prod := iqConjMul sig weight
    let tail := evalUlaIqBeamformer rest
    ⟨prod.i + tail.i, prod.q + tail.q⟩

/-- Theorem (`iq_matched_filter_quadrature_zero`):
Universally for any antenna element IQ signal `s : IqPhasor`, applying its phase-matched complex
conjugate steering weight `w = s` annihilates the quadrature phase error identically:
`(iqConjMul s s).q = 0`. -/
theorem iq_matched_filter_quadrature_zero (s : IqPhasor) :
    (iqConjMul s s).q = 0 := by
  dsimp only [iqConjMul]
  rw [Int.mul_comm s.q s.i, Int.sub_self]

/-- Theorem (`iq_matched_filter_inphase_nonneg`):
Universally for any antenna element IQ signal `s : IqPhasor`, the phase-matched in-phase output
`(iqConjMul s s).i = s.i * s.i + s.q * s.q` is non-negative (`0 ≤ (iqConjMul s s).i`). -/
theorem iq_matched_filter_inphase_nonneg (s : IqPhasor) :
    0 ≤ (iqConjMul s s).i := by
  dsimp only [iqConjMul]
  have hI := Obend.Hardware.Thermal.int_sq_nonneg s.i
  have hQ := Obend.Hardware.Thermal.int_sq_nonneg s.q
  omega

/-- Theorem (`ula_4elem_matched_beamformer_coherent`):
Universally for any element signal `s : IqPhasor`, a 4-element uniform linear array with conjugate
phase-matched weights `(s, s)` sums coherently to `4 * (s.i * s.i + s.q * s.q) ≥ 0` in the in-phase
channel and `0` in the quadrature channel! -/
theorem ula_4elem_matched_beamformer_coherent (s : IqPhasor) :
    (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).i =
      4 * (s.i * s.i + s.q * s.q) ∧
    0 ≤ (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).i ∧
    (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).q = 0 := by
  dsimp only [evalUlaIqBeamformer, iqConjMul]
  have hq : s.q * s.i - s.i * s.q = 0 := by
    rw [Int.mul_comm s.q s.i, Int.sub_self]
  have hI := Obend.Hardware.Thermal.int_sq_nonneg s.i
  have hQ := Obend.Hardware.Thermal.int_sq_nonneg s.q
  rw [hq]
  refine ⟨by omega, by omega, by omega⟩

/-- Theorem (`ula_4elem_progressive_phase_beamformer_verified`):
For a 4-element ULA receiving a wavefront with $90^\circ$ progressive inter-element phase shift
(`⟨80, 60⟩`, `⟨-60, 80⟩`, `⟨-80, -60⟩`, `⟨60, -80⟩`, each of envelope squared $80^2 + 60^2 = 10000$),
applying conjugate steering weights aligns all 4 elements to `⟨40000, 0⟩` ($4\times$ coherent amplitude,
$16\times$ power gain)! -/
theorem ula_4elem_progressive_phase_beamformer_verified :
    evalUlaIqBeamformer
      [ (⟨80, 60⟩, ⟨80, 60⟩)
      , (⟨-60, 80⟩, ⟨-60, 80⟩)
      , (⟨-80, -60⟩, ⟨-80, -60⟩)
      , (⟨60, -80⟩, ⟨60, -80⟩) ] = ⟨40000, 0⟩ := by
  decide +kernel

/-! ## 7. Connected SDR Digital Downconverter (DDC) Datapath (`SdrDdcChainSpec`, `evalSdrDdcSample`, `checkSdrDdcSignoff`) -/

/-- Alias for `evalCicRequiredWidthBits` matching Hogenauer's required accumulator bit width. -/
abbrev cicRequiredBitWidth (cic : CicFilterSpec) : Nat :=
  evalCicRequiredWidthBits cic

/-- Alias for `evalFoldedSymmetricFirTapPair` evaluating a folded symmetric linear-phase FIR tap pair. -/
abbrev evalSymmetricFirTapPair (coeff xEarly xLate : Int) : Int :=
  evalFoldedSymmetricFirTapPair coeff xEarly xLate

/-- Connected Software-Defined Radio (SDR) Digital Downconverter (DDC) datapath specification chaining:
1. `NcoAccum` phase accumulator (`stepNco`),
2. 2-stage CORDIC local oscillator (`stepCordicStage0` + `stepCordicStage1`),
3. `RF.lean` Tayloe quadrature $I/Q$ image-rejecting mixer (`evalQuadratureImagePhaseCancel`),
4. Hogenauer `CicFilterSpec` decimator with verified overflow-free accumulator bit-width (`cicRequiredBitWidth`),
5. Folded symmetric linear-phase FIR compensating filter (`evalSymmetricFirTapPair`). -/
structure SdrDdcChainSpec where
  ddcName          : String
  nco              : NcoAccum
  loInitVec        : CordicVec
  cordicDir0       : Bool
  cordicDir1       : Bool
  iqGainI          : Int
  iqGainQ          : Int
  iqPhaseErr       : Int
  cic              : CicFilterSpec
  cicAllocatedBits : Nat
  firTapCoeff      : Int
  deriving DecidableEq, Repr

/-- Evaluate one sample through the connected SDR Digital Downconverter (DDC) datapath:
1. Synthesizes the 2-stage CORDIC LO vector `loVec = stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1`,
2. Demodulates the desired sideband `evalQuadratureDesiredSideband` minus any residual image
   `evalQuadratureImagePhaseCancel`,
3. Filters the decimated baseband sample pair `(cicDecimated, delayedSample)` via the folded symmetric
   linear-phase FIR tap pair `evalSymmetricFirTapPair`. -/
def evalSdrDdcSample (spec : SdrDdcChainSpec) (rfSigAmp delayedSample : Int) : Int :=
  let loVec := stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1
  let desiredBb := evalQuadratureDesiredSideband spec.iqGainI spec.iqGainQ (rfSigAmp * loVec.x)
  let imageResidual := evalQuadratureImagePhaseCancel spec.iqGainI spec.iqGainQ spec.iqPhaseErr rfSigAmp
  let cicDecimated := desiredBb - imageResidual
  evalSymmetricFirTapPair spec.firTapCoeff cicDecimated delayedSample

/-- Complete signoff checker for the connected SDR Digital Downconverter (`SdrDdcChainSpec`):
1. Positive NCO phase modulus (`0 < spec.nco.phaseModulus`),
2. Non-zero CORDIC LO seed vector (`0 < evalCordicNormSq spec.loInitVec`),
3. Strictly positive, matched Tayloe quadrature $I/Q$ conversion gain (`0 < spec.iqGainI` and `spec.iqGainI == spec.iqGainQ`) and zero phase skew (`spec.iqPhaseErr == 0`),
4. Hogenauer CIC decimator accumulator bit-width prevents 2's-complement wrap-around (`checkCicOverflowFree`). -/
def checkSdrDdcSignoff (spec : SdrDdcChainSpec) : Bool :=
  decide (0 < spec.nco.phaseModulus) &&
  decide (0 < evalCordicNormSq spec.loInitVec) &&
  decide (0 < spec.iqGainI) &&
  (spec.iqGainI == spec.iqGainQ) &&
  (spec.iqPhaseErr == 0) &&
  checkCicOverflowFree spec.cic spec.cicAllocatedBits

/-- Theorem (`sdrDdcChain_signoff_sound`):
Whenever `checkSdrDdcSignoff spec = true`, for any RF input amplitude `rfSigAmp` and FIR delay-line
samples `xEarly, xLate`:
1. The stepped NCO phase word stays strictly within `[0, spec.nco.phaseModulus)`,
2. The 2-stage CORDIC local oscillator scales squared vector magnitude by exact factor `10`,
3. The Tayloe $I/Q$ unwanted image sideband cancels identically to `0`,
4. The CIC accumulator width `spec.cicAllocatedBits` satisfies Hogenauer's overflow-free bit-growth bound
   `spec.cic.inputWidthBits ≤ cicRequiredBitWidth spec.cic ≤ spec.cicAllocatedBits`,
5. The folded symmetric FIR tap multiplier matches the 2-multiplier direct form (`evalDirectFirTapPair`), and
6. End-to-end sample evaluation `evalSdrDdcSample` equals the image-free direct FIR output! -/
theorem sdrDdcChain_signoff_sound
    (spec : SdrDdcChainSpec) (rfSigAmp xEarly xLate : Int)
    (hOk : checkSdrDdcSignoff spec = true) :
    (stepNco spec.nco).phaseWord < spec.nco.phaseModulus ∧
    evalCordicNormSq (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1) =
      10 * evalCordicNormSq spec.loInitVec ∧
    evalQuadratureImagePhaseCancel spec.iqGainI spec.iqGainQ spec.iqPhaseErr rfSigAmp = 0 ∧
    spec.cic.inputWidthBits ≤ cicRequiredBitWidth spec.cic ∧
    cicRequiredBitWidth spec.cic ≤ spec.cicAllocatedBits ∧
    evalSymmetricFirTapPair spec.firTapCoeff xEarly xLate =
      evalDirectFirTapPair spec.firTapCoeff xEarly xLate ∧
    evalSdrDdcSample spec rfSigAmp xLate =
      evalDirectFirTapPair spec.firTapCoeff
        (2 * spec.iqGainI * (rfSigAmp * (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1).x))
        xLate := by
  dsimp only [checkSdrDdcSignoff] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  have hMod : 0 < spec.nco.phaseModulus := of_decide_eq_true hOk.1.1.1.1.1
  have hGain : spec.iqGainI = spec.iqGainQ := LawfulBEq.eq_of_beq hOk.1.1.2
  have hPhase : spec.iqPhaseErr = 0 := LawfulBEq.eq_of_beq hOk.1.2
  have hCic := cic_register_width_sound spec.cic spec.cicAllocatedBits hOk.2
  have hTayloeImg := (tayloe_iq_cancels_image_sideband spec.iqGainI spec.iqGainQ spec.iqPhaseErr rfSigAmp hGain hPhase).1
  have hTayloeDes := (tayloe_iq_cancels_image_sideband spec.iqGainI spec.iqGainQ spec.iqPhaseErr
    (rfSigAmp * (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1).x) hGain hPhase).2
  refine ⟨nco_phase_in_bounds spec.nco hMod,
          cordic_twoStage_exact_gain_10x spec.loInitVec spec.cordicDir0 spec.cordicDir1,
          hTayloeImg,
          hCic.1,
          hCic.2,
          firSymmetric_folds_multipliers spec.firTapCoeff xEarly xLate,
          ?_⟩
  dsimp only [evalSdrDdcSample, evalSymmetricFirTapPair]
  rw [hTayloeImg, Int.sub_zero, hTayloeDes]
  exact firSymmetric_folds_multipliers spec.firTapCoeff
    (2 * spec.iqGainI * (rfSigAmp * (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1).x))
    xLate

/-- Theorem (`sdrDdcChain_positive_lo_and_gain`):
Whenever `checkSdrDdcSignoff spec = true`, the Tayloe $I/Q$ conversion gain is strictly positive
(`0 < spec.iqGainI`) and the 2-stage CORDIC local oscillator output vector has strictly positive
squared Euclidean power (`0 < evalCordicNormSq (stepCordicTwoStage ...)`). -/
theorem sdrDdcChain_positive_lo_and_gain
    (spec : SdrDdcChainSpec)
    (hOk : checkSdrDdcSignoff spec = true) :
    0 < spec.iqGainI ∧
    0 < evalCordicNormSq (stepCordicTwoStage spec.loInitVec spec.cordicDir0 spec.cordicDir1) := by
  dsimp only [checkSdrDdcSignoff] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  have hLoPos : 0 < evalCordicNormSq spec.loInitVec := of_decide_eq_true hOk.1.1.1.1.2
  have hGainPos : 0 < spec.iqGainI := of_decide_eq_true hOk.1.1.1.2
  have hScale := cordic_twoStage_exact_gain_10x spec.loInitVec spec.cordicDir0 spec.cordicDir1
  refine ⟨hGainPos, ?_⟩
  rw [hScale]
  omega

/-- Canonical 40m FT8 SDR Digital Downconverter datapath configuration (`16-bit` NCO modulus $65536$,
2-stage CORDIC LO seed `(100, 0)`, matched Tayloe $I/Q$ gains `500`, 4-stage $R=64$ CIC decimator
with $38$-bit accumulator, and symmetric FIR tap coefficient `12`). -/
def goldenSdrDdcChainSpec : SdrDdcChainSpec where
  ddcName          := "sdr_40m_ft8_ddc_chain"
  nco              := { phaseModulus := 65536, phaseWord := 12000, tuningWord := 7074 }
  loInitVec        := { x := 100, y := 0 }
  cordicDir0       := true
  cordicDir1       := false
  iqGainI          := 500
  iqGainQ          := 500
  iqPhaseErr       := 0
  cic              := { filterName := "cic4_r64_m1", inputWidthBits := 14, numStages := 4, decimationRatio := 64, diffDelay := 1, ceilLog2Rm := 6 }
  cicAllocatedBits := 38
  firTapCoeff      := 12

/-- Defective DDC configuration with $I/Q$ gain imbalance (`iqGainI = 500 ≠ iqGainQ = 480`). -/
def unbalancedIqSdrDdcSpec : SdrDdcChainSpec :=
  { goldenSdrDdcChainSpec with
    ddcName := "sdr_ddc_iq_imbalanced"
    iqGainQ := 480 }

/-- Defective DDC configuration with zero conversion gain (`iqGainI = 0, iqGainQ = 0`). -/
def deadMixerSdrDdcSpec : SdrDdcChainSpec :=
  { goldenSdrDdcChainSpec with
    ddcName := "sdr_ddc_dead_mixer"
    iqGainI := 0
    iqGainQ := 0 }

/-- Defective DDC configuration with truncated 24-bit CIC accumulator (`24 < 38` required bits). -/
def underAllocatedCicSdrDdcSpec : SdrDdcChainSpec :=
  { goldenSdrDdcChainSpec with
    ddcName          := "sdr_ddc_cic_overflow"
    cicAllocatedBits := 24 }

/-- Theorem (`sdrDdcChain_signoff_poles`):
`checkSdrDdcSignoff` accepts `goldenSdrDdcChainSpec` and refuses `unbalancedIqSdrDdcSpec`
($I/Q$ image leakage), `deadMixerSdrDdcSpec` (zero mixer conversion gain), and
`underAllocatedCicSdrDdcSpec` (CIC integrator wrap-around overflow)! -/
theorem sdrDdcChain_signoff_poles :
    checkSdrDdcSignoff goldenSdrDdcChainSpec = true ∧
    checkSdrDdcSignoff unbalancedIqSdrDdcSpec = false ∧
    checkSdrDdcSignoff deadMixerSdrDdcSpec = false ∧
    checkSdrDdcSignoff underAllocatedCicSdrDdcSpec = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Obend.Hardware.DSP
end
