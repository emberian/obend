module
/-
# Obend.Hardware.Accelerators — integer identities behind accelerator arithmetic

Integer identities, over `Int` and `List Int`, that accelerator designs rest on: they are algebra, not
models of any device, and are labelled as such (`review/FABLE-COUNCIL-20261101.md` §2.4). A model of a
GPU that nothing ran (an `AmdGpuInst` interpreter, 2026-11-01) lived here until 2026-11-05; the GPU path
is `Obend.Hardware.Gpu`, run on the devices by `hardware/gpu/verify_gpu.sh`.

1. **Ozaki Scheme I/II with Base-13 `FP4 (E2M1)` limbs (`arXiv:2608.06812`, Hayashi et al. 2026)**:
   the 15-element doubled `FP4 (E2M1)` set $S_{\text{E2M1}} = \{0, \pm 1, \pm 2, \pm 3, \pm 4, \pm 6, \pm 8, \pm 12\}$,
   the base-13 digit decomposition $d = r + 13 q$ (`encodeBase13Fp4Digit`,
   `ozaki_fp4_base13_covers_all_25_digits`), and the exactness of limb products and $K$-limb dot
   products in an integer accumulator (`ozaki_base13_2limb_product_exact`, `ozaki_base13_klimb_mul_exact`,
   `ozaki_base13_klimb_dot_exact`): polynomial identities in the limbs.
2. **OCP Microscaling (`MXFP`) blocks and the Kulisch accumulator (`arXiv:2607.13898`)**: block-scaled
   vectors sharing an `E8M0` exponent, and `kulisch_dot_append_exact`, that a dot product split across
   sub-blocks and summed in a wide accumulator is the whole dot product: a fold identity.
3. **Interval enclosure for rounded addition (`arXiv:2510.16028`, `arXiv:2610.24548`)**: `FloatInterval`
   and `interval_add_encloses_true_sum`, over `Int` bounds with an ulp slack.
4. **Systolic chain and `DSP58` cascade folds**: `runSystolicMacChain`, `runDsp58Cascade` and
   `systolic_tpu_eq_dsp58_cascade_eq_kulisch_dot`, three folds over `Int` lists being the same fold.
-/
public import Obend.Hardware.Thermal
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.Accelerators
open Obend.Hardware.Thermal
open Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Ozaki Scheme I/II with Base-13 `FP4 (E2M1)` Limb Representation (`arXiv:2608.06812`) -/

/-- Exact 15-element set of doubled `FP4 (E2M1)` numbers (`2 * (±2^{E-1} * (1 + M/2))` plus subnormals):
$$S_{\text{E2M1}} = \{0, \pm 1, \pm 2, \pm 3, \pm 4, \pm 6, \pm 8, \pm 12\}.$$
Every value in $S_{\text{E2M1}}$ is bit-exactly representable in 4-bit `E2M1` Tensor Cores! -/
def isDoubledFp4E2M1 (r : Int) : Bool :=
  r == 0 ||
  r == 1  || r == -1 ||
  r == 2  || r == -2 ||
  r == 3  || r == -3 ||
  r == 4  || r == -4 ||
  r == 6  || r == -6 ||
  r == 8  || r == -8 ||
  r == 12 || r == -12

/-- Decompose any integer $d \in [-12, 12]$ into a pair `(r, q)` where `r` is a doubled `FP4 (E2M1)`
value (`isDoubledFp4E2M1 r = true`), `q ∈ {-1, 0, 1}`, and $d = r + 13 \cdot q$
(Fig. 1 of Hayashi et al., `arXiv:2608.06812`). -/
def encodeBase13Fp4Digit (d : Int) : Int × Int :=
  if isDoubledFp4E2M1 d then (d, 0)
  else if d == 5  then (-8, 1)
  else if d == 7  then (-6, 1)
  else if d == 9  then (-4, 1)
  else if d == 10 then (-3, 1)
  else if d == 11 then (-2, 1)
  else if d == -5  then (8, -1)
  else if d == -7  then (6, -1)
  else if d == -9  then (4, -1)
  else if d == -10 then (3, -1)
  else if d == -11 then (2, -1)
  else (0, 0)

/-- Check that `encodeBase13Fp4Digit d` produces a valid doubled `FP4 (E2M1)` limb `r` and shift `q`
that reconstruct `d = r + 13 * q` without error. -/
def checkBase13Fp4DigitValid (d : Int) : Bool :=
  let (r, q) := encodeBase13Fp4Digit d
  isDoubledFp4E2M1 r && decide (-1 ≤ q ∧ q ≤ 1) && decide (r + 13 * q = d)

/-- All 25 integers in the symmetric base-13 range $[-12, 12]$. -/
def allBase13Digits : List Int :=
  [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1,
    0,   1,   2,   3,  4,  5,  6,  7,  8,  9, 10, 11, 12]

/-- **Hayashi–Mukunoki–Hoshino–Katagiri Base-13 `FP4` Coverage Theorem (`ozaki_fp4_base13_covers_all_25_digits`)**:
Every integer in $[-12, 12]$ is decomposed error-free into a doubled `FP4 (E2M1)` value $r \in S_{\text{E2M1}}$
plus a multiple of $13$ ($q \in \{-1, 0, 1\}$) such that $r + 13 q = d$. -/
-- fixture kept (2026-11-04): exhaustive over the 25 base-13 FP4 digits: this is the whole statement, decided
example :
    allBase13Digits.all checkBase13Fp4DigitValid = true := by
  decide +kernel

/-- Evaluate a 2-limb base-13 integer $a_0 + 13 a_1$. -/
def evalBase13Limb2 (a0 a1 : Int) : Int :=
  a0 + 13 * a1

/-- Reconstruct the product of two 2-limb base-13 numbers from four `FP4` Tensor-Core partial products
$(a_0 b_0,\, a_0 b_1,\, a_1 b_0,\, a_1 b_1)$ accumulated in an exact `FP32` / Kulisch integer accumulator. -/
def evalOzakiBase13Product2 (a0 a1 b0 b1 : Int) : Int :=
  (a0 * b0) + 13 * (a0 * b1 + a1 * b0) + 169 * (a1 * b1)

/-- **Universal 2-Limb Base-13 Ozaki Error-Free Product Theorem (`ozaki_base13_2limb_product_exact`)**:
For ALL limbs `a0, a1, b0, b1 : Int`, the Ozaki 4-product base-13 accumulation `evalOzakiBase13Product2`
is algebraically identical to the exact integer product `(a0 + 13 * a1) * (b0 + 13 * b1)` with
zero intermediate rounding error! -/
theorem ozaki_base13_2limb_product_exact (a0 a1 b0 b1 : Int) :
    evalOzakiBase13Product2 a0 a1 b0 b1 =
      evalBase13Limb2 a0 a1 * evalBase13Limb2 b0 b1 := by
  dsimp only [evalOzakiBase13Product2, evalBase13Limb2]
  rw [Int.add_mul, Int.mul_add a0 b0 (13 * b1), Int.mul_add (13 * a1) b0 (13 * b1)]
  have h1 : a0 * (13 * b1) = 13 * (a0 * b1) := by
    rw [← Int.mul_assoc a0 13 b1, Int.mul_comm a0 13, Int.mul_assoc 13 a0 b1]
  have h2 : 13 * a1 * b0 = 13 * (a1 * b0) := by
    rw [Int.mul_assoc 13 a1 b0]
  have h3 : 13 * a1 * (13 * b1) = 169 * (a1 * b1) := by
    have hSub : 13 * a1 * (13 * b1) = (13 * 13) * (a1 * b1) := by
      rw [Int.mul_assoc 13 a1 (13 * b1), ← Int.mul_assoc a1 13 b1,
          Int.mul_comm a1 13, Int.mul_assoc 13 a1 b1, ← Int.mul_assoc 13 13 (a1 * b1)]
    exact hSub
  rw [h1, h2, h3, Int.mul_add 13 (a0 * b1) (a1 * b0)]
  omega

/-- Evaluate an arbitrary $K$-limb base-13 integer $\sum_{k=0}^{K-1} a_k \cdot 13^k$
(little-endian limb list `a_0 :: a_1 :: ...`). -/
def evalBase13Limbs : List Int → Int
  | [] => 0
  | a :: rest => a + 13 * evalBase13Limbs rest

/-- Scale every limb of a $K$-limb base-13 representation by scalar `c : Int`. -/
def scaleBase13Limbs (c : Int) : List Int → List Int
  | [] => []
  | a :: rest => (c * a) :: scaleBase13Limbs c rest

/-- Limbwise addition of two multi-limb base-13 representations (without carry propagation,
accumulating in wide Kulisch/FP32 limbs). -/
def addBase13Limbs : List Int → List Int → List Int
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addBase13Limbs as bs

/-- Cauchy convolution of two multi-limb base-13 representations (`arXiv:2608.06812` §III):
computes all $K_A \times K_B$ `FP4 (E2M1)` Tensor-Core limb products and accumulates them by radix-13 degree. -/
def mulBase13Limbs : List Int → List Int → List Int
  | [], _ => []
  | a :: as, bs => addBase13Limbs (scaleBase13Limbs a bs) (0 :: mulBase13Limbs as bs)

/-- Check that every limb in a $K$-limb representation is a valid doubled `FP4 (E2M1)` value in $S_{\text{E2M1}}$. -/
def allLimbsDoubledFp4 (limbs : List Int) : Bool :=
  limbs.all isDoubledFp4E2M1

/-- **Universal $K$-Limb Base-13 Limbwise Addition Exactness (`evalBase13Limbs_add_exact`)**:
Evaluating the limbwise sum `addBase13Limbs as bs` equals `evalBase13Limbs as + evalBase13Limbs bs`
for all limb lists `as, bs : List Int`. -/
theorem evalBase13Limbs_add_exact (as bs : List Int) :
    evalBase13Limbs (addBase13Limbs as bs) =
      evalBase13Limbs as + evalBase13Limbs bs := by
  induction as generalizing bs with
  | nil =>
    simp [addBase13Limbs, evalBase13Limbs]
  | cons a restA ih =>
    cases bs with
    | nil =>
      simp [addBase13Limbs, evalBase13Limbs]
    | cons b restB =>
      dsimp only [addBase13Limbs, evalBase13Limbs]
      rw [ih restB]
      omega

/-- **Universal $K$-Limb Base-13 Scalar Scaling Exactness (`evalBase13Limbs_scale_exact`)**:
Scaling every limb of `as` by `c` scales its base-13 value by `c` (`c * evalBase13Limbs as`). -/
theorem evalBase13Limbs_scale_exact (c : Int) (as : List Int) :
    evalBase13Limbs (scaleBase13Limbs c as) = c * evalBase13Limbs as := by
  induction as with
  | nil =>
    simp [scaleBase13Limbs, evalBase13Limbs]
  | cons a rest ih =>
    dsimp only [scaleBase13Limbs, evalBase13Limbs]
    rw [ih, Int.mul_add]
    have hAssoc : 13 * (c * evalBase13Limbs rest) = c * (13 * evalBase13Limbs rest) := by
      rw [← Int.mul_assoc 13 c, Int.mul_comm 13 c, Int.mul_assoc c 13]
    rw [hAssoc]

/-- **Universal $K$-Limb Ozaki Base-13 Cauchy Convolution Exactness (`ozaki_base13_klimb_mul_exact`)**:
For ANY two arbitrary-length limb lists `as, bs : List Int`, evaluating their Cauchy limb convolution
`mulBase13Limbs as bs` reproduces the exact integer product `evalBase13Limbs as * evalBase13Limbs bs`
with zero intermediate truncation or rounding error! -/
theorem ozaki_base13_klimb_mul_exact (as bs : List Int) :
    evalBase13Limbs (mulBase13Limbs as bs) =
      evalBase13Limbs as * evalBase13Limbs bs := by
  induction as with
  | nil =>
    simp [mulBase13Limbs, evalBase13Limbs]
  | cons a restA ih =>
    dsimp only [mulBase13Limbs, evalBase13Limbs]
    rw [evalBase13Limbs_add_exact, evalBase13Limbs_scale_exact]
    dsimp only [evalBase13Limbs]
    rw [ih, Int.zero_add, Int.add_mul]
    have hAssoc : 13 * (evalBase13Limbs restA * evalBase13Limbs bs) =
        13 * evalBase13Limbs restA * evalBase13Limbs bs := by
      rw [Int.mul_assoc]
    rw [hAssoc]

/-! ## 2. OCP Microscaling (`MXFP`) Block-Floating-Point & Kulisch Exact Accumulator (`arXiv:2607.13898`) -/

/-- A Microscaling (`MXFP8` / `MXFP6` / `MXFP4`) block sharing an 8-bit unsigned `E8M0` scale exponent
(`bias = 127`) across a vector of integer-aligned mantissa significands. -/
structure MxfpBlock where
  scaleExpE8M0 : Nat
  significands : List Int
  deriving DecidableEq, Repr

/-- Wide fixed-point **Kulisch exact dot-product accumulator** (`arXiv:2607.13898` §II-B):
computes $\sum_i x_i y_i$ without intermediate rounding or truncation. -/
def kulischDot : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + kulischDot xs ys

/-- Evaluate an `MXFP` block dot product returning `(mantissaSum, combinedExponentBiasAdjusted)`
where the combined scale exponent is $X_a + X_b - 254$ (`arXiv:2607.13898` §II-A). -/
def evalMxfpBlockDot (blkA blkB : MxfpBlock) : Int × Int :=
  ( kulischDot blkA.significands blkB.significands
  , Int.ofNat blkA.scaleExpE8M0 + Int.ofNat blkB.scaleExpE8M0 - 254 )

/-- **Universal Kulisch Block-Partitioning Exactness Theorem (`kulisch_dot_append_exact`)**:
Splitting a long dot product across sub-blocks `(xs1, ys1)` and `(xs2, ys2)` of equal length
and summing their wide Kulisch accumulators yields the exact same integer as the monolithic
dot product `kulischDot (xs1 ++ xs2) (ys1 ++ ys2)` (eliminating floating-point non-associativity!). -/
theorem kulisch_dot_append_exact
    (xs1 xs2 ys1 ys2 : List Int)
    (hLen : xs1.length = ys1.length) :
    kulischDot (xs1 ++ xs2) (ys1 ++ ys2) =
      kulischDot xs1 ys1 + kulischDot xs2 ys2 := by
  induction xs1 generalizing ys1 with
  | nil =>
    cases ys1 with
    | nil =>
      simp [kulischDot]
    | cons _ _ =>
      contradiction
  | cons x restX ih =>
    cases ys1 with
    | nil =>
      contradiction
    | cons y restY =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      have hSub := ih restY hLen
      simp only [List.cons_append, kulischDot]
      omega

/-- Limbwise Cauchy inner-product accumulator over two vectors of $K$-limb base-13 numbers:
accumulates the Cauchy convolution `mulBase13Limbs x y` across all vector positions without
collapsing limbs until final reduction. -/
def accumOzakiBase13KLimbDot : List (List Int) → List (List Int) → List Int
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => addBase13Limbs (mulBase13Limbs x y) (accumOzakiBase13KLimbDot xs ys)

/-- Multi-limb ($K$-limb) Ozaki Base-13 `FP4` Tensor-Core inner product (`arXiv:2608.06812` §III):
evaluates the limbwise Cauchy dot-product accumulation `accumOzakiBase13KLimbDot xs ys` in a
wide Kulisch accumulator. -/
def evalOzakiBase13KLimbDot (xs ys : List (List Int)) : Int :=
  evalBase13Limbs (accumOzakiBase13KLimbDot xs ys)

/-- **Universal $K$-Limb Ozaki Base-13 Inner-Product Exactness (`ozaki_base13_klimb_dot_exact`)**:
For ANY two vectors of $K$-limb base-13 representations `xs, ys : List (List Int)`, the multi-limb
Tensor-Core inner product `evalOzakiBase13KLimbDot xs ys` equals the exact Kulisch wide inner
product `kulischDot (xs.map evalBase13Limbs) (ys.map evalBase13Limbs)` with zero intermediate
rounding error! -/
theorem ozaki_base13_klimb_dot_exact (xs ys : List (List Int)) :
    evalOzakiBase13KLimbDot xs ys =
      kulischDot (xs.map evalBase13Limbs) (ys.map evalBase13Limbs) := by
  induction xs generalizing ys with
  | nil =>
    simp [evalOzakiBase13KLimbDot, accumOzakiBase13KLimbDot, evalBase13Limbs, kulischDot]
  | cons x restX ih =>
    cases ys with
    | nil =>
      simp [evalOzakiBase13KLimbDot, accumOzakiBase13KLimbDot, evalBase13Limbs, kulischDot]
    | cons y restY =>
      unfold evalOzakiBase13KLimbDot at *
      dsimp only [accumOzakiBase13KLimbDot, List.map, kulischDot]
      rw [evalBase13Limbs_add_exact, ozaki_base13_klimb_mul_exact, ih restY]

/-! ## 3. IEEE-754 / TAO Operator Rounding Interval Enclosure (`arXiv:2510.16028` & `arXiv:2610.24548`) -/

/-- Certified interval enclosure `[lo, hi]` bounding floating-point rounding drift across
heterogeneous GPU/TPU/FPGA operators (`arXiv:2510.16028`). -/
structure FloatInterval where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

/-- Membership of a scalar value `x` inside interval `iv` (`iv.lo ≤ x ∧ x ≤ iv.hi`). -/
def FloatInterval.contains (iv : FloatInterval) (x : Int) : Prop :=
  iv.lo ≤ x ∧ x ≤ iv.hi

/-- Interval addition with outward rounding slack `ulpSlack ≥ 0`. -/
def intervalAddWithUlp (a b : FloatInterval) (ulpSlack : Int) : FloatInterval where
  lo := a.lo + b.lo - ulpSlack
  hi := a.hi + b.hi + ulpSlack

/-- **Universal Interval Enclosure Soundness (`interval_add_encloses_true_sum`)**:
If `a` encloses `x`, `b` encloses `y`, and hardware rounding error `err` satisfies `|err| ≤ ulpSlack`
(`-ulpSlack ≤ err ∧ err ≤ ulpSlack`), then `intervalAddWithUlp a b ulpSlack` rigorously encloses
the rounded hardware sum `x + y + err`! -/
theorem interval_add_encloses_true_sum
    (a b : FloatInterval) (x y err ulpSlack : Int)
    (hx : a.contains x)
    (hy : b.contains y)
    (hErrLo : -ulpSlack ≤ err)
    (hErrHi : err ≤ ulpSlack) :
    (intervalAddWithUlp a b ulpSlack).contains (x + y + err) := by
  rcases hx with ⟨hxLo, hxHi⟩
  rcases hy with ⟨hyLo, hyHi⟩
  dsimp only [FloatInterval.contains, intervalAddWithUlp]
  constructor <;> omega

/-! ## 4. 2D Systolic Array TPU & FPGA `DSP58` `PCIN -> PCOUT` Hardware Cascade -/

/-- Single Processing Element (PE) step in a TPU Systolic Array:
receives partial sum `psumIn`, weight `w`, and activation `act`, emitting `psumOut = psumIn + w * act`. -/
def stepSystolicPe (psumIn w act : Int) : Int :=
  psumIn + w * act

/-- Execute a systolic array PE chain over weight stream `ws` and activation stream `acts`
starting from initial partial sum `psumIn`. -/
def runSystolicMacChain (psumIn : Int) : List Int → List Int → Int
  | [], _ => psumIn
  | _, [] => psumIn
  | w :: ws, a :: as_ => runSystolicMacChain (stepSystolicPe psumIn w a) ws as_

/-- Dedicated FPGA `DSP58` / `DSP48E2` `PCIN -> PCOUT` hardware cascade chain:
each DSP slice computes `PCOUT_k = PCIN_k + A_k * B_k` over dedicated silicon cascade wires without
fabric LUT routing. -/
def runDsp58Cascade (pcin : Int) : List (Int × Int) → Int
  | [] => pcin
  | (a, b) :: rest => runDsp58Cascade (pcin + a * b) rest

/-- **Universal Systolic TPU vs. Kulisch Dot Equivalence (`systolic_tpu_eq_kulisch_dot`)**:
For ANY initial partial sum `psumIn : Int` and ANY streams `ws, acts : List Int`,
the TPU systolic PE chain computes `psumIn + kulischDot ws acts` identically! -/
theorem systolic_tpu_eq_kulisch_dot (psumIn : Int) (ws acts : List Int) :
    runSystolicMacChain psumIn ws acts = psumIn + kulischDot ws acts := by
  induction ws generalizing psumIn acts with
  | nil =>
    simp [runSystolicMacChain, kulischDot]
  | cons w restW ih =>
    cases acts with
    | nil =>
      simp [runSystolicMacChain, kulischDot]
    | cons a restA =>
      dsimp only [runSystolicMacChain, stepSystolicPe, kulischDot]
      rw [ih (psumIn + w * a) restA]
      omega

/-- **Universal FPGA `DSP58` Cascade vs. Systolic TPU Equivalence (`dsp58_cascade_eq_systolic_tpu`)**:
For ANY initial cascade input `pcin : Int` and ANY streams `ws, acts : List Int`,
`runDsp58Cascade pcin (ws.zip acts)` equals `runSystolicMacChain pcin ws acts` identically! -/
theorem dsp58_cascade_eq_systolic_tpu (pcin : Int) (ws acts : List Int) :
    runDsp58Cascade pcin (ws.zip acts) = runSystolicMacChain pcin ws acts := by
  induction ws generalizing pcin acts with
  | nil =>
    simp [List.zip, runDsp58Cascade, runSystolicMacChain]
  | cons w restW ih =>
    cases acts with
    | nil =>
      simp [List.zip, runDsp58Cascade, runSystolicMacChain]
    | cons a restA =>
      dsimp only [List.zip, List.zipWith, runDsp58Cascade, runSystolicMacChain, stepSystolicPe]
      exact ih (pcin + w * a) restA

/-- **Master 3-Way Hardware Accelerator Equivalence (`systolic_tpu_eq_dsp58_cascade_eq_kulisch_dot`)**:
The TPU Systolic Array PE chain, the FPGA `DSP58` `PCIN -> PCOUT` cascade, and the exact Kulisch
wide accumulator `pcin + kulischDot ws acts` agree bit-for-bit across all inputs! -/
theorem systolic_tpu_eq_dsp58_cascade_eq_kulisch_dot (pcin : Int) (ws acts : List Int) :
    runDsp58Cascade pcin (ws.zip acts) = runSystolicMacChain pcin ws acts ∧
    runSystolicMacChain pcin ws acts = pcin + kulischDot ws acts :=
  ⟨dsp58_cascade_eq_systolic_tpu pcin ws acts, systolic_tpu_eq_kulisch_dot pcin ws acts⟩

end Obend.Hardware.Accelerators
end
