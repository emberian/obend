module
public import Obend.Hardware.Tpu.Machine
import all Obend.Hardware.Tpu.Machine
public import Obend.Hardware.Gpu.NttDFTSpec
public import Obend.Crypto.PikkuFoldLayered
public import Obend.Crypto.DualSpine
import all Obend.Crypto.DualSpine
import all Obend.Judge.Computational

public section
namespace Obend.Hardware.Tpu
open Obend.Crypto Obend.Crypto.Fast Obend.Apps.ZkNtt
open Obend.Hardware.Gpu.Ntt

/-! Exact byte-plane arithmetic. All limb products use the same 128-deep
unsigned MXU dot operation as the machine. Recombination is a VPU-side integer
specification; each Horner step executes the machine's bounded VPU reducer.

The universal arithmetic and forward-DFT theorems below are kernel checked.
The instruction generators have concrete end-to-end machine tests; a general
simulation theorem for those instruction streams is still outstanding. The
external product uses a signed circulant lowering; a twist/NTT/inverse-NTT
lowering is also still outstanding.
-/

def byteLimb (x i : Nat) : Nat := x / 256^i % 256

def radixSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f 0 + 256 * radixSum n (fun i => f (i+1))

theorem byteLimb_lt (x i : Nat) : byteLimb x i < 256 := Nat.mod_lt _ (by decide)

theorem radixSum_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) : radixSum n f = radixSum n g := by
  induction n generalizing f g with
  | zero => simp [radixSum]
  | succ n ih =>
    simp only [radixSum]
    rw [h 0 (by omega), ih _ _ (fun i hi => h (i+1) (by omega))]

theorem byteLimb_div (x i : Nat) : byteLimb (x/256) i = byteLimb x (i+1) := by
  simp [byteLimb, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem radixSum_bytes (n x : Nat) (hx : x < 256^n) :
    radixSum n (byteLimb x) = x := by
  induction n generalizing x with
  | zero =>
    simp only [Nat.pow_zero] at hx
    have hx0 : x = 0 := by omega
    simp [radixSum, hx0]
  | succ n ih =>
    rw [radixSum]
    have hd : x / 256 < 256^n := by
      apply Nat.div_lt_of_lt_mul
      simpa only [Nat.pow_succ, Nat.mul_comm] using hx
    have he : (fun i => byteLimb x (i+1)) = byteLimb (x/256) := by
      funext i; exact (byteLimb_div x i).symm
    rw [he, ih _ hd]
    simpa [byteLimb] using Nat.mod_add_div x 256

theorem radixSum_mul_right (n : Nat) (f : Nat → Nat) (c : Nat) :
    radixSum n (fun i => f i * c) = radixSum n f * c := by
  induction n generalizing f with
  | zero => simp [radixSum]
  | succ n ih => simp only [radixSum, ih, Nat.add_mul, Nat.mul_assoc]

theorem radixSum_mul_left (n : Nat) (f : Nat → Nat) (c : Nat) :
    radixSum n (fun i => c * f i) = c * radixSum n f := by
  simpa only [Nat.mul_comm c] using radixSum_mul_right n f c

theorem radixSum_sum (n count : Nat) (f : Nat → Nat → Nat) :
    radixSum n (fun i => Sum.sum count (f i)) =
      Sum.sum count (fun k => radixSum n (fun i => f i k)) := by
  induction n generalizing f with
  | zero => simp [radixSum]
  | succ n ih =>
    simp only [radixSum, ih, Sum.add, Sum.mul_left]

theorem sum_bound (n bound : Nat) (f : Nat → Nat) (h : ∀ k, k < n → f k ≤ bound) :
    Sum.sum n f ≤ n * bound := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := ih (fun k hk => h k (by omega))
    have := h n (by omega)
    simp only [Sum.succ, Nat.succ_mul]; omega

theorem u8_mxu128_no_int32_overflow (a b : Nat → Nat)
    (ha : ∀ k, k < 128 → a k < 256) (hb : ∀ k, k < 128 → b k < 256) :
    Sum.sum 128 (fun k => a k * b k) ≤ 8323200 ∧
      8323200 < 2^23 ∧ 2^23 < 2^31-1 := by
  refine ⟨?_, by decide, by decide⟩
  apply sum_bound 128 (255*255)
  intro k hk
  exact Nat.mul_le_mul (by have := ha k hk; omega) (by have := hb k hk; omega)

/-- Every nonnegative partial sum in a u7 dot product fits within binary32's
24-bit significand. This theorem is an integer representability bound; the IEEE
rounding implementation is separately executable in Machine. -/
theorem u7_bf16_mxu128_exact (a b : Nat → Nat)
    (ha : ∀ k, k < 128 → a k < 128) (hb : ∀ k, k < 128 → b k < 128)
    (n : Nat) (hn : n ≤ 128) :
    Sum.sum n (fun k => a k * b k) ≤ 2064512 ∧
      2064512 < 2^21 ∧ 2^21 < 2^24 := by
  refine ⟨?_, by decide, by decide⟩
  have h := sum_bound n (127*127) (fun k => a k * b k) (by
    intro k hk
    exact Nat.mul_le_mul (by have := ha k (by omega); omega) (by have := hb k (by omega); omega))
  have := Nat.mul_le_mul_right (127*127) hn
  omega

theorem mxuDot_unsigned_exact (a b : Nat → UInt64) :
    (mxuDot .unsigned8 a b).toNat =
      Sum.sum 128 (fun k => (a k).toNat % 256 * ((b k).toNat % 256)) := by
  have h := u8_mxu128_no_int32_overflow
    (fun k => (a k).toNat % 256) (fun k => (b k).toNat % 256)
    (fun _ _ => Nat.mod_lt _ (by decide)) (fun _ _ => Nat.mod_lt _ (by decide))
  simp only [mxuDot, UInt32.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

def limbMxuDot (a b : Nat → Nat) (i j : Nat) : Nat :=
  (mxuDot .unsigned8 (fun k => UInt64.ofNat (byteLimb (a k) i))
    (fun k => UInt64.ofNat (byteLimb (b k) j))).toNat

theorem limbMxuDot_eq (a b : Nat → Nat) (i j : Nat) :
    limbMxuDot a b i j = Sum.sum 128 (fun k => byteLimb (a k) i * byteLimb (b k) j) := by
  unfold limbMxuDot
  rw [mxuDot_unsigned_exact]
  apply Sum.cong
  intro k _
  have ha := byteLimb_lt (a k) i
  have hb := byteLimb_lt (b k) j
  simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show byteLimb (a k) i < 2^64 by omega),
    Nat.mod_eq_of_lt (show byteLimb (b k) j < 2^64 by omega), Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

def vpuReduceNat (x : Nat) : Nat :=
  (evalVpu .goldilocksReduce (UInt64.ofNat (x%2^64)) (UInt64.ofNat (x/2^64))).toNat

theorem vpuReduceNat_eq (x : Nat) (hx : x < 2^128) :
    vpuReduceNat x = x % goldilocksPrime := by
  have hlo : x%2^64 < 2^64 := Nat.mod_lt _ (by decide)
  have hhi : x/2^64 < 2^64 := Nat.div_lt_of_lt_mul (by simpa using hx)
  have h := goldilocksReduce128Spec_sound hlo hhi
  simp only [vpuReduceNat, evalVpu, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h.1 (by decide)), h.2, Nat.mod_add_div]

def radixSumMod : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => vpuReduceNat (f 0 + 256 * radixSumMod n (fun i => f (i+1)))

theorem radixSumMod_eq (n : Nat) (f : Nat → Nat) (hf : ∀ i, i < n → f i < 2^64) :
    radixSumMod n f = radixSum n f % goldilocksPrime := by
  induction n generalizing f with
  | zero => simp [radixSumMod, radixSum]
  | succ n ih =>
    simp only [radixSumMod, radixSum]
    have ht := ih (fun i => f (i+1)) (fun i hi => hf (i+1) (by omega))
    have hm := Nat.mod_lt (radixSum n (fun i => f (i+1))) (by decide : 0 < goldilocksPrime)
    have hzero := hf 0 (by omega)
    have hwide : f 0 + 256 * radixSumMod n (fun i => f (i+1)) < 2^128 := by
      rw [ht]
      have hp : goldilocksPrime < 2^64 := by decide
      omega
    rw [vpuReduceNat_eq _ hwide, ht]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

private theorem radixSum_mod_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i % goldilocksPrime = g i % goldilocksPrime) :
    radixSum n f % goldilocksPrime = radixSum n g % goldilocksPrime := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [radixSum, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    rw [h 0 (by omega), ih _ _ (fun i hi => h (i+1) (by omega))]

def mxuGoldilocksDot (a b : Nat → Nat) : Nat :=
  radixSumMod 8 (fun i => radixSumMod 8 (fun j => limbMxuDot a b i j))

/-- All 64 limb-plane dot products are recombined through the machine's VPU
128-to-64 reduction. Every Horner intermediate fits below 2^128. -/
theorem mxuGoldilocksDot_eq (a b : Nat → Nat)
    (ha : ∀ k, k < 128 → a k < 2^64) (hb : ∀ k, k < 128 → b k < 2^64) :
    mxuGoldilocksDot a b = Sum.sum 128 (fun k => a k * b k) % goldilocksPrime := by
  have hl (i j : Nat) : limbMxuDot a b i j < 2^64 := by
    unfold limbMxuDot
    exact Nat.lt_trans (UInt32.toNat_lt _) (by decide)
  have hi (i : Nat) : radixSumMod 8 (fun j => limbMxuDot a b i j) =
      radixSum 8 (fun j => limbMxuDot a b i j) % goldilocksPrime :=
    radixSumMod_eq 8 _ (fun j _ => hl i j)
  unfold mxuGoldilocksDot
  rw [radixSumMod_eq 8 _ (by
    intro i _
    rw [hi]
    exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  have he := radixSum_mod_congr 8
    (fun i => radixSumMod 8 (fun j => limbMxuDot a b i j))
    (fun i => radixSum 8 (fun j => limbMxuDot a b i j))
    (fun i _ => by rw [hi]; exact Nat.mod_mod _ _)
  rw [he]
  simp only [limbMxuDot_eq, radixSum_sum]
  apply congrArg (fun x => x % goldilocksPrime)
  apply Sum.cong
  intro k hk
  simp only [radixSum_mul_left, radixSum_mul_right]
  rw [radixSum_bytes 8 (a k) (by simpa using ha k hk),
      radixSum_bytes 8 (b k) (by simpa using hb k hk)]


private theorem radixSumMod_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) : radixSumMod n f = radixSumMod n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [radixSumMod]
    rw [h 0 (by omega), ih _ _ (fun i hi => h (i+1) (by omega))]

/-- Materialize the 128 input coordinates once. Without this cache, composing
matrix transforms would reevaluate a whole preceding column per limb product. -/
def mxuGoldilocksDotExec (a b : Nat → Nat) : Nat :=
  let aa : Sized Nat 128 := Sized.ofFn (fun k => a k.val)
  let bb : Sized Nat 128 := Sized.ofFn (fun k => b k.val)
  radixSumMod 8 (fun i => radixSumMod 8 (fun j =>
    (mxuDot .unsigned8
      (fun k => UInt64.ofNat (byteLimb (aa.spec ⟨k%128, Nat.mod_lt _ (by decide)⟩) i))
      (fun k => UInt64.ofNat (byteLimb (bb.spec ⟨k%128, Nat.mod_lt _ (by decide)⟩) j))).toNat))

@[csimp] theorem mxuGoldilocksDot_eq_exec : @mxuGoldilocksDot = @mxuGoldilocksDotExec := by
  funext a b
  unfold mxuGoldilocksDot mxuGoldilocksDotExec
  apply radixSumMod_congr
  intro i _
  apply radixSumMod_congr
  intro j _
  unfold limbMxuDot
  rw [mxuDot_unsigned_exact, mxuDot_unsigned_exact]
  apply Sum.cong
  intro k hk
  simp only [Sized.spec_ofFn, Nat.mod_eq_of_lt hk]

def mxuGoldilocksGemm (a b : Tile) : Tile :=
  Sized.ofFn fun ij => UInt64.ofNat (mxuGoldilocksDot
    (fun k => a.coeffs[ij.val / 128 * 128 + k]!.toNat)
    (fun k => b.coeffs[k * 128 + ij.val % 128]!.toNat))

def specMatMul (a b : Tile) (r c : Fin 128) : Nat :=
  Sum.sum 128 (fun k => a.coeffs[r.val*128+k]!.toNat * b.coeffs[k*128+c.val]!.toNat) % goldilocksPrime

theorem mxuGoldilocksGemm_eq_specMatMul (a b : Tile) (r c : Fin 128) :
    (tileAt (mxuGoldilocksGemm a b) r c).toNat = specMatMul a b r c := by
  have hr := r.isLt
  have hc := c.isLt
  have hd : (r.val*128+c.val)/128 = r.val := by omega
  have hm : (r.val*128+c.val)%128 = c.val := by omega
  simp only [tileAt, mxuGoldilocksGemm, Sized.spec_ofFn, hd, hm, UInt64.toNat_ofNat']
  rw [mxuGoldilocksDot_eq _ _ (fun _ _ => UInt64.toNat_lt _) (fun _ _ => UInt64.toNat_lt _)]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

/-! Bailey factorization uses input j=r*C+c and output k=u+R*v.
The first transform runs down r, the twiddle is w^(c*u), and the second runs
down c. Transposes are explicit changes of array indexing, not extra DFTs. -/

private theorem sum_pad (n m : Nat) (hn : n ≤ m) (f : Nat → Nat) :
    Sum.sum m (fun i => if i < n then f i else 0) = Sum.sum n f := by
  induction m generalizing n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm : n ≤ m
    · rw [Sum.succ, ih n hnm]
      simp [show ¬m < n by omega]
    · have hnEq : n = m+1 := by omega
      subst n
      apply Sum.cong
      intro i hi
      simp only [hi, ↓reduceIte]

/-- A transform column is a zero-padded 128-deep integer MXU dot, with eight
byte planes and VPU reduction, rather than a call to the reference DFT. -/
def mxuDft (n root : Nat) (input : Nat → Nat) (k : Nat) : Nat :=
  mxuGoldilocksDot (fun i => if i < n then input i % goldilocksPrime else 0)
    (fun i => modPow root (i*k))

theorem mxuDft_eq_dft (n root : Nat) (input : Nat → Nat) (k : Nat) (hn : n ≤ 128) :
    mxuDft n root input k = dft n root input k := by
  unfold mxuDft
  rw [mxuGoldilocksDot_eq _ _ (by
    intro i _
    split
    · exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    · decide) (by
    intro i _
    rw [modPow_eq]
    exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  have hs := Sum.cong 128
    (fun i => (if i < n then input i % goldilocksPrime else 0) * modPow root (i*k))
    (fun i => if i < n then input i % goldilocksPrime * modPow root (i*k) else 0)
    (by intro i _; split <;> simp_all)
  rw [hs, sum_pad n 128 hn]
  unfold dft sumMod
  apply Sum.cong_mod
  intro i _
  exact Nat.mod_mul_mod _ _ _


/-- Matrix-index form of the XLU transpose; tileAt_transpose is its hardware
refinement for a physical 128×128 tile. -/
def matrixTranspose {α : Type} (m : Nat → Nat → α) : Nat → Nat → α := fun i j => m j i

def baileyColumn (r c root : Nat) (input : Nat → Nat) (u j : Nat) : Nat :=
  mxuDft r (modPow root c) (fun i => input (i*c+j)) u

def baileyMxuNtt (r c root : Nat) (input : Nat → Nat) (u v : Nat) : Nat :=
  let first := matrixTranspose (baileyColumn r c root input)
  let twiddled := fun j k => mulMod (first j k) (modPow root (j*k))
  let second := fun k j => mxuDft c (modPow root r) (fun i => twiddled i j) k
  matrixTranspose second u v

private theorem bailey_phase (r c root i j u v : Nat) (period : modPow root (r*c) = 1) :
    modPow root ((i*c+j)*(u+r*v)) =
      mulMod (mulMod (modPow (modPow root c) (i*u)) (modPow root (j*u)))
        (modPow (modPow root r) (j*v)) := by
  have he : (i*c+j)*(u+r*v) = (c*(i*u)+j*u+r*(j*v))+(r*c)*(i*v) := by
    simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [he, modPow_add, modPow_mul root (r*c), period, modPow_one_base]
  simp only [Nat.mul_one]
  rw [modPow_add, modPow_add]
  simp only [modPow_mul, mulMod, Nat.mod_mod]

/-- Exact equality to the shared textbook DFT for every factorization and every
root with the stated period. Primitivity is needed for inversion, not this
forward-transform factorization. -/
theorem baileyMxuNtt_eq_specNtt (r c root : Nat) (input : Nat → Nat) (u v : Nat)
    (period : modPow root (r*c) = 1) (hr : r ≤ 128) (hc : c ≤ 128) :
    baileyMxuNtt r c root input u v = dft (r*c) root input (u+r*v) := by
  unfold baileyMxuNtt matrixTranspose
  dsimp only
  rw [mxuDft_eq_dft _ _ _ _ hc]
  simp only [baileyColumn, mxuDft_eq_dft r _ _ _ hr]
  unfold dft sumMod
  simp only [mulMod, Nat.mod_mul_mod, Nat.mod_mul_mod]
  rw [Sum.blocks, Obend.Hardware.Gpu.Ntt.Sum.swap r c]
  apply Sum.cong_mod
  intro j _
  simp only [Nat.mul_assoc, Nat.mod_mul_mod]
  rw [← Sum.mul_right]
  apply Sum.cong_mod
  intro i _
  rw [bailey_phase r c root i j u v period]
  simp [mulMod, Nat.mul_assoc]


inductive Ternary where
  | neg | zero | pos
  deriving DecidableEq, BEq, Repr

def ternaryInt : Ternary → Int
  | .neg => -1 | .zero => 0 | .pos => 1

def ternaryByte : Ternary → UInt64
  | .neg => 255 | .zero => 0 | .pos => 1

theorem signedByte_ternary (t : Ternary) : signedByte (ternaryByte t) = ternaryInt t := by
  cases t <;> decide

def centeredByte (x : Nat) : UInt64 := UInt64.ofNat ((x+128)%256)

theorem signedByte_centered (x : Nat) (hx : x < 256) :
    signedByte (centeredByte x) = (x : Int)-128 := by
  have hm : (x+128)%256 < 256 := Nat.mod_lt _ (by decide)
  simp only [centeredByte, signedByte, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show (x+128)%256 < 2^64 by omega), Nat.mod_eq_of_lt hm]
  split <;> omega

theorem signedByte_bound (x : UInt64) : (signedByte x).natAbs ≤ 128 := by
  have hm := Nat.mod_lt x.toNat (by decide : 0 < 256)
  unfold signedByte
  dsimp only
  split <;> omega

theorem mxuDot_signed_exact (a b : Nat → UInt64) :
    (mxuDot .signed8 a b).toInt32.toInt = sumInt 128 (fun k => signedByte (a k) * signedByte (b k)) := by
  have h := sumInt_bound 128 (128*128) (fun k => signedByte (a k) * signedByte (b k)) (by
    intro k _
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (signedByte_bound _) (signedByte_bound _))
  simp only [mxuDot, Int32.toInt32_toUInt32]
  apply Int32.toInt_ofInt_of_le <;> omega

/-- One signed MXU pass per unsigned witness byte. Recentring avoids interpreting
128..255 as negative witness values; the VPU adds 128 times the row sum back. -/
def mxuTernaryByteDot (a : Nat → Ternary) (b : Nat → Nat) : Int :=
  (mxuDot .signed8 (fun k => ternaryByte (a k)) (fun k => centeredByte (b k))).toInt32.toInt +
    128 * sumInt 128 (fun k => ternaryInt (a k))

theorem mxuTernaryByteDot_eq (a : Nat → Ternary) (b : Nat → Nat)
    (hb : ∀ k, k < 128 → b k < 256) :
    mxuTernaryByteDot a b = sumInt 128 (fun k => ternaryInt (a k) * (b k : Int)) := by
  unfold mxuTernaryByteDot
  rw [mxuDot_signed_exact, ← sumInt_mul, ← sumInt_add]
  apply sumInt_congr
  intro k hk
  rw [signedByte_ternary, signedByte_centered _ (hb k hk)]
  simp [Int.sub_mul, Int.mul_comm]

/-- Dense ternary projection with exact dimensions, connected to the existing
PikkuFold matrix-vector specification. Large witnesses are processed bytewise
by mxuTernaryByteDot and recombined outside the int32 accumulator. -/
def ternaryMatrix {rows : Nat} (a : Fin rows → Nat → Ternary) : IntMatrix rows 128 :=
  Sized.ofFn fun r => Sized.ofFn fun k => ternaryInt (a r k.val)

def mxuTernaryProjection {rows : Nat} (a : Fin rows → Nat → Ternary)
    (w : Sized UInt8 128) : FastIntPoly rows :=
  Sized.ofFn fun r => mxuTernaryByteDot (a r) (fun k => w.coeffs[k]!.toNat)

theorem mxuTernaryProjection_eq_matVec {rows : Nat} (a : Fin rows → Nat → Ternary)
    (w : Sized UInt8 128) :
    mxuTernaryProjection a w = matVec (ternaryMatrix a)
      (Sized.ofFn fun k => (w.spec k).toNat) := by
  apply Sized.ext
  funext r
  simp only [mxuTernaryProjection, matVec, Sized.spec_ofFn]
  rw [mxuTernaryByteDot_eq _ _ (fun _ _ => UInt8.toNat_lt _)]
  unfold dot
  apply sumInt_congr
  intro k hk
  simp only [hk, ↓reduceDIte, ternaryMatrix, Sized.spec_ofFn]
  have hw : k < w.coeffs.size := by rw [w.size_eq]; exact hk
  simp [Sized.spec, getElem!_pos, hw]



def ternaryAjtaiParams (rows : List (Nat → Ternary)) (q : Nat)
    (hr : 0 < rows.length) (hq : 0 < q) : AjtaiParams where
  rows := rows.length
  cols := 128
  rows_pos := hr
  modulus := q
  modulus_pos := hq
  matrix := rows.map (fun row => (List.range 128).map (fun i => ternaryInt (row i)))
  matrix_rows := by simp
  matrix_cols := by
    intro row hrow
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hrow
    simp

def byteWitness (w : Nat → UInt8) : List Int :=
  (List.range 128).map (fun i => (w i).toNat)

def mxuTernaryAjtai (rows : List (Nat → Ternary)) (q : Nat) (w : Nat → UInt8) : List Int :=
  rows.map (fun row => mxuTernaryByteDot row (fun i => (w i).toNat) % (q : Int))

private theorem dotProd_map (xs : List Nat) (f g : Nat → Int) :
    Obend.Judge.Computational.dotProd (xs.map f) (xs.map g) =
      (xs.map (fun i => f i * g i)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Obend.Judge.Computational.dotProd, ih]

private theorem sumInt_list_range (n : Nat) (f : Nat → Int) :
    ((List.range n).map f).sum = sumInt n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, ih, sumInt]

/-- The target is DualSpine's actual Ajtai commitment, with an arbitrary positive
lattice modulus. Each row executes a single signed MXU pass for this witness
byte, including the correction for values in 128..255. -/
theorem mxuTernaryAjtai_eq_ajtaiCommit (rows : List (Nat → Ternary)) (q : Nat)
    (hr : 0 < rows.length) (hq : 0 < q) (w : Nat → UInt8) :
    mxuTernaryAjtai rows q w =
      ajtaiCommit (ternaryAjtaiParams rows q hr hq) (byteWitness w)
        (by simp [ternaryAjtaiParams, byteWitness]) := by
  unfold mxuTernaryAjtai ajtaiCommit ajtaiCommitRaw
  rw [mapRowsDot_eq_matVecMul]
  simp only [ternaryAjtaiParams, Obend.Judge.Computational.matVecMul, List.map_map]
  apply congrArg (fun f => rows.map f)
  funext row
  simp only [Function.comp_def, byteWitness, dotProd_map, sumInt_list_range]
  rw [mxuTernaryByteDot_eq _ _ (fun _ _ => UInt8.toNat_lt _)]

/-- Negacyclic multiplication is a signed circulant matrix-vector product.
The wrap sign implements X^128=-1 and is independent of gadget decomposition. -/
def negacyclicCoefficient (b : Fin 128 → Goldilocks) (k : Fin 128) (i : Nat) : Nat :=
  let value := (b ⟨(k.val+128-i)%128, Nat.mod_lt _ (by decide)⟩).val
  if i ≤ k.val then value else goldilocksPrime-value

def mxuRlweExternalProduct (a b : Fin 128 → Goldilocks) (k : Fin 128) : Nat :=
  mxuGoldilocksDot (fun i => (a ⟨i%128, Nat.mod_lt _ (by decide)⟩).val)
    (negacyclicCoefficient b k)

def polyMul (a b : Fin 128 → Goldilocks) (k : Fin 128) : Int :=
  negacyclicSpec (fun i => (a i).val) (fun i => (b i).val) k % goldP

private theorem sum_nat_int (n : Nat) (f : Nat → Nat) :
    (Sum.sum n f : Int) = sumInt n (fun i => (f i : Int)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Sum.succ, sumInt, ih]

private theorem sumInt_mod_congr (n : Nat) (q : Int) (f g : Nat → Int)
    (h : ∀ i, i < n → f i % q = g i % q) : sumInt n f % q = sumInt n g % q := by
  calc
    sumInt n f % q = sumInt n (fun i => f i % q) % q := (sumInt_mod n q f).symm
    _ = sumInt n (fun i => g i % q) % q := congrArg (fun x => x % q) (sumInt_congr h)
    _ = sumInt n g % q := sumInt_mod n q g

/-- Exact gadget-plane MXU lowering of a negacyclic product. The right-hand side
is the existing signed integer polynomial specification, reduced modulo p.
This is the circulant lowering, not a claim about an inverse-NTT implementation. -/
theorem mxuRlweExternalProduct_eq_polyMul (a b : Fin 128 → Goldilocks) (k : Fin 128) :
    (mxuRlweExternalProduct a b k : Int) = polyMul a b k := by
  unfold mxuRlweExternalProduct
  rw [mxuGoldilocksDot_eq _ _ (fun _ _ => Goldilocks.val_lt_two_pow_64 _) (by
    intro i _
    unfold negacyclicCoefficient
    dsimp only
    have h := (b ⟨(k.val+128-i)%128, Nat.mod_lt _ (by decide)⟩).isLt
    have hp : goldilocksPrime < 2^64 := by decide
    split <;> omega)]
  rw [Int.natCast_emod, sum_nat_int]
  unfold polyMul negacyclicSpec
  apply sumInt_mod_congr
  intro i hi
  simp only [hi, ↓reduceDIte, Nat.mod_eq_of_lt hi, negacyclicCoefficient, wrapSign,
    Int.natCast_mul]
  split
  · rfl
  · rename_i hwrap
    have hb := (b ⟨(k.val+128-i)%128, Nat.mod_lt _ (by decide)⟩).isLt
    rw [Int.ofNat_sub (Nat.le_of_lt hb), Int.mul_sub]
    exact Int.mul_sub_emod_self_right _ _ _


/-- Two uint32 planes encode each uint64 value. This avoids enabling JAX x64
on a backend whose native vector arithmetic is 32-bit. HBM/VMEM refs have shape
(2,128,128), VREG refs (2,8,128), and SMEM refs (2,1). Callers supply allocated
refs and DMA/regular semaphores through a Pallas kernel launch. -/
def pallasPrelude : String := r#"
import jax
import jax.numpy as jnp
from jax.experimental import pallas as pl
from jax.experimental.pallas import tpu as pltpu

def _pair(lo, hi):
    return jnp.stack((lo.astype(jnp.uint32), hi.astype(jnp.uint32)))

def _add64(a, b):
    lo = a[0] + b[0]
    return _pair(lo, a[1] + b[1] + (lo < a[0]).astype(jnp.uint32))

def _mulhi32(a, b):
    mask = jnp.uint32(65535)
    a0, a1 = a & mask, a >> 16
    b0, b1 = b & mask, b >> 16
    t = a0 * b0
    u = a1 * b0 + (t >> 16)
    v = a0 * b1 + (u & mask)
    return a1 * b1 + (u >> 16) + (v >> 16)

def _shift64(a, n, left):
    n = n & jnp.uint32(63)
    s = n & jnp.uint32(31)
    cross = (jnp.uint32(32) - s) & jnp.uint32(31)
    if left:
        lo = jnp.where(n < 32, a[0] << s, jnp.uint32(0))
        hi = jnp.where(n < 32, (a[1] << s) | jnp.where(s == 0, 0, a[0] >> cross), a[0] << s)
    else:
        hi = jnp.where(n < 32, a[1] >> s, jnp.uint32(0))
        lo = jnp.where(n < 32, (a[0] >> s) | jnp.where(s == 0, 0, a[1] << cross), a[1] >> s)
    return _pair(lo, hi)

def _ge64(a, b):
    return (a[1] > b[1]) | ((a[1] == b[1]) & (a[0] >= b[0]))

def _sub64(a, b):
    return _pair(a[0] - b[0], a[1] - b[1] - (a[0] < b[0]).astype(jnp.uint32))

def _select64(condition, a, b):
    return _pair(jnp.where(condition, a[0], b[0]), jnp.where(condition, a[1], b[1]))

def _reduce128(a, b):
    # Goldilocks: 2^64 = 2^32-1 and 2^96 = -1 modulo p.
    z = jnp.zeros_like(a[0])
    p = _pair(jnp.ones_like(z), jnp.full_like(z, 0xffffffff))
    ca = _select64(_ge64(a, p), _sub64(a, p), a)
    mid = _pair(z - b[0], jnp.where(b[0] == 0, z, b[0] - jnp.uint32(1)))
    remaining = _sub64(p, mid)
    t = _select64(_ge64(ca, remaining), _sub64(ca, remaining), _add64(ca, mid))
    high = _pair(b[1], z)
    return _select64(_ge64(t, high), _sub64(t, high), _add64(_sub64(p, high), t))

def _vpu(op, a, b):
    z = jnp.zeros_like(a[0])
    if op == 'add32': return _pair(a[0] + b[0], z)
    if op == 'mul32': return _pair(a[0] * b[0], z)
    if op == 'shl32': return _pair(a[0] << (b[0] & 31), z)
    if op == 'shr32': return _pair(a[0] >> (b[0] & 31), z)
    if op == 'add64': return _add64(a, b)
    if op == 'mul64': return _pair(a[0] * b[0], _mulhi32(a[0], b[0]) + a[0] * b[1] + a[1] * b[0])
    if op == 'mulHigh64':
        # Four base-2^16 digits keep every carry below 2^32.
        mask = jnp.uint32(65535)
        aa = (a[0] & mask, a[0] >> 16, a[1] & mask, a[1] >> 16)
        bb = (b[0] & mask, b[0] >> 16, b[1] & mask, b[1] >> 16)
        limbs = [z] * 8
        for i in range(4):
            carry = z
            for j in range(4):
                t = limbs[i+j] + aa[i] * bb[j] + carry
                limbs[i+j] = t & mask
                carry = t >> 16
            limbs[i+4] = carry
        return _pair(limbs[4] | (limbs[5] << 16), limbs[6] | (limbs[7] << 16))
    if op == 'shl64': return _shift64(a, b[0], True)
    if op == 'shr64': return _shift64(a, b[0], False)
    if op == 'carry32': return _pair((a[0] + b[0] < a[0]).astype(jnp.uint32), z)
    if op == 'carry64':
        hi = a[1] + b[1]
        c = (a[0] + b[0] < a[0]).astype(jnp.uint32)
        return _pair(((hi < a[1]) | (hi + c < hi)).astype(jnp.uint32), z)
    if op == 'goldilocksReduce': return _reduce128(a, b)
    raise ValueError('unknown VPU operation')

"#

def emitVpuName : VpuOp → String
  | .add32 => "add32" | .add64 => "add64" | .mul32 => "mul32" | .mul64 => "mul64"
  | .shl32 => "shl32" | .shr32 => "shr32" | .shl64 => "shl64" | .shr64 => "shr64"
  | .mulHigh64 => "mulHigh64"
  | .carry32 => "carry32" | .carry64 => "carry64" | .goldilocksReduce => "goldilocksReduce"

def emitTileRef (a : TileAddr) : String :=
  (match a.space with | .hbm => "hbm" | .vmem => "vmem") ++ s!"[{a.index}]"

/-- Source generation tracks each copy descriptor separately. A DMA wait consumes
whole descriptor credits. Mixing regular and DMA semaphore uses is refused by
checkPallasSemaphores, because these are distinct Pallas semaphore types. -/
def emitPallasInstr (index : Nat) : TpuInstr → String
  | .dma src dst sem =>
    s!"    copy_{index} = pltpu.make_async_copy({emitTileRef src}, {emitTileRef dst}, dma_sems[{sem}])\n" ++
    s!"    copy_{index}.start()\n    pending.setdefault({sem}, []).append(copy_{index})\n"
  | .wait sem count =>
    s!"    if {sem} in pending:\n        for _ in range({count}):\n            pending[{sem}].pop(0).wait()\n" ++
    s!"    else:\n        pl.semaphore_wait(regular_sems[{sem}], {count})\n"
  | .signal sem count => s!"    pl.semaphore_signal(regular_sems[{sem}], {count})\n"
  | .mxu mode dst lhs rhs =>
    let prep := match mode with
      | .unsigned8 => s!"    lhs_u = (vmem[{lhs}][0] & 255).astype(jnp.int32)\n    rhs_u = (vmem[{rhs}][0] & 255).astype(jnp.int32)\n    lhs = (lhs_u - 128).astype(jnp.int8)\n    rhs = (rhs_u - 128).astype(jnp.int8)\n"
      | .signed8 => s!"    lhs = vmem[{lhs}][0].astype(jnp.int8)\n    rhs = vmem[{rhs}][0].astype(jnp.int8)\n"
      | .bf16 => s!"    lhs = jax.lax.bitcast_convert_type(vmem[{lhs}][0].astype(jnp.uint16), jnp.bfloat16)\n" ++
          s!"    rhs = jax.lax.bitcast_convert_type(vmem[{rhs}][0].astype(jnp.uint16), jnp.bfloat16)\n"
    let product := match mode with
      | .bf16 => "    product = jax.lax.bitcast_convert_type(jnp.matmul(lhs, rhs, preferred_element_type=jnp.float32), jnp.uint32)\n"
      | .unsigned8 => "    product = (jnp.matmul(lhs, rhs, preferred_element_type=jnp.int32) + 128 * jnp.sum(lhs_u, axis=1, keepdims=True) + 128 * jnp.sum(rhs_u, axis=0, keepdims=True) - 2097152).astype(jnp.uint32)\n"
      | .signed8 => "    product = jnp.matmul(lhs, rhs, preferred_element_type=jnp.int32).astype(jnp.uint32)\n"
    prep ++ product ++ s!"    vmem[{dst}][...] = _pair(product, jnp.zeros_like(product))\n"
  | .transpose dst src =>
    s!"    tile = vmem[{src}][...]\n    vmem[{dst}][...] = _pair(tile[0].T, tile[1].T)\n"
  | .vpu op dst lhs rhs =>
    s!"    vreg[{dst}][...] = _vpu('{emitVpuName op}', vreg[{lhs}][...], vreg[{rhs}][...])\n"
  | .loadVReg dst tile subTile =>
    s!"    vreg[{dst}][...] = vmem[{tile}][:, {subTile*8}:{(subTile+1)*8}, :]\n"
  | .storeVReg tile subTile src =>
    s!"    vmem[{tile}][:, {subTile*8}:{(subTile+1)*8}, :] = vreg[{src}][...]\n"
  | .permute dst src lanes =>
    s!"    vreg[{dst}][...] = jnp.take(vreg[{src}][...], jnp.array({lanes.toList}, dtype=jnp.int32), axis=2)\n"
  | .fillVReg dst value =>
    s!"    vreg[{dst}][...] = _pair(jnp.full((8, 128), {value.toNat%2^32}, jnp.uint32), jnp.full((8, 128), {value.toNat/2^32}, jnp.uint32))\n"
  | .scalar dst value =>
    s!"    smem[{dst}][...] = jnp.array([[{value.toNat%2^32}], [{value.toNat/2^32}]], dtype=jnp.uint32)\n"
  | .finish => "    assert all(not copies for copies in pending.values()), 'undrained DMA descriptors'\n"

def checkPallasSemaphores (p : TpuProg) : Bool :=
  let dmaSems := p.filterMap fun i => match i with | .dma _ _ s => some s | _ => none
  let sigSems := p.filterMap fun i => match i with | .signal s _ => some s | _ => none
  !dmaSems.any (fun s => sigSems.contains s)

def programSemaphoreCount (p : TpuProg) : Nat :=
  p.foldl (fun n i => match i with
    | .dma _ _ s | .wait s _ | .signal s _ => max n (s+1)
    | _ => n) 0

/-- Blocks below 16 and lane permutations total on 128 lanes: what `stepBody` traps on at every allocation. -/
def checkInstrShape : TpuInstr → Bool
  | .loadVReg _ _ block | .storeVReg _ block _ => block < 16
  | .permute _ _ lanes => lanes.size == 128 && lanes.all (· < 128)
  | _ => true

def emitPallasKernelBody (p : TpuProg) : String :=
  pallasPrelude ++ "def kernel(hbm, vmem, smem, vreg, dma_sems, regular_sems):\n    pending = {}\n" ++
  String.join (p.zipIdx |>.map fun (i,index) => emitPallasInstr index i) ++
  "    assert all(not copies for copies in pending.values()), 'undrained DMA descriptors'\n"

/-- A kernel-body emitter, to be passed refs allocated by pl.pallas_call or
pl.kernel. It rejects hazardous or undrained programs before emitting the body.
No claim of a verified Python/Mosaic compiler is made by this function. -/
def emitPallasTpuKernel (p : TpuProg) : String :=
  if checkDmaSemaphores (programSemaphoreCount p) p && checkPallasSemaphores p && p.all checkInstrShape then
    emitPallasKernelBody p
  else "raise ValueError('TPU program has a DMA/semaphore hazard, mixed semaphore types or an out-of-range block')\n"

/-- The kernel body for explicit HBM, VMEM, scalar and VREG allocations: emitted only when every instruction is
in bounds (`checkProgramBounds`, so `WellSized` holds of the freshly allocated core) and the DMA/semaphore
analysis accepts. -/
def emitCheckedPallasTpuKernel (hbmTiles vmemTiles scalarRegs vregCount : Nat) (p : TpuProg) : Option String :=
  if checkProgramBounds hbmTiles vmemTiles scalarRegs vregCount (programSemaphoreCount p) p &&
      checkDmaSemaphores (programSemaphoreCount p) p && checkPallasSemaphores p then
    some (emitPallasKernelBody p)
  else none

/-- The checked emitter emits exactly when the bounds check, the DMA/semaphore analysis and the semaphore-kind
check all accept, and then emits the kernel body. -/
theorem emitCheckedPallasTpuKernel_iff (hbmTiles vmemTiles scalarRegs vregCount : Nat) (p : TpuProg) (src : String) :
    emitCheckedPallasTpuKernel hbmTiles vmemTiles scalarRegs vregCount p = some src ↔
      (checkProgramBounds hbmTiles vmemTiles scalarRegs vregCount (programSemaphoreCount p) p = true ∧
        checkDmaSemaphores (programSemaphoreCount p) p = true ∧ checkPallasSemaphores p = true) ∧
      src = emitPallasKernelBody p := by
  unfold emitCheckedPallasTpuKernel
  split
  · rename_i h; simp only [Bool.and_eq_true] at h
    exact ⟨fun e => ⟨⟨h.1.1, h.1.2, h.2⟩, (Option.some.inj e).symm⟩, fun e => by rw [e.2]⟩
  · rename_i h; simp only [Bool.and_eq_true] at h
    exact ⟨fun e => (by cases e), fun e => absurd ⟨⟨e.1.1, e.1.2.1⟩, e.1.2.2⟩ h⟩

theorem emitCheckedPallasTpuKernel_sound (hbmTiles vmemTiles scalarRegs vregCount : Nat) (p : TpuProg) (src : String)
    (h : emitCheckedPallasTpuKernel hbmTiles vmemTiles scalarRegs vregCount p = some src) :
    src = emitPallasKernelBody p ∧
    WellSized (TpuCoreState.initial hbmTiles vmemTiles scalarRegs vregCount (programSemaphoreCount p)) p ∧
    checkDmaSemaphores (programSemaphoreCount p) p = true := by
  unfold emitCheckedPallasTpuKernel at h; split at h
  · rename_i hc; simp only [Bool.and_eq_true] at hc; injection h with hs
    exact ⟨hs.symm, checkProgramBounds_initial _ _ _ _ _ p hc.1.1, hc.1.2⟩
  · cases h



/-- Fill a tile through the sixteen [8,128] VREG slices. -/
def fillTileProgram (dst : Nat) (value : UInt64) : TpuProg :=
  [.fillVReg 0 value] ++ (List.range 16).map (fun block => .storeVReg dst block 0)

/-- Extract one byte plane. The MXU masks to its low eight bits. -/
def bytePlaneProgram (dst src byte : Nat) : TpuProg :=
  [.fillVReg 1 (UInt64.ofNat (8*byte))] ++ (List.range 16).flatMap (fun block =>
    [.loadVReg 0 src block, .vpu .shr64 0 0 1, .storeVReg dst block 0])

/-- acc := (256*acc+term) mod p. Carries form the full 128-bit VPU input. -/
def radixAccProgram (acc term : Nat) : TpuProg :=
  [.fillVReg 2 8, .fillVReg 3 56] ++ (List.range 16).flatMap (fun block =>
    [.loadVReg 0 acc block, .loadVReg 1 term block,
     .vpu .shl64 4 0 2, .vpu .shr64 5 0 3, .vpu .carry64 6 4 1,
     .vpu .add64 5 5 6, .vpu .add64 4 4 1, .vpu .goldilocksReduce 0 4 5,
     .storeVReg acc block 0])

/-- Seven VREGs and four consecutive scratch tiles. Scratch, inputs and output
must be disjoint. The analyzer checks DMA hazards; it does not establish this
algorithm-specific aliasing contract. There are exactly 64 int8 MXU passes. -/
def goldilocksGemmProgram (dst lhs rhs scratch : Nat) : TpuProg :=
  fillTileProgram dst 0 ++ (List.range 8).reverse.flatMap (fun i =>
    bytePlaneProgram scratch lhs i ++ fillTileProgram (scratch+3) 0 ++
    (List.range 8).reverse.flatMap (fun j =>
      bytePlaneProgram (scratch+1) rhs j ++ [.mxu .unsigned8 (scratch+2) scratch (scratch+1)] ++
      radixAccProgram (scratch+3) (scratch+2)) ++ radixAccProgram dst (scratch+3))

/-- Exact elementwise modular product through the low/high halves and reducer. -/
def goldilocksPointwiseProgram (dst lhs rhs : Nat) : TpuProg :=
  (List.range 16).flatMap fun block =>
    [.loadVReg 0 lhs block, .loadVReg 1 rhs block,
     .vpu .mul64 2 0 1, .vpu .mulHigh64 3 0 1, .vpu .goldilocksReduce 4 2 3,
     .storeVReg dst block 4]

/-- Two 128×128 column transforms, two XLU transposes and fine twiddles.
The caller supplies W_R, W_C and the transposed twiddle matrix as VMEM tiles.
Scratch occupies six tiles; output must be disjoint from inputs and scratch. -/
def baileyNttProgram (dst input wr wc twiddle scratch : Nat) : TpuProg :=
  goldilocksGemmProgram scratch wr input (scratch+2) ++
  [.transpose (scratch+1) scratch] ++
  goldilocksPointwiseProgram (scratch+1) (scratch+1) twiddle ++
  goldilocksGemmProgram scratch wc (scratch+1) (scratch+2) ++
  [.transpose dst scratch]

/-! Checked tile layouts. `goldilocksGemmProgram` and `baileyNttProgram` take raw tile indices; a layout that
aliases the output or the scratch tiles with an input silently clobbers that input. The validators below refuse
such layouts and out-of-range tiles, and their soundness theorems give the machine's bounds check and the
preservation of every input tile by the synchronous run. -/

/-- `i` stays inside `vmemTiles` tiles and `vregCount` VREGs, uses no DMA, semaphore or scalar register, and
writes no tile of `prot`. -/
def layoutInstrOk (vmemTiles vregCount : Nat) (prot : List Nat) : TpuInstr → Bool
  | .mxu _ dst a b => dst < vmemTiles && a < vmemTiles && b < vmemTiles && prot.all (· != dst)
  | .transpose dst src => dst < vmemTiles && src < vmemTiles && prot.all (· != dst)
  | .vpu _ d a b => d < vregCount && a < vregCount && b < vregCount
  | .loadVReg d tile blk => d < vregCount && tile < vmemTiles && blk < 16
  | .storeVReg tile blk src => tile < vmemTiles && blk < 16 && src < vregCount && prot.all (· != tile)
  | .fillVReg d _ => d < vregCount
  | _ => false

example : layoutInstrOk 4 2 [0, 1] (.mxu .unsigned8 2 0 1) = true := by decide

theorem layoutInstrOk_sound (hbmSize vmemTiles smemSize vregCount semSize : Nat) (prot : List Nat) (i : TpuInstr)
    (h : layoutInstrOk vmemTiles vregCount prot i = true) :
    checkInstrBounds hbmSize vmemTiles smemSize vregCount semSize i = true ∧
    ∀ t ∈ prot, i.mayWriteVmem t = false := by
  cases i <;> simp_all [layoutInstrOk, checkInstrBounds, TpuInstr.mayWriteVmem]
  all_goals exact fun t ht e => h.2 t ht e.symm

/-- A program of `layoutInstrOk` instructions passes the bounds check at any HBM, scalar and semaphore sizes, and
its synchronous run leaves every protected tile as it found it. -/
theorem layoutProgramOk_sound (hbmSize vmemTiles smemSize vregCount semSize : Nat) (prot : List Nat) (p : TpuProg)
    (h : p.all (layoutInstrOk vmemTiles vregCount prot) = true) :
    checkProgramBounds hbmSize vmemTiles smemSize vregCount semSize p = true ∧
    ∀ t ∈ prot, ∀ s : TpuCoreState, (runSync s p).vmem[t]? = s.vmem[t]? := by
  have hi := fun i hi => layoutInstrOk_sound hbmSize vmemTiles smemSize vregCount semSize prot i
    (List.all_eq_true.mp h i hi)
  exact ⟨by unfold checkProgramBounds; exact List.all_eq_true.mpr fun i m => (hi i m).1,
    fun t ht s => runSync_vmem_frame s p t fun i m => (hi i m).2 t ht⟩

private theorem fillTile_ok {v r : Nat} {prot : List Nat} {dst : Nat} (val : UInt64) (hd : dst < v) (hr : 7 ≤ r)
    (hp : prot.all (· != dst) = true) : (fillTileProgram dst val).all (layoutInstrOk v r prot) = true := by
  have ⟨h0, h1, h2, h3, h4, h5, h6⟩ : 0 < r ∧ 1 < r ∧ 2 < r ∧ 3 < r ∧ 4 < r ∧ 5 < r ∧ 6 < r := by omega
  simp [fillTileProgram, layoutInstrOk, *]

private theorem bytePlane_ok {v r : Nat} {prot : List Nat} {dst src : Nat} (byte : Nat) (hd : dst < v) (hs : src < v)
    (hr : 7 ≤ r) (hp : prot.all (· != dst) = true) :
    (bytePlaneProgram dst src byte).all (layoutInstrOk v r prot) = true := by
  have ⟨h0, h1, h2, h3, h4, h5, h6⟩ : 0 < r ∧ 1 < r ∧ 2 < r ∧ 3 < r ∧ 4 < r ∧ 5 < r ∧ 6 < r := by omega
  simp [bytePlaneProgram, layoutInstrOk, *]

private theorem radixAcc_ok {v r : Nat} {prot : List Nat} {acc term : Nat} (ha : acc < v) (ht : term < v)
    (hr : 7 ≤ r) (hp : prot.all (· != acc) = true) :
    (radixAccProgram acc term).all (layoutInstrOk v r prot) = true := by
  have ⟨h0, h1, h2, h3, h4, h5, h6⟩ : 0 < r ∧ 1 < r ∧ 2 < r ∧ 3 < r ∧ 4 < r ∧ 5 < r ∧ 6 < r := by omega
  simp [radixAccProgram, layoutInstrOk, *]

private theorem pointwise_ok {v r : Nat} {prot : List Nat} {dst lhs rhs : Nat} (hd : dst < v) (hl : lhs < v)
    (hrhs : rhs < v) (hr : 7 ≤ r) (hp : prot.all (· != dst) = true) :
    (goldilocksPointwiseProgram dst lhs rhs).all (layoutInstrOk v r prot) = true := by
  have ⟨h0, h1, h2, h3, h4, h5, h6⟩ : 0 < r ∧ 1 < r ∧ 2 < r ∧ 3 < r ∧ 4 < r ∧ 5 < r ∧ 6 < r := by omega
  simp [goldilocksPointwiseProgram, layoutInstrOk, *]

/-- The GEMM program is `layoutInstrOk` when its tiles are in range and no protected tile is the output or one of
the four scratch tiles. -/
theorem goldilocksGemm_layout_ok {v r : Nat} {prot : List Nat} {dst lhs rhs scratch : Nat}
    (hd : dst < v) (hl : lhs < v) (hrhs : rhs < v) (hs : scratch + 3 < v) (hr : 7 ≤ r)
    (hp : ∀ t, t = dst ∨ (scratch ≤ t ∧ t ≤ scratch + 3) → prot.all (· != t) = true) :
    (goldilocksGemmProgram dst lhs rhs scratch).all (layoutInstrOk v r prot) = true := by
  have p0 := hp dst (Or.inl rfl)
  have p1 := hp scratch (Or.inr (by omega))
  have p2 := hp (scratch + 1) (Or.inr (by omega))
  have p3 := hp (scratch + 2) (Or.inr (by omega))
  have p4 := hp (scratch + 3) (Or.inr (by omega))
  have hmxu : layoutInstrOk v r prot (.mxu .unsigned8 (scratch + 2) scratch (scratch + 1)) = true := by
    simp [layoutInstrOk, p3]; omega
  simp [goldilocksGemmProgram, List.all_flatMap, hmxu,
    fillTile_ok (0 : UInt64) hd hr p0, fillTile_ok (0 : UInt64) (show scratch + 3 < v by omega) hr p4,
    fun b => bytePlane_ok (r := r) b (show scratch < v by omega) hl hr p1,
    fun b => bytePlane_ok (r := r) b (show scratch + 1 < v by omega) hrhs hr p2,
    radixAcc_ok (show scratch + 3 < v by omega) (show scratch + 2 < v by omega) hr p4,
    radixAcc_ok hd (show scratch + 3 < v by omega) hr p0]

/-- Output, inputs and the four scratch tiles in range, seven VREGs, and no aliasing: the output is neither input,
and output and inputs lie outside `scratch … scratch + 3`. The two inputs may coincide (a square). -/
def validateGemmTileLayout (vmemTiles vregCount dst lhs rhs scratch : Nat) : Bool :=
  decide (dst < vmemTiles) && decide (lhs < vmemTiles) && decide (rhs < vmemTiles) &&
  decide (scratch + 3 < vmemTiles) && decide (7 ≤ vregCount) && decide (dst ≠ lhs) && decide (dst ≠ rhs) &&
  [dst, lhs, rhs].all fun t => decide (t < scratch ∨ scratch + 3 < t)

example : validateGemmTileLayout 7 7 2 0 1 3 = true := by decide

def goldilocksGemmChecked (vmemTiles vregCount dst lhs rhs scratch : Nat) : Option TpuProg :=
  if validateGemmTileLayout vmemTiles vregCount dst lhs rhs scratch then
    some (goldilocksGemmProgram dst lhs rhs scratch) else none

/-- **A validated GEMM layout is in bounds and does not clobber its inputs**: the program passes
`checkProgramBounds` at any HBM, scalar and semaphore sizes, and from every machine state its synchronous run
leaves the `lhs` and `rhs` tiles unchanged. -/
theorem validateGemmTileLayout_sound (hbmSize vmemTiles smemSize vregCount semSize dst lhs rhs scratch : Nat)
    (h : validateGemmTileLayout vmemTiles vregCount dst lhs rhs scratch = true) :
    checkProgramBounds hbmSize vmemTiles smemSize vregCount semSize (goldilocksGemmProgram dst lhs rhs scratch) = true ∧
    ∀ s : TpuCoreState,
      (runSync s (goldilocksGemmProgram dst lhs rhs scratch)).vmem[lhs]? = s.vmem[lhs]? ∧
      (runSync s (goldilocksGemmProgram dst lhs rhs scratch)).vmem[rhs]? = s.vmem[rhs]? := by
  simp only [validateGemmTileLayout, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hd, hl⟩, hr⟩, hs⟩, hreg⟩, hdl⟩, hdr⟩, hd', hl', hr'⟩ := h
  have ok := goldilocksGemm_layout_ok (prot := [lhs, rhs]) hd hl hr hs hreg (by
    intro t ht; rcases ht with rfl | ht <;> simp <;> omega)
  have ⟨hb, hf⟩ := layoutProgramOk_sound hbmSize vmemTiles smemSize vregCount semSize [lhs, rhs] _ ok
  exact ⟨hb, fun s => ⟨hf lhs (by simp) s, hf rhs (by simp) s⟩⟩

example : (goldilocksGemmChecked 7 7 2 0 1 3).isSome = true := by decide

theorem goldilocksGemmChecked_sound (hbmSize vmemTiles smemSize vregCount semSize dst lhs rhs scratch : Nat)
    (p : TpuProg) (h : goldilocksGemmChecked vmemTiles vregCount dst lhs rhs scratch = some p) :
    p = goldilocksGemmProgram dst lhs rhs scratch ∧
    checkProgramBounds hbmSize vmemTiles smemSize vregCount semSize p = true ∧
    ∀ s : TpuCoreState, (runSync s p).vmem[lhs]? = s.vmem[lhs]? ∧ (runSync s p).vmem[rhs]? = s.vmem[rhs]? := by
  unfold goldilocksGemmChecked at h; split at h
  · rename_i hv; injection h with hp; subst hp
    exact ⟨rfl, validateGemmTileLayout_sound hbmSize vmemTiles smemSize vregCount semSize dst lhs rhs scratch hv⟩
  · cases h

/-- Output, the four input tiles and six scratch tiles in range, seven VREGs; output and inputs outside
`scratch … scratch + 5`; the output is none of the inputs. -/
def validateBaileyNttTileLayout (vmemTiles vregCount dst input wr wc twiddle scratch : Nat) : Bool :=
  ([dst, input, wr, wc, twiddle].all fun t => decide (t < vmemTiles) && decide (t < scratch ∨ scratch + 5 < t)) &&
  decide (scratch + 5 < vmemTiles) && decide (7 ≤ vregCount) &&
  [input, wr, wc, twiddle].all fun t => decide (dst ≠ t)

example : validateBaileyNttTileLayout 12 7 5 0 1 2 3 6 = true := by decide

def baileyNttChecked (vmemTiles vregCount dst input wr wc twiddle scratch : Nat) : Option TpuProg :=
  if validateBaileyNttTileLayout vmemTiles vregCount dst input wr wc twiddle scratch then
    some (baileyNttProgram dst input wr wc twiddle scratch) else none

/-- **A validated Bailey layout is in bounds and preserves the input, both root matrices and the twiddles.** -/
theorem validateBaileyNttTileLayout_sound
    (hbmSize vmemTiles smemSize vregCount semSize dst input wr wc twiddle scratch : Nat)
    (h : validateBaileyNttTileLayout vmemTiles vregCount dst input wr wc twiddle scratch = true) :
    checkProgramBounds hbmSize vmemTiles smemSize vregCount semSize
      (baileyNttProgram dst input wr wc twiddle scratch) = true ∧
    ∀ t ∈ [input, wr, wc, twiddle], ∀ s : TpuCoreState,
      (runSync s (baileyNttProgram dst input wr wc twiddle scratch)).vmem[t]? = s.vmem[t]? := by
  simp only [validateBaileyNttTileLayout, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at h
  obtain ⟨⟨⟨⟨⟨hd, hd'⟩, ⟨hi, hi'⟩, ⟨hwr, hwr'⟩, ⟨hwc, hwc'⟩, htw, htw'⟩, hs⟩, hreg⟩, n1, n2, n3, n4⟩ := h
  have hp : ∀ t, t = dst ∨ (scratch ≤ t ∧ t ≤ scratch + 5) → [input, wr, wc, twiddle].all (· != t) = true := by
    intro t ht; rcases ht with rfl | ht <;> simp <;> omega
  have g1 := goldilocksGemm_layout_ok (prot := [input, wr, wc, twiddle]) (dst := scratch) (lhs := wr)
    (rhs := input) (scratch := scratch + 2) (v := vmemTiles) (by omega) hwr hi (by omega) hreg
    (fun t ht => hp t (Or.inr (by omega)))
  have g2 := goldilocksGemm_layout_ok (prot := [input, wr, wc, twiddle]) (dst := scratch) (lhs := wc)
    (rhs := scratch + 1) (scratch := scratch + 2) (v := vmemTiles) (by omega) hwc (by omega) (by omega) hreg
    (fun t ht => hp t (Or.inr (by omega)))
  have pw := pointwise_ok (prot := [input, wr, wc, twiddle]) (dst := scratch + 1) (lhs := scratch + 1)
    (rhs := twiddle) (v := vmemTiles) (by omega) (by omega) htw hreg (hp _ (Or.inr (by omega)))
  have t1 : layoutInstrOk vmemTiles vregCount [input, wr, wc, twiddle] (.transpose (scratch + 1) scratch) = true := by
    simp only [layoutInstrOk, hp (scratch + 1) (Or.inr (by omega)), Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]; omega
  have t2 : layoutInstrOk vmemTiles vregCount [input, wr, wc, twiddle] (.transpose dst scratch) = true := by
    simp only [layoutInstrOk, hp dst (Or.inl rfl), Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  exact layoutProgramOk_sound hbmSize vmemTiles smemSize vregCount semSize [input, wr, wc, twiddle] _
    (by simp [baileyNttProgram, g1, g2, pw, t1, t2])


end Obend.Hardware.Tpu
