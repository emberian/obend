module
public import Std
public import Obend.Hardware.ArrayKernel
public import Obend.Hardware.Gpu.GoldilocksSource
public section

namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.Gpu.GoldilocksSource

/-! ## The NTT -/

/-- Binary modular exponentiation. The exponent decreases by a factor of two;
the zero case preserves the previous implementation's value even at modulus one. -/
@[expose] def powMod (b e m : Nat) : Nat :=
  if h : e = 0 then 1 else
    let r := powMod b (e / 2) m
    let square := r * r % m
    if e % 2 = 0 then square else square * b % m
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- A primitive `2^32`-th root of unity in the Goldilocks field (`7^((p-1)/2^32)`). -/
@[expose] def rootOfUnity2to32 : Nat := powMod 7 ((goldilocksP - 1) / 2 ^ 32) goldilocksP

/-- A primitive `n`-th root, `n` a power of two dividing `2^32`. -/
@[expose] def rootOfUnity (n : Nat) : Nat := powMod rootOfUnity2to32 (2 ^ 32 / n) goldilocksP

/-! The NTT source uses the general index-parametric multi-output array language.
Each upload is ec-gpu's Stockham map. A radix-4 (or final radix-2) subnetwork stays in
one invocation's registers; successive subnetworks exchange arrays in workgroup
memory. Input/output layout expressions fuse Stockham's transpose into the loads
and stores. No index tables, global gather intermediates, or NTT shader template.
-/

namespace BlockNtt
open Obend.Hardware.ArrayKernel

def addI (a b : Ix) : Ix := .add a b

theorem addI_eq (a b : Ix) : addI a b = .add a b := by rfl
@[expose] def mulI (a : Ix) (b : Nat) : Ix := .mul a (.lit b)

/-- Bit reversal is an index expression, not an index buffer or a dispatch. -/
def reverseBits (bits : Nat) (i : Ix) : Ix :=
  (List.range bits).foldl (fun acc bit =>
    addI acc (mulI (.mod (.div i (2^bit)) 2) (2^(bits-1-bit)))) (.lit 0)

/-- Register position within the whole upload tile, with lane/register
coordinates transposed so a register butterfly follows the global DIF layer. -/
def phaseIndex (radix stride r : Nat) : Ix :=
  addI (addI (mulI (.div .lane stride) (radix*stride)) (.mod .lane stride))
    (.lit (r*stride))

def phaseLoadIndex (n count radix stride : Nat) (first : Bool) (r : Nat) : Ix :=
  if first then addI .group (mulI (phaseIndex radix stride r) (n/count))
  else phaseIndex radix stride r

def phaseSaveIndex (count logCount p radix stride : Nat) (last : Bool) (r : Nat) : Ix :=
  if last then
    let k : Ix := .mod .group p
    addI (addI (mulI (.div .group p) (p*count)) k)
      (mulI (reverseBits logCount (phaseIndex radix stride r)) p)
  else phaseIndex radix stride r

end BlockNtt

/-- Tail-recursive linear-time twiddle generation. Each entry is computed by one
field multiplication, with no per-entry modular exponentiation. -/
def powersLoop (ω : Nat) : Nat → Array Word → Nat → Array Word
  | 0, xs, _ => xs
  | count+1, xs, v => powersLoop ω count (xs.push (BitVec.ofNat 64 v)) (v*ω%goldilocksP)

def twiddlePowers (n ω : Nat) : Array Word := powersLoop ω n #[] 1

end Obend.Hardware.Gpu.Ntt

section
namespace Obend.Hardware.Gpu.Ntt.Sum

/-- A finite natural sum, with no implicit reduction or ordering assumption. -/
@[expose] def sum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => sum n f + f n

@[simp] theorem zero (f : Nat → Nat) : sum 0 f = 0 := by rfl
@[simp] theorem succ (n : Nat) (f : Nat → Nat) : sum (n+1) f = sum n f + f n := by rfl

theorem cong (n : Nat) (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ,succ,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem cong_mod (m n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i % m = g i % m) : sum n f % m = sum n g % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (sum n f + f n) % m = (sum n g + g n) % m
    conv => lhs; rw [Nat.add_mod]
    conv => rhs; rw [Nat.add_mod]
    rw [ih (fun i hi => h i (by omega)),h n (by omega)]

@[simp] theorem sum_zero (n : Nat) : sum n (fun _ => 0) = 0 := by
  induction n <;> simp_all

theorem add (n : Nat) (f g : Nat → Nat) :
    sum n (fun i => f i + g i) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem mul_right (n : Nat) (f : Nat → Nat) (c : Nat) :
    sum n (fun i => f i * c) = sum n f * c := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih,Nat.add_mul]

theorem mul_left (n : Nat) (f : Nat → Nat) (c : Nat) :
    sum n (fun i => c * f i) = c * sum n f := by
  simpa only [Nat.mul_comm c] using mul_right n f c

theorem swap (m n : Nat) (f : Nat → Nat → Nat) :
    sum m (fun i => sum n (f i)) = sum n (fun j => sum m (fun i => f i j)) := by
  induction m with
  | zero => simp
  | succ m ih => simp only [succ,ih,add]

theorem append (m n : Nat) (f : Nat → Nat) :
    sum (m+n) f = sum m f + sum n (fun i => f (m+i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    change sum (m+n+1) f = sum m f + (sum n (fun i => f (m+i)) + f (m+n))
    rw [succ,ih,Nat.add_assoc]

/-- Quotient/remainder decomposition of the whole summation domain. -/
theorem blocks (m n : Nat) (f : Nat → Nat) :
    sum (m*n) f = sum m (fun i => sum n (fun j => f (i*n+j))) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul,append,ih,succ]

theorem map_mod (m n : Nat) (f : Nat → Nat) :
    sum n (fun i => f i % m) % m = sum n f % m :=
  cong_mod m n _ _ (by intro i hi; simp)

theorem list_range (n : Nat) (f : Nat → Nat) :
    (List.range n |>.map f).sum = sum n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ,ih]

/-- Left-fold reduction is the same modular sum for every initial accumulator. -/
theorem foldl_mod (xs : List Nat) (m acc : Nat) :
    xs.foldl (fun a x => (a+x)%m) acc % m = (acc + xs.sum)%m := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.sum_cons]
    rw [ih]
    rw [Nat.mod_add_mod,Nat.add_assoc]

end Obend.Hardware.Gpu.Ntt.Sum
end

section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource

/-- The efficient source computation denotes ordinary modular exponentiation.
The modulus premise also preserves the historical `powMod b 0 m = 1` convention. -/
theorem powMod_eq (b e m : Nat) (hm : 1 < m) : powMod b e m = b^e % m := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [powMod]
    split
    · rename_i he
      simp [he, Nat.mod_eq_of_lt hm]
    · rename_i he
      have hi := ih (e/2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))
      have hd := Nat.mod_add_div e 2
      have hr := Nat.mod_lt e (by decide : 0 < 2)
      rw [hi]
      split
      · rename_i hz
        have ee : e = e/2 + e/2 := by omega
        conv => rhs; rw [ee, Nat.pow_add]
        simp
      · rename_i hn
        have ho : e%2 = 1 := by omega
        have ee : e = (e/2 + e/2) + 1 := by omega
        conv => rhs; rw [ee, Nat.pow_add, Nat.pow_add]
        simp

abbrev modPow (b e : Nat) : Nat := powMod b e goldilocksP

private theorem modulus_gt_one : 1 < goldilocksP := by decide +kernel

theorem modPow_eq (b e : Nat) : modPow b e = b^e % goldilocksP :=
  powMod_eq b e goldilocksP modulus_gt_one

@[simp] theorem modPow_zero (b : Nat) : modPow b 0 = 1 := by
  simp [modPow_eq, Nat.mod_eq_of_lt modulus_gt_one]

@[simp] theorem modPow_one (b : Nat) : modPow b 1 = b % goldilocksP := by
  simp [modPow_eq]

@[simp] theorem modPow_one_base (e : Nat) : modPow 1 e = 1 := by
  simp [modPow_eq, Nat.mod_eq_of_lt modulus_gt_one]

theorem modPow_add (b e f : Nat) :
    modPow b (e+f) = (modPow b e * modPow b f) % goldilocksP := by
  simp [modPow_eq, Nat.pow_add]

theorem modPow_mul (b e f : Nat) :
    modPow b (e*f) = modPow (modPow b e) f := by
  simp only [modPow_eq, Nat.pow_mul]
  exact Nat.pow_mod _ _ _

/-- A kernel-checked logarithmic certificate, not a sampled size check. -/
theorem root32_value : rootOfUnity2to32 = 1753635133440165772 := by decide +kernel

theorem root32_half : modPow rootOfUnity2to32 (2^31) = goldilocksP-1 := by decide +kernel

theorem root32_full : modPow rootOfUnity2to32 (2^32) = 1 := by decide +kernel

theorem minus_one_square : modPow (goldilocksP-1) 2 = 1 := by decide +kernel

/-- Exponents can be reduced modulo any certified period. -/
theorem modPow_periodic (b n e : Nat) (hn : modPow b n = 1) :
    modPow b e = modPow b (e % n) := by
  conv => lhs; rw [← Nat.mod_add_div e n]
  rw [modPow_add, modPow_mul, hn, modPow_one_base]
  simp [modPow_eq]

theorem modPow_period_add (b n e : Nat) (hn : modPow b n = 1) :
    modPow b (e+n) = modPow b e := by
  rw [modPow_add, hn]
  simp [modPow_eq]

theorem minus_one_odd (e : Nat) (he : e % 2 = 1) :
    modPow (goldilocksP-1) e = goldilocksP-1 := by
  rw [modPow_periodic _ 2 e minus_one_square, he, modPow_one]
  exact Nat.mod_eq_of_lt (by decide)

/-- For a power-of-two period, the half-period value `-1` excludes every
smaller order. This argument uses only modular exponent laws, not primality. -/
theorem power_two_order (k b e : Nat)
    (half : 0 < k → modPow b (2^(k-1)) = goldilocksP-1)
    (one : modPow b e = 1) : 2^k ∣ e := by
  induction k generalizing b e with
  | zero => simp
  | succ k ih =>
    have hhalf : modPow b (2^k) = goldilocksP-1 := by simpa using half (by omega)
    have even : e % 2 = 0 := by
      have hr := Nat.mod_lt e (by decide : 0 < 2)
      by_cases hz : e%2=0
      · exact hz
      · have odd : e%2=1 := by omega
        have hex : modPow (modPow b e) (2^k) = modPow (modPow b (2^k)) e := by
          rw [← modPow_mul, ← modPow_mul, Nat.mul_comm e]
        rw [one, modPow_one_base, hhalf, minus_one_odd e odd] at hex
        have bad : goldilocksP-1 ≠ 1 := by decide
        exact False.elim (bad hex.symm)
    have ee : e = 2*(e/2) := by omega
    have small : modPow (modPow b 2) (e/2) = 1 := by
      rw [← modPow_mul, ← ee]
      exact one
    have smallHalf : 0 < k → modPow (modPow b 2) (2^(k-1)) = goldilocksP-1 := by
      intro hk
      rw [← modPow_mul]
      have hp : 2 * 2^(k-1) = 2^k := by
        rw [Nat.mul_comm, ← Nat.pow_succ]
        congr 1
        omega
      rw [hp]
      exact hhalf
    obtain ⟨q,hq⟩ := ih (modPow b 2) (e/2) smallHalf small
    refine ⟨q, ?_⟩
    rw [ee, hq, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm]

/-- Primitive order as an exact divisibility characterization of every exponent. -/
theorem primitive_of_half (k b : Nat)
    (full : modPow b (2^k) = 1)
    (half : 0 < k → modPow b (2^(k-1)) = goldilocksP-1) (e : Nat) :
    modPow b e = 1 ↔ 2^k ∣ e := by
  constructor
  · exact power_two_order k b e half
  · rintro ⟨q,rfl⟩
    rw [modPow_mul, full, modPow_one_base]

theorem root32_order (e : Nat) : modPow rootOfUnity2to32 e = 1 ↔ 2^32 ∣ e :=
  primitive_of_half 32 rootOfUnity2to32 root32_full (fun _ => root32_half) e

/-- The runtime root definition is the appropriate power of the fixed root. -/
theorem root_power (k : Nat) (hk : k ≤ 32) :
    rootOfUnity (2^k) = modPow rootOfUnity2to32 (2^(32-k)) := by
  unfold rootOfUnity
  rw [Nat.pow_div hk (by decide)]

theorem root_full (k : Nat) (hk : k ≤ 32) :
    modPow (rootOfUnity (2^k)) (2^k) = 1 := by
  rw [root_power k hk, ← modPow_mul, Nat.pow_sub_mul_pow 2 hk]
  exact root32_full

theorem root_half (k : Nat) (hk : 1 ≤ k) (hk32 : k ≤ 32) :
    modPow (rootOfUnity (2^k)) (2^(k-1)) = goldilocksP-1 := by
  rw [root_power k hk32, ← modPow_mul, ← Nat.pow_add]
  have he : 32-k+(k-1) = 31 := by omega
  rw [he]
  exact root32_half

/-- All supported NTT sizes (indeed every `1 ≤ k ≤ 32`) have primitive roots. -/
theorem root_order (k : Nat) (hk : 1 ≤ k) (hk32 : k ≤ 32) (e : Nat) :
    modPow (rootOfUnity (2^k)) e = 1 ↔ 2^k ∣ e :=
  primitive_of_half k _ (root_full k hk32) (fun _ => root_half k hk hk32) e

theorem root_periodic (k : Nat) (hk : k ≤ 32) (e : Nat) :
    modPow (rootOfUnity (2^k)) e = modPow (rootOfUnity (2^k)) (e % 2^k) :=
  modPow_periodic _ _ _ (root_full k hk)

theorem modPow_lt (b e : Nat) : modPow b e < goldilocksP := by
  rw [modPow_eq]
  exact Nat.mod_lt _ (by decide)

theorem root_lt (k : Nat) : rootOfUnity (2^k) < goldilocksP :=
  modPow_lt _ _

/-- Half-period stated with the actual runtime transform size. -/
theorem root_half_size (k : Nat) (hk : 1 ≤ k) (hk32 : k ≤ 32) :
    modPow (rootOfUnity (2^k)) (2^k / 2) = goldilocksP-1 := by
  have hd : 2^k / 2 = 2^(k-1) := by
    simpa using (Nat.pow_div hk (by decide : 0 < 2))
  rw [hd]
  exact root_half k hk hk32

/-- Squaring an NTT root yields the root for its two half-size transforms. -/
theorem root_square (k : Nat) (hk : k < 32) :
    modPow (rootOfUnity (2^(k+1))) 2 = rootOfUnity (2^k) := by
  rw [root_power (k+1) (by omega), root_power k (by omega), ← modPow_mul,
    ← Nat.pow_succ]
  have he : (32-(k+1)).succ = 32-k := by omega
  rw [he]

/-- The butterfly's half-period shift multiplies its twiddle by minus one. -/
theorem root_half_shift (k : Nat) (hk : 1 ≤ k) (hk32 : k ≤ 32) (e : Nat) :
    modPow (rootOfUnity (2^k)) (e + 2^k/2) =
      (modPow (rootOfUnity (2^k)) e * (goldilocksP-1)) % goldilocksP := by
  rw [modPow_add, root_half_size k hk hk32]

/-- No exponent strictly between zero and the transform size is a period. -/
theorem root_no_short_period (k : Nat) (hk : 1 ≤ k) (hk32 : k ≤ 32)
    (e : Nat) (he : 0 < e) (hen : e < 2^k) :
    modPow (rootOfUnity (2^k)) e ≠ 1 := by
  intro h
  have hd := (root_order k hk hk32 e).mp h
  have hh := Nat.le_of_dvd he hd
  omega

/-- A transform's strided twiddles are exactly the shared smaller-transform root. -/
theorem root_subtransform (bits degree : Nat) (hd : degree ≤ bits) (hb : bits ≤ 32) :
    modPow (rootOfUnity (2^bits)) (2^(bits-degree)) = rootOfUnity (2^degree) := by
  rw [root_power bits hb,root_power degree (by omega),← modPow_mul,← Nat.pow_add]
  have he : 32-bits+(bits-degree)=32-degree := by omega
  rw [he]

/-- The whole-vector layer and the source's global-root twiddle agree. -/
theorem root_layer_twiddle (bits level j : Nat) (hl : level ≤ bits) (hb : bits ≤ 32) :
    modPow (rootOfUnity (2^(bits-level))) j =
      modPow (rootOfUnity (2^bits)) (j*2^level) := by
  have hr := root_subtransform bits (bits-level) (by omega) hb
  have he : bits-(bits-level)=level := by omega
  rw [he] at hr
  rw [←hr,←modPow_mul,Nat.mul_comm]

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource

/-- Canonical modular operations. Their laws below need no primality assumption. -/
@[expose] def addMod (a b : Nat) : Nat := (a+b) % goldilocksP
@[expose] def mulMod (a b : Nat) : Nat := (a*b) % goldilocksP
def negMod (a : Nat) : Nat := mulMod (goldilocksP-1) a
def subMod (a b : Nat) : Nat := addMod a (negMod b)

@[simp] theorem addMod_residue_left (a b : Nat) : addMod (a%goldilocksP) b = addMod a b := by
  simp [addMod]
@[simp] theorem addMod_residue_right (a b : Nat) : addMod a (b%goldilocksP) = addMod a b := by
  simp [addMod]
@[simp] theorem mulMod_residue_left (a b : Nat) : mulMod (a%goldilocksP) b = mulMod a b := by
  simp [mulMod]
@[simp] theorem mulMod_residue_right (a b : Nat) : mulMod a (b%goldilocksP) = mulMod a b := by
  simp [mulMod]
@[simp] theorem mulMod_one (a : Nat) : mulMod a 1 = a%goldilocksP := by simp [mulMod]
@[simp] theorem one_mulMod (a : Nat) : mulMod 1 a = a%goldilocksP := by simp [mulMod]

theorem addMod_assoc (a b c : Nat) : addMod (addMod a b) c = addMod a (addMod b c) := by
  simp [addMod, Nat.add_assoc]
theorem addMod_comm (a b : Nat) : addMod a b = addMod b a := by simp [addMod,Nat.add_comm]
theorem mulMod_assoc (a b c : Nat) : mulMod (mulMod a b) c = mulMod a (mulMod b c) := by
  simp [mulMod, Nat.mul_assoc]
theorem mulMod_comm (a b : Nat) : mulMod a b = mulMod b a := by simp [mulMod,Nat.mul_comm]
theorem mulMod_addMod (a b c : Nat) :
    mulMod a (addMod b c) = addMod (mulMod a b) (mulMod a c) := by
  simp [mulMod, addMod, Nat.mul_add]
theorem addMod_mulMod (a b c : Nat) :
    mulMod (addMod a b) c = addMod (mulMod a c) (mulMod b c) := by
  simp [mulMod, addMod, Nat.add_mul]

theorem minus_one_even (e : Nat) : modPow (goldilocksP-1) (2*e) = 1 := by
  rw [modPow_mul, minus_one_square, modPow_one_base]

theorem modPow_even (w j k : Nat) :
    modPow w (j*(2*k)) = modPow (modPow w 2) (j*k) := by
  rw [← modPow_mul]
  congr 1
  simp [Nat.mul_assoc, Nat.mul_comm]

theorem modPow_odd (w j k : Nat) :
    modPow w (j*(2*k+1)) = mulMod (modPow w j) (modPow (modPow w 2) (j*k)) := by
  rw [Nat.mul_add, Nat.mul_one, modPow_add, modPow_even]
  exact Nat.mul_comm _ _ |> congrArg (· % goldilocksP)

theorem modPow_block (w n j e : Nat) :
    modPow w ((n+j)*e) = mulMod (modPow (modPow w n) e) (modPow w (j*e)) := by
  rw [Nat.add_mul, modPow_add, modPow_mul]
  rfl

/-- The even-frequency pair in a DIF butterfly. -/
theorem dif_even_pair (w n j k a b : Nat) (half : modPow w n = goldilocksP-1) :
    addMod (mulMod a (modPow w (j*(2*k))))
      (mulMod b (modPow w ((n+j)*(2*k)))) =
    mulMod (addMod a b) (modPow (modPow w 2) (j*k)) := by
  rw [modPow_block, half, minus_one_even, one_mulMod]
  simp only [mulMod_residue_right, modPow_even]
  exact (addMod_mulMod _ _ _).symm

/-- The odd-frequency pair in a DIF butterfly. -/
theorem dif_odd_pair (w n j k a b : Nat) (half : modPow w n = goldilocksP-1) :
    addMod (mulMod a (modPow w (j*(2*k+1))))
      (mulMod b (modPow w ((n+j)*(2*k+1)))) =
    mulMod (mulMod (subMod a b) (modPow w j)) (modPow (modPow w 2) (j*k)) := by
  rw [modPow_block, half, minus_one_odd _ (by omega), modPow_odd]
  simp only [subMod, negMod]
  rw [mulMod_assoc, addMod_mulMod]
  simp only [mulMod_assoc]
  congr 1
  rw [← mulMod_assoc b, mulMod_comm b (goldilocksP-1), mulMod_assoc]

/-- Mathematical finite sum, reduced once after the exact natural sum. -/
@[expose] def sumMod (n : Nat) (f : Nat → Nat) : Nat := Sum.sum n f % goldilocksP

/-- Forward DFT. Inputs need not already be canonical residues. -/
@[expose] def dft (n root : Nat) (input : Nat → Nat) (k : Nat) : Nat :=
  sumMod n (fun j => input j * modPow root (j*k))

theorem dft_even (n root : Nat) (input : Nat → Nat) (k : Nat)
    (half : modPow root n = goldilocksP-1) :
    dft (n+n) root input (2*k) =
      dft n (modPow root 2) (fun j => addMod (input j) (input (n+j))) k := by
  unfold dft sumMod
  rw [Sum.append, ← Sum.add]
  apply Sum.cong_mod
  intro j _
  simpa [addMod, mulMod] using dif_even_pair root n j k (input j) (input (n+j)) half

theorem dft_odd (n root : Nat) (input : Nat → Nat) (k : Nat)
    (half : modPow root n = goldilocksP-1) :
    dft (n+n) root input (2*k+1) =
      dft n (modPow root 2)
        (fun j => mulMod (subMod (input j) (input (n+j))) (modPow root j)) k := by
  unfold dft sumMod
  rw [Sum.append, ← Sum.add]
  apply Sum.cong_mod
  intro j _
  simpa [addMod, mulMod] using dif_odd_pair root n j k (input j) (input (n+j)) half

theorem dft_congr_mod (n root k : Nat) (input other : Nat → Nat)
    (h : ∀ j, j < n → input j % goldilocksP = other j % goldilocksP) :
    dft n root input k = dft n root other k := by
  unfold dft sumMod
  apply Sum.cong_mod
  intro j hj
  conv => lhs; rw [Nat.mul_mod]
  conv => rhs; rw [Nat.mul_mod]
  rw [h j hj]

theorem dft_input_mod (n root : Nat) (input : Nat → Nat) (k : Nat) :
    dft n root (fun j => input j % goldilocksP) k = dft n root input k :=
  dft_congr_mod n root k _ _ (by intro j hj; simp)

private theorem sub_residue_nat (m a b : Nat) (hm : 0 < m) (hb : b ≤ m) :
    (a+(m-1)*b)%m = (a+m-b)%m := by
  have hmul : m*b = b+(m-1)*b := by
    have he : m=(m-1)+1 := by omega
    conv => lhs; rw [he,Nat.add_mul,Nat.one_mul]
    omega
  have he : (a+m-b)+m*b = (a+(m-1)*b)+m := by omega
  have h := congrArg (fun n => n%m) he
  simpa only [Nat.add_mod,Nat.mul_mod_right,Nat.mod_self,Nat.add_zero,Nat.mod_mod] using h.symm

/-- The algebraic difference is ordinary natural subtraction modulo p for a
canonical subtrahend, matching the source Goldilocks subtraction contract. -/
theorem subMod_eq_nat (a b : Nat) (hb : b < goldilocksP) :
    subMod a b = (a+goldilocksP-b) % goldilocksP := by
  unfold subMod negMod mulMod addMod
  rw [Nat.add_mod_mod]
  exact sub_residue_nat goldilocksP a b (by decide) (by omega)

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt.Stockham
open GoldilocksSource

/-- The value invariant after `p` transformed digits. The remaining digits are
strided by `stride`; it specializes to the DFT when `stride = 1`. -/
def partialTransform (p stride : Nat) (ω : Nat) (input : Nat → Nat) (b k : Nat) : Nat :=
  Sum.sum p (fun j => input (b+j*stride) * modPow ω (j*k*stride)) % goldilocksP

theorem partialTransform_eq (p stride : Nat) (ω : Nat) (input : Nat → Nat) (b k : Nat) :
    partialTransform p stride ω input b k = Sum.sum p (fun j => input (b+j*stride) * modPow ω (j*k*stride)) % goldilocksP := by rfl

theorem initial (ω : Nat) (input : Nat → Nat) (b k stride : Nat) :
    partialTransform 1 stride ω input b k = input b % goldilocksP := by
  simp [partialTransform,Sum.sum]

theorem period_multiple (ω n e q : Nat) (hn : modPow ω n = 1) :
    modPow ω (e+n*q) = modPow ω e := by
  rw [modPow_add,modPow_mul,hn,modPow_one_base]
  simp [modPow_eq]

/-- The exponent identity of one Stockham upload, including the discarded full
period. This is universal in all coordinates, rather than a checked table. -/
theorem exponent (p c m j t k r : Nat) :
    (j*c+t)*(k+r*p)*m =
      j*k*(c*m) + t*k*m + t*r*(p*m) + (p*c*m)*(j*r) := by
  simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- One term of the strided partial DFT after combining an upload. -/
theorem term (p c m ω j t k r q : Nat) (input : Nat → Nat)
    (hperiod : modPow ω (p*c*m) = 1) :
    ((input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m)) *
      modPow ω (t*k*m)) * modPow ω (t*r*(p*m))) % goldilocksP =
    (input (q+(j*c+t)*m) * modPow ω ((j*c+t)*(k+r*p)*m)) % goldilocksP := by
  have hi : q+t*m+j*(c*m) = q+(j*c+t)*m := by
    simp [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rw [hi,exponent,period_multiple _ _ _ _ hperiod]
  simp [modPow_add,Nat.mul_assoc]

/-- A radix-`c` Stockham upload: each old partial transform is twiddled, then
transformed across the next digit. This is the exact algebraic invariant used
by the fused load/store permutation of `BlockNtt.phase`. -/
theorem upload (p c m ω q k r : Nat) (input : Nat → Nat)
    (hperiod : modPow ω (p*c*m) = 1) :
    Sum.sum c (fun t =>
      partialTransform p (c*m) ω input (q+t*m) k *
        modPow ω (t*k*m) * modPow ω (t*r*(p*m))) % goldilocksP =
      partialTransform (p*c) m ω input q (k+r*p) := by
  unfold partialTransform
  have expand : ∀ t,
      ((Sum.sum p (fun j => input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m))) % goldilocksP) *
        modPow ω (t*k*m) * modPow ω (t*r*(p*m))) % goldilocksP =
      Sum.sum p (fun j => input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m)) *
        modPow ω (t*k*m) * modPow ω (t*r*(p*m))) % goldilocksP := by
    intro t
    rw [Sum.mul_right,Sum.mul_right]
    simp [Nat.mul_assoc]
  calc
    _ = Sum.sum c (fun t => Sum.sum p (fun j =>
          input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m)) *
            modPow ω (t*k*m) * modPow ω (t*r*(p*m)))) % goldilocksP :=
      Sum.cong_mod _ _ _ _ (fun t _ => expand t)
    _ = Sum.sum c (fun t => Sum.sum p (fun j =>
          input (q+(j*c+t)*m) * modPow ω ((j*c+t)*(k+r*p)*m))) % goldilocksP := by
      apply Sum.cong_mod
      intro t ht
      apply Sum.cong_mod
      intro j hj
      exact term p c m ω j t k r q input hperiod
    _ = _ := by
      rw [Sum.swap]
      exact congrArg (fun v => v % goldilocksP)
        (Sum.blocks p c (fun j => input (q+j*m) * modPow ω (j*(k+r*p)*m))).symm

/-- The upload factorization stated with the shared DFT specification. The
input view is exactly the strided load view of a Stockham workgroup. -/
theorem upload_dft (p c m ω q k r : Nat) (input values : Nat → Nat)
    (hperiod : modPow ω (p*c*m) = 1)
    (hvalues : ∀ t, t < c → values t % goldilocksP =
      partialTransform p (c*m) ω input (q+t*m) k) :
    dft c (modPow ω (p*m))
      (fun t => mulMod (values t) (modPow ω (t*k*m))) r =
      partialTransform (p*c) m ω input q (k+r*p) := by
  rw [← upload p c m ω q k r input hperiod]
  unfold dft sumMod
  apply Sum.cong_mod
  intro t ht
  have hp : modPow (modPow ω (p*m)) (t*r) = modPow ω (t*r*(p*m)) := by
    rw [← modPow_mul,Nat.mul_comm (p*m)]
  rw [hp,← hvalues t ht]
  simp [mulMod,Nat.mul_assoc]

/-- Canonical output indexing after one upload. These coordinates account for
all outputs, including the transpose fused into each final register store. -/
theorem output_index (p c m q k r : Nat) (hp : 0 < p) (hk : k < p)
    (hr : r < c) (hq : q < m) :
    let g := q*p+k
    g/p*(p*c) + g%p + r*p = q*(p*c)+(k+r*p) ∧
      k+r*p < p*c ∧ q*(p*c)+(k+r*p) < p*c*m := by
  have hd : (q*p+k)/p = q := by
    rw [Nat.mul_comm q p,Nat.mul_add_div hp,Nat.div_eq_of_lt hk,Nat.add_zero]
  have hm : (q*p+k)%p = k := Nat.mul_add_mod_of_lt hk
  have hkr : k+r*p < p*c := by
    have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul,Nat.mul_comm c p] at h
    omega
  dsimp only
  rw [hd,hm]
  constructor
  · omega
  constructor
  · exact hkr
  · have h := Nat.mul_le_mul_right (p*c) (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul,Nat.mul_comm m (p*c)] at h
    omega

/-- Input addressing of a workgroup exposes one next-digit sequence of the old
partial transforms, with no gather table or intermediate global transpose. -/
theorem input_index (p m q k t : Nat) :
    q*p+k+t*(p*m) = (q+t*m)*p+k := by
  simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Natural-order partial transforms in the physical Stockham device layout. -/
@[expose] def LayoutValues (p stride ω : Nat) (input values : Nat → Nat) : Prop :=
  ∀ b, b < stride → ∀ k, k < p → values (b*p+k) % goldilocksP =
    partialTransform p stride ω input b k

/-- The permutation and twiddle theorem lifted from a single workgroup to its
whole device array. `execute` is the tile-DFT interface discharged by the actual
phase/register proof; no DFT values are supplied to construction or emission. -/
theorem layout_upload (p c m ω : Nat) (input before after : Nat → Nat)
    (hp : 0 < p) (hc : 0 < c) (hperiod : modPow ω (p*c*m) = 1)
    (previous : LayoutValues p (c*m) ω input before)
    (execute : ∀ g, g < p*m → ∀ r, r < c →
      after (g/p*(p*c)+g%p+r*p) =
        dft c (modPow ω (p*m))
          (fun t => mulMod (before (g+t*(p*m))) (modPow ω (t*(g%p)*m))) r) :
    LayoutValues (p*c) m ω input after := by
  intro q hq k hk
  let low := k%p
  let high := k/p
  have hlo : low < p := Nat.mod_lt k hp
  have hhi : high < c := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using hk)
  have hsplit : low+high*p = k := by
    simpa [low,high,Nat.mul_comm] using Nat.mod_add_div k p
  let g := q*p+low
  have hg : g < p*m := by
    have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul,Nat.mul_comm m p] at h
    omega
  have hgm : g%p = low := Nat.mul_add_mod_of_lt hlo
  have hgi := (output_index p c m q low high hp hlo hhi hq).1
  have he := execute g hg high hhi
  rw [hgm] at he
  have indexEq : g/p*(p*c)+g%p+high*p = q*(p*c)+k := by
    simpa only [hsplit] using hgi
  rw [hgm] at indexEq
  rw [indexEq] at he
  have values : ∀ t, t < c → before (g+t*(p*m)) % goldilocksP =
      partialTransform p (c*m) ω input (q+t*m) low := by
    intro t ht
    have hb : q+t*m < c*m := by
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt ht)
      rw [Nat.succ_mul] at h
      omega
    change before (q*p+low+t*(p*m)) % goldilocksP = _
    rw [input_index]
    exact previous (q+t*m) hb low hlo
  have hu := upload_dft p c m ω q low high input (fun t => before (g+t*(p*m))) hperiod values
  rw [hsplit] at hu
  rw [he,hu]
  simp [partialTransform]

/-- The upload's natural output permutation covers every device position. -/
theorem output_cover (p c m i : Nat) (hp : 0 < p) (hc : 0 < c) (hi : i < p*c*m) :
    ∃ g, g < p*m ∧ ∃ r, r < c ∧ g/p*(p*c)+g%p+r*p = i := by
  let q := i/(p*c)
  let k := i%(p*c)
  have hpc : 0 < p*c := Nat.mul_pos hp hc
  have hq : q < m := (Nat.div_lt_iff_lt_mul hpc).mpr (by simpa [Nat.mul_comm] using hi)
  have hk : k < p*c := Nat.mod_lt i hpc
  let low := k%p
  let high := k/p
  have hlo : low < p := Nat.mod_lt k hp
  have hhi : high < c := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using hk)
  have hs : low+high*p = k := by simpa [low,high,Nat.mul_comm] using Nat.mod_add_div k p
  have hiq : q*(p*c)+k = i := by simpa [q,k,Nat.mul_comm] using Nat.div_add_mod i (p*c)
  refine ⟨q*p+low,?_,high,hhi,?_⟩
  · have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul,Nat.mul_comm m p] at h
    omega
  · rw [(output_index p c m q low high hp hlo hhi hq).1,hs,hiq]

theorem output_bounded (p c m bound : Nat) (after : Nat → Nat) (hp : 0 < p) (hc : 0 < c)
    (written : ∀ g, g < p*m → ∀ r, r < c → after (g/p*(p*c)+g%p+r*p) < bound)
    (i : Nat) (hi : i < p*c*m) : after i < bound := by
  obtain ⟨g,hg,r,hr,he⟩ := output_cover p c m i hp hc hi
  rw [← he]
  exact written g hg r hr

end Obend.Hardware.Gpu.Ntt.Stockham
end

section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource Obend.Hardware.ArrayHypergraph

theorem powersLoop_values (ω count start : Nat) (xs : Array Word) :
    (powersLoop ω count xs (modPow ω start)).toList = xs.toList ++
      (List.range' start count).map (fun e => BitVec.ofNat 64 (modPow ω e)) := by
  induction count generalizing start xs with
  | zero => simp [powersLoop]
  | succ count ih =>
    have next : modPow ω start * ω % goldilocksP = modPow ω (start+1) := by
      rw [modPow_add,modPow_one]
      simp
    simp only [powersLoop,next,ih,List.range'_succ,List.map_cons,Array.toList_push]
    simp [List.append_assoc]

/-- The actual linear-time source table contains the certified root powers. -/
theorem twiddlePowers_values (n ω : Nat) :
    (twiddlePowers n ω).toList =
      (List.range n).map (fun e => BitVec.ofNat 64 (modPow ω e)) := by
  have h := powersLoop_values ω n 0 #[]
  simpa [twiddlePowers,List.range_eq_range'] using h

theorem twiddlePowers_size (n ω : Nat) : (twiddlePowers n ω).size = n := by
  have h := congrArg List.length (twiddlePowers_values n ω)
  simpa using h

theorem twiddlePowers_getD (n ω i : Nat) (hi : i < n) :
    (twiddlePowers n ω).getD i 0#64 = BitVec.ofNat 64 (modPow ω i) := by
  have h := congrArg (fun xs : List Word => xs[i]?) (twiddlePowers_values n ω)
  simp only [Array.getElem?_toList,List.getElem?_map,List.getElem?_range hi,Option.map_some] at h
  simp [Array.getD_eq_getD_getElem?,h]

theorem twiddlePowers_toNat (n ω i : Nat) (hi : i < n) :
    ((twiddlePowers n ω).getD i 0#64).toNat = modPow ω i := by
  rw [twiddlePowers_getD n ω i hi]
  apply Nat.mod_eq_of_lt
  have h := modPow_lt ω i
  have hp : goldilocksP < 2^64 := by decide
  omega

open Obend.Hardware.ArrayKernel


end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource

/-- Storage-order bit reversal: the highest storage bit becomes the lowest
frequency bit. The theorem below only queries the finite domain `i < 2^bits`. -/
def reverseIndex : Nat → Nat → Nat
  | 0, _ => 0
  | bits+1, i =>
      if i < 2^bits then 2 * reverseIndex bits i
      else 2 * reverseIndex bits (i-2^bits) + 1

/-- Mathematical DIF network: one butterfly layer, then the two recursive
half-size networks. This is a specification of the register network, not an
alternative executable source builder. -/
def difStorage : Nat → (Nat → Nat) → Nat → Nat
  | 0, input, _ => input 0 % goldilocksP
  | bits+1, input, i =>
      let half := 2^bits
      if i < half then
        difStorage bits (fun j => addMod (input j) (input (half+j))) i
      else
        difStorage bits (fun j => mulMod (subMod (input j) (input (half+j)))
          (modPow (rootOfUnity (2^(bits+1))) j)) (i-half)

theorem reverseIndex_lt (bits i : Nat) (hi : i < 2^bits) : reverseIndex bits i < 2^bits := by
  induction bits generalizing i with
  | zero => simp [reverseIndex]
  | succ bits ih =>
    simp only [reverseIndex]
    have hp : 2^(bits+1) = 2^bits+2^bits := by rw [Nat.pow_succ]; omega
    rw [hp] at hi ⊢
    split
    · rename_i h
      have := ih i h
      omega
    · rename_i h
      have := ih (i-2^bits) (by omega)
      omega

theorem reverseIndex_low (bits i : Nat) (h : i < 2^bits) :
    reverseIndex (bits+1) i = 2 * reverseIndex bits i := by
  rw [reverseIndex, if_pos h]

theorem reverseIndex_high (bits i : Nat) (h : ¬ i < 2^bits) :
    reverseIndex (bits+1) i = 2 * reverseIndex bits (i-2^bits) + 1 := by
  rw [reverseIndex, if_neg h]

/-- Moving one low storage bit through bit reversal. -/
theorem reverseIndex_low_bit (bits i bit : Nat) (hi : i < 2^bits) (hb : bit < 2) :
    reverseIndex (bits+1) (2*i+bit) = reverseIndex bits i + bit*2^bits := by
  induction bits generalizing i with
  | zero =>
    have hz : i=0 := by simpa using hi
    subst i
    have cases : bit=0 ∨ bit=1 := by omega
    rcases cases with h | h <;> subst bit <;> simp [reverseIndex]
  | succ bits ih =>
    have hp : 2^(bits+1) = 2*2^bits := by rw [Nat.pow_succ, Nat.mul_comm]
    have hib : i < 2*2^bits := by simpa [hp] using hi
    by_cases h : i < 2^bits
    · have hbig : 2*i+bit < 2^(bits+1) := by rw [hp]; omega
      rw [reverseIndex_low (bits+1) _ hbig, reverseIndex_low bits i h, ih i h, hp]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · have hbig : ¬ 2*i+bit < 2^(bits+1) := by rw [hp]; omega
      have hi' : i-2^bits < 2^bits := by omega
      have he : 2*i+bit-2^(bits+1) = 2*(i-2^bits)+bit := by rw [hp]; omega
      rw [reverseIndex_high (bits+1) _ hbig, reverseIndex_high bits i h, he, ih (i-2^bits) hi', hp]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Bit reversal is its own inverse on the finite transform domain. -/
theorem reverseIndex_involution (bits i : Nat) (hi : i < 2^bits) :
    reverseIndex bits (reverseIndex bits i) = i := by
  induction bits generalizing i with
  | zero =>
    have : i=0 := by simpa using hi
    subst i
    rfl
  | succ bits ih =>
    have hp : 2^(bits+1) = 2*2^bits := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases h : i < 2^bits
    · rw [reverseIndex_low bits i h]
      have ht := reverseIndex_low_bit bits (reverseIndex bits i) 0 (reverseIndex_lt bits i h) (by decide)
      simpa [ih i h] using ht
    · have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
      rw [reverseIndex_high bits i h]
      rw [reverseIndex_low_bit bits _ 1 (reverseIndex_lt bits _ hi') (by decide), ih _ hi']
      simp only [Nat.one_mul]
      omega

/-- Universal mathematical DIF correctness, including bit-reversed storage.
It uses the same supported root function as the actual source builder. -/
theorem difStorage_eq_dft (bits : Nat) (hbits : bits ≤ 32)
    (input : Nat → Nat) (i : Nat) (hi : i < 2^bits) :
    difStorage bits input i = dft (2^bits) (rootOfUnity (2^bits)) input (reverseIndex bits i) := by
  induction bits generalizing input i with
  | zero => simp [difStorage, reverseIndex, dft, sumMod, Sum.sum]
  | succ bits ih =>
    have hb : bits < 32 := by omega
    have hp : 2^(bits+1) = 2^bits+2^bits := by rw [Nat.pow_succ]; omega
    have hh : modPow (rootOfUnity (2^(bits+1))) (2^bits) = goldilocksP-1 := by
      simpa using root_half (bits+1) (by omega) hbits
    simp only [difStorage, reverseIndex]
    split
    · rename_i h
      rw [ih (by omega) _ i h]
      have ht := dft_even (2^bits) (rootOfUnity (2^(bits+1))) input (reverseIndex bits i) hh
      rw [← hp, root_square bits hb] at ht
      exact ht.symm
    · rename_i h
      have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
      rw [ih (by omega) _ (i-2^bits) hi']
      have ht := dft_odd (2^bits) (rootOfUnity (2^(bits+1))) input (reverseIndex bits (i-2^bits)) hh
      rw [← hp, root_square bits hb] at ht
      exact ht.symm

/-- Writing the DIF storage to bit-reversed output indices produces the DFT
in ordinary frequency order. -/
theorem difStorage_reverse_eq_dft (bits : Nat) (hbits : bits ≤ 32)
    (input : Nat → Nat) (k : Nat) (hk : k < 2^bits) :
    difStorage bits input (reverseIndex bits k) = dft (2^bits) (rootOfUnity (2^bits)) input k := by
  rw [difStorage_eq_dft bits hbits input _ (reverseIndex_lt bits k hk), reverseIndex_involution bits k hk]

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt
open ArrayKernel

private theorem sum_head (n : Nat) (f : Nat → Nat) :
    Sum.sum (n+1) f = f 0 + Sum.sum n (fun i => f (1+i)) := by
  have h := Sum.append 1 n f
  rw [Nat.add_comm n 1]
  simpa only [Sum.sum, Nat.zero_add] using h

/-- The closed bit-sum formula equals the recursive storage permutation. -/
theorem reverseIndex_sum (bits i : Nat) (hi : i < 2^bits) :
    Sum.sum bits (fun b => (i / 2^b % 2) * 2^(bits-1-b)) = reverseIndex bits i := by
  induction bits generalizing i with
  | zero => rfl
  | succ bits ih =>
    have hdiv : i/2 < 2^bits := by
      have hp : 2^(bits+1) = 2*2^bits := by rw [Nat.pow_succ,Nat.mul_comm]
      rw [hp] at hi
      omega
    have hmod : i%2 < 2 := Nat.mod_lt i (by decide)
    have he : 2*(i/2)+i%2 = i := by omega
    have hr := reverseIndex_low_bit bits (i/2) (i%2) hdiv hmod
    rw [he] at hr
    rw [sum_head]
    have hs : Sum.sum bits (fun b => (i / 2^(1+b) % 2) * 2^(bits-(1+b))) =
        Sum.sum bits (fun b => ((i/2) / 2^b % 2) * 2^(bits-1-b)) := by
      apply Sum.cong
      intro b _
      have hp : 2^(1+b) = 2*2^b := by simp [Nat.pow_add]
      rw [hp, ← Nat.div_div_eq_div_mul]
      congr 2
      omega
    simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
    rw [hs, ih (i/2) hdiv, hr]
    exact Nat.add_comm _ _

private theorem reverseBits_fold_eval (bits g l : Nat) (i acc : Ix) (xs : List Nat) :
    ((xs.foldl (fun acc b => BlockNtt.addI acc
      (BlockNtt.mulI (.mod (.div i (2^b)) 2) (2^(bits-1-b)))) acc).eval g l) =
      acc.eval g l + (xs.map (fun b => (i.eval g l / 2^b % 2) * 2^(bits-1-b))).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    simp [BlockNtt.addI,BlockNtt.mulI,Ix.eval,Nat.add_assoc]

/-- Actual source index expression, for any group/lane environment and bounded
input expression, denotes the mathematical bit-reversal permutation. -/
theorem reverseBits_eval (bits g l : Nat) (i : Ix) (hi : i.eval g l < 2^bits) :
    (BlockNtt.reverseBits bits i).eval g l = reverseIndex bits (i.eval g l) := by
  rw [BlockNtt.reverseBits, reverseBits_fold_eval]
  simp only [Ix.eval,Nat.zero_add,Sum.list_range]
  exact reverseIndex_sum bits (i.eval g l) hi

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource

/-- One whole-vector DIF level. Later levels act independently in the two
halves. The closed index formula below identifies the ordinary flattened loop. -/
def difLayer : Nat → Nat → (Nat → Nat) → Nat → Nat
  | 0, _, input, i => input i
  | bits+1, 0, input, i =>
      if i < 2^bits then addMod (input i) (input (2^bits+i))
      else mulMod (subMod (input (i-2^bits)) (input i))
        (modPow (rootOfUnity (2^(bits+1))) (i-2^bits))
  | bits+1, level+1, input, i =>
      if i < 2^bits then difLayer bits level input i
      else difLayer bits level (fun j => input (2^bits+j)) (i-2^bits)

theorem difLayer_zero (input : Nat → Nat) (level i : Nat) : difLayer 0 level input i = input i := by rfl

theorem difLayer_succ_zero (bits : Nat) (input : Nat → Nat) (i : Nat) :
    difLayer (bits+1) 0 input i =
      (if i < 2^bits then addMod (input i) (input (2^bits+i))
      else mulMod (subMod (input (i-2^bits)) (input i))
        (modPow (rootOfUnity (2^(bits+1))) (i-2^bits))) := by rfl

theorem difLayer_succ_succ (bits level : Nat) (input : Nat → Nat) (i : Nat) :
    difLayer (bits+1) (level+1) input i =
      (if i < 2^bits then difLayer bits level input i
      else difLayer bits level (fun j => input (2^bits+j)) (i-2^bits)) := by rfl

/-- Sequential whole-vector layers, with a start level so register fusion is
ordinary function composition rather than a separate arithmetic semantics. -/
@[expose] def difStages (bits start : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, input => input
  | count+1, input => difLayer bits (start+count) (difStages bits start count input)

theorem difStages_fuse (bits start a b : Nat) (input : Nat → Nat) :
    difStages bits start (a+b) input =
      difStages bits (start+a) b (difStages bits start a input) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change difLayer bits (start+(a+b)) (difStages bits start (a+b) input) =
      difLayer bits ((start+a)+b) (difStages bits (start+a) b (difStages bits start a input))
    rw [ih,Nat.add_assoc]

theorem difLayer_congr (bits level : Nat) (input other : Nat → Nat)
    (h : ∀ i, i < 2^bits → input i = other i) (i : Nat) (hi : i < 2^bits) :
    difLayer bits level input i = difLayer bits level other i := by
  induction bits generalizing level input other i with
  | zero => exact h i hi
  | succ bits ih =>
    have hp : 2^(bits+1) = 2^bits+2^bits := by rw [Nat.pow_succ]; omega
    have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
    cases level with
    | zero =>
      simp only [difLayer]
      split
      · rename_i hh
        rw [h i hi,h (2^bits+i) (by rw [hp]; omega)]
      · rw [h (i-2^bits) (by rw [hp]; omega),h i hi]
    | succ level =>
      simp only [difLayer]
      split
      · rename_i hh
        exact ih level input other (fun j hj => h j (by rw [hp]; omega)) i hh
      · exact ih level _ _ (fun j hj => h (2^bits+j) (by rw [hp]; omega)) _ hi'

theorem difStages_congr (bits start count : Nat) (input other : Nat → Nat)
    (h : ∀ i, i < 2^bits → input i = other i) (i : Nat) (hi : i < 2^bits) :
    difStages bits start count input i = difStages bits start count other i := by
  induction count generalizing i with
  | zero => exact h i hi
  | succ count ih =>
    exact difLayer_congr bits (start+count) _ _
      (fun j hj => ih j hj) i hi

/-- Remaining whole-vector levels project to the lower half's level sequence. -/
theorem difStages_low (bits start count : Nat) (input : Nat → Nat)
    (i : Nat) (hi : i < 2^bits) :
    difStages (bits+1) (start+1) count input i = difStages bits start count input i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [difStages]
    have he : start+1+count = (start+count)+1 := by omega
    rw [he,difLayer,if_pos hi]
    apply difLayer_congr
    · exact fun j hj => ih j hj
    · exact hi

/-- Remaining whole-vector levels project to the upper half's level sequence. -/
theorem difStages_high (bits start count : Nat) (input : Nat → Nat)
    (i : Nat) (hi : i < 2^bits) :
    difStages (bits+1) (start+1) count input (2^bits+i) =
      difStages bits start count (fun j => input (2^bits+j)) i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [difStages]
    have he : start+1+count = (start+count)+1 := by omega
    rw [he,difLayer,if_neg (by omega : ¬ 2^bits+i < 2^bits),Nat.add_sub_cancel_left]
    apply difLayer_congr
    · exact fun j hj => ih j hj
    · exact hi

/-- Every sequential DIF level has the recursive network semantics. The sole
canonical-input premise accounts for the zero-layer size-one transform. -/
theorem difStages_eq_storage (bits : Nat) (input : Nat → Nat)
    (canonical : ∀ i, i < 2^bits → input i < goldilocksP)
    (i : Nat) (hi : i < 2^bits) :
    difStages bits 0 bits input i = difStorage bits input i := by
  induction bits generalizing input i with
  | zero =>
    have hz : i=0 := by simpa using hi
    subst i
    simp only [difStages,difStorage]
    exact (Nat.mod_eq_of_lt (canonical 0 hi)).symm
  | succ bits ih =>
    have hp : 2^(bits+1) = 2^bits+2^bits := by rw [Nat.pow_succ]; omega
    have hsplit := difStages_fuse (bits+1) 0 1 bits input
    have he : bits+1=1+bits := by omega
    rw [← he] at hsplit
    rw [hsplit]
    change difStages (bits+1) 1 bits (difLayer (bits+1) 0 input) i = _
    by_cases h : i < 2^bits
    · rw [difStages_low bits 0 bits _ i h]
      have hstage := difStages_congr bits 0 bits (difLayer (bits+1) 0 input)
        (fun j => addMod (input j) (input (2^bits+j)))
        (by intro j hj; simp only [difLayer,if_pos hj]) i h
      rw [hstage, ih _ (by intro j hj; exact Nat.mod_lt _ (by decide)) i h]
      simp only [difStorage,if_pos h]
    · have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
      have he : i = 2^bits+(i-2^bits) := by omega
      conv => lhs; rw [he]
      rw [difStages_high bits 0 bits _ _ hi']
      have hstage := difStages_congr bits 0 bits
        (fun j => difLayer (bits+1) 0 input (2^bits+j))
        (fun j => mulMod (subMod (input j) (input (2^bits+j)))
          (modPow (rootOfUnity (2^(bits+1))) j))
        (by intro j hj; simp only [difLayer,if_neg (by omega : ¬ 2^bits+j < 2^bits),Nat.add_sub_cancel_left])
        (i-2^bits) hi'
      rw [hstage, ih _ (by intro j hj; exact Nat.mod_lt _ (by decide)) _ hi']
      simp only [difStorage,if_neg h]

/-- Closed flattened butterfly addressing. `half` is the current pair distance;
all blocks execute the same pair operation from one immutable input snapshot. -/
def flatButterfly (half root : Nat) (input : Nat → Nat) (i : Nat) : Nat :=
  let within :=  i % (2*half)
  let low := i-within + within%half
  if within < half then addMod (input low) (input (low+half))
  else mulMod (subMod (input low) (input (low+half))) (modPow root (within%half))

theorem flatButterfly_shift (half root offset : Nat) (input : Nat → Nat)
    (aligned : offset % (2*half) = 0) (i : Nat) :
    flatButterfly half root input (offset+i) =
      flatButterfly half root (fun j => input (offset+j)) i := by
  have hm : (offset+i)%(2*half) = i%(2*half) := by
    rw [Nat.add_mod,aligned]
    simp
  have hl := Nat.mod_le i (2*half)
  have he : offset+i-i%(2*half) = offset+(i-i%(2*half)) := by omega
  simp only [flatButterfly,hm,he,Nat.add_assoc]

/-- Point readback for the lower write of one flattened butterfly pair. -/
theorem flatButterfly_pair_low (half root base j : Nat) (input : Nat → Nat)
    (aligned : base % (2*half) = 0) (hj : j < half) :
    flatButterfly half root input (base+j) =
      addMod (input (base+j)) (input (base+j+half)) := by
  rw [flatButterfly_shift half root base input aligned j]
  have hj2 : j < 2*half := by omega
  simp only [flatButterfly,Nat.mod_eq_of_lt hj2,Nat.mod_eq_of_lt hj,
    Nat.sub_self,Nat.zero_add,if_pos hj,Nat.add_assoc]

/-- Point readback for the upper write of one flattened butterfly pair. -/
theorem flatButterfly_pair_high (half root base j : Nat) (input : Nat → Nat)
    (aligned : base % (2*half) = 0) (hj : j < half) :
    flatButterfly half root input (base+j+half) =
      mulMod (subMod (input (base+j)) (input (base+j+half))) (modPow root j) := by
  rw [Nat.add_assoc base j half,flatButterfly_shift half root base input aligned (j+half)]
  have hj2 : j+half < 2*half := by omega
  have hm : (j+half)%half=j := by rw [Nat.add_mod_right,Nat.mod_eq_of_lt hj]
  have hn : ¬ j+half < half := by omega
  simp only [flatButterfly,Nat.mod_eq_of_lt hj2,hm,Nat.sub_self,Nat.zero_add,
    if_neg hn,Nat.add_assoc]

/-- The recursive level description is the ordinary flat pair-address loop. -/
theorem difLayer_flat (bits level : Nat) (input : Nat → Nat)
    (hl : level < bits) (i : Nat) (hi : i < 2^bits) :
    difLayer bits level input i =
      flatButterfly (2^(bits-level-1)) (rootOfUnity (2^(bits-level))) input i := by
  induction bits generalizing level input i with
  | zero => omega
  | succ bits ih =>
    have hp : 2^(bits+1) = 2*2^bits := by rw [Nat.pow_succ,Nat.mul_comm]
    cases level with
    | zero =>
      have him : i%(2*2^bits)=i := Nat.mod_eq_of_lt (by rw [←hp]; exact hi)
      simp only [Nat.sub_zero,Nat.add_sub_cancel,difLayer,flatButterfly,him,Nat.sub_self,Nat.zero_add]
      by_cases h : i<2^bits
      · simp only [if_pos h,Nat.mod_eq_of_lt h]
        rw [Nat.add_comm i]
      · have hrest : i-2^bits < 2^bits := by rw [hp] at hi; omega
        have hm : i%2^bits=i-2^bits := by
          rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt hrest]
        have he : i-2^bits+2^bits=i := by omega
        simp only [if_neg h,hm,he]
    | succ level =>
      have hl' : level<bits := by omega
      have hs : bits+1-(level+1) = bits-level := by omega
      simp only [hs,difLayer]
      by_cases h : i<2^bits
      · rw [if_pos h]
        exact ih level input hl' i h
      · have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
        rw [if_neg h,ih level _ hl' _ hi']
        have hpow : 2 * 2^(bits-level-1) = 2^(bits-level) := by
          rw [Nat.mul_comm,← Nat.pow_succ]
          congr 1
          omega
        have halign : 2^bits % (2*2^(bits-level-1)) = 0 := by
          rw [hpow]
          exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
        have he : i=2^bits+(i-2^bits) := by omega
        conv => rhs; rw [he]
        exact (flatButterfly_shift _ _ _ input halign _).symm

/-- Full flat-level execution is the DFT in bit-reversed storage. -/
theorem difStages_eq_dft (bits : Nat) (hbits : bits ≤ 32) (input : Nat → Nat)
    (canonical : ∀ i, i < 2^bits → input i < goldilocksP)
    (i : Nat) (hi : i < 2^bits) :
    difStages bits 0 bits input i = dft (2^bits) (rootOfUnity (2^bits)) input (reverseIndex bits i) := by
  rw [difStages_eq_storage bits input canonical i hi,difStorage_eq_dft bits hbits input i hi]

/-- Direct flattened-layer semantics for the register schedule. -/
def flatStages (bits start : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, input => input
  | count+1, input => flatButterfly (2^(bits-(start+count)-1))
      (rootOfUnity (2^(bits-(start+count)))) (flatStages bits start count input)

theorem flatStages_eq (bits start count : Nat) (hc : start+count ≤ bits)
    (input : Nat → Nat) (i : Nat) (hi : i < 2^bits) :
    flatStages bits start count input i = difStages bits start count input i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [flatStages,difStages]
    rw [← difLayer_flat bits (start+count) _ (by omega) i hi]
    exact difLayer_congr bits (start+count) _ _ (fun j hj => ih (by omega) j hj) i hi

/-- Consecutive fused flattened passes denote one uninterrupted level sequence. -/
theorem flatStages_fuse (bits start a b : Nat) (hc : start+a+b ≤ bits)
    (input : Nat → Nat) (i : Nat) (hi : i < 2^bits) :
    flatStages bits (start+a) b (flatStages bits start a input) i =
      flatStages bits start (a+b) input i := by
  rw [flatStages_eq bits (start+a) b hc _ i hi,
    flatStages_eq bits start (a+b) (by omega) input i hi,difStages_fuse]
  exact difStages_congr bits (start+a) b _ _
    (fun j hj => flatStages_eq bits start a (by omega) input j hj) i hi

theorem flatStages_eq_dft (bits : Nat) (hbits : bits ≤ 32) (input : Nat → Nat)
    (canonical : ∀ i, i < 2^bits → input i < goldilocksP)
    (i : Nat) (hi : i < 2^bits) :
    flatStages bits 0 bits input i = dft (2^bits) (rootOfUnity (2^bits)) input (reverseIndex bits i) := by
  rw [flatStages_eq bits 0 bits (by omega) input i hi,difStages_eq_dft bits hbits input canonical i hi]

/-- Arbitrary word inputs are reduced by the actual first-stage canonicalizer;
the canonicalized flat network still denotes their original modular DFT. -/
theorem flatStages_canonical_eq_dft (bits : Nat) (hbits : bits ≤ 32) (input : Nat → Nat)
    (i : Nat) (hi : i < 2^bits) :
    flatStages bits 0 bits (fun j => input j % goldilocksP) i =
      dft (2^bits) (rootOfUnity (2^bits)) input (reverseIndex bits i) := by
  rw [flatStages_eq_dft bits hbits _ (by intro j hj; exact Nat.mod_lt _ (by decide)) i hi,dft_input_mod]

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt.RegisterValues
open GoldilocksSource

/-- A mathematical register-value update, used to state the refinement of the
actual phase source loop. It creates no graph, code, phase, or dispatch. -/
def update (v : Nat → Nat) (i value : Nat) : Nat → Nat := fun j => if j=i then value else v j

theorem update_eq (v : Nat → Nat) (i value : Nat) :
    update v i value = fun j => if j=i then value else v j := by rfl

/-- Field denotation of one source butterfly pair. -/
@[expose] def pairStep (bit twiddle j : Nat) (values : Nat → Nat) : Nat → Nat :=
  let i0 := 2*j-j%bit
  let i1 := i0+bit
  update (update values i0 ((values i0+values i1)%goldilocksP)) i1
    ((((values i0+goldilocksP-values i1)%goldilocksP)*twiddle)%goldilocksP)

/-- Denotation of the source's sequential pair loop, preserving operand order. -/
def roundValues (pairs bit : Nat) (twiddle : Nat → Nat) (values : Nat → Nat) : Nat → Nat :=
  (List.range pairs).foldl (fun v j => pairStep bit (twiddle j) j v) values

theorem roundValues_eq (pairs bit : Nat) (twiddle : Nat → Nat) (values : Nat → Nat) :
    roundValues pairs bit twiddle values = (List.range pairs).foldl (fun v j => pairStep bit (twiddle j) j v) values := by rfl

end Obend.Hardware.Gpu.Ntt.RegisterValues
end

section
namespace Obend.Hardware.Gpu.Ntt
open ArrayKernel GoldilocksSource

/-- Numeric denotation of the actual lane/register source index. -/
def laneRegisterIndex (radix stride lane r : Nat) : Nat :=
  lane/stride*(radix*stride) + lane%stride + r*stride

theorem laneRegisterIndex_eq (radix stride lane r : Nat) :
    laneRegisterIndex radix stride lane r = lane/stride*(radix*stride) + lane%stride + r*stride := by rfl

theorem phaseIndex_eval (radix stride r group lane : Nat) :
    (BlockNtt.phaseIndex radix stride r).eval group lane = laneRegisterIndex radix stride lane r := by rfl

theorem laneRegisterIndex_decomp (radix stride lane r : Nat) :
    laneRegisterIndex radix stride lane r = stride*(radix*(lane/stride)+r)+lane%stride := by
  simp only [laneRegisterIndex,Nat.mul_add]
  simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem laneRegisterIndex_div (radix stride lane r : Nat) (hs : 0 < stride) :
    laneRegisterIndex radix stride lane r / stride = radix*(lane/stride)+r := by
  rw [laneRegisterIndex_decomp,Nat.mul_add_div hs]
  have hm := Nat.mod_lt lane hs
  rw [Nat.div_eq_of_lt hm,Nat.add_zero]

theorem laneRegisterIndex_mod (radix stride lane r : Nat) :
    laneRegisterIndex radix stride lane r % stride = lane%stride := by
  rw [laneRegisterIndex_decomp]
  simp

/-- Register coordinate recovered from the actual physical index. -/
theorem laneRegisterIndex_register (radix stride lane r : Nat) (hs : 0 < stride) (hr : r < radix) :
    laneRegisterIndex radix stride lane r / stride % radix = r := by
  rw [laneRegisterIndex_div _ _ _ _ hs]
  simp [Nat.mod_eq_of_lt hr]

/-- Lane coordinate recovered from the actual physical index. -/
theorem laneRegisterIndex_lane (radix stride lane r : Nat) (hs : 0 < stride) (hr : r < radix) :
    (laneRegisterIndex radix stride lane r / stride / radix)*stride +
      laneRegisterIndex radix stride lane r % stride = lane := by
  rw [laneRegisterIndex_div _ _ _ _ hs,laneRegisterIndex_mod,
    Nat.mul_add_div (by omega : 0 < radix),Nat.div_eq_of_lt hr,Nat.add_zero]
  have h := Nat.mod_add_div lane stride
  rw [Nat.mul_comm (lane/stride) stride]
  omega

/-- The lane/register map is injective; no pair of distinct invocations writes
the same tile position. This is an actual source-coordinate fact. -/
theorem laneRegisterIndex_injective (radix stride lane lane' r r' : Nat)
    (hs : 0 < stride) (hr : r < radix) (hr' : r' < radix)
    (h : laneRegisterIndex radix stride lane r = laneRegisterIndex radix stride lane' r') :
    lane=lane' ∧ r=r' := by
  constructor
  · have hl := laneRegisterIndex_lane radix stride lane r hs hr
    have hl' := laneRegisterIndex_lane radix stride lane' r' hs hr'
    rw [h] at hl
    omega
  · have hl := laneRegisterIndex_register radix stride lane r hs hr
    have hl' := laneRegisterIndex_register radix stride lane' r' hs hr'
    rw [h] at hl
    omega

theorem laneRegisterIndex_lt (radix stride blocks lane r : Nat)
    (hs : 0 < stride) (hl : lane < blocks*stride) (hr : r < radix) :
    laneRegisterIndex radix stride lane r < (radix*blocks)*stride := by
  apply (Nat.div_lt_iff_lt_mul hs).mp
  rw [laneRegisterIndex_div _ _ _ _ hs]
  have hb : lane/stride < blocks := (Nat.div_lt_iff_lt_mul hs).mpr hl
  calc
    radix*(lane/stride)+r < radix*(lane/stride)+radix := Nat.add_lt_add_left hr _
    _ = radix*(lane/stride+1) := by simp [Nat.mul_add]
    _ ≤ radix*blocks := Nat.mul_le_mul_left _ (by omega)

/-- Every tile cell has an explicit lane/register preimage. -/
theorem laneRegisterIndex_cover (radix stride i : Nat) (hs : 0 < stride) (hr : 0 < radix) :
    laneRegisterIndex radix stride ((i/stride/radix)*stride+i%stride) (i/stride%radix) = i := by
  have hm := Nat.mod_lt i hs
  have hl : ((i/stride/radix)*stride+i%stride)/stride = i/stride/radix := by
    rw [Nat.mul_comm (i/stride/radix),Nat.mul_add_div hs,Nat.div_eq_of_lt hm,Nat.add_zero]
  have hmod : ((i/stride/radix)*stride+i%stride)%stride = i%stride := by simp
  rw [laneRegisterIndex_decomp,hl,hmod]
  have h1 := Nat.mod_add_div (i/stride) radix
  have h2 := Nat.mod_add_div i stride
  have he : radix*(i/stride/radix)+i/stride%radix=i/stride := by omega
  rw [he]
  omega

/-- Preimage lanes lie in the launched domain, rather than merely in an
unbounded arithmetic extension of the index map. -/
theorem laneRegisterIndex_cover_lane_lt (radix stride blocks i : Nat)
    (hs : 0 < stride) (hr : 0 < radix) (hi : i < (radix*blocks)*stride) :
    (i/stride/radix)*stride+i%stride < blocks*stride := by
  have hq : i/stride < radix*blocks := (Nat.div_lt_iff_lt_mul hs).mpr hi
  have hb : i/stride/radix < blocks := (Nat.div_lt_iff_lt_mul hr).mpr (by simpa [Nat.mul_comm] using hq)
  have hm := Nat.mod_lt i hs
  have hl := Nat.mul_le_mul_right stride (by omega : i/stride/radix+1 ≤ blocks)
  rw [Nat.add_mul] at hl
  omega

/-- The actual stride division is exact for a supported fused round count. -/
theorem phase_stride (bits done degree : Nat) (h : done+degree ≤ bits) :
    2^bits / (2^done * 2^degree) = 2^(bits-done-degree) := by
  rw [← Nat.pow_add,Nat.pow_div h (by decide)]
  congr 1
  omega

/-- Source load expression, including the first upload's strided input map. -/
theorem phaseLoadIndex_eval (n count radix stride r group lane : Nat) (first : Bool) :
    (BlockNtt.phaseLoadIndex n count radix stride first r).eval group lane =
      if first then group+laneRegisterIndex radix stride lane r*(n/count)
      else laneRegisterIndex radix stride lane r := by
  cases first <;> rfl

/-- Source output expression, including its actual bit-reversal permutation. -/
theorem phaseSaveIndex_eval (count bits p radix stride r group lane : Nat) (last : Bool)
    (hi : laneRegisterIndex radix stride lane r < 2^bits) :
    (BlockNtt.phaseSaveIndex count bits p radix stride last r).eval group lane =
      if last then group/p*(p*count)+group%p+reverseIndex bits (laneRegisterIndex radix stride lane r)*p
      else laneRegisterIndex radix stride lane r := by
  cases last with
  | false => rfl
  | true =>
    simp only [BlockNtt.phaseSaveIndex,ite_true,BlockNtt.addI,BlockNtt.mulI,Ix.eval]
    rw [reverseBits_eval bits group lane (BlockNtt.phaseIndex radix stride r) hi]
    rfl

/-- Source pair-register arithmetic, before multiplying by the physical stride. -/
theorem pair_register_low (j bit : Nat) :
    2*j-j%bit = 2*(bit*(j/bit))+j%bit := by
  have h := Nat.mod_add_div j bit
  omega

def phasePairBase (radix stride lane j bit : Nat) : Nat :=
  lane/stride*(radix*stride) + 2*(bit*(j/bit))*stride

def phasePairOffset (stride lane j bit : Nat) : Nat :=
  lane%stride + j%bit*stride

theorem phasePairOffset_eq (stride lane j bit : Nat) :
    phasePairOffset stride lane j bit = lane%stride + j%bit*stride := by rfl

theorem phase_pair_low_index (radix stride lane j bit : Nat) :
    laneRegisterIndex radix stride lane (2*j-j%bit) =
      phasePairBase radix stride lane j bit + phasePairOffset stride lane j bit := by
  rw [laneRegisterIndex,pair_register_low,Nat.add_mul]
  simp [phasePairBase,phasePairOffset,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem phase_pair_high_index (radix stride lane j bit : Nat) :
    laneRegisterIndex radix stride lane (2*j-j%bit+bit) =
      phasePairBase radix stride lane j bit + phasePairOffset stride lane j bit + bit*stride := by
  have h := phase_pair_low_index radix stride lane j bit
  simpa only [laneRegisterIndex,Nat.add_mul,Nat.add_assoc] using congrArg (· + bit*stride) h

theorem phase_pair_offset_lt (stride lane j bit : Nat) (hs : 0 < stride) (hb : 0 < bit) :
    phasePairOffset stride lane j bit < bit*stride := by
  have hm := Nat.mod_lt lane hs
  have hj := Nat.mod_lt j hb
  have hx := Nat.mul_le_mul_right stride (by omega : j%bit+1 ≤ bit)
  rw [Nat.add_mul,Nat.one_mul] at hx
  unfold phasePairOffset
  omega

theorem phase_pair_aligned (radix stride lane j bit : Nat) (hd : 2*bit ∣ radix) :
    phasePairBase radix stride lane j bit % (2*(bit*stride)) = 0 := by
  obtain ⟨q,hq⟩ := hd
  have he : phasePairBase radix stride lane j bit =
      (2*(bit*stride))*((lane/stride)*q+j/bit) := by
    simp [phasePairBase,hq,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  rw [he,Nat.mul_mod_right]

/-- The flattened level at the source's exact lower register coordinate. -/
theorem phase_pair_low_value (radix stride lane j bit root : Nat) (input : Nat → Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) :
    flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane (2*j-j%bit)) =
      addMod (input (laneRegisterIndex radix stride lane (2*j-j%bit)))
        (input (laneRegisterIndex radix stride lane (2*j-j%bit+bit))) := by
  rw [phase_pair_low_index,phase_pair_high_index]
  exact flatButterfly_pair_low _ _ _ _ input
    (phase_pair_aligned radix stride lane j bit hd) (phase_pair_offset_lt stride lane j bit hs hb)

/-- The flattened level at the source's exact upper register coordinate. -/
theorem phase_pair_high_value (radix stride lane j bit root : Nat) (input : Nat → Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) :
    flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane (2*j-j%bit+bit)) =
      mulMod (subMod (input (laneRegisterIndex radix stride lane (2*j-j%bit)))
        (input (laneRegisterIndex radix stride lane (2*j-j%bit+bit))))
        (modPow root (phasePairOffset stride lane j bit)) := by
  rw [phase_pair_low_index,phase_pair_high_index]
  exact flatButterfly_pair_high _ _ _ _ input
    (phase_pair_aligned radix stride lane j bit hd) (phase_pair_offset_lt stride lane j bit hs hb)

/-- Source register pair distance is the whole-vector level's exact half-size. -/
theorem phase_pair_distance (bits done degree round : Nat)
    (h : done+degree ≤ bits) (hr : round < degree) :
    (2^degree / 2^(round+1)) * (2^bits / (2^done*2^degree)) =
      2^(bits-(done+round)-1) := by
  rw [phase_stride bits done degree h,Nat.pow_div (by omega) (by decide),←Nat.pow_add]
  congr 1
  omega

/-- Source global-table twiddle is exactly the root used by the flattened level. -/
theorem phase_twiddle (total bits done round offset : Nat)
    (ht : total ≤ 32) (hb : bits ≤ total) (hl : done+round ≤ bits) :
    modPow (rootOfUnity (2^total)) (offset*(2^(done+round)*(2^total/2^bits))) =
      modPow (rootOfUnity (2^(bits-(done+round)))) offset := by
  rw [root_layer_twiddle bits (done+round) offset hl (by omega)]
  have hr := root_subtransform total bits hb ht
  rw [←hr,←modPow_mul,Nat.pow_div hb (by decide)]
  congr 1
  simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- Both registers of a source butterfly use the same already-proved transpose
map (radix two), making disjointness and coverage reusable facts. -/
theorem pair_register_as_index (j bit side : Nat) :
    2*j-j%bit+side*bit = laneRegisterIndex 2 bit j side := by
  rw [pair_register_low,laneRegisterIndex_decomp]
  simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem pair_register_injective (j j' bit side side' : Nat) (hb : 0 < bit)
    (hs : side < 2) (hs' : side' < 2)
    (h : 2*j-j%bit+side*bit = 2*j'-j'%bit+side'*bit) : j=j' ∧ side=side' := by
  simp only [pair_register_as_index] at h
  exact laneRegisterIndex_injective 2 bit j j' side side' hb hs hs' h

theorem pair_register_bounds (radix j bit : Nat) (hb : 0 < bit)
    (hd : 2*bit ∣ radix) (hj : j < radix/2) :
    2*j-j%bit < radix ∧ 2*j-j%bit+bit < radix := by
  obtain ⟨q,hq⟩ := hd
  have hj' : j < q*bit := by
    rw [hq] at hj
    have he : (2*bit*q)/2 = q*bit := by
      rw [Nat.mul_assoc,Nat.mul_div_right _ (by decide : 0<2),Nat.mul_comm]
    rwa [he] at hj
  have bound (side : Nat) (hs : side < 2) : 2*j-j%bit+side*bit < radix := by
    rw [pair_register_as_index]
    have h := laneRegisterIndex_lt 2 bit q j side hb hj' hs
    have he : (2*q)*bit = radix := by rw [hq]; simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rwa [he] at h
  constructor
  · simpa using bound 0 (by decide)
  · simpa using bound 1 (by decide)

/-- The source's computed bit distance is positive and divides its radix. -/
theorem phase_bit (degree round : Nat) (hr : round < degree) :
    0 < 2^degree/2^(round+1) ∧ 2*(2^degree/2^(round+1)) ∣ 2^degree := by
  rw [Nat.pow_div (by omega) (by decide)]
  constructor
  · exact Nat.two_pow_pos _
  · have he : 2 * 2^(degree-(round+1)) = 2^(degree-round) := by
      rw [Nat.mul_comm,←Nat.pow_succ]
      congr 1
      omega
    rw [he]
    exact Nat.pow_dvd_pow 2 (by omega)

/-- Bounds needed by the actual `regs[i0]!` and `regs[i1]!` accesses. -/
theorem phase_register_bounds (degree round j : Nat) (hr : round < degree)
    (hj : j < 2^degree/2) :
    2*j-j%(2^degree/2^(round+1)) < 2^degree ∧
      2*j-j%(2^degree/2^(round+1)) + 2^degree/2^(round+1) < 2^degree := by
  have hb := phase_bit degree round hr
  exact pair_register_bounds (2^degree) j _ hb.1 hb.2 hj

/-- Actual launched lanes and allocated radix imply a bounded shared-tile index. -/
theorem phase_index_lt (bits done degree lane r : Nat)
    (h : done+degree ≤ bits) (hl : lane < 2^bits/2^degree) (hr : r < 2^degree) :
    laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r < 2^bits := by
  rw [phase_stride bits done degree h]
  have he : 2^bits = (2^degree*2^done)*2^(bits-done-degree) := by
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega
  have hlanes : 2^bits/2^degree = 2^done*2^(bits-done-degree) := by
    conv => lhs; rw [he,Nat.mul_assoc,Nat.mul_div_right _ (Nat.two_pow_pos degree)]
  rw [hlanes] at hl
  have hb := laneRegisterIndex_lt (2^degree) (2^(bits-done-degree)) (2^done) lane r
    (Nat.two_pow_pos _) hl hr
  rwa [←he] at hb

/-- Actual first-phase strided loads stay within the original transform input. -/
theorem phase_load_first_lt (total bits done degree group lane r : Nat)
    (hb : bits ≤ total) (h : done+degree ≤ bits)
    (hg : group < 2^total/2^bits) (hl : lane < 2^bits/2^degree) (hr : r < 2^degree) :
    (BlockNtt.phaseLoadIndex (2^total) (2^bits) (2^degree)
      (2^bits/(2^done*2^degree)) true r).eval group lane < 2^total := by
  rw [phaseLoadIndex_eval]
  simp only [ite_true]
  have hi := phase_index_lt bits done degree lane r h hl hr
  have hp : 2^bits*(2^total/2^bits) = 2^total :=
    Nat.mul_div_cancel_left' (Nat.pow_dvd_pow 2 hb)
  have hx := Nat.mul_le_mul_right (2^total/2^bits) (by omega :
    laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r+1 ≤ 2^bits)
  rw [Nat.add_mul,Nat.one_mul,hp] at hx
  omega

/-- Later-phase shared loads stay within the tile. -/
theorem phase_load_later_lt (n bits done degree group lane r : Nat)
    (h : done+degree ≤ bits) (hl : lane < 2^bits/2^degree) (hr : r < 2^degree) :
    (BlockNtt.phaseLoadIndex n (2^bits) (2^degree)
      (2^bits/(2^done*2^degree)) false r).eval group lane < 2^bits :=
  phase_index_lt bits done degree lane r h hl hr

/-- Every actual register-round exponent is below the complete twiddle table. -/
theorem phase_round_exponent_lt (total bits done degree round lane j : Nat)
    (hb : bits ≤ total) (h : done+degree ≤ bits) (hr : round < degree) :
    phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)) *
      (2^(done+round)*(2^total/2^bits)) < 2^total := by
  have hs : 0 < 2^bits/(2^done*2^degree) := by
    rw [phase_stride bits done degree h]
    exact Nat.two_pow_pos _
  have hbit := (phase_bit degree round hr).1
  have hoff := phase_pair_offset_lt _ lane j _ hs hbit
  rw [phase_pair_distance bits done degree round h hr] at hoff
  have hscale : 0 < 2^(done+round)*(2^total/2^bits) := by
    rw [Nat.pow_div hb (by decide)]
    exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have hx := Nat.mul_lt_mul_of_pos_right hoff hscale
  have he : 2^(bits-(done+round)-1)*(2^(done+round)*(2^total/2^bits)) = 2^(total-1) := by
    rw [Nat.pow_div hb (by decide),←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega
  rw [he] at hx
  exact Nat.lt_trans hx (Nat.pow_lt_pow_of_lt (by decide) (by omega))

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt.RegisterValues
open GoldilocksSource

abbrev pairIndex (bit j side : Nat) : Nat := 2*j-j%bit+side*bit

theorem pairStep_low (bit twiddle j : Nat) (hb : 0 < bit) (values : Nat → Nat) :
    pairStep bit twiddle j values (2*j-j%bit) =
      (values (2*j-j%bit)+values (2*j-j%bit+bit))%goldilocksP := by
  simp [pairStep,update,show bit ≠ 0 by omega]

theorem pairStep_high (bit twiddle j : Nat) (values : Nat → Nat) :
    pairStep bit twiddle j values (2*j-j%bit+bit) =
      (((values (2*j-j%bit)+goldilocksP-values (2*j-j%bit+bit))%goldilocksP)*twiddle)%goldilocksP := by
  simp [pairStep,update]

/-- A different pair cannot change either register of this pair. -/
theorem pairStep_frame_other (bit twiddle j target side : Nat) (hb : 0 < bit)
    (hs : side < 2) (hne : j ≠ target) (values : Nat → Nat) :
    pairStep bit twiddle j values (pairIndex bit target side) = values (pairIndex bit target side) := by
  have hl : pairIndex bit target side ≠ 2*j-j%bit := by
    intro he
    have hx := pair_register_injective target j bit side 0 hb hs (by decide) (by simpa using he)
    exact hne hx.1.symm
  have hh : pairIndex bit target side ≠ 2*j-j%bit+bit := by
    intro he
    have hx := pair_register_injective target j bit side 1 hb hs (by decide) (by simpa using he)
    exact hne hx.1.symm
  simp [pairStep,update,hl,hh]

theorem pairStep_pair_congr (bit twiddle j side : Nat) (hb : 0 < bit) (hs : side < 2)
    (v w : Nat → Nat) (h0 : v (2*j-j%bit)=w (2*j-j%bit))
    (h1 : v (2*j-j%bit+bit)=w (2*j-j%bit+bit)) :
    pairStep bit twiddle j v (pairIndex bit j side) = pairStep bit twiddle j w (pairIndex bit j side) := by
  have hside : side=0 ∨ side=1 := by omega
  rcases hside with rfl | rfl
  · simpa only [pairIndex,Nat.zero_mul,Nat.add_zero,pairStep_low bit twiddle j hb,h0,h1]
  · simpa only [pairIndex,Nat.one_mul,pairStep_high,h0,h1]

private theorem fold_frame (xs : List Nat) (bit target side : Nat) (hb : 0 < bit) (hs : side < 2)
    (twiddle values : Nat → Nat) (hne : ∀ j, j ∈ xs → j ≠ target) :
    (xs.foldl (fun v j => pairStep bit (twiddle j) j v) values) (pairIndex bit target side) =
      values (pairIndex bit target side) := by
  induction xs generalizing values with
  | nil => rfl
  | cons j xs ih =>
    rw [List.foldl_cons,ih _ (fun k hk => hne k (by simp [hk]))]
    exact pairStep_frame_other bit _ j target side hb hs (hne j (by simp)) values

/-- Sequential updates read the original pair values because pair footprints
are disjoint. This identifies the actual order-preserving fold, not a parallel oracle. -/
theorem fold_pair (xs : List Nat) (bit target side : Nat) (hb : 0 < bit) (hs : side < 2)
    (twiddle values : Nat → Nat) (hu : xs.Nodup) (ht : target ∈ xs) :
    (xs.foldl (fun v j => pairStep bit (twiddle j) j v) values) (pairIndex bit target side) =
      pairStep bit (twiddle target) target values (pairIndex bit target side) := by
  induction xs generalizing values with
  | nil => cases ht
  | cons j xs ih =>
    have hn := List.nodup_cons.mp hu
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ht with he | htail
    · subst target
      apply fold_frame xs bit j side hb hs twiddle
      intro k hk he
      subst k
      exact hn.1 hk
    · rw [ih _ hn.2 htail]
      have hne : j ≠ target := fun he => hn.1 (he.symm ▸ htail)
      apply pairStep_pair_congr bit _ target side hb hs
      · simpa [pairIndex] using pairStep_frame_other bit (twiddle j) j target 0 hb (by decide) hne values
      · simpa [pairIndex] using pairStep_frame_other bit (twiddle j) j target 1 hb (by decide) hne values

theorem roundValues_pair (pairs bit target side : Nat) (hb : 0 < bit) (hs : side < 2)
    (twiddle values : Nat → Nat) (ht : target < pairs) :
    roundValues pairs bit twiddle values (pairIndex bit target side) =
      pairStep bit (twiddle target) target values (pairIndex bit target side) :=
  fold_pair _ bit target side hb hs twiddle values (List.nodup_range) (List.mem_range.mpr ht)

/-- Both source pair writes have the whole-vector flattened butterfly value. -/
theorem roundValues_flat_pair (radix stride lane bit root j side : Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) (hj : j < radix/2) (hside : side < 2)
    (input values : Nat → Nat)
    (hvalues : ∀ r, r<radix → values r=input (laneRegisterIndex radix stride lane r))
    (canonical : ∀ r, r<radix → values r<goldilocksP) :
    roundValues (radix/2) bit (fun j => modPow root (phasePairOffset stride lane j bit)) values (pairIndex bit j side) =
      flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane (pairIndex bit j side)) := by
  rw [roundValues_pair _ _ _ _ hb hside _ _ hj]
  have hr := pair_register_bounds radix j bit hb hd hj
  have h0 := hvalues _ hr.1
  have h1 := hvalues _ hr.2
  have hc := canonical _ hr.2
  have hcases : side=0 ∨ side=1 := by omega
  rcases hcases with rfl | rfl
  · simp only [pairIndex,Nat.zero_mul,Nat.add_zero,pairStep_low bit _ j hb,
      phase_pair_low_value radix stride lane j bit root input hs hb hd]
    simpa only [addMod,h0,h1]
  · simp only [pairIndex,Nat.one_mul,pairStep_high,
      phase_pair_high_value radix stride lane j bit root input hs hb hd]
    rw [←h0,←h1,subMod_eq_nat _ _ hc]
    rfl

theorem pair_cover (radix bit r : Nat) (hb : 0 < bit) (hd : 2*bit ∣ radix) (hr : r < radix) :
    ∃ j, j<radix/2 ∧ ∃ side, side<2 ∧ pairIndex bit j side=r := by
  obtain ⟨q,hq⟩ := hd
  have he : radix=(2*q)*bit := by rw [hq]; simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hcount : radix/2=q*bit := by
    rw [he,Nat.mul_assoc,Nat.mul_div_right _ (by decide : 0<2)]
  refine ⟨(r/bit/2)*bit+r%bit,?_,r/bit%2,Nat.mod_lt _ (by decide),?_⟩
  · rw [hcount]
    exact laneRegisterIndex_cover_lane_lt 2 bit q r hb (by decide) (by rwa [←he])
  · rw [pairIndex,pair_register_as_index]
    exact laneRegisterIndex_cover 2 bit r hb (by decide)

/-- A complete sequential source pair loop is exactly the simultaneous flat DIF
layer at every register position. No restriction to sampled radices is used. -/
theorem roundValues_flat (radix stride lane bit root r : Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) (hr : r<radix)
    (input values : Nat → Nat)
    (hvalues : ∀ r, r<radix → values r=input (laneRegisterIndex radix stride lane r))
    (canonical : ∀ r, r<radix → values r<goldilocksP) :
    roundValues (radix/2) bit (fun j => modPow root (phasePairOffset stride lane j bit)) values r =
      flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane r) := by
  obtain ⟨j,hj,side,hside,he⟩ := pair_cover radix bit r hb hd hr
  rw [←he]
  exact roundValues_flat_pair radix stride lane bit root j side hs hb hd hj hside input values hvalues canonical

/-- The actual register-round arithmetic and actual global-table exponents denote
one whole-vector DIF level, at the source's exact lane/register coordinates. -/
theorem phase_roundValues_layer (total bits done degree round lane r : Nat)
    (ht : total ≤ 32) (hb : bits ≤ total) (hdegree : done+degree ≤ bits)
    (hround : round<degree) (hlane : lane < 2^bits/2^degree) (hr : r<2^degree)
    (input values : Nat → Nat)
    (hvalues : ∀ r, r<2^degree → values r=input
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r))
    (canonical : ∀ r, r<2^degree → values r<goldilocksP) :
    roundValues (2^degree/2) (2^degree/2^(round+1))
      (fun j => modPow (rootOfUnity (2^total))
        (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)) *
          (2^(done+round)*(2^total/2^bits)))) values r =
      difLayer bits (done+round) input
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  have hi := phase_index_lt bits done degree lane r hdegree hlane hr
  rw [difLayer_flat bits (done+round) input (by omega) _ hi]
  have twiddle_eq : (fun j => modPow (rootOfUnity (2^total))
      (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)) *
        (2^(done+round)*(2^total/2^bits)))) =
      (fun j => modPow (rootOfUnity (2^(bits-(done+round))))
        (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)))) := by
    funext j
    exact phase_twiddle total bits done round _ ht hb (by omega)
  rw [twiddle_eq,←phase_pair_distance bits done degree round hdegree hround]
  have hs : 0 < 2^bits/(2^done*2^degree) := by
    rw [phase_stride bits done degree hdegree]
    exact Nat.two_pow_pos _
  have hbit := phase_bit degree round hround
  exact roundValues_flat (2^degree) _ lane _ _ r hs hbit.1 hbit.2 hr input values hvalues canonical

end Obend.Hardware.Gpu.Ntt.RegisterValues
end

end
