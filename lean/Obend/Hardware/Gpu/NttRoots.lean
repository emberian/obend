module
public import Obend.Hardware.Gpu.Ntt
@[expose] public section

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
