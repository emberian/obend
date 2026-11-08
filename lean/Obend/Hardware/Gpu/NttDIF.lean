module
public import Obend.Hardware.Gpu.NttDFTSpec
@[expose] public section

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
