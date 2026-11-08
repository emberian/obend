module
public import Obend.Hardware.Gpu.NttRoots
public import Obend.Hardware.Gpu.NttSum
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource

/-- Canonical modular operations. Their laws below need no primality assumption. -/
def addMod (a b : Nat) : Nat := (a+b) % goldilocksP
def mulMod (a b : Nat) : Nat := (a*b) % goldilocksP
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
def sumMod (n : Nat) (f : Nat → Nat) : Nat := Sum.sum n f % goldilocksP

/-- Forward DFT. Inputs need not already be canonical residues. -/
def dft (n root : Nat) (input : Nat → Nat) (k : Nat) : Nat :=
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
