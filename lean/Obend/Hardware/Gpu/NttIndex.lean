module
public import Obend.Hardware.Gpu.NttDIF
@[expose] public section

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
