module
public import Obend.Hardware.Gpu.Limbs
public import Obend.Apps.ZkNtt.Goldilocks

/-! # Goldilocks arithmetic refined to portable u32 words

`mul_sound` composes the universal 16-bit partial-product, u32 carry, full 128-bit
assembly, and special-prime reduction theorems. Inputs need not be canonical.
The reduction follows the existing `goldilocksReduce128Spec` exactly; this is
ordinary representation arithmetic, without Montgomery-domain conversions.
-/
@[expose] public section
namespace Obend.Hardware.Gpu.Limbs.Goldilocks
open Obend.Apps.ZkNtt

def prime : Word := ofNat goldilocksPrime

def canon (a : Word) : Word := if lt a prime then a else sub a prime

def addCanonical (a b : Word) : Word :=
  let rem := Limbs.sub prime b
  if lt a rem then Limbs.add a b else Limbs.sub a rem

def subCanonical (a b : Word) : Word :=
  if lt a b then Limbs.add (Limbs.sub prime b) a else Limbs.sub a b

def add (a b : Word) : Word := addCanonical (canon a) (canon b)
def sub (a b : Word) : Word := subCanonical (canon a) (canon b)

theorem prime_val : prime.val = goldilocksPrime := by
  rw [prime, ofNat_val]
  decide

theorem canon_val (a : Word) : (canon a).val = goldilocksCanon64 a.val := by
  have ha := a.val_lt
  unfold canon goldilocksCanon64
  split <;> rename_i h
  · have hlt := (lt_spec a prime).mp h
    rw [prime_val] at hlt
    split <;> omega
  · have hlt : ¬ a.val < goldilocksPrime := by
      intro hh
      exact h ((lt_spec a prime).mpr (by rwa [prime_val]))
    rw [Limbs.sub_val, prime_val]
    unfold goldilocksPrime at *
    split <;> omega

theorem add_val (a b : Word) : (add a b).val = goldilocksAddSpec a.val b.val := by
  have ha := a.val_lt
  have hb := b.val_lt
  have hca := (goldilocksCanon64_spec ha).1
  have hcb := (goldilocksCanon64_spec hb).1
  have hrem : (Limbs.sub prime (canon b)).val = goldilocksPrime - goldilocksCanon64 b.val := by
    rw [Limbs.sub_val, prime_val, canon_val]
    unfold goldilocksPrime at *
    omega
  rw [← goldilocksAddSpec_eq_obend ha hb]
  unfold add addCanonical
  dsimp only
  split <;> rename_i h
  · have hh := (lt_spec _ _).mp h
    rw [canon_val, hrem] at hh
    rw [Limbs.add_val, canon_val, canon_val]
    split <;> unfold goldilocksPrime at * <;> omega
  · have hh : ¬ (canon a).val < (Limbs.sub prime (canon b)).val := by
      intro hh
      exact h ((lt_spec _ _).mpr hh)
    rw [canon_val, hrem] at hh
    rw [Limbs.sub_val, canon_val, hrem]
    split <;> unfold goldilocksPrime at * <;> omega

theorem sub_val (a b : Word) : (sub a b).val = goldilocksSubSpec a.val b.val := by
  have hca := (goldilocksCanon64_spec a.val_lt).1
  have hcb := (goldilocksCanon64_spec b.val_lt).1
  unfold sub subCanonical goldilocksSubSpec
  dsimp only
  split <;> rename_i h
  · have hh := (lt_spec _ _).mp h
    rw [canon_val, canon_val] at hh
    rw [Limbs.add_val, Limbs.sub_val, prime_val, canon_val, canon_val]
    split <;> unfold goldilocksPrime at * <;> omega
  · have hh : ¬ (canon a).val < (canon b).val := by
      intro hh
      exact h ((lt_spec _ _).mpr hh)
    rw [canon_val, canon_val] at hh
    rw [Limbs.sub_val, canon_val, canon_val]
    split <;> unfold goldilocksPrime at * <;> omega

/-- Fold x = lo + 2^64 hi using 2^64 = 2^32−1 and 2^96 = −1 mod p. -/
def reduce (x : Wide) : Word :=
  let middle := Limbs.sub ⟨0#32, x.hi.lo⟩ ⟨x.hi.lo, 0#32⟩
  sub (add x.lo middle) ⟨x.hi.hi, 0#32⟩

theorem reduce_val (x : Wide) : (reduce x).val = goldilocksReduce128Spec x.lo.val x.hi.val := by
  have hl := x.hi.lo.isLt
  have hh := x.hi.hi.isLt
  unfold reduce
  rw [sub_val, add_val, Limbs.sub_val]
  have hlow : x.hi.val % 4294967296 = x.hi.lo.toNat := by unfold Word.val; omega
  have hhigh : x.hi.val / 4294967296 = x.hi.hi.toNat := by unfold Word.val; omega
  unfold goldilocksReduce128Spec
  rw [hlow, hhigh]
  have hmid : ((18446744073709551616 + (⟨0#32, x.hi.lo⟩ : Word).val -
      (⟨x.hi.lo, 0#32⟩ : Word).val) % 18446744073709551616) =
      x.hi.lo.toNat * 4294967296 - x.hi.lo.toNat := by
    simp only [Word.val, BitVec.toNat_ofNat]
    omega
  rw [hmid]
  congr 1

theorem reduce_sound (x : Wide) :
    (reduce x).val < goldilocksPrime ∧ (reduce x).val = x.val % goldilocksPrime := by
  rw [reduce_val]
  exact goldilocksReduce128Spec_sound x.lo.val_lt x.hi.val_lt

theorem canon_eq {a : Word} (h : a.val < goldilocksPrime) : canon a = a := by
  apply (Word.val_inj _ _).mp
  rw [canon_val]
  unfold goldilocksCanon64
  split <;> omega

/-- The exact existing glMul graph's reduction: canonicalize lo once, then use
canonical add/sub. The bounds below justify those input preconditions. -/
def reduceNetwork (x : Wide) : Word :=
  let middle := Limbs.sub ⟨0#32, x.hi.lo⟩ ⟨x.hi.lo, 0#32⟩
  subCanonical (addCanonical (canon x.lo) middle) ⟨x.hi.hi, 0#32⟩

theorem reduceNetwork_eq_reduce (x : Wide) : reduceNetwork x = reduce x := by
  let middle := Limbs.sub (⟨0#32, x.hi.lo⟩ : Word) ⟨x.hi.lo, 0#32⟩
  have hm : middle.val < goldilocksPrime := by
    have hl := x.hi.lo.isLt
    dsimp only [middle]
    rw [Limbs.sub_val]
    simp only [Word.val, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add,
      Nat.mul_zero, Nat.add_zero]
    rw [Nat.add_sub_assoc (show x.hi.lo.toNat ≤ 4294967296 * x.hi.lo.toNat by omega),
      Nat.add_mod_left, Nat.mod_eq_of_lt (show 4294967296 * x.hi.lo.toNat - x.hi.lo.toNat <
        18446744073709551616 by omega)]
    unfold goldilocksPrime
    omega
  have ht : (add x.lo middle).val < goldilocksPrime := by
    rw [add_val]
    exact (goldilocksAddSpec_spec x.lo.val_lt middle.val_lt).1
  have hh : (⟨x.hi.hi, 0#32⟩ : Word).val < goldilocksPrime := by
    rw [zeroExtend_val]
    have := x.hi.hi.isLt
    unfold goldilocksPrime
    omega
  have hc := canon_eq hm
  have hct := canon_eq ht
  have hch := canon_eq hh
  change subCanonical (addCanonical (canon x.lo) middle) ⟨x.hi.hi, 0#32⟩ =
    sub (add x.lo middle) ⟨x.hi.hi, 0#32⟩
  unfold sub
  rw [hct, hch]
  unfold add
  rw [hc]

/-- Actual scalar glMul network after replacing each 64-bit primitive by its
proved pair-of-u32 implementation. -/
def mul (a b : Word) : Word := reduceNetwork (mulNetwork a b)

theorem mul_sound (a b : Word) : (mul a b).val = goldilocksMulSpec a.val b.val := by
  have hh := (reduce_sound (mulNetwork a b)).2
  rw [mulNetwork_sound] at hh
  unfold mul goldilocksMulSpec glN
  rw [reduceNetwork_eq_reduce, hh, Nat.mul_mod]

end Obend.Hardware.Gpu.Limbs.Goldilocks
