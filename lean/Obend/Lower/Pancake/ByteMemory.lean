module
public import Obend.Lower.Pancake.WordBuffer
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer
public import Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Spec

public section
namespace Obend.Lower.Pancake.ByteMemory

abbrev Memory := Word → Word
def offset (p : Word) (i : Nat) := p + BitVec.ofNat 64 i
def read (m : Memory) (a : Word) := get_byte a (m (byte_align a)) false
def put (m : Memory) (a : Word) (b : UInt8) :=
  UPDATE (byte_align a) (set_byte a b.toBitVec (m (byte_align a)) false) m
def Holds (m : Memory) (p : Word) (xs : List UInt8) :=
  ∀ i (hi : i < xs.length), read m (offset p i) = xs[i].toBitVec

private theorem align_nat (a : Word) : (byte_align a).toNat = a.toNat / 8 * 8 := by
  have ha := a.isLt
  simp only [byte_align, align, word_slice, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  omega

theorem align_offset (p : Word) (i : Nat) (aligned : p.toNat % 8 = 0) :
    byte_align (offset p i) = offset p (i/8*8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [align_nat, offset, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem read_put_other_word (a z w : Word) (b : UInt8)
    (h : byte_align a = byte_align z) (ne : a ≠ z) :
    get_byte z (set_byte a b.toBitVec w false) false = get_byte z w false := by
  have hq := congrArg BitVec.toNat h
  simp only [align_nat] at hq
  have hn : a.toNat ≠ z.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
  have hdiff : a.toNat % 8 ≠ z.toNat % 8 := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [get_byte, set_byte, byte_index, Bool.false_eq_true, ↓reduceIte,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, word_slice_alt, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hl : z.toNat % 8 < a.toNat % 8
  · simp [show 8*(z.toNat%8)+i < 64 by omega, show 8*(z.toNat%8)+i < 8*(a.toNat%8) by omega,
      show ¬8*(a.toNat%8)+8 ≤ 8*(z.toNat%8)+i by omega,
      BitVec.getLsbD]
  · have he : 8*(a.toNat%8)+8 ≤ 8*(z.toNat%8)+i := by omega
    have bit : b.toNat.testBit (8*(z.toNat%8)+i-8*(a.toNat%8)) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toBitVec.isLt
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [he, bit, show 8*(z.toNat%8)+i < 64 by omega,
      show ¬8*(z.toNat%8)+i < 8*(a.toNat%8) by omega,
      show 8*(z.toNat%8)+i-(8*(a.toNat%8)+8) < 56-8*(a.toNat%8) by omega,
      BitVec.getLsbD]

theorem read_put (m : Memory) (a z : Word) (b : UInt8) :
    read (put m a b) z = if a = z then b.toBitVec else read m z := by
  by_cases eq : a = z
  · subst z
    have h := mem_load_byte_after_store_same (m := m) (dm := fun _ => true)
      (w := a) (b := b.toBitVec) (be := false) rfl
    simpa [mem_load_byte, read, put, UPDATE] using h
  · by_cases ha : byte_align a = byte_align z
    · simpa [read, put, UPDATE, ha, eq] using read_put_other_word a z (m (byte_align z)) b ha eq
    · simp [read, put, UPDATE, ha, eq]

theorem holds_push {m p xs} (h : Holds m p xs) (x : UInt8) (bound : xs.length < 2^64) :
    Holds (put m (offset p xs.length) x) p (xs ++ [x]) := by
  intro i hi
  rw [read_put]
  by_cases lt : i < xs.length
  · have ne : offset p xs.length ≠ offset p i := by
      simp [offset]
      intro e
      have eq := congrArg BitVec.toNat e
      simp [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans lt bound)] at eq
      omega
    simp [ne, List.getElem_append_left lt, h i lt]
  · have eq : i = xs.length := by simp at hi; omega
    subst i
    simp

/-- An aligned little-endian load reassembles exactly the eight bytes in the
    list specification. The proof inspects an arbitrary bit of each partial fold. -/
theorem lane_eq (w : Word) (block : List UInt8) (lane : Nat)
    (bytes : ∀ j, j < 8 → (block.getD (8*lane+j) 0).toBitVec = (w >>> (8*j)).setWidth 8) :
    Obend.Digest.Cshake256.laneFromBlock block lane = w := by
  let part (n : Nat) := (List.range n).foldl (fun acc j =>
    acc ^^^ BitVec.ofNat 64 ((block.getD (8*lane+j) 0).toNat * 2^(8*j))) (0 : Word)
  have fold (n : Nat) (hn : n ≤ 8) (k : Nat) (hk : k < 64) :
      (part n).getLsbD k = (decide (k < 8*n) && w.getLsbD k) := by
    induction n with
    | zero => simp [part]
    | succ n ih =>
      have step : part (n+1) = part n ^^^ BitVec.ofNat 64
          ((block.getD (8*lane+n) 0).toNat * 2^(8*n)) := by simp [part, List.range_succ]
      have bit := congrArg (fun b : Byte => b.getLsbD (k-8*n)) (bytes n (by omega))
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at bit
      change (block.getD (8*lane+n) 0).toNat.testBit (k-8*n) = _ at bit
      rw [step, BitVec.getLsbD_xor, ih (by omega), BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow, bit]
      by_cases h : k < 8*n
      · simp [h, hk, Nat.not_le_of_lt h, show k < 8*(n+1) by omega]
      · by_cases h' : k < 8*(n+1)
        · simp [h, h', hk, Nat.le_of_not_lt h, show k-8*n < 8 by omega,
            show 8*n+(k-8*n) = k by omega]
        · simp [h, h', hk, show ¬k-8*n < 8 by omega]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (part 8).getLsbD k = _
  simpa [hk] using fold 8 (by decide) k hk

end Obend.Lower.Pancake.ByteMemory
