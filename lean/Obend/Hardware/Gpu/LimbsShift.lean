module
public import Obend.Hardware.Gpu.Limbs
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

/-! Universal bit-level refinement for the portable word shifts. The separate
module keeps bit-blasting work out of the arithmetic core's elaboration cycle. -/
@[expose] public section
namespace Obend.Hardware.Gpu.Limbs

theorem shr_bits (a b : Word) : (shr a b).bits = a.bits >>> b.bits := by
  cases a with | mk al ah =>
    cases b with | mk bl bh =>
      unfold shr Word.bits
      dsimp only
      bv_decide

theorem shl_bits (a b : Word) : (shl a b).bits = a.bits <<< b.bits := by
  cases a with | mk al ah =>
    cases b with | mk bl bh =>
      unfold shl Word.bits
      dsimp only
      bv_decide

theorem lt_bits (a b : Word) : lt a b = a.bits.ult b.bits := by
  apply Bool.eq_iff_iff.mpr
  rw [lt_spec, BitVec.ult_iff_toNat_lt, Word.bits_val, Word.bits_val]

/-- The source glMul graph's mask and fixed shifts are exactly limb projections. -/
theorem mask32_bits (a : Word) :
    (⟨a.lo, 0#32⟩ : Word).bits = a.bits &&& 0xFFFFFFFF#64 := by
  change (0#32 ++ a.lo) = (a.hi ++ a.lo) &&& (0#32 ++ 0xFFFFFFFF#32)
  rw [BitVec.and_append]
  change (0#32 ++ a.lo) = ((a.hi &&& 0#32) ++ (a.lo &&& BitVec.allOnes 32))
  rw [BitVec.and_allOnes,BitVec.and_zero]

theorem shr32_bits (a : Word) :
    (⟨a.hi, 0#32⟩ : Word).bits = a.bits >>> 32 := by
  cases a with | mk lo hi => unfold Word.bits; dsimp only; bv_decide

theorem shl32_bits (a : Word) :
    (⟨0#32, a.lo⟩ : Word).bits = a.bits <<< 32 := by
  cases a with | mk lo hi => unfold Word.bits; dsimp only; bv_decide

theorem pack32_bits (a b : Word) :
    (⟨a.lo, b.lo⟩ : Word).bits =
      (a.bits &&& 0xFFFFFFFF#64) ||| ((b.bits &&& 0xFFFFFFFF#64) <<< 32) := by
  rw [← mask32_bits a,← mask32_bits b,← shl32_bits (⟨b.lo,0#32⟩ : Word)]
  change (b.lo ++ a.lo) = (0#32 ++ a.lo) ||| (b.lo ++ 0#32)
  rw [BitVec.or_append]
  simp

end Obend.Hardware.Gpu.Limbs
