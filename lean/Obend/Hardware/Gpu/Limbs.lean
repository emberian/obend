module
public import Lean

/-!
# Portable u32 limb arithmetic

The multiplication schedule splits each u32 into 16-bit digits. Each product and
accumulator fits u32; neither shader-int64 nor a software 64-bit multiply is needed.
The carry-chain organization follows ec-gpu's generated field implementation
(`ec-gpu-gen/src/cl/field.cl`) and ICICLE's `primitives/field.cuh`.
For Goldilocks we retain the special-prime fold used by Plonky3's
`goldilocks/src/goldilocks.rs::reduce128`, rather than generic Montgomery or Barrett
reduction (Handbook of Applied Cryptography, Algorithms 14.32 and 14.42): this avoids
Montgomery conversions and Barrett's reciprocal products.

Sources consulted:
* https://github.com/emberian/ec-gpu/blob/efea2cf0d1d5dcb4506e1faee7ebec5ac48ec431/ec-gpu-gen/src/cl/field.cl
* https://github.com/ingonyama-zk/icicle/blob/v1.1.0/icicle/primitives/field.cuh
* https://github.com/Plonky3/Plonky3/blob/main/goldilocks/src/goldilocks.rs
* https://cacr.uwaterloo.ca/hac/about/chap14.pdf
-/
@[expose] public section
namespace Obend.Hardware.Gpu.Limbs

/-- Little-endian pair of actual 32-bit words; the WGSL carrier is `vec2<u32>`. -/
structure Word where
  lo : BitVec 32
  hi : BitVec 32
  deriving BEq, DecidableEq, Repr

def Word.val (a : Word) : Nat := a.lo.toNat + 4294967296 * a.hi.toNat

theorem Word.val_lt (a : Word) : a.val < 2^64 := by
  have hl := a.lo.isLt
  have hh := a.hi.isLt
  unfold Word.val
  omega

/-- The natural-number schedule for 32×32→64. Divisions and remainders are
power-of-two shifts and masks; `mul32_bounds` checks every accumulator. -/
def mul32Nat (a b : Nat) : Nat × Nat :=
  let a0 := a % 65536
  let a1 := a / 65536
  let b0 := b % 65536
  let b1 := b / 65536
  let w0 := a0 * b0
  let t := a1 * b0 + w0 / 65536
  let u := a0 * b1 + t % 65536
  (w0 % 65536 + 65536 * (u % 65536),
   a1 * b1 + t / 65536 + u / 65536)

theorem mul32Nat_sound (a b : Nat) :
    (mul32Nat a b).1 + 4294967296 * (mul32Nat a b).2 = a * b := by
  have ha := Nat.mod_add_div a 65536
  have hb := Nat.mod_add_div b 65536
  have hp := Nat.mod_add_div (a % 65536 * (b % 65536)) 65536
  have ht := Nat.mod_add_div (a / 65536 * (b % 65536) +
    a % 65536 * (b % 65536) / 65536) 65536
  have hu := Nat.mod_add_div (a % 65536 * (b / 65536) +
    (a / 65536 * (b % 65536) + a % 65536 * (b % 65536) / 65536) % 65536) 65536
  have he : a * b = a % 65536 * (b % 65536) +
      65536 * (a / 65536 * (b % 65536)) +
      65536 * (a % 65536 * (b / 65536)) +
      4294967296 * (a / 65536 * (b / 65536)) := by
    calc
      a * b = (a % 65536 + 65536 * (a / 65536)) *
          (b % 65536 + 65536 * (b / 65536)) := by rw [ha, hb]
      _ = _ := by simp only [Nat.add_mul, Nat.mul_add]; grind
  unfold mul32Nat
  dsimp only
  omega

theorem mul32Nat_bounds {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    (mul32Nat a b).1 < 4294967296 ∧ (mul32Nat a b).2 < 4294967296 := by
  have hp := Nat.mul_le_mul (show a ≤ 4294967295 by omega)
    (show b ≤ 4294967295 by omega)
  have hs := mul32Nat_sound a b
  constructor
  · unfold mul32Nat
    dsimp only
    omega
  · omega

/-- Every multiplication below has two 16-bit operands. The two mixed accumulators
are also below 2^32. This is the portable substitute for WGSL's absent `mulExtended`. -/
def mul32 (a b : BitVec 32) : Word :=
  let a0 := a % 65536#32
  let a1 := a / 65536#32
  let b0 := b % 65536#32
  let b1 := b / 65536#32
  let w0 := a0 * b0
  let t := a1 * b0 + w0 / 65536#32
  let u := a0 * b1 + t % 65536#32
  ⟨w0 % 65536#32 + 65536#32 * (u % 65536#32),
   a1 * b1 + t / 65536#32 + u / 65536#32⟩

private theorem digit_mul_le {a b : Nat} (ha : a < 65536) (hb : b < 65536) :
    a * b ≤ 4294836225 :=
  Nat.mul_le_mul (show a ≤ 65535 by omega) (show b ≤ 65535 by omega)

 theorem mul32_refines (a b : BitVec 32) :
    (mul32 a b).lo.toNat = (mul32Nat a.toNat b.toNat).1 ∧
    (mul32 a b).hi.toNat = (mul32Nat a.toNat b.toNat).2 := by
  have ha := a.isLt
  have hb := b.isLt
  have ha0 : a.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have hb0 : b.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have ha1 : a.toNat / 65536 < 65536 := by omega
  have hb1 : b.toNat / 65536 < 65536 := by omega
  have hp00 := digit_mul_le ha0 hb0
  have hp01 := digit_mul_le ha0 hb1
  have hp10 := digit_mul_le ha1 hb0
  have hp11 := digit_mul_le ha1 hb1
  have hbnd := mul32Nat_bounds ha hb
  unfold mul32Nat at hbnd ⊢
  unfold mul32
  dsimp only at hbnd ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_umod,
    BitVec.toNat_udiv, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

 theorem mul32_sound (a b : BitVec 32) : (mul32 a b).val = a.toNat * b.toNat := by
  rcases mul32_refines a b with ⟨hl, hh⟩
  unfold Word.val
  rw [hl, hh]
  exact mul32Nat_sound _ _

def add (a b : Word) : Word :=
  let l := a.lo + b.lo
  ⟨l, a.hi + b.hi + (if l.ult a.lo then 1#32 else 0#32)⟩

def sub (a b : Word) : Word :=
  ⟨a.lo - b.lo, a.hi - b.hi - (if a.lo.ult b.lo then 1#32 else 0#32)⟩

def lt (a b : Word) : Bool := a.hi.ult b.hi || (a.hi == b.hi && a.lo.ult b.lo)

def ofNat (n : Nat) : Word := ⟨BitVec.ofNat 32 n, BitVec.ofNat 32 (n / 4294967296)⟩

theorem ofNat_val (n : Nat) : (ofNat n).val = n % 18446744073709551616 := by
  simp only [ofNat, Word.val, BitVec.toNat_ofNat]
  omega

theorem lt_spec (a b : Word) : lt a b = true ↔ a.val < b.val := by
  have ha := a.lo.isLt
  have hb := b.lo.isLt
  simp only [lt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    BitVec.ult_iff_toNat_lt, ← BitVec.toNat_inj, Word.val]
  omega

theorem add_val (a b : Word) : (add a b).val = (a.val + b.val) % 18446744073709551616 := by
  have ha0 := a.lo.isLt
  have ha1 := a.hi.isLt
  have hb0 := b.lo.isLt
  have hb1 := b.hi.isLt
  unfold add Word.val
  simp only [BitVec.toNat_add, BitVec.ult_iff_toNat_lt]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem sub_val (a b : Word) : (sub a b).val =
    (18446744073709551616 + a.val - b.val) % 18446744073709551616 := by
  have ha0 := a.lo.isLt
  have ha1 := a.hi.isLt
  have hb0 := b.lo.isLt
  have hb1 := b.hi.isLt
  unfold sub Word.val
  simp only [BitVec.toNat_sub, BitVec.ult_iff_toNat_lt]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- Truncated 64-bit multiplication using one exact u32 product and two low products. -/
def mul (a b : Word) : Word :=
  let p := mul32 a.lo b.lo
  ⟨p.lo, p.hi + a.lo * b.hi + a.hi * b.lo⟩

theorem mul_val (a b : Word) : (mul a b).val =
    (a.val * b.val) % 18446744073709551616 := by
  have hp := mul32_sound a.lo b.lo
  have hpl := (mul32 a.lo b.lo).lo.isLt
  have hph := (mul32 a.lo b.lo).hi.isLt
  have he : a.val * b.val = a.lo.toNat * b.lo.toNat +
      4294967296 * (a.lo.toNat * b.hi.toNat + a.hi.toNat * b.lo.toNat) +
      18446744073709551616 * (a.hi.toNat * b.hi.toNat) := by
    unfold Word.val
    grind
  unfold mul Word.val at hp he ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  omega

/-- Add two u32 words and retain the carry as a second u32 word. -/
def addCarry (a b : BitVec 32) : Word :=
  let s := a + b
  ⟨s, if s.ult a then 1#32 else 0#32⟩

theorem addCarry_val (a b : BitVec 32) : (addCarry a b).val = a.toNat + b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  unfold addCarry Word.val
  simp only [BitVec.toNat_add, BitVec.ult_iff_toNat_lt]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem addCarry_hi (a b : BitVec 32) : (addCarry a b).hi.toNat ≤ 1 := by
  unfold addCarry
  dsimp only
  split <;> decide

structure Wide where
  lo : Word
  hi : Word
  deriving BEq, DecidableEq, Repr

def Wide.val (x : Wide) : Nat := x.lo.val + 18446744073709551616 * x.hi.val

/-- Four exact u32 products. Carries remain independent u32 values until their
addition into the high word; no accumulator silently needs a 33rd bit. -/
def assemble (p00 p01 p10 p11 : Word) : Wide :=
  let middle := add (add ⟨p00.hi, 0#32⟩ ⟨p01.lo, 0#32⟩) ⟨p10.lo, 0#32⟩
  let h1 := add p11 ⟨p01.hi, 0#32⟩
  let h2 := add h1 ⟨p10.hi, 0#32⟩
  let h3 := add h2 ⟨middle.hi, 0#32⟩
  ⟨⟨p00.lo, middle.lo⟩, h3⟩

def mulWide (a b : Word) : Wide :=
  assemble (mul32 a.lo b.lo) (mul32 a.lo b.hi) (mul32 a.hi b.lo) (mul32 a.hi b.hi)

/-- Zero-extension does not change a limb's natural value. -/
theorem zeroExtend_val (x : BitVec 32) : (⟨x, 0#32⟩ : Word).val = x.toNat := by
  simp [Word.val]

private theorem assemble_val (p00 p01 p10 p11 : Word)
    (bound : p00.val + 4294967296 * (p01.val + p10.val) +
      18446744073709551616 * p11.val < 340282366920938463463374607431768211456) :
    (assemble p00 p01 p10 p11).val =
      p00.val + 4294967296 * (p01.val + p10.val) + 18446744073709551616 * p11.val := by
  let middle := add (add ⟨p00.hi, 0#32⟩ ⟨p01.lo, 0#32⟩) ⟨p10.lo, 0#32⟩
  have hm : middle.val = p00.hi.toNat + p01.lo.toNat + p10.lo.toNat := by
    have h00 := p00.hi.isLt
    have h01 := p01.lo.isLt
    have h10 := p10.lo.isLt
    dsimp only [middle]
    simp only [add_val, zeroExtend_val]
    omega
  let high := p11.val + p01.hi.toNat + p10.hi.toNat + middle.hi.toNat
  have key : p00.lo.toNat + 4294967296 * middle.lo.toNat + 18446744073709551616 * high =
      p00.val + 4294967296 * (p01.val + p10.val) + 18446744073709551616 * p11.val := by
    unfold high Word.val at *
    omega
  have hHigh : high < 18446744073709551616 := by omega
  have h1 : p11.val + p01.hi.toNat < 18446744073709551616 := by
    unfold high at hHigh; omega
  have h2 : p11.val + p01.hi.toNat + p10.hi.toNat < 18446744073709551616 := by
    unfold high at hHigh; omega
  change (⟨p00.lo, middle.lo⟩ : Word).val + 18446744073709551616 *
    (add (add (add p11 ⟨p01.hi, 0#32⟩) ⟨p10.hi, 0#32⟩)
      ⟨middle.hi, 0#32⟩).val = _
  simp only [add_val, zeroExtend_val, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  change p00.lo.toNat + 4294967296 * middle.lo.toNat +
    18446744073709551616 * (high % 18446744073709551616) = _
  rw [Nat.mod_eq_of_lt hHigh]
  exact key

theorem mulWide_sound (a b : Word) : (mulWide a b).val = a.val * b.val := by
  have hp00 := mul32_sound a.lo b.lo
  have hp01 := mul32_sound a.lo b.hi
  have hp10 := mul32_sound a.hi b.lo
  have hp11 := mul32_sound a.hi b.hi
  have he : (mul32 a.lo b.lo).val + 4294967296 *
      ((mul32 a.lo b.hi).val + (mul32 a.hi b.lo).val) +
      18446744073709551616 * (mul32 a.hi b.hi).val = a.val * b.val := by
    rw [hp00, hp01, hp10, hp11]
    unfold Word.val
    grind
  have bound : a.val * b.val < 340282366920938463463374607431768211456 := by
    have hh := Nat.mul_le_mul
      (show a.val ≤ 18446744073709551615 by have := a.val_lt; omega)
      (show b.val ≤ 18446744073709551615 by have := b.val_lt; omega)
    omega
  unfold mulWide
  rw [assemble_val _ _ _ _ (by omega), he]

theorem Word.val_inj (a b : Word) : a.val = b.val ↔ a = b := by
  constructor
  · intro h
    have ha := a.lo.isLt
    have hb := b.lo.isLt
    have hl : a.lo.toNat = b.lo.toNat := by unfold Word.val at h; omega
    have hh : a.hi.toNat = b.hi.toNat := by unfold Word.val at h; omega
    cases a; cases b
    simp only [Word.mk.injEq]
    exact ⟨BitVec.eq_of_toNat_eq hl, BitVec.eq_of_toNat_eq hh⟩
  · intro h; rw [h]

/-- The graph's 64-bit multiply of zero-extended u32 operands is precisely mul32. -/
theorem mul_zeroExtend (a b : BitVec 32) : mul ⟨a, 0#32⟩ ⟨b, 0#32⟩ = mul32 a b := by
  apply (Word.val_inj _ _).mp
  rw [mul_val, zeroExtend_val, zeroExtend_val, mul32_sound]
  exact Nat.mod_eq_of_lt (BitVec.toNat_mul_toNat_lt (x := a) (y := b))

/-- The existing glMul graph's four generic word multiplications and assembly.
Fixed mask/shift32 operations are represented by projection and zero-extension. -/
def mulNetwork (a b : Word) : Wide :=
  assemble (mul ⟨a.lo, 0#32⟩ ⟨b.lo, 0#32⟩)
    (mul ⟨a.lo, 0#32⟩ ⟨b.hi, 0#32⟩)
    (mul ⟨a.hi, 0#32⟩ ⟨b.lo, 0#32⟩)
    (mul ⟨a.hi, 0#32⟩ ⟨b.hi, 0#32⟩)

theorem mulNetwork_eq_mulWide (a b : Word) : mulNetwork a b = mulWide a b := by
  simp only [mulNetwork, mulWide, mul_zeroExtend]

theorem mulNetwork_sound (a b : Word) : (mulNetwork a b).val = a.val * b.val := by
  rw [mulNetwork_eq_mulWide, mulWide_sound]

def Word.bits (a : Word) : BitVec 64 := a.hi ++ a.lo

theorem Word.bits_val (a : Word) : a.bits.toNat = a.val := by
  rw [Word.bits, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a.lo.isLt,
    Nat.shiftLeft_eq]
  unfold Word.val
  omega

/-- Native unsigned 32×32 widening multiplication has the same exact result as
our proved portable schedule. Both inputs are u32; the 64-bit type here denotes
the product's width, not an unconstrained 64×64 multiplication. -/
theorem mul32_widen (a b : BitVec 32) :
    (mul32 a b).bits = a.setWidth 64 * b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [Word.bits_val, mul32_sound, BitVec.toNat_mul,
    BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_setWidth_of_le (by decide),
    Nat.mod_eq_of_lt (BitVec.toNat_mul_toNat_lt (x := a) (y := b))]

/-- Explicit low/high extraction form used by a widening multiply helper. -/
theorem mul32_widen_limbs (a b : BitVec 32) :
    mul32 a b =
      ⟨(a.setWidth 64 * b.setWidth 64).extractLsb' 0 32,
       (a.setWidth 64 * b.setWidth 64).extractLsb' 32 32⟩ := by
  rw [← mul32_widen]
  simp only [Word.bits, BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]

theorem add_bits (a b : Word) : (add a b).bits = a.bits + b.bits := by
  apply BitVec.eq_of_toNat_eq
  rw [Word.bits_val, add_val, BitVec.toNat_add, Word.bits_val, Word.bits_val]

theorem mul_bits (a b : Word) : (mul a b).bits = a.bits * b.bits := by
  apply BitVec.eq_of_toNat_eq
  rw [Word.bits_val, mul_val, BitVec.toNat_mul, Word.bits_val, Word.bits_val]

theorem sub_bits (a b : Word) : (sub a b).bits = a.bits - b.bits := by
  apply BitVec.eq_of_toNat_eq
  rw [Word.bits_val, sub_val, BitVec.toNat_sub, Word.bits_val, Word.bits_val]
  have hh := b.val_lt
  omega

def shr (a b : Word) : Word :=
  if b.hi != 0#32 || !(b.lo.ult 64#32) then ⟨0#32, 0#32⟩
  else if b.lo == 0#32 then a
  else if !(b.lo.ult 32#32) then ⟨a.hi >>> (b.lo - 32#32), 0#32⟩
  else ⟨(a.lo >>> b.lo) ||| (a.hi <<< (32#32 - b.lo)), a.hi >>> b.lo⟩

def shl (a b : Word) : Word :=
  if b.hi != 0#32 || !(b.lo.ult 64#32) then ⟨0#32, 0#32⟩
  else if b.lo == 0#32 then a
  else if !(b.lo.ult 32#32) then ⟨0#32, a.lo <<< (b.lo - 32#32)⟩
  else ⟨a.lo <<< b.lo, (a.hi <<< b.lo) ||| (a.lo >>> (32#32 - b.lo))⟩

/-- WGSL counterparts of the proved word primitives. u64 is a name for a
little-endian pair; only `u32_mul_wide` uses the shader u64 extension. Shift counts ≥64 yield zero,
including counts whose upper word is nonzero, as in BitVec semantics. -/
def wgslPrelude : String := r#"
fn u32_mul_wide(a: u32, b: u32) -> vec2<u32> {
  // Bounded u32 operands: the backend emits native low/high u32 products.
  let product = u64(a) * u64(b);
  return vec2<u32>(u32(product), u32(product >> 32u));
}
fn u64_add(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  let lo = a.x + b.x;
  return vec2<u32>(lo, a.y + b.y + select(0u, 1u, lo < a.x));
}
fn u64_sub(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  return vec2<u32>(a.x - b.x, a.y - b.y - select(0u, 1u, a.x < b.x));
}
fn u64_lt(a: vec2<u32>, b: vec2<u32>) -> bool {
  return a.y < b.y || (a.y == b.y && a.x < b.x);
}
fn u64_mul(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  let p = u32_mul_wide(a.x, b.x);
  return vec2<u32>(p.x, p.y + a.x * b.y + a.y * b.x);
}
fn u64_shr(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  if (b.y != 0u || b.x >= 64u) { return vec2<u32>(0u); }
  if (b.x == 0u) { return a; }
  if (b.x >= 32u) { return vec2<u32>(a.y >> (b.x - 32u), 0u); }
  return vec2<u32>((a.x >> b.x) | (a.y << (32u - b.x)), a.y >> b.x);
}
fn u64_shl(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  if (b.y != 0u || b.x >= 64u) { return vec2<u32>(0u); }
  if (b.x == 0u) { return a; }
  if (b.x >= 32u) { return vec2<u32>(0u, a.x << (b.x - 32u)); }
  return vec2<u32>(a.x << b.x, (a.y << b.x) | (a.x >> (32u - b.x)));
}
"#

end Obend.Hardware.Gpu.Limbs
