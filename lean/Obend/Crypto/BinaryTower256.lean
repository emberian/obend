module
public import Obend.Crypto.Sumcheck
public import Obend.Digest.HashBytes
import all Obend.Crypto.Sumcheck

public section
namespace Obend.Crypto.BinaryTower256
set_option autoImplicit false

/-- Coordinates in the quadratic algebra `X² + xₖ X + 1`. -/
@[expose] def TowerElem : Nat → Type
  | 0 => Bool
  | k + 1 => TowerElem k × TowerElem k

abbrev Tower128 := TowerElem 7
abbrev Tower256 := TowerElem 8
abbrev TowerBitVec (k : Nat) := BitVec (2 ^ k)
abbrev Tower128Exec := BitVec 128
abbrev Tower256Exec := BitVec 256

@[expose] def towerZero : (k : Nat) → TowerElem k
  | 0 => false
  | k + 1 => (towerZero k, towerZero k)

@[expose] def towerOne : (k : Nat) → TowerElem k
  | 0 => true
  | k + 1 => (towerOne k, towerZero k)

def towerX : (k : Nat) → TowerElem k
  | 0 => true
  | k + 1 => (towerZero k, towerOne k)

@[expose] def towerAdd : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a ^^ b
  | k + 1, a, b => (towerAdd k a.1 b.1, towerAdd k a.2 b.2)

/-- Polynomial-reduction specification. The three-product implementation is below. -/
@[expose] def towerMul : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a && b
  | k + 1, a, b =>
    (towerAdd k (towerMul k a.1 b.1) (towerMul k a.2 b.2),
     towerAdd k (towerAdd k (towerMul k a.1 b.2) (towerMul k a.2 b.1))
       (towerMul k (towerX k) (towerMul k a.2 b.2)))

@[expose] def towerScaleX : (k : Nat) → TowerElem k → TowerElem k
  | 0, a => a
  | k + 1, a => (a.2, towerAdd k a.1 (towerScaleX k a.2))

instance towerDecidableEq : (k : Nat) → DecidableEq (TowerElem k)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | k + 1 => @instDecidableEqProd _ _ (towerDecidableEq k) (towerDecidableEq k)

@[simp] theorem towerAdd_self_zero (k : Nat) (a : TowerElem k) :
    towerAdd k a a = towerZero k := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => exact Prod.ext (ih a.1) (ih a.2)

theorem towerAdd_comm (k : Nat) (a b : TowerElem k) :
    towerAdd k a b = towerAdd k b a := by
  induction k with
  | zero => cases a <;> cases b <;> rfl
  | succ k ih => exact Prod.ext (ih a.1 b.1) (ih a.2 b.2)

theorem towerAdd_assoc (k : Nat) (a b c : TowerElem k) :
    towerAdd k (towerAdd k a b) c = towerAdd k a (towerAdd k b c) := by
  induction k with
  | zero => cases a <;> cases b <;> cases c <;> rfl
  | succ k ih => exact Prod.ext (ih a.1 b.1 c.1) (ih a.2 b.2 c.2)

@[simp] theorem towerAdd_zero (k : Nat) (a : TowerElem k) :
    towerAdd k a (towerZero k) = a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => exact Prod.ext (ih a.1) (ih a.2)

@[simp] theorem towerZero_add (k : Nat) (a : TowerElem k) :
    towerAdd k (towerZero k) a = a := by rw [towerAdd_comm, towerAdd_zero]

theorem towerAdd_left_comm (k : Nat) (a b c : TowerElem k) :
    towerAdd k a (towerAdd k b c) = towerAdd k b (towerAdd k a c) := by
  rw [← towerAdd_assoc, towerAdd_comm k a b, towerAdd_assoc]

@[simp] theorem towerAdd_cancel (k : Nat) (a b : TowerElem k) :
    towerAdd k a (towerAdd k a b) = b := by
  rw [← towerAdd_assoc, towerAdd_self_zero, towerZero_add]

@[simp] theorem towerMul_zero (k : Nat) (a : TowerElem k) :
    towerMul k a (towerZero k) = towerZero k := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => simp only [towerMul, towerZero, ih, towerAdd_self_zero]; rfl

theorem towerMul_comm (k : Nat) (a b : TowerElem k) :
    towerMul k a b = towerMul k b a := by
  induction k with
  | zero => cases a <;> cases b <;> rfl
  | succ k ih =>
    simp only [towerMul]
    rw [ih a.1 b.1, ih a.2 b.2, ih a.1 b.2, ih a.2 b.1,
      towerAdd_comm k (towerMul k b.2 a.1) (towerMul k b.1 a.2)]

@[simp] theorem towerZero_mul (k : Nat) (a : TowerElem k) :
    towerMul k (towerZero k) a = towerZero k := by rw [towerMul_comm, towerMul_zero]

@[simp] theorem towerMul_one (k : Nat) (a : TowerElem k) :
    towerMul k a (towerOne k) = a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => cases a; simp [towerMul, towerOne, ih]; rfl

@[simp] theorem towerOne_mul (k : Nat) (a : TowerElem k) :
    towerMul k (towerOne k) a = a := by rw [towerMul_comm, towerMul_one]

theorem towerMul_add_distrib (k : Nat) (a b c : TowerElem k) :
    towerMul k a (towerAdd k b c) =
      towerAdd k (towerMul k a b) (towerMul k a c) := by
  induction k with
  | zero => cases a <;> cases b <;> cases c <;> rfl
  | succ k ih =>
    simp only [towerMul, towerAdd, ih]
    congr 1 <;> simp only [towerAdd_assoc, towerAdd_left_comm]

theorem towerAdd_mul_distrib (k : Nat) (a b c : TowerElem k) :
    towerMul k (towerAdd k a b) c =
      towerAdd k (towerMul k a c) (towerMul k b c) := by
  rw [towerMul_comm, towerMul_add_distrib, towerMul_comm k c a, towerMul_comm k c b]

theorem towerMul_left_comm_of_assoc (k : Nat)
    (ha : ∀ a b c, towerMul k (towerMul k a b) c = towerMul k a (towerMul k b c))
    (a b c : TowerElem k) :
    towerMul k a (towerMul k b c) = towerMul k b (towerMul k a c) := by
  rw [← ha, towerMul_comm k a b, ha]

theorem towerMul_assoc (k : Nat) (a b c : TowerElem k) :
    towerMul k (towerMul k a b) c = towerMul k a (towerMul k b c) := by
  induction k with
  | zero => cases a <;> cases b <;> cases c <;> rfl
  | succ k ih =>
    simp only [towerMul, towerMul_add_distrib, towerAdd_mul_distrib]
    congr 1 <;>
      simp only [ih, towerMul_comm k, towerMul_left_comm_of_assoc k ih,
        towerAdd_assoc, towerAdd_comm, towerAdd_left_comm]

theorem towerScaleX_eq_mul (k : Nat) (a : TowerElem k) :
    towerScaleX k a = towerMul k (towerX k) a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => simp [towerScaleX, towerX, towerMul, ih] <;> rfl

/-- Structural Karatsuba: three recursive products and a linear generator multiply. -/
def towerKaratsuba : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a && b
  | k + 1, a, b =>
    let p := towerKaratsuba k a.1 b.1
    let q := towerKaratsuba k a.2 b.2
    let r := towerKaratsuba k (towerAdd k a.1 a.2) (towerAdd k b.1 b.2)
    (towerAdd k p q, towerAdd k (towerAdd k r (towerAdd k p q)) (towerScaleX k q))

theorem towerKaratsuba_eq (k : Nat) (a b : TowerElem k) :
    towerKaratsuba k a b = towerMul k a b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [towerKaratsuba, ih, towerMul, towerMul_add_distrib,
      towerAdd_mul_distrib, towerScaleX_eq_mul]
    congr 1
    simp only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm,
      towerAdd_self_zero, towerAdd_zero, towerAdd_cancel]

@[csimp] theorem towerMul_eq_karatsuba : towerMul = towerKaratsuba := by
  funext k a b
  exact (towerKaratsuba_eq k a b).symm

/-- Subalgebra inclusion in the constant coordinate. -/
@[expose] def embedTower (k : Nat) (a : TowerElem k) : TowerElem (k + 1) := (a, towerZero k)

theorem embedTower_zero (k : Nat) : embedTower k (towerZero k) = towerZero (k + 1) := rfl
theorem embedTower_one (k : Nat) : embedTower k (towerOne k) = towerOne (k + 1) := rfl

theorem embedTower_add (k : Nat) (a b : TowerElem k) :
    embedTower k (towerAdd k a b) = towerAdd (k + 1) (embedTower k a) (embedTower k b) := by
  simp [embedTower, towerAdd] <;> rfl

theorem embedTower_mul (k : Nat) (a b : TowerElem k) :
    embedTower k (towerMul k a b) = towerMul (k + 1) (embedTower k a) (embedTower k b) := by
  simp [embedTower, towerMul] <;> rfl

theorem embedTower_injective (k : Nat) (a b : TowerElem k)
    (h : embedTower k a = embedTower k b) : a = b := congrArg Prod.fst h

def embedTowerChain (k : Nat) : (d : Nat) → TowerElem k → TowerElem (k + d)
  | 0, a => a
  | d + 1, a => embedTower (k + d) (embedTowerChain k d a)

theorem embedTowerChain_injective (k d : Nat) (a b : TowerElem k)
    (h : embedTowerChain k d a = embedTowerChain k d b) : a = b := by
  induction d with
  | zero => exact h
  | succ d ih => exact ih (embedTower_injective _ _ _ h)

instance towerRing (k : Nat) : LawfulCommRing (TowerElem k) where
  zero := towerZero k
  one := towerOne k
  add := towerAdd k
  mul := towerMul k
  neg := id
  sub := towerAdd k
  add_assoc := towerAdd_assoc k
  add_comm := towerAdd_comm k
  zero_add := towerZero_add k
  add_zero := towerAdd_zero k
  add_left_neg := towerAdd_self_zero k
  sub_eq_add_neg _ _ := rfl
  mul_assoc := towerMul_assoc k
  mul_comm := towerMul_comm k
  one_mul := towerOne_mul k
  mul_one := towerMul_one k
  left_distrib := towerMul_add_distrib k
  right_distrib := towerAdd_mul_distrib k

/-- Low coordinates occupy the low half of the packed word. -/
def joinBits (k : Nat) (lo hi : TowerBitVec k) : TowerBitVec (k + 1) :=
  (hi ++ lo).cast (by simp [Nat.pow_succ, Nat.mul_two])

def lowBits (k : Nat) (a : TowerBitVec (k + 1)) : TowerBitVec k := a.extractLsb' 0 (2 ^ k)
def highBits (k : Nat) (a : TowerBitVec (k + 1)) : TowerBitVec k := a.extractLsb' (2 ^ k) (2 ^ k)

@[simp] theorem lowBits_join (k : Nat) (lo hi : TowerBitVec k) :
    lowBits k (joinBits k lo hi) = lo := by
  simp [lowBits, joinBits, BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_right]

@[simp] theorem highBits_join (k : Nat) (lo hi : TowerBitVec k) :
    highBits k (joinBits k lo hi) = hi := by
  simp [highBits, joinBits, BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_left]

@[simp] theorem joinBits_split (k : Nat) (a : TowerBitVec (k + 1)) :
    joinBits k (lowBits k a) (highBits k a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [joinBits, lowBits, highBits, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  split <;> simp_all [Nat.pow_succ, Nat.mul_two] <;> omega

theorem joinBits_xor (k : Nat) (a b c d : TowerBitVec k) :
    joinBits k (a ^^^ b) (c ^^^ d) = joinBits k a c ^^^ joinBits k b d := by
  simp [joinBits, BitVec.xor_append]

@[expose] def packTower : (k : Nat) → TowerElem k → TowerBitVec k
  | 0, a => BitVec.ofBool a
  | k + 1, a => joinBits k (packTower k a.1) (packTower k a.2)

@[expose] def unpackTower : (k : Nat) → TowerBitVec k → TowerElem k
  | 0, a => a.getLsbD 0
  | k + 1, a => (unpackTower k (lowBits k a), unpackTower k (highBits k a))

@[simp] theorem unpackTower_packTower (k : Nat) (a : TowerElem k) :
    unpackTower k (packTower k a) = a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih =>
    cases a
    simp only [packTower, unpackTower, lowBits_join, highBits_join, ih]; rfl

@[simp] theorem packTower_unpackTower (k : Nat) (a : TowerBitVec k) :
    packTower k (unpackTower k a) = a := by
  induction k with
  | zero =>
    exact (BitVec.setWidth_one (x := a)).symm.trans (BitVec.setWidth_eq _)
  | succ k ih => simp only [packTower, unpackTower, ih, joinBits_split]

theorem packTower_injective (k : Nat) (a b : TowerElem k)
    (h : packTower k a = packTower k b) : a = b := by
  have := congrArg (unpackTower k) h
  simpa only [unpackTower_packTower] using this

theorem packTower_add (k : Nat) (a b : TowerElem k) :
    packTower k (towerAdd k a b) = packTower k a ^^^ packTower k b := by
  induction k with
  | zero => exact BitVec.ofBool_xor_ofBool.symm
  | succ k ih => simp only [packTower, towerAdd, ih, joinBits_xor]

/-- Packed generator multiplication uses only splits, joins and XOR. -/
def scaleXExec : (k : Nat) → TowerBitVec k → TowerBitVec k
  | 0, a => a
  | k + 1, a => joinBits k (highBits k a) (lowBits k a ^^^ scaleXExec k (highBits k a))

/-- Packed Karatsuba never materializes the recursive specification carrier. -/
def mulExec : (k : Nat) → TowerBitVec k → TowerBitVec k → TowerBitVec k
  | 0, a, b => a &&& b
  | k + 1, a, b =>
    let al := lowBits k a; let ah := highBits k a
    let bl := lowBits k b; let bh := highBits k b
    let p := mulExec k al bl
    let q := mulExec k ah bh
    let r := mulExec k (al ^^^ ah) (bl ^^^ bh)
    joinBits k (p ^^^ q) (r ^^^ (p ^^^ q) ^^^ scaleXExec k q)

theorem scaleXExec_refines (k : Nat) (a : TowerElem k) :
    scaleXExec k (packTower k a) = packTower k (towerScaleX k a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [scaleXExec, packTower, lowBits_join, highBits_join,
      ih, towerScaleX, packTower_add]

theorem mulExec_refines (k : Nat) (a b : TowerElem k) :
    mulExec k (packTower k a) (packTower k b) = packTower k (towerMul k a b) := by
  induction k with
  | zero => exact BitVec.ofBool_and_ofBool
  | succ k ih =>
    rw [← towerKaratsuba_eq]
    simp only [mulExec, packTower, lowBits_join, highBits_join, ← packTower_add,
      ih, scaleXExec_refines, towerKaratsuba, towerKaratsuba_eq]

def Simulates (k : Nat) (spec : TowerElem k) (exec : TowerBitVec k) : Prop :=
  packTower k spec = exec

theorem Simulates.add (k : Nat) {a b : TowerElem k} {x y : TowerBitVec k}
    (ha : Simulates k a x) (hb : Simulates k b y) :
    Simulates k (towerAdd k a b) (x ^^^ y) := by
  unfold Simulates at *
  rw [packTower_add, ha, hb]

theorem Simulates.mul (k : Nat) {a b : TowerElem k} {x y : TowerBitVec k}
    (ha : Simulates k a x) (hb : Simulates k b y) :
    Simulates k (towerMul k a b) (mulExec k x y) := by
  unfold Simulates at *
  rw [← ha, ← hb, mulExec_refines]

def toExec256 (a : Tower256) : Tower256Exec := packTower 8 a
def ofExec256 (a : Tower256Exec) : Tower256 := unpackTower 8 a

@[simp] theorem ofExec256_toExec256 (a : Tower256) : ofExec256 (toExec256 a) = a :=
  unpackTower_packTower 8 a
@[simp] theorem toExec256_ofExec256 (a : Tower256Exec) : toExec256 (ofExec256 a) = a :=
  packTower_unpackTower 8 a

/-- Canonical big-endian 32-byte serialization; all 256 bits are retained. -/
def toBytes32 (a : Tower256Exec) : ByteArray :=
  ⟨(Obend.Digest.HashBytes.be 32 a.toNat).toArray⟩

def ofBytes32 (bs : ByteArray) : Option Tower256Exec :=
  if bs.size = 32 then some (.ofNat 256 (Obend.Digest.HashBytes.ofBE bs.data.toList)) else none

theorem toBytes32_size (a : Tower256Exec) : (toBytes32 a).size = 32 := by
  change (Obend.Digest.HashBytes.be 32 a.toNat).toArray.size = 32
  simp

theorem ofBytes32_toBytes32 (a : Tower256Exec) : ofBytes32 (toBytes32 a) = some a := by
  have hp : 256 ^ 32 = 2 ^ 256 := by decide
  have ha : a.toNat < 256 ^ 32 := by rw [hp]; exact a.isLt
  have ht : (toBytes32 a).data.toList = Obend.Digest.HashBytes.be 32 a.toNat := by
    exact List.toList_toArray
  unfold ofBytes32
  rw [toBytes32_size, ite_eq_left rfl, ht, Obend.Digest.HashBytes.ofBE_be ha]
  exact congrArg some ((BitVec.ofNat_toNat 256 a).trans (BitVec.setWidth_eq a))

private theorem be_ofBE (xs : List UInt8) :
    Obend.Digest.HashBytes.be xs.length (Obend.Digest.HashBytes.ofBE xs) = xs := by
  suffices h : ∀ ys : List UInt8,
      Obend.Digest.HashBytes.be ys.reverse.length (Obend.Digest.HashBytes.ofBE ys.reverse) = ys.reverse by
    simpa only [List.reverse_reverse] using h xs.reverse
  intro ys
  induction ys with
  | nil => rfl
  | cons b ys ih =>
    let xs := ys.reverse
    rw [List.reverse_cons]
    change Obend.Digest.HashBytes.be (xs ++ [b]).length
      (Obend.Digest.HashBytes.ofBE (xs ++ [b])) = xs ++ [b]
    simp only [List.length_append, List.length_singleton, Obend.Digest.HashBytes.ofBE_append_single,
      Obend.Digest.HashBytes.be]
    have hb := b.toNat_lt
    have hdiv : (Obend.Digest.HashBytes.ofBE xs * 256 + b.toNat) / 256 =
        Obend.Digest.HashBytes.ofBE xs := by omega
    have hmod : (Obend.Digest.HashBytes.ofBE xs * 256 + b.toNat) % 256 = b.toNat := by omega
    rw [hdiv, hmod, ih, UInt8.ofNat_toNat]

theorem toBytes32_ofBytes32 (bs : ByteArray) (a : Tower256Exec)
    (h : ofBytes32 bs = some a) : toBytes32 a = bs := by
  unfold ofBytes32 at h
  split at h
  · rename_i hs
    have he := Option.some.inj h
    subst a
    have hlen : bs.data.toList.length = 32 := by
      rw [Array.length_toList, ByteArray.size_data, hs]
    have hlt := Obend.Digest.HashBytes.ofBE_lt bs.data.toList
    rw [hlen] at hlt
    have hp : 256 ^ 32 = 2 ^ 256 := by decide
    rw [hp] at hlt
    apply ByteArray.ext
    apply Array.toList_inj.mp
    change (Obend.Digest.HashBytes.be 32 (BitVec.ofNat 256
      (Obend.Digest.HashBytes.ofBE bs.data.toList)).toNat).toArray.toList = bs.data.toList
    rw [List.toList_toArray, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ← hlen, be_ofBE]
  · cases h

/-- Tower-basis polynomial authentication. A TLS wire adapter must supply the
AES-GCM polynomial-basis isomorphism; reinterpreting its bytes is insufficient. -/
def ghashPoly (H : Tower128) (blocks : List Tower128) : Tower128 :=
  RoundPoly.evalCoeffs (towerZero 7 :: blocks.reverse) H

def ghashAuth (H : Tower128) (aadBlocks ctBlocks : List Tower128) (lenBlock : Tower128) : Tower128 :=
  ghashPoly H (aadBlocks ++ ctBlocks ++ [lenBlock])

/-- Raw lists are not injective polynomial encodings: leading zero blocks vanish. -/
theorem ghashPoly_leading_zero (H : Tower128) :
    ghashPoly H [] = ghashPoly H [towerZero 7] := by
  simp [ghashPoly, RoundPoly.evalCoeffs, CommRingOps.zero, CommRingOps.add, CommRingOps.mul]

/-- The absolute trace, computed by successive relative quadratic traces. -/
def towerTrace : (k : Nat) → TowerElem k → Bool
  | 0, a => a
  | k + 1, a => towerTrace k (towerMul k (towerX k) a.2)

@[simp] theorem towerTrace_zero (k : Nat) : towerTrace k (towerZero k) = false := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [towerTrace, towerZero, towerMul_zero] using ih

theorem towerTrace_add (k : Nat) (a b : TowerElem k) :
    towerTrace k (towerAdd k a b) = (towerTrace k a ^^ towerTrace k b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [towerTrace, towerAdd, towerMul_add_distrib, ih]

@[simp] theorem towerTrace_X (k : Nat) : towerTrace k (towerX k) = true := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [towerTrace, towerX, towerMul_one] using ih

theorem towerTrace_square (k : Nat) (a : TowerElem k) :
    towerTrace k (towerMul k a a) = towerTrace k a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih =>
    simp only [towerTrace, towerMul]
    rw [towerMul_comm k a.2 a.1, towerAdd_self_zero, towerZero_add]
    have h : towerMul k (towerX k) (towerMul k (towerX k) (towerMul k a.2 a.2)) =
        towerMul k (towerMul k (towerX k) a.2) (towerMul k (towerX k) a.2) := by
      simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
    rw [h, ih]

/-- Inverse of the distinguished generator, directly from its defining quadratic. -/
def towerInvX : (k : Nat) → TowerElem k
  | 0 => true
  | k + 1 => (towerX k, towerOne k)

@[simp] theorem towerX_mul_invX (k : Nat) :
    towerMul k (towerX k) (towerInvX k) = towerOne k := by
  cases k with
  | zero => rfl
  | succ k => simp [towerMul, towerX, towerInvX, towerOne]; rfl

@[simp] theorem towerTrace_invX (k : Nat) : towerTrace k (towerInvX k) = true := by
  cases k with
  | zero => rfl
  | succ k => simp only [towerTrace, towerInvX, towerMul_one, towerTrace_X]

theorem towerOne_ne_zero (k : Nat) : towerOne k ≠ towerZero k := by
  induction k with
  | zero => decide
  | succ k ih => exact fun h => ih (congrArg Prod.fst h)

/-- No root of the defining quadratic exists at any level. Multiplying by xₖ⁻²
would produce an Artin–Schreier equation with trace one on its right side. -/
theorem tower_quadratic_no_root (k : Nat) (z : TowerElem k) :
    towerAdd k (towerAdd k (towerMul k z z) (towerMul k (towerX k) z)) (towerOne k) ≠
      towerZero k := by
  intro hz
  let u := towerInvX k
  let v := towerMul k z u
  have hi : towerMul k (towerX k) u = towerOne k := towerX_mul_invX k
  have he := congrArg (towerMul k (towerMul k u u)) hz
  rw [towerMul_add_distrib, towerMul_add_distrib, towerMul_one, towerMul_zero] at he
  have hsq : towerMul k (towerMul k u u) (towerMul k z z) = towerMul k v v := by
    dsimp [v]
    simp only [towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
  have hx : towerMul k (towerMul k u u) (towerMul k (towerX k) z) = v := by
    calc
      _ = towerMul k (towerMul k (towerX k) u) (towerMul k z u) := by
        simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
      _ = v := by rw [hi, towerOne_mul]
  rw [hsq, hx] at he
  have ht := congrArg (towerTrace k) he
  rw [towerTrace_add, towerTrace_add, towerTrace_square, towerTrace_square,
    towerTrace_zero] at ht
  have hu : towerTrace k u = true := towerTrace_invX k
  rw [hu, Bool.xor_self] at ht
  contradiction

/-- Quadratic norm, in the previous level. -/
def towerNorm (k : Nat) (a : TowerElem (k + 1)) : TowerElem k :=
  towerAdd k (towerAdd k (towerMul k a.1 a.1)
    (towerMul k (towerX k) (towerMul k a.1 a.2))) (towerMul k a.2 a.2)

/-- Recursive norm inversion. At zero it returns zero. -/
def towerInv : (k : Nat) → TowerElem k → TowerElem k
  | 0, a => a
  | k + 1, a =>
    let ni := towerInv k (towerNorm k a)
    (towerMul k (towerAdd k a.1 (towerMul k (towerX k) a.2)) ni,
     towerMul k a.2 ni)

theorem towerNorm_ne_zero (k : Nat)
    (hi : ∀ a : TowerElem k, a ≠ towerZero k → towerMul k a (towerInv k a) = towerOne k)
    (a : TowerElem (k + 1)) (ha : a ≠ towerZero (k + 1)) :
    towerNorm k a ≠ towerZero k := by
  intro hn
  by_cases hb : a.2 = towerZero k
  · have h0 : a.1 ≠ towerZero k := by
      intro h0
      apply ha
      exact Prod.ext h0 hb
    have hsq : towerMul k a.1 a.1 = towerZero k := by
      simpa [towerNorm, hb] using hn
    have he := congrArg (towerMul k (towerInv k a.1)) hsq
    rw [← towerMul_assoc, towerMul_comm k (towerInv k a.1), hi a.1 h0,
      towerOne_mul, towerMul_zero] at he
    exact h0 he
  · let b := towerInv k a.2
    have hiB : towerMul k a.2 b = towerOne k := hi a.2 hb
    let z := towerMul k a.1 b
    have he := congrArg (towerMul k (towerMul k b b)) hn
    simp only [towerNorm, towerMul_add_distrib, towerMul_zero] at he
    have h1 : towerMul k (towerMul k b b) (towerMul k a.1 a.1) = towerMul k z z := by
      dsimp [z]
      simp only [towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
    have h2 : towerMul k (towerMul k b b)
        (towerMul k (towerX k) (towerMul k a.1 a.2)) = towerMul k (towerX k) z := by
      calc
        _ = towerMul k (towerMul k a.2 b) (towerMul k (towerX k) z) := by
          dsimp [z]
          simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
        _ = _ := by rw [hiB, towerOne_mul]
    have h3 : towerMul k (towerMul k b b) (towerMul k a.2 a.2) = towerOne k := by
      calc
        _ = towerMul k (towerMul k a.2 b) (towerMul k a.2 b) := by
          simp only [towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
        _ = _ := by rw [hiB, towerOne_mul]
    rw [h1, h2, h3] at he
    exact tower_quadratic_no_root k z he

theorem towerMul_inv (k : Nat) (a : TowerElem k) (ha : a ≠ towerZero k) :
    towerMul k a (towerInv k a) = towerOne k := by
  induction k with
  | zero => cases a <;> simp_all [towerZero, towerMul, towerInv, towerOne] <;> rfl
  | succ k ih =>
    have hn := towerNorm_ne_zero k ih a ha
    have hni := ih (towerNorm k a) hn
    simp only [towerInv, towerMul, towerMul_add_distrib, towerAdd_mul_distrib]
    apply Prod.ext
    · change _ = towerOne k
      rw [← hni]
      simp only [towerNorm, towerAdd_mul_distrib, towerMul_assoc,
        towerMul_comm, towerAdd_comm, towerAdd_left_comm]
    · change _ = towerZero k
      simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k),
        towerAdd_self_zero, towerAdd_cancel]

theorem towerMul_eq_zero_iff (k : Nat) (a b : TowerElem k) :
    towerMul k a b = towerZero k ↔ a = towerZero k ∨ b = towerZero k := by
  constructor
  · intro h
    if ha : a = towerZero k then exact Or.inl ha
    else
      right
      have he := congrArg (towerMul k (towerInv k a)) h
      rw [← towerMul_assoc, towerMul_comm k (towerInv k a), towerMul_inv k a ha,
        towerOne_mul, towerMul_zero] at he
      exact he
  · rintro (rfl | rfl) <;> simp

instance towerNoZeroDivisors (k : Nat) : NoZeroDivisors (TowerElem k) where
  eq_zero_or_eq_zero_of_mul_eq_zero h := (towerMul_eq_zero_iff k _ _).mp h

theorem towerMul_cancel_left (k : Nat) (a b c : TowerElem k)
    (ha : a ≠ towerZero k) (h : towerMul k a b = towerMul k a c) : b = c := by
  have he := congrArg (towerMul k (towerInv k a)) h
  simpa only [← towerMul_assoc, towerMul_comm k (towerInv k a) a,
    towerMul_inv k a ha, towerOne_mul] using he

/-- Root counting requires different polynomial functions, not merely different
raw lists (leading zero blocks are an explicit counterexample above). -/
theorem ghashDiff_roots_bound (bs₁ bs₂ : List Tower128) (L : Nat) (keys : List Tower128)
    (h₁ : bs₁.length ≤ L) (h₂ : bs₂.length ≤ L) (hnd : keys.Nodup)
    (hne : ∃ H, ghashPoly H bs₁ ≠ ghashPoly H bs₂)
    (heq : ∀ H ∈ keys, ghashPoly H bs₁ = ghashPoly H bs₂) : keys.length ≤ L := by
  let cs := RoundPoly.subCoeffs (towerZero 7 :: bs₁.reverse) (towerZero 7 :: bs₂.reverse)
  have hlen : cs.length ≤ L + 1 := by
    simp only [cs, RoundPoly.subCoeffs_length, List.length_cons, List.length_reverse]
    exact Nat.max_le.mpr ⟨Nat.succ_le_succ h₁, Nat.succ_le_succ h₂⟩
  have hev (H : Tower128) : RoundPoly.evalCoeffs cs H =
      towerAdd 7 (ghashPoly H bs₁) (ghashPoly H bs₂) :=
    RoundPoly.evalCoeffs_sub _ _ H
  have hnz : ∃ H, RoundPoly.evalCoeffs cs H ≠ towerZero 7 := by
    obtain ⟨H, hH⟩ := hne
    refine ⟨H, ?_⟩
    rw [hev]
    intro h
    have := congrArg (towerAdd 7 (ghashPoly H bs₁)) h
    rw [towerAdd_cancel, towerAdd_zero] at this
    exact hH this.symm
  have hb := RoundPoly.roots_nodup_length_le L cs keys hnd hlen hnz
  have hf : keys.filter (fun H => decide (RoundPoly.evalCoeffs cs H = towerZero 7)) = keys := by
    apply List.filter_eq_self.mpr
    intro H hH
    simp only [hev, heq H hH, towerAdd_self_zero, decide_true]
  change (keys.filter (fun H => decide (RoundPoly.evalCoeffs cs H = towerZero 7))).length ≤ L at hb
  rw [hf] at hb
  exact hb

end Obend.Crypto.BinaryTower256
