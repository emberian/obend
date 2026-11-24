module
/-
# Obend.Digest.HashBytes — fixed-width big-endian bytes, byte hashes, and their collisions

The byte vocabulary the tree's commitments are built from. Pred's `hashEq` atom
(`Pred.HashEqDigest`) and Core4's `digest` primitive (`Obend.Core.Digest`) both read a
hash's 32 output bytes with `ofBE` and state binding as "equal, or a `Collision` of the hash", so
the two layers share one carrier for the hash's failure rather than two that agree by accident.

* `be w n` — the low `w` bytes of `n`, big-endian; `be_injective` below `256 ^ w`, and `ofBE_be`
  reads them back.
* `ofBE` — big-endian bytes as a natural; `ofBE_lt` bounds it by the byte count.
* `Hash`, `Collision` — a byte hash and a collision of it at the integer reading of its output.

Init only: the channel library and the C differential link this module's compiled object.
-/
public section

namespace Obend.Digest.HashBytes

set_option autoImplicit false

/-- The low `w` bytes of `n`, big-endian. -/
@[expose] def be : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => be w (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Big-endian bytes read back as a natural. -/
@[expose] def ofBE (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

@[simp] theorem length_be (w n : Nat) : (be w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [be, ih]

theorem be_injective {w n m : Nat} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : be w n = be w m) : n = m := by
  induction w generalizing n m with
  | zero => simp at hn hm; omega
  | succ w ih =>
    simp only [be] at h
    obtain ⟨hhi, hlo⟩ := List.append_inj h (by simp)
    have hbyte : (UInt8.ofNat (n % 256)).toNat = (UInt8.ofNat (m % 256)).toNat := by
      rw [List.cons.inj hlo |>.1]
    simp only [UInt8.toNat_ofNat'] at hbyte
    have hpow : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
    have hn' : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hn)
    have hm' : m / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hm)
    have hq := ih hn' hm' hhi
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h8] at hbyte
    omega

/-- Appending one byte shifts the reading by a byte. -/
theorem ofBE_append_single (bytes : List UInt8) (b : UInt8) :
    ofBE (bytes ++ [b]) = ofBE bytes * 256 + b.toNat := by
  simp [ofBE, List.foldl_append]

/-- `be` is read back exactly below `256 ^ w`. -/
theorem ofBE_be {w n : Nat} (hn : n < 256 ^ w) : ofBE (be w n) = n := by
  induction w generalizing n with
  | zero => simp at hn; subst hn; rfl
  | succ w ih =>
    have hpow : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
    have hn' : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hn)
    simp only [be, ofBE_append_single, ih hn', UInt8.toNat_ofNat']
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h8]
    omega

/-- A `w`-byte reading is below `256 ^ w`. -/
theorem ofBE_lt_aux : ∀ (bytes : List UInt8) (acc : Nat),
    bytes.foldl (fun acc b => acc * 256 + b.toNat) acc < (acc + 1) * 256 ^ bytes.length
  | [], acc => by simp
  | b :: rest, acc => by
    have hb : b.toNat < 256 := b.toNat_lt
    have ih := ofBE_lt_aux rest (acc * 256 + b.toNat)
    simp only [List.foldl_cons, List.length_cons]
    have hle : (acc * 256 + b.toNat + 1) ≤ (acc + 1) * 256 := by omega
    have hmono := Nat.mul_le_mul_right (256 ^ rest.length) hle
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ rest.length) 256, ← Nat.mul_assoc]
    omega

theorem ofBE_lt (bytes : List UInt8) : ofBE bytes < 256 ^ bytes.length := by
  have := ofBE_lt_aux bytes 0
  simpa [ofBE] using this

/-- A byte hash. -/
abbrev Hash := List UInt8 → List UInt8

/-- A collision of `H` at the integer reading of its output. Over all byte strings
and a fixed-width `H` this is true by pigeonhole (`Theory.CollisionFloor`), so a
binding theorem ends in `CollisionAmong` over the inputs it actually hashed. -/
@[expose] def Collision (H : Hash) : Prop := ∃ a b : List UInt8, a ≠ b ∧ ofBE (H a) = ofBE (H b)

/-- A collision of `H` between two inputs that both satisfy `S`. -/
@[expose] def CollisionAmong (H : Hash) (S : List UInt8 → Prop) : Prop :=
  ∃ a b : List UInt8, S a ∧ S b ∧ a ≠ b ∧ ofBE (H a) = ofBE (H b)

theorem CollisionAmong.mono {H : Hash} {S T : List UInt8 → Prop} (sub : ∀ x, S x → T x)
    (c : CollisionAmong H S) : CollisionAmong H T := by
  obtain ⟨a, b, ha, hb, ne, eq⟩ := c
  exact ⟨a, b, sub a ha, sub b hb, ne, eq⟩

/-- The scoped collision forgets to the global one (never the converse). -/
theorem CollisionAmong.global {H : Hash} {S : List UInt8 → Prop} (c : CollisionAmong H S) :
    Collision H := by
  obtain ⟨a, b, _, _, ne, eq⟩ := c
  exact ⟨a, b, ne, eq⟩

/-! ## Unboxed `UInt64` & `ByteArray` `Exec` Refinements (`@[csimp]`) -/

/-- Single-pass tail-recursive big-endian byte accumulator without quadratic `++`. -/
def beAcc : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | w + 1, n, acc => beAcc w (n / 256) (UInt8.ofNat (n % 256) :: acc)

theorem beAcc_eq (w n : Nat) (acc : List UInt8) : beAcc w n acc = be w n ++ acc := by
  induction w generalizing n acc with
  | zero => simp [beAcc, be]
  | succ w ih =>
    simp only [beAcc, be, ih, List.append_assoc, List.singleton_append]

/-- Unboxed `UInt64` big-endian byte accumulator for up to 8 bytes. -/
@[inline] def beU64Acc : Nat → UInt64 → List UInt8 → List UInt8
  | 0, _, acc => acc
  | w + 1, v, acc => beU64Acc w (v >>> 8) (v.toUInt8 :: acc)

theorem beU64Acc_eq_beAcc (w : Nat) (v : UInt64) (acc : List UInt8) :
    beU64Acc w v acc = beAcc w v.toNat acc := by
  induction w generalizing v acc with
  | zero => rfl
  | succ w ih =>
    have hb : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := by
      apply UInt8.toNat_inj.mp
      simp [UInt8.toNat_ofNat']
    have hs : (v >>> 8).toNat = v.toNat / 256 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    simp only [beU64Acc, beAcc, hb, ih, hs]

theorem be_add (a b n : Nat) : be (a + b) n = be a (n / 256 ^ b) ++ be b n := by
  induction b generalizing n with
  | zero => simp [be]
  | succ b ih =>
    rw [Nat.add_succ, be, be, ih (n / 256), Nat.div_div_eq_div_mul,
      Nat.mul_comm 256 (256 ^ b), ← Nat.pow_succ, List.append_assoc]

theorem be_mod_pow : ∀ (w k n : Nat), w ≤ k → be w (n % 256 ^ k) = be w n
  | 0, _, _, _ => rfl
  | w + 1, 0, _, hw => absurd hw (Nat.not_succ_le_zero w)
  | w + 1, k + 1, n, hw => by
    let P := 256 ^ k
    have hP : 0 < P := Nat.pow_pos (show 0 < 256 by decide)
    have hpow : 256 ^ (k + 1) = 256 * P := by
      dsimp only [P]
      rw [Nat.pow_succ, Nat.mul_comm]
    let q := n / (256 * P)
    let r := n % (256 * P)
    have hn : n = r + 256 * (P * q) := by
      dsimp only [q, r]
      rw [← Nat.mul_assoc, Nat.add_comm]
      exact (Nat.div_add_mod n (256 * P)).symm
    have hr_lt : r < P * 256 := by
      dsimp only [r]
      rw [Nat.mul_comm]
      exact Nat.mod_lt n (Nat.mul_pos hP (show 0 < 256 by decide))
    have hr_div_lt : r / 256 < P :=
      (Nat.div_lt_iff_lt_mul (show 0 < 256 by decide)).mpr hr_lt
    have hmod : (n % 256 ^ (k + 1)) % 256 = n % 256 := by
      rw [hpow]
      change r % 256 = n % 256
      rw [hn, Nat.add_mul_mod_self_left]
    have hdiv : (n % 256 ^ (k + 1)) / 256 = (n / 256) % P := by
      rw [hpow]
      change r / 256 = (n / 256) % P
      rw [hn, Nat.add_mul_div_left r (P * q) (show 0 < 256 by decide),
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_div_lt]
    simp only [be, hmod, hdiv]
    rw [be_mod_pow w k (n / 256) (Nat.le_of_succ_le_succ hw)]

/-- Peel 64-bit limbs into unboxed `UInt64` shifts so `be` avoids bignum division per byte and `++`. -/
def beExecAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | w + 1, n, acc =>
    if w + 1 ≤ 8 then
      beU64Acc (w + 1) (UInt64.ofNat n) acc
    else
      beExecAux (w + 1 - 8) (n >>> 64) (beU64Acc 8 (UInt64.ofNat n) acc)
termination_by w => w

theorem beExecAux_eq (w n : Nat) (acc : List UInt8) :
    beExecAux w n acc = be w n ++ acc := by
  induction w using Nat.strongRecOn generalizing n acc with
  | ind w ih =>
    cases w with
    | zero => simp [beExecAux, be]
    | succ w =>
      unfold beExecAux
      have hpow8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
      have hu64 : (UInt64.ofNat n).toNat = n % 256 ^ 8 := by
        rw [UInt64.toNat_ofNat', hpow8]
      by_cases hw : w + 1 ≤ 8
      · simp only [hw, ↓reduceIte, beU64Acc_eq_beAcc, hu64, beAcc_eq, be_mod_pow _ 8 n hw]
      · simp only [hw, ↓reduceIte, beU64Acc_eq_beAcc, hu64, beAcc_eq,
          be_mod_pow 8 8 n (Nat.le_refl 8)]
        have hlt : w + 1 - 8 < w + 1 := by omega
        have hsh : n >>> 64 = n / 256 ^ 8 := by
          rw [Nat.shiftRight_eq_div_pow, hpow8]
        rw [ih (w + 1 - 8) hlt, hsh, ← List.append_assoc, ← be_add (w + 1 - 8) 8 n,
          show w + 1 - 8 + 8 = w + 1 by omega]

def beExec (w n : Nat) : List UInt8 := beExecAux w n []

@[csimp] theorem be_eq_beExec : @be = @beExec := by
  funext w n
  simpa [beExec] using (beExecAux_eq w n []).symm

/-- Accumulate big-endian bytes 8 at a time in unboxed `UInt64` before flushing to `Nat`. -/
def ofBELoop : List UInt8 → Nat → UInt64 → Nat → Nat
  | [], hi, lo, k => (hi <<< (8 * k)) + lo.toNat
  | b :: bs, hi, lo, k =>
    if k < 8 then
      ofBELoop bs hi ((lo <<< 8) + b.toUInt64) (k + 1)
    else
      ofBELoop bs ((hi <<< 64) + lo.toNat) b.toUInt64 1

theorem ofBELoop_eq : ∀ (bs : List UInt8) (hi : Nat) (lo : UInt64) (k : Nat),
    k ≤ 8 → lo.toNat < 256 ^ k →
    ofBELoop bs hi lo k = bs.foldl (fun acc b => acc * 256 + b.toNat) (hi * 256 ^ k + lo.toNat)
  | [], hi, lo, k, _, _ => by
    simp only [ofBELoop, List.foldl_nil, Nat.shiftLeft_eq]
    have hp : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
    rw [hp]
  | b :: bs, hi, lo, k, hk, hlo => by
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [ofBELoop, List.foldl_cons]
    by_cases hlt : k < 8
    · simp only [hlt, ↓reduceIte]
      have hk1 : k + 1 ≤ 8 := by omega
      have hpow_le : 256 ^ (k + 1) ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hk1
      have hpow8 : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
      have h2_64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
      have hsum_lt : lo.toNat * 256 + b.toNat < 256 ^ (k + 1) := by
        rw [Nat.pow_succ]
        calc lo.toNat * 256 + b.toNat
          _ < lo.toNat * 256 + 256 := Nat.add_lt_add_left hb _
          _ = (lo.toNat + 1) * 256 := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ 256 ^ k * 256 := Nat.mul_le_mul_right 256 hlo
      have hsum_u64 : lo.toNat * 256 + b.toNat < 18446744073709551616 :=
        Nat.lt_of_lt_of_le hsum_lt (hpow8 ▸ hpow_le)
      have hlo_lt_u64 : lo.toNat * 256 < 18446744073709551616 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ b.toNat) hsum_u64
      have hlo_sh : (lo <<< 8).toNat = lo.toNat * 256 := by
        simp only [UInt64.toNat_shiftLeft, show (8 : UInt64).toNat % 64 = 8 by decide,
          Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 by decide]
        rw [h2_64]
        exact Nat.mod_eq_of_lt hlo_lt_u64
      have hlo_next : ((lo <<< 8) + b.toUInt64).toNat = lo.toNat * 256 + b.toNat := by
        rw [UInt64.toNat_add, hlo_sh, UInt8.toNat_toUInt64, h2_64]
        exact Nat.mod_eq_of_lt hsum_u64
      rw [ofBELoop_eq bs hi _ (k + 1) hk1 (hlo_next ▸ hsum_lt), hlo_next]
      congr 1
      rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    · simp only [hlt, ↓reduceIte]
      have hk8 : k = 8 := by omega
      subst hk8
      have hsh64 : (hi <<< 64) = hi * 256 ^ 8 := by
        rw [Nat.shiftLeft_eq]
      have hb1 : b.toUInt64.toNat < 256 ^ 1 := by
        simpa [UInt8.toNat_toUInt64] using hb
      rw [ofBELoop_eq bs _ b.toUInt64 1 (by decide) hb1, hsh64, UInt8.toNat_toUInt64]

def ofBEExec (bytes : List UInt8) : Nat := ofBELoop bytes 0 0 0

@[csimp] theorem ofBE_eq_ofBEExec : @ofBE = @ofBEExec := by
  funext bytes
  simpa [ofBE, ofBEExec] using (ofBELoop_eq bytes 0 0 0 (by decide) (by decide)).symm

/-- Push `k` big-endian bytes of `v : UInt64` (`k ≤ 8`) directly into `out : ByteArray`. -/
@[inline] def pushBEU64 : Nat → UInt64 → ByteArray → ByteArray
  | 0, _, out => out
  | k + 1, v, out => pushBEU64 k v (out.push (v >>> UInt64.ofNat (8 * k)).toUInt8)

private theorem push_toList (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  cases b
  simp [ByteArray.push]

theorem pushBEU64_toList (k : Nat) (hk : k ≤ 8) (v : UInt64) (out : ByteArray) :
    (pushBEU64 k v out).data.toList = out.data.toList ++ be k v.toNat := by
  induction k generalizing out with
  | zero => simp [pushBEU64, be]
  | succ k ih =>
    have hk' : k ≤ 8 := by omega
    have h8k : 8 * k < 64 := by omega
    have hsh : (v >>> UInt64.ofNat (8 * k)).toUInt8 = UInt8.ofNat ((v.toNat / 256 ^ k) % 256) := by
      apply UInt8.toNat_inj.mp
      simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
        Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat']
      have hlt64 : 8 * k < 2 ^ 64 := by omega
      have hp : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
      rw [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt h8k, hp]
      change (v.toNat / 256 ^ k) % 256 = ((v.toNat / 256 ^ k) % 256) % 256
      exact (Nat.mod_mod _ _).symm
    have hstep : be (k + 1) v.toNat = [UInt8.ofNat ((v.toNat / 256 ^ k) % 256)] ++ be k v.toNat := by
      have hadd := be_add 1 k v.toNat
      rw [Nat.add_comm 1 k] at hadd
      exact hadd.trans (by simp [be])
    rw [pushBEU64, ih hk', push_toList, hsh, List.append_assoc, ← hstep]

/-- Push `w` big-endian bytes of `n : Nat` directly into `out : ByteArray` without `List UInt8`. -/
def pushBENat : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | w + 1, n, out =>
    if w + 1 ≤ 8 then
      pushBEU64 (w + 1) (UInt64.ofNat n) out
    else
      let top := w % 8 + 1
      let rest := w + 1 - top
      pushBENat rest n (pushBEU64 top (UInt64.ofNat (n >>> (8 * rest))) out)
termination_by w => w

theorem pushBENat_toList (w n : Nat) (out : ByteArray) :
    (pushBENat w n out).data.toList = out.data.toList ++ be w n := by
  induction w using Nat.strongRecOn generalizing n out with
  | ind w ih =>
    cases w with
    | zero => simp [pushBENat, be]
    | succ w =>
      unfold pushBENat
      have hpow8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
      by_cases hw : w + 1 ≤ 8
      · simp only [hw, ↓reduceIte, pushBEU64_toList (w + 1) hw, UInt64.toNat_ofNat', hpow8,
          be_mod_pow _ 8 n hw]
      · simp only [hw, ↓reduceIte]
        let top := w % 8 + 1
        let rest := w + 1 - top
        have htop_le : top ≤ 8 := by dsimp [top]; omega
        have hrest_lt : rest < w + 1 := by dsimp [rest, top]; omega
        have hsh : n >>> (8 * rest) = n / 256 ^ rest := by
          rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
        change (pushBENat rest n (pushBEU64 top (UInt64.ofNat (n >>> (8 * rest))) out)).data.toList = _
        rw [ih rest hrest_lt, pushBEU64_toList top htop_le, UInt64.toNat_ofNat', hpow8,
          be_mod_pow top 8 _ htop_le, hsh, List.append_assoc, ← be_add top rest n,
          show top + rest = w + 1 by dsimp [top, rest]; omega]

/-- Big-endian `ByteArray` encoding of the low `w` bytes of `n` (`0` intermediate `List UInt8`s). -/
def beByteArray (w n : Nat) : ByteArray :=
  pushBENat w n (ByteArray.emptyWithCapacity w)

theorem beByteArray_toList (w n : Nat) : (beByteArray w n).data.toList = be w n := by
  have hemp : (ByteArray.emptyWithCapacity w).data.toList = [] := rfl
  simpa [beByteArray, hemp] using pushBENat_toList w n (ByteArray.emptyWithCapacity w)

@[simp] theorem beByteArray_size (w n : Nat) : (beByteArray w n).size = w := by
  rw [← ByteArray.size_data, ← Array.length_toList, beByteArray_toList, length_be]

/-- Read big-endian bytes straight from borrowed `bs : @& ByteArray` in unboxed `UInt64` limbs. -/
def ofBEByteArrayLoop (bs : @& ByteArray) : Nat → Nat → Nat → UInt64 → Nat → Nat
  | 0, _, hi, lo, k => (hi <<< (8 * k)) + lo.toNat
  | fuel + 1, i, hi, lo, k =>
    if h : i < bs.size then
      let b := bs[i]'h
      if k < 8 then
        ofBEByteArrayLoop bs fuel (i + 1) hi ((lo <<< 8) + b.toUInt64) (k + 1)
      else
        ofBEByteArrayLoop bs fuel (i + 1) ((hi <<< 64) + lo.toNat) b.toUInt64 1
    else
      (hi <<< (8 * k)) + lo.toNat

theorem ofBEByteArrayLoop_eq (bs : ByteArray) :
    ∀ (fuel i hi : Nat) (lo : UInt64) (k : Nat),
      bs.size - i ≤ fuel →
      ofBEByteArrayLoop bs fuel i hi lo k = ofBELoop (bs.data.toList.drop i) hi lo k
  | 0, i, hi, lo, k, hf => by
    have hi_ge : bs.data.toList.length ≤ i := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    rw [List.drop_eq_nil_of_le hi_ge]
    rfl
  | fuel + 1, i, hi, lo, k, hf => by
    unfold ofBEByteArrayLoop
    by_cases h : i < bs.size
    · have hl : i < bs.data.toList.length := by
        rwa [Array.length_toList, ByteArray.size_data]
      have hdrop : bs.data.toList.drop i = (bs[i]'h) :: bs.data.toList.drop (i + 1) :=
        List.drop_eq_getElem_cons hl
      simp only [h, ↓reduceDIte, hdrop, ofBELoop]
      split
      · exact ofBEByteArrayLoop_eq bs fuel (i + 1) hi _ (k + 1) (by omega)
      · exact ofBEByteArrayLoop_eq bs fuel (i + 1) _ _ 1 (by omega)
    · have hi_ge : bs.data.toList.length ≤ i := by
        rw [Array.length_toList, ByteArray.size_data]; omega
      simp only [h, ↓reduceDIte, List.drop_eq_nil_of_le hi_ge, ofBELoop]

/-- Zero-`List` big-endian `ByteArray → Nat` reader. -/
def ofBEByteArray (bs : @& ByteArray) : Nat :=
  ofBEByteArrayLoop bs bs.size 0 0 0 0

theorem ofBEByteArray_eq (bs : ByteArray) : ofBEByteArray bs = ofBE bs.data.toList := by
  rw [ofBEByteArray, ofBEByteArrayLoop_eq bs bs.size 0 0 0 0 (by omega), List.drop_zero,
    ofBELoop_eq _ 0 0 0 (by decide) (by decide)]
  rfl

/-- Fixed-width 256-bit big-endian `ByteArray` writer and reader (`0` list allocations). -/
def be256ByteArray (d : BitVec 256) : ByteArray := beByteArray 32 d.toNat
def ofBE256ByteArray (bs : @& ByteArray) : BitVec 256 := BitVec.ofNat 256 (ofBEByteArray bs)

theorem ofBE256ByteArray_be256ByteArray (d : BitVec 256) :
    ofBE256ByteArray (be256ByteArray d) = d := by
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [ofBE256ByteArray, be256ByteArray, ofBEByteArray_eq, beByteArray_toList,
    ofBE_be (h256 ▸ d.isLt), BitVec.toNat_ofNat, Nat.mod_eq_of_lt d.isLt]

end Obend.Digest.HashBytes

end