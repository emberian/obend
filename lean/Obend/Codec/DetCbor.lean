module
/-
# Obend.Codec.DetCbor — RFC 8949 §4.2 deterministic CBOR over `ByteArray`, verified
A two-tier codec for the core deterministic encoding of RFC 8949 §4.2: definite lengths only,
shortest-width arguments, map keys strictly ascending in the bytewise lexicographic order of
their encodings (§4.2.1), no floats, no tags.
**Reasoning tier.** `encHeadSpec`/`decHeadSpec` and `encSpec`/`decSpecAt` over `List UInt8`.
`decHeadSpec` rejects every non-minimal width and every additional-information value above 27,
indefinite lengths included. `decSpecAt textOk strict` is a total parser by nesting-depth fuel,
parametric in its text predicate and an order flag: at `isValidUtf8 true` it is the canonical
decoder, checking UTF-8 text and key order as it reads; at `(fun _ => true) false` it is the
plain structural parser, used only to state injectivity under the weakest hypothesis (and so
that injectivity never mentions the UTF-8 validator, whose core definition carries
`Classical.choice`).
**Execution tier.** `pushDetCbor` writes into one `ByteArray`; `readDetCborAt` is an offset
cursor that copies only byte and text payloads, compares adjacent map keys in place on the input
(`lexLtGo`), and reads an array or map with an accumulator. `pushDetCbor_data` and
`readDetCborAt_eq` are the refinements to the reasoning tier.
**Theorems.**
* `decodeDetCbor_encodeDetCbor`: a canonical value decodes from its encoding.
* `decodeDetCbor_canonical`, `decodeDetCbor_encode_of_some`: whatever decodes is canonical and
  re-encodes to exactly the input, so no second byte string decodes to the same value
  (`decodeDetCbor_unique`).
* `encodeDetCbor_injective`: encoding is injective on values within the 64-bit length range
  (`WithinWidth`), canonical or not; `encodeDetCbor_injective_canonical` is the corollary.
* `canonicalMap_sorted`, `canonicalMap_keys_nodup`: a canonical map has no duplicate key.
* `lexLtBytes_irrefl`, `lexLtBytes_trans`, `lexLtBytes_total`: the key order is a strict total
  order; `sortedSearch_eq_find`: binary search of an array sorted by it is the linear search.
**The length bound is necessary.** An argument is 64 bits, so a list of `2^64` items wraps its
count: without the bound, `[[], 0, …, 0]` (`2^64` zeros) and `[[0, …, 0]]` have the same bytes.
`WithinWidth` is the exact side condition, and `CanonicalCbor` implies it by definition.
Text validity is core Lean's `ByteArray.validateUTF8`, which core proves equal to
`ByteArray.IsValidUTF8` (`isValidUtf8_iff`) and compiles to the runtime's validator.
The head byte is computed as `major * 32 + ai` on `Nat`, which is `(major <<< 5) ||| ai`.
What is not here: tags (major type 6), floats and the other simple values, and the length-first
key order of RFC 7049; a decoder that reports why it refused.
-/

public section

namespace Obend.Codec.DetCbor
set_option autoImplicit false

/-! ## 1. Big-endian arguments and the head -/
/-- `k` bytes of `v`, big-endian. -/
def beNat : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, v => beNat k (v / 256) ++ [UInt8.ofNat v]
/-- The number a big-endian byte list denotes. -/
def ofBe (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0
theorem beNat_length : ∀ (k v : Nat), (beNat k v).length = k
  | 0, _ => rfl
  | k + 1, v => by simp [beNat, beNat_length k]
theorem ofBe_snoc (l : List UInt8) (b : UInt8) : ofBe (l ++ [b]) = ofBe l * 256 + b.toNat := by
  simp [ofBe, List.foldl_append]
theorem ofBe_beNat : ∀ (k v : Nat), v < 256 ^ k → ofBe (beNat k v) = v
  | 0, v, h => by
    have h0 : v = 0 := by simpa using h
    subst h0; rfl
  | k + 1, v, h => by
    have hd : v / 256 < 256 ^ k := by rw [Nat.pow_succ] at h; omega
    rw [beNat, ofBe_snoc, ofBe_beNat k _ hd, UInt8.toNat_ofNat']; omega
theorem snoc_of_length_succ {α : Type} {l : List α} {k : Nat} (h : l.length = k + 1) :
    ∃ (l' : List α) (b : α), l = l' ++ [b] ∧ l'.length = k := by
  rcases List.eq_nil_or_concat l with h0 | ⟨l', b, hl⟩
  · rw [h0] at h; cases h
  · rw [List.concat_eq_append] at hl; subst hl
    exact ⟨l', b, rfl, by simpa using h⟩
theorem ofBe_lt : ∀ (k : Nat) (l : List UInt8), l.length = k → ofBe l < 256 ^ k
  | 0, l, h => by
    rw [List.length_eq_zero_iff.1 h]
    decide
  | k + 1, l, h => by
    obtain ⟨l', b, rfl, hl'⟩ := snoc_of_length_succ h; have ih := ofBe_lt k l' hl'; have hb := UInt8.toNat_lt b
    rw [ofBe_snoc, Nat.pow_succ]; omega
theorem beNat_ofBe : ∀ (k : Nat) (l : List UInt8), l.length = k → beNat k (ofBe l) = l
  | 0, l, h => by rw [List.length_eq_zero_iff.1 h]; rfl
  | k + 1, l, h => by
    obtain ⟨l', b, rfl, hl'⟩ := snoc_of_length_succ h; have hb := UInt8.toNat_lt b
    have hdiv : (ofBe l' * 256 + b.toNat) / 256 = ofBe l' := by omega
    have hlow : UInt8.ofNat (ofBe l' * 256 + b.toNat) = b := by
      apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
    rw [ofBe_snoc, beNat, hdiv, hlow, beNat_ofBe k l' hl']
/-- The initial byte: major type in the top three bits, additional information below. -/
def headByte (major : UInt8) (ai : Nat) : UInt8 := UInt8.ofNat (major.toNat * 32 + ai)
theorem headByte_toNat {major : UInt8} {ai : Nat} (hm : major.toNat < 8) (ha : ai < 32) :
    (headByte major ai).toNat = major.toNat * 32 + ai := by
  rw [headByte, UInt8.toNat_ofNat']; omega
/-- **The shortest-width head** of RFC 8949 §4.2.1: the argument in the initial byte below 24,
else in the fewest of 1, 2, 4 or 8 following bytes. -/
def encHeadSpec (major : UInt8) (n : UInt64) : List UInt8 :=
  if n.toNat < 24 then [headByte major n.toNat]
  else if n.toNat < 256 then headByte major 24 :: beNat 1 n.toNat
  else if n.toNat < 65536 then headByte major 25 :: beNat 2 n.toNat
  else if n.toNat < 4294967296 then headByte major 26 :: beNat 4 n.toNat
  else headByte major 27 :: beNat 8 n.toNat
/-- The following-byte count and the least argument an additional-information value may carry;
`none` for 28–31 (reserved and indefinite length). -/
def argWidth (ai : Nat) : Option (Nat × Nat) :=
  if ai = 24 then some (1, 24)
  else if ai = 25 then some (2, 256)
  else if ai = 26 then some (4, 65536)
  else if ai = 27 then some (8, 4294967296)
  else none
/-- Read a `k`-byte argument that must be at least `lo`. -/
def decArg (k lo : Nat) (bs : List UInt8) : Option (Nat × List UInt8) :=
  if k ≤ bs.length ∧ lo ≤ ofBe (bs.take k) then some (ofBe (bs.take k), bs.drop k) else none
/-- **The head reader**, strict on width: it accepts exactly the output of `encHeadSpec`. -/
def decHeadSpec : List UInt8 → Option (UInt8 × UInt64 × List UInt8)
  | [] => none
  | b :: rest =>
    if b.toNat % 32 < 24 then some (UInt8.ofNat (b.toNat / 32), UInt64.ofNat (b.toNat % 32), rest)
    else
      match argWidth (b.toNat % 32) with
      | none => none
      | some (k, lo) =>
        (decArg k lo rest).map fun p => (UInt8.ofNat (b.toNat / 32), UInt64.ofNat p.1, p.2)
theorem encHeadSpec_pos (major : UInt8) (n : UInt64) : 0 < (encHeadSpec major n).length := by
  unfold encHeadSpec
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp
theorem decArg_beNat (k lo v : Nat) (rest : List UInt8) (hv : v < 256 ^ k) (hlo : lo ≤ v) :
    decArg k lo (beNat k v ++ rest) = some (v, rest) := by
  have hl := beNat_length k v; unfold decArg; rw [List.take_left' hl, List.drop_left' hl, ofBe_beNat k v hv]
  rw [ite_eq_left]; exact ⟨by simp [hl], hlo⟩
theorem decArg_sound {k lo : Nat} {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decArg k lo bs = some (v, rest)) : lo ≤ v ∧ v < 256 ^ k ∧ bs = beNat k v ++ rest := by
  unfold decArg at h
  split at h
  · rename_i hc
    cases h
    have hlen : (bs.take k).length = k := by simp [List.length_take]; omega
    exact ⟨hc.2, ofBe_lt k _ hlen, by rw [beNat_ofBe k _ hlen, List.take_append_drop]⟩
  · cases h
theorem headByte_div {major : UInt8} {ai : Nat} (hm : major.toNat < 8) (ha : ai < 32) :
    UInt8.ofNat ((headByte major ai).toNat / 32) = major := by
  rw [headByte_toNat hm ha]
  have : (major.toNat * 32 + ai) / 32 = major.toNat := by omega
  rw [this, UInt8.ofNat_toNat]
theorem headByte_mod {major : UInt8} {ai : Nat} (hm : major.toNat < 8) (ha : ai < 32) :
    (headByte major ai).toNat % 32 = ai := by
  rw [headByte_toNat hm ha]; omega
/-- The head reader inverts the head writer on every suffix. -/
theorem decHeadSpec_encHeadSpec (major : UInt8) (n : UInt64) (rest : List UInt8)
    (hm : major.toNat < 8) : decHeadSpec (encHeadSpec major n ++ rest) = some (major, n, rest) := by
  have hn := UInt64.toNat_lt n; unfold encHeadSpec
  by_cases h1 : n.toNat < 24
  · rw [ite_eq_left h1]; simp only [List.cons_append, List.nil_append, decHeadSpec]
    rw [headByte_mod hm (by omega), ite_eq_left h1, headByte_div hm (by omega), UInt64.ofNat_toNat]
  · rw [ite_eq_right h1]
    by_cases h2 : n.toNat < 256
    · rw [ite_eq_left h2]; simp only [List.cons_append, decHeadSpec]
      rw [headByte_mod hm (by omega), ite_eq_right (by omega), headByte_div hm (by omega)]
      simp only [argWidth, ↓reduceIte]; rw [decArg_beNat 1 24 n.toNat rest (by omega) (by omega)]
      simp [UInt64.ofNat_toNat]
    · rw [ite_eq_right h2]
      by_cases h3 : n.toNat < 65536
      · rw [ite_eq_left h3]; simp only [List.cons_append, decHeadSpec]
        rw [headByte_mod hm (by omega), ite_eq_right (by omega), headByte_div hm (by omega)]
        simp only [argWidth, Nat.reduceEqDiff, ↓reduceIte]; rw [decArg_beNat 2 256 n.toNat rest (by omega) (by omega)]
        simp [UInt64.ofNat_toNat]
      · rw [ite_eq_right h3]
        by_cases h4 : n.toNat < 4294967296
        · rw [ite_eq_left h4]; simp only [List.cons_append, decHeadSpec]
          rw [headByte_mod hm (by omega), ite_eq_right (by omega), headByte_div hm (by omega)]
          simp only [argWidth, Nat.reduceEqDiff, ↓reduceIte]
          rw [decArg_beNat 4 65536 n.toNat rest (by omega) (by omega)]; simp [UInt64.ofNat_toNat]
        · rw [ite_eq_right h4]; simp only [List.cons_append, decHeadSpec]
          rw [headByte_mod hm (by omega), ite_eq_right (by omega), headByte_div hm (by omega)]
          simp only [argWidth, Nat.reduceEqDiff, ↓reduceIte]
          rw [decArg_beNat 8 4294967296 n.toNat rest (by omega) (by omega)]; simp [UInt64.ofNat_toNat]
theorem headByte_self (b : UInt8) : headByte (UInt8.ofNat (b.toNat / 32)) (b.toNat % 32) = b := by
  have hb := UInt8.toNat_lt b; apply UInt8.toNat_inj.1; rw [headByte, UInt8.toNat_ofNat', UInt8.toNat_ofNat']; omega
/-- **Reject non-minimal.** Whatever the head reader accepts is the shortest-width head of what
it returns, followed by the rest; the major type is one of the eight. -/
theorem decHeadSpec_sound {bs : List UInt8} {major : UInt8} {n : UInt64} {rest : List UInt8}
    (h : decHeadSpec bs = some (major, n, rest)) :
    bs = encHeadSpec major n ++ rest ∧ major.toNat < 8 := by
  cases bs with
  | nil => cases h
  | cons b tail =>
    have hb := UInt8.toNat_lt b
    have hmaj : (UInt8.ofNat (b.toNat / 32)).toNat < 8 := by rw [UInt8.toNat_ofNat']; omega
    simp only [decHeadSpec] at h
    by_cases h1 : b.toNat % 32 < 24
    · rw [ite_eq_left h1] at h; cases h; refine ⟨?_, hmaj⟩
      have hn : (UInt64.ofNat (b.toNat % 32)).toNat = b.toNat % 32 := by rw [UInt64.toNat_ofNat']; omega
      unfold encHeadSpec; rw [hn, ite_eq_left h1, headByte_self]; rfl
    · rw [ite_eq_right h1] at h; cases hw : argWidth (b.toNat % 32) with
      | none => simp [hw] at h
      | some kl =>
        obtain ⟨k, lo⟩ := kl; simp only [hw] at h; obtain ⟨⟨v, r⟩, hd, he⟩ := Option.map_eq_some_iff.1 h; cases he
        obtain ⟨hlo, hlt, htail⟩ := decArg_sound hd; refine ⟨?_, hmaj⟩
        unfold argWidth at hw
        by_cases a24 : b.toNat % 32 = 24
        · rw [ite_eq_left a24] at hw; cases hw
          have hn : (UInt64.ofNat v).toNat = v := by rw [UInt64.toNat_ofNat']; omega
          unfold encHeadSpec; rw [hn, ite_eq_right (by omega), ite_eq_left (by omega), ← a24, headByte_self, htail]
          rfl
        · rw [ite_eq_right a24] at hw
          by_cases a25 : b.toNat % 32 = 25
          · rw [ite_eq_left a25] at hw; cases hw
            have hn : (UInt64.ofNat v).toNat = v := by rw [UInt64.toNat_ofNat']; omega
            unfold encHeadSpec; rw [hn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
              ← a25, headByte_self, htail]
            rfl
          · rw [ite_eq_right a25] at hw
            by_cases a26 : b.toNat % 32 = 26
            · rw [ite_eq_left a26] at hw; cases hw
              have hn : (UInt64.ofNat v).toNat = v := by rw [UInt64.toNat_ofNat']; omega
              unfold encHeadSpec; rw [hn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
                ite_eq_left (by omega), ← a26, headByte_self, htail]
              rfl
            · rw [ite_eq_right a26] at hw
              by_cases a27 : b.toNat % 32 = 27
              · rw [ite_eq_left a27] at hw; cases hw
                have hn : (UInt64.ofNat v).toNat = v := by rw [UInt64.toNat_ofNat']; omega
                unfold encHeadSpec; rw [hn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
                  ite_eq_right (by omega), ← a27, headByte_self, htail]
                rfl
              · rw [ite_eq_right a27] at hw; cases hw

/-! ## 2. Bytewise lexicographic order -/
/-- The bytewise lexicographic order of RFC 8949 §4.2.1: the first differing byte decides, and
a proper prefix sorts first. -/
def lexLtList : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x.toNat < y.toNat) || (x == y && lexLtList xs ys)
theorem lexLtList_irrefl : ∀ (a : List UInt8), lexLtList a a = false
  | [] => rfl
  | x :: xs => by simp [lexLtList, lexLtList_irrefl xs]
theorem lexLtList_trans : ∀ (a b c : List UInt8),
    lexLtList a b = true → lexLtList b c = true → lexLtList a c = true
  | [], [], _, h, _ => by simp [lexLtList] at h
  | [], _ :: _, [], _, h => by simp [lexLtList] at h
  | [], _ :: _, _ :: _, _, _ => by simp [lexLtList]
  | _ :: _, [], _, h, _ => by simp [lexLtList] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLtList] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [lexLtList, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, _⟩
      · exact Or.inl (by omega)
      · exact Or.inl h1
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, lexLtList_trans xs ys zs h1 h2⟩
theorem lexLtList_total : ∀ (a b : List UInt8),
    lexLtList a b = false → lexLtList b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [lexLtList] at h
  | _ :: _, [], _, h => by simp [lexLtList] at h
  | x :: xs, y :: ys, h1, h2 => by
    by_cases hxy : x = y
    · subst hxy; simp only [lexLtList, Nat.lt_irrefl, decide_false, beq_self_eq_true, Bool.true_and,
        Bool.false_or] at h1 h2
      rw [lexLtList_total xs ys h1 h2]
    · have hne : x.toNat ≠ y.toNat := fun h => hxy (UInt8.toNat_inj.1 h)
      by_cases hlt : x.toNat < y.toNat
      · simp [lexLtList, hlt] at h1
      · have hgt : y.toNat < x.toNat := by omega
        simp [lexLtList, hgt] at h2
/-- Byte at an index, zero past the end. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0
theorem drop_byteAt (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.data.toList.drop i = byteAt b i :: b.data.toList.drop (i + 1) := by
  have hl : i < b.data.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons hl]; have hg : b.data.toList[i]'hl = b[i]'h := rfl; rw [hg, byteAt, dite_eq_left h]
/-- Compare the slice `[i, e₁)` of `a` with the slice `[j, e₂)` of `b`, in place. -/
def lexLtGo (a b : ByteArray) : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, i, e₁, j, e₂ =>
    if i < e₁ then
      if j < e₂ then
        if (byteAt a i).toNat < (byteAt b j).toNat then true
        else if byteAt a i == byteAt b j then lexLtGo a b fuel (i + 1) e₁ (j + 1) e₂
        else false
      else false
    else decide (j < e₂)
theorem slice_cons (b : ByteArray) (i e : Nat) (hi : i < e) (he : e ≤ b.size) :
    (b.data.toList.drop i).take (e - i) =
      byteAt b i :: (b.data.toList.drop (i + 1)).take (e - (i + 1)) := by
  have hsub : e - i = (e - (i + 1)) + 1 := by omega
  rw [drop_byteAt b i (by omega), hsub, List.take_succ_cons]
theorem slice_nil (b : ByteArray) (i e : Nat) (hi : ¬ i < e) :
    (b.data.toList.drop i).take (e - i) = [] := by
  have : e - i = 0 := by omega
  rw [this, List.take_zero]
/-- The in-place comparison is the list order on the two slices. -/
theorem lexLtGo_eq (a b : ByteArray) : ∀ (fuel i e₁ j e₂ : Nat),
    e₁ ≤ a.size → e₂ ≤ b.size → e₁ - i < fuel →
    lexLtGo a b fuel i e₁ j e₂ =
      lexLtList ((a.data.toList.drop i).take (e₁ - i)) ((b.data.toList.drop j).take (e₂ - j))
  | 0, _, _, _, _, _, _, hf => by omega
  | fuel + 1, i, e₁, j, e₂, h1, h2, hf => by
    unfold lexLtGo
    by_cases hi : i < e₁
    · rw [ite_eq_left hi, slice_cons a i e₁ hi h1]
      by_cases hj : j < e₂
      · rw [ite_eq_left hj, slice_cons b j e₂ hj h2]
        by_cases hlt : (byteAt a i).toNat < (byteAt b j).toNat
        · simp [lexLtList, hlt]
        · rw [ite_eq_right hlt]
          by_cases heq : (byteAt a i == byteAt b j) = true
          · rw [ite_eq_left heq, lexLtGo_eq a b fuel (i + 1) e₁ (j + 1) e₂ h1 h2 (by omega)]
            simp [lexLtList, hlt, heq]
          · rw [ite_eq_right heq]; simp [lexLtList, hlt, heq]
      · rw [ite_eq_right hj, slice_nil b j e₂ hj]; rfl
    · rw [ite_eq_right hi, slice_nil a i e₁ hi]
      by_cases hj : j < e₂
      · rw [slice_cons b j e₂ hj h2]; simp [lexLtList, hj]
      · rw [slice_nil b j e₂ hj]; simp [lexLtList, hj]
/-- **Bytewise lexicographic order on byte arrays**, one pass, no allocation. -/
def lexLtBytes (a b : ByteArray) : Bool := lexLtGo a b (a.size + 1) 0 a.size 0 b.size
theorem lexLtBytes_eq (a b : ByteArray) :
    lexLtBytes a b = lexLtList a.data.toList b.data.toList := by
  unfold lexLtBytes; rw [lexLtGo_eq a b _ 0 a.size 0 b.size (Nat.le_refl _) (Nat.le_refl _) (by omega)]
  have ha : a.data.toList.length = a.size := Array.length_toList
  have hb : b.data.toList.length = b.size := Array.length_toList; simp only [List.drop_zero, Nat.sub_zero]
  rw [← ha, ← hb, List.take_length, List.take_length]
theorem lexLtBytes_irrefl (a : ByteArray) : lexLtBytes a a = false := by rw [lexLtBytes_eq, lexLtList_irrefl]
theorem lexLtBytes_trans {a b c : ByteArray} (h1 : lexLtBytes a b = true)
    (h2 : lexLtBytes b c = true) : lexLtBytes a c = true := by
  rw [lexLtBytes_eq] at h1 h2 ⊢
  exact lexLtList_trans _ _ _ h1 h2
theorem byteArray_eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.toList_inj.1 h)
theorem lexLtBytes_total {a b : ByteArray} (h1 : lexLtBytes a b = false)
    (h2 : lexLtBytes b a = false) : a = b := by
  rw [lexLtBytes_eq] at h1 h2; exact byteArray_eq_of_toList (lexLtList_total _ _ h1 h2)

/-! ## 3. The data model and the reasoning-tier encoder -/
/-- The deterministic CBOR data model: the two integer major types never overlap (`nint n` is
`-1 - n`), text is carried as its UTF-8 bytes, and there is no float and no indefinite length. -/
inductive CborVal where
  | uint (n : UInt64)
  | nint (n : UInt64)
  | bytes (b : ByteArray)
  | text (utf8 : ByteArray)
  | array (items : List CborVal)
  | map (entries : List (CborVal × CborVal))
  | simpleBool (b : Bool)
/-- Text validity: core Lean's verified UTF-8 validator. -/
@[expose] def isValidUtf8 (b : ByteArray) : Bool := b.validateUTF8
theorem isValidUtf8_iff (b : ByteArray) : isValidUtf8 b = true ↔ b.IsValidUTF8 :=
  ByteArray.validateUTF8_eq_true_iff
/-- A string as a CBOR text item: its UTF-8 bytes (`String.toByteArray`, which reduces in the
kernel where `String.toUTF8` does not). -/
@[expose] def CborVal.ofString (s : String) : CborVal := .text s.toByteArray
theorem CborVal.ofString_eq (s : String) : CborVal.ofString s = .text s.toUTF8 := by
  rw [String.toUTF8_eq_toByteArray]; rfl
theorem isValidUtf8_toUTF8 (s : String) : isValidUtf8 s.toUTF8 = true := by
  rw [String.toUTF8_eq_toByteArray]; exact (isValidUtf8_iff _).2 s.isValidUTF8
mutual
/-- **The reasoning-tier encoder.** -/
def encSpec : CborVal → List UInt8
  | .uint n => encHeadSpec 0 n
  | .nint n => encHeadSpec 1 n
  | .bytes b => encHeadSpec 2 b.size.toUInt64 ++ b.data.toList
  | .text b => encHeadSpec 3 b.size.toUInt64 ++ b.data.toList
  | .array xs => encHeadSpec 4 xs.length.toUInt64 ++ encListSpec xs
  | .map kvs => encHeadSpec 5 kvs.length.toUInt64 ++ encMapSpec kvs
  | .simpleBool b => encHeadSpec 7 (if b then 21 else 20)
def encListSpec : List CborVal → List UInt8
  | [] => []
  | x :: xs => encSpec x ++ encListSpec xs
def encMapSpec : List (CborVal × CborVal) → List UInt8
  | [] => []
  | (k, v) :: rest => encSpec k ++ (encSpec v ++ encMapSpec rest)
end
theorem encSpec_pos (v : CborVal) : 0 < (encSpec v).length := by
  cases v <;> simp only [encSpec, List.length_append] <;>
    first
      | exact encHeadSpec_pos _ _
      | exact Nat.lt_of_lt_of_le (encHeadSpec_pos _ _) (Nat.le_add_right _ _)
theorem encSpec_length_le_of_mem {x : CborVal} : ∀ {xs : List CborVal}, x ∈ xs →
    (encSpec x).length ≤ (encListSpec xs).length
  | [], h => by cases h
  | y :: ys, h => by
    simp only [encListSpec, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := encSpec_length_le_of_mem h; omega
theorem encSpec_length_le_of_mem_map {p : CborVal × CborVal} :
    ∀ {kvs : List (CborVal × CborVal)}, p ∈ kvs →
      (encSpec p.1).length ≤ (encMapSpec kvs).length ∧
        (encSpec p.2).length ≤ (encMapSpec kvs).length
  | [], h => by cases h
  | (k, v) :: rest, h => by
    simp only [encMapSpec, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · dsimp only
      constructor <;> omega
    · have := encSpec_length_le_of_mem_map h
      constructor <;> omega
/-- The order check between a map key and the key before it. Off in the lax mode. -/
def keyOrderOk (strict : Bool) (prev : Option (List UInt8)) (cur : List UInt8) : Bool :=
  !strict ||
    match prev with
    | none => true
    | some p => lexLtList p cur
mutual
/-- Well-formedness at a text predicate and an order flag: every length fits the 64-bit
argument, every text string passes `textOk`, and (when `strict`) every map's keys ascend strictly
by encoding. The lax instance `(fun _ => true) false` never mentions the UTF-8 validator. -/
def wfVal (textOk : ByteArray → Bool) (strict : Bool) : CborVal → Bool
  | .uint _ => true
  | .nint _ => true
  | .bytes b => decide (b.size < 18446744073709551616)
  | .text b => decide (b.size < 18446744073709551616) && textOk b
  | .array xs => decide (xs.length < 18446744073709551616) && wfList textOk strict xs
  | .map kvs => decide (kvs.length < 18446744073709551616) && wfMap textOk strict none kvs
  | .simpleBool _ => true
def wfList (textOk : ByteArray → Bool) (strict : Bool) : List CborVal → Bool
  | [] => true
  | x :: xs => wfVal textOk strict x && wfList textOk strict xs
def wfMap (textOk : ByteArray → Bool) (strict : Bool) (prev : Option (List UInt8)) :
    List (CborVal × CborVal) → Bool
  | [] => true
  | (k, v) :: rest =>
    keyOrderOk strict prev (encSpec k) && wfVal textOk strict k && wfVal textOk strict v &&
      wfMap textOk strict (some (encSpec k)) rest
end
/-- **Canonical**: within width, valid text, and every map's keys strictly ascending in the
bytewise order of their encodings. -/
@[expose] def CanonicalCbor (v : CborVal) : Bool := wfVal isValidUtf8 true v
/-- Every length fits a 64-bit argument: the exact side condition of injectivity. -/
@[expose] def WithinWidth (v : CborVal) : Bool := wfVal (fun _ => true) false v
theorem wfList_mem {textOk : ByteArray → Bool} {strict : Bool} {x : CborVal} : ∀ {xs : List CborVal},
    wfList textOk strict xs = true → x ∈ xs → wfVal textOk strict x = true
  | [], _, h => by cases h
  | y :: ys, hw, h => by
    simp only [wfList, Bool.and_eq_true] at hw
    rcases List.mem_cons.1 h with rfl | h
    · exact hw.1
    · exact wfList_mem hw.2 h
theorem wfMap_mem {textOk : ByteArray → Bool} {strict : Bool} {p : CborVal × CborVal} :
    ∀ {kvs : List (CborVal × CborVal)} {prev : Option (List UInt8)},
      wfMap textOk strict prev kvs = true → p ∈ kvs → wfVal textOk strict p.1 = true ∧ wfVal textOk strict p.2 = true
  | [], _, _, h => by cases h
  | (k, v) :: rest, prev, hw, h => by
    simp only [wfMap, Bool.and_eq_true] at hw
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨hw.1.1.2, hw.1.2⟩
    · exact wfMap_mem hw.2 h

/-! ## 4. The reasoning-tier decoder -/
/-- Read `c` items with an item reader. -/
def decItemsWith (dec : List UInt8 → Option (CborVal × List UInt8)) :
    Nat → List UInt8 → Option (List CborVal × List UInt8)
  | 0, bs => some ([], bs)
  | c + 1, bs =>
    match dec bs with
    | none => none
    | some (x, r) =>
      match decItemsWith dec c r with
      | none => none
      | some (xs, r') => some (x :: xs, r')
/-- Read `c` key/value pairs, checking each key against the one before it. -/
def decPairsWith (strict : Bool) (dec : List UInt8 → Option (CborVal × List UInt8)) :
    Nat → Option (List UInt8) → List UInt8 → Option (List (CborVal × CborVal) × List UInt8)
  | 0, _, bs => some ([], bs)
  | c + 1, prev, bs =>
    match dec bs with
    | none => none
    | some (k, r1) =>
      if keyOrderOk strict prev (encSpec k) then
        match dec r1 with
        | none => none
        | some (v, r2) =>
          match decPairsWith strict dec c (some (encSpec k)) r2 with
          | none => none
          | some (kvs, r3) => some ((k, v) :: kvs, r3)
      else none
/-- The payload of a byte or text string: the next `n` bytes. -/
def takeBytes (n : Nat) (rest : List UInt8) : ByteArray := ⟨(rest.take n).toArray⟩
/-- One item after its head, given the reader for nested items. -/
def decBody (textOk : ByteArray → Bool) (strict : Bool)
    (dec : List UInt8 → Option (CborVal × List UInt8))
    (major : UInt8) (n : UInt64) (rest : List UInt8) : Option (CborVal × List UInt8) :=
  if major = 0 then some (.uint n, rest)
  else if major = 1 then some (.nint n, rest)
  else if major = 2 then
    if n.toNat ≤ rest.length then some (.bytes (takeBytes n.toNat rest), rest.drop n.toNat)
    else none
  else if major = 3 then
    if n.toNat ≤ rest.length ∧ textOk (takeBytes n.toNat rest) = true then
      some (.text (takeBytes n.toNat rest), rest.drop n.toNat)
    else none
  else if major = 4 then
    (decItemsWith dec n.toNat rest).map fun p => (.array p.1, p.2)
  else if major = 5 then
    (decPairsWith strict dec n.toNat none rest).map fun p => (.map p.1, p.2)
  else if major = 7 then
    if n = 20 then some (.simpleBool false, rest)
    else if n = 21 then some (.simpleBool true, rest)
    else none
  else none
/-- **The reasoning-tier decoder** at a nesting-depth fuel. -/
def decSpecAt (textOk : ByteArray → Bool) (strict : Bool) :
    Nat → List UInt8 → Option (CborVal × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
    match decHeadSpec bs with
    | none => none
    | some (major, n, rest) => decBody textOk strict (decSpecAt textOk strict fuel) major n rest
theorem decItemsWith_sound {textOk : ByteArray → Bool} {strict : Bool} {dec : List UInt8 → Option (CborVal × List UInt8)}
    (hdec : ∀ bs v rest, dec bs = some (v, rest) → bs = encSpec v ++ rest ∧ wfVal textOk strict v = true) :
    ∀ (c : Nat) (bs : List UInt8) (xs : List CborVal) (rest : List UInt8),
      decItemsWith dec c bs = some (xs, rest) →
        bs = encListSpec xs ++ rest ∧ xs.length = c ∧ wfList textOk strict xs = true
  | 0, bs, xs, rest, h => by
    simp only [decItemsWith, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | c + 1, bs, xs, rest, h => by unfold decItemsWith at h; cases hd : dec bs with
    | none => simp [hd] at h
    | some p =>
      obtain ⟨x, r⟩ := p; simp only [hd] at h; cases hr : decItemsWith dec c r with
      | none => simp [hr] at h
      | some q =>
        obtain ⟨ys, r'⟩ := q; simp only [hr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hbs, hwx⟩ := hdec bs x r hd; obtain ⟨hr', hlen, hwl⟩ := decItemsWith_sound hdec c r ys r' hr
        refine ⟨?_, by simp [hlen], by simp [wfList, hwx, hwl]⟩
        rw [hbs, hr', encListSpec, List.append_assoc]
theorem decPairsWith_sound {textOk : ByteArray → Bool} {strict : Bool} {dec : List UInt8 → Option (CborVal × List UInt8)}
    (hdec : ∀ bs v rest, dec bs = some (v, rest) → bs = encSpec v ++ rest ∧ wfVal textOk strict v = true) :
    ∀ (c : Nat) (prev : Option (List UInt8)) (bs : List UInt8)
      (kvs : List (CborVal × CborVal)) (rest : List UInt8),
      decPairsWith strict dec c prev bs = some (kvs, rest) →
        bs = encMapSpec kvs ++ rest ∧ kvs.length = c ∧ wfMap textOk strict prev kvs = true
  | 0, prev, bs, kvs, rest, h => by
    simp only [decPairsWith, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | c + 1, prev, bs, kvs, rest, h => by unfold decPairsWith at h; cases hk : dec bs with
    | none => simp [hk] at h
    | some p =>
      obtain ⟨k, r1⟩ := p; simp only [hk] at h
      by_cases hord : keyOrderOk strict prev (encSpec k) = true
      · rw [ite_eq_left hord] at h; cases hv : dec r1 with
        | none => simp [hv] at h
        | some q =>
          obtain ⟨v, r2⟩ := q; simp only [hv] at h; cases hr : decPairsWith strict dec c (some (encSpec k)) r2 with
          | none => simp [hr] at h
          | some q' =>
            obtain ⟨rest', r3⟩ := q'; simp only [hr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hbs, hwk⟩ := hdec bs k r1 hk; obtain ⟨hr1, hwv⟩ := hdec r1 v r2 hv
            obtain ⟨hr2, hlen, hwm⟩ := decPairsWith_sound hdec c _ r2 rest' r3 hr
            refine ⟨?_, by simp [hlen], by simp [wfMap, hord, hwk, hwv, hwm]⟩
            rw [hbs, hr1, hr2, encMapSpec, List.append_assoc, List.append_assoc]
      · rw [ite_eq_right hord] at h; cases h
theorem takeBytes_size {n : Nat} {rest : List UInt8} (h : n ≤ rest.length) :
    (takeBytes n rest).size = n := by
  simp [takeBytes, ByteArray.size, List.length_take, Nat.min_eq_left h]
theorem takeBytes_data (n : Nat) (rest : List UInt8) :
    (takeBytes n rest).data.toList = rest.take n := by
  simp [takeBytes]
theorem toUInt64_toNat (n : UInt64) : n.toNat.toUInt64 = n := by rw [Nat.toUInt64_eq, UInt64.ofNat_toNat]
theorem toNat_toUInt64 {k : Nat} (h : k < 18446744073709551616) : k.toUInt64.toNat = k := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
theorem decBody_sound {textOk : ByteArray → Bool} {strict : Bool} {dec : List UInt8 → Option (CborVal × List UInt8)}
    (hdec : ∀ bs v rest, dec bs = some (v, rest) → bs = encSpec v ++ rest ∧ wfVal textOk strict v = true)
    {major : UInt8} {n : UInt64} {r0 : List UInt8} {v : CborVal} {rest : List UInt8}
    (h : decBody textOk strict dec major n r0 = some (v, rest)) :
    encHeadSpec major n ++ r0 = encSpec v ++ rest ∧ wfVal textOk strict v = true := by
  have hn := UInt64.toNat_lt n; unfold decBody at h
  by_cases m0 : major = 0
  · rw [ite_eq_left m0] at h; cases h; subst m0; exact ⟨rfl, rfl⟩
  rw [ite_eq_right m0] at h
  by_cases m1 : major = 1
  · rw [ite_eq_left m1] at h; cases h; subst m1; exact ⟨rfl, rfl⟩
  rw [ite_eq_right m1] at h
  by_cases m2 : major = 2
  · rw [ite_eq_left m2] at h; subst m2
    by_cases hl : n.toNat ≤ r0.length
    · rw [ite_eq_left hl] at h; cases h; refine ⟨?_, ?_⟩
      · rw [encSpec, takeBytes_size hl, toUInt64_toNat, takeBytes_data, List.append_assoc,
          List.take_append_drop]
      · simp only [wfVal, takeBytes_size hl, decide_eq_true_eq]; omega
    · rw [ite_eq_right hl] at h; cases h
  rw [ite_eq_right m2] at h
  by_cases m3 : major = 3
  · rw [ite_eq_left m3] at h; subst m3
    by_cases hl : n.toNat ≤ r0.length ∧ textOk (takeBytes n.toNat r0) = true
    · rw [ite_eq_left hl] at h; cases h; refine ⟨?_, ?_⟩
      · rw [encSpec, takeBytes_size hl.1, toUInt64_toNat, takeBytes_data, List.append_assoc,
          List.take_append_drop]
      · simp only [wfVal, takeBytes_size hl.1, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, hl.2⟩
    · rw [ite_eq_right hl] at h; cases h
  rw [ite_eq_right m3] at h
  by_cases m4 : major = 4
  · rw [ite_eq_left m4] at h; subst m4; obtain ⟨⟨xs, r⟩, hi, he⟩ := Option.map_eq_some_iff.1 h; cases he
    obtain ⟨hr0, hlen, hwl⟩ := decItemsWith_sound hdec n.toNat r0 xs _ hi; refine ⟨?_, ?_⟩
    · rw [encSpec, hlen, toUInt64_toNat, List.append_assoc, ← hr0]
    · simp only [wfVal, hlen, hwl, Bool.and_true, decide_eq_true_eq]; omega
  rw [ite_eq_right m4] at h
  by_cases m5 : major = 5
  · rw [ite_eq_left m5] at h; subst m5; obtain ⟨⟨kvs, r⟩, hi, he⟩ := Option.map_eq_some_iff.1 h; cases he
    obtain ⟨hr0, hlen, hwm⟩ := decPairsWith_sound hdec n.toNat none r0 kvs _ hi; refine ⟨?_, ?_⟩
    · rw [encSpec, hlen, toUInt64_toNat, List.append_assoc, ← hr0]
    · simp only [wfVal, hlen, hwm, Bool.and_true, decide_eq_true_eq]; omega
  rw [ite_eq_right m5] at h
  by_cases m7 : major = 7
  · rw [ite_eq_left m7] at h; subst m7
    by_cases n20 : n = 20
    · rw [ite_eq_left n20] at h; cases h; subst n20; exact ⟨rfl, rfl⟩
    · rw [ite_eq_right n20] at h
      by_cases n21 : n = 21
      · rw [ite_eq_left n21] at h; cases h; subst n21; exact ⟨rfl, rfl⟩
      · rw [ite_eq_right n21] at h; cases h
  · rw [ite_eq_right m7] at h; cases h
/-- **Decoder soundness.** Whatever the reasoning-tier decoder returns re-encodes to exactly
the bytes it consumed and is well formed at the decoder's strictness. -/
theorem decSpecAt_sound (textOk : ByteArray → Bool) (strict : Bool) :
    ∀ (fuel : Nat) (bs : List UInt8) (v : CborVal) (rest : List UInt8),
      decSpecAt textOk strict fuel bs = some (v, rest) → bs = encSpec v ++ rest ∧ wfVal textOk strict v = true
  | 0, _, _, _, h => by simp [decSpecAt] at h
  | fuel + 1, bs, v, rest, h => by unfold decSpecAt at h; cases hh : decHeadSpec bs with
    | none => simp [hh] at h
    | some t =>
      obtain ⟨major, n, r0⟩ := t; simp only [hh] at h; obtain ⟨hbs, _⟩ := decHeadSpec_sound hh
      obtain ⟨he, hw⟩ := decBody_sound (decSpecAt_sound textOk strict fuel) h; exact ⟨hbs.trans he, hw⟩
theorem decItemsWith_enc {dec : List UInt8 → Option (CborVal × List UInt8)} :
    ∀ (xs : List CborVal) (rest : List UInt8),
      (∀ x ∈ xs, ∀ r, dec (encSpec x ++ r) = some (x, r)) →
      decItemsWith dec xs.length (encListSpec xs ++ rest) = some (xs, rest)
  | [], rest, _ => rfl
  | x :: xs, rest, h => by
    simp only [List.length_cons, decItemsWith, encListSpec, List.append_assoc]; rw [h x List.mem_cons_self]
    simp only []; rw [decItemsWith_enc xs rest (fun y hy => h y (List.mem_cons_of_mem _ hy))]
theorem decPairsWith_enc {textOk : ByteArray → Bool} {strict : Bool} {dec : List UInt8 → Option (CborVal × List UInt8)} :
    ∀ (kvs : List (CborVal × CborVal)) (prev : Option (List UInt8)) (rest : List UInt8),
      (∀ p ∈ kvs, ∀ r, dec (encSpec p.1 ++ r) = some (p.1, r) ∧
        dec (encSpec p.2 ++ r) = some (p.2, r)) →
      wfMap textOk strict prev kvs = true →
      decPairsWith strict dec kvs.length prev (encMapSpec kvs ++ rest) = some (kvs, rest)
  | [], _, _, _, _ => rfl
  | (k, v) :: kvs, prev, rest, h, hw => by
    simp only [wfMap, Bool.and_eq_true] at hw
    simp only [List.length_cons, decPairsWith, encMapSpec, List.append_assoc]; rw [(h (k, v) List.mem_cons_self _).1]
    simp only []; rw [ite_eq_left hw.1.1.1, (h (k, v) List.mem_cons_self _).2]; simp only []
    rw [decPairsWith_enc kvs _ rest (fun p hp => h p (List.mem_cons_of_mem _ hp)) hw.2]
/-- The head and major type of a value's encoding, and the payload after the head. -/
def headOf : CborVal → UInt8 × UInt64
  | .uint n => (0, n)
  | .nint n => (1, n)
  | .bytes b => (2, b.size.toUInt64)
  | .text b => (3, b.size.toUInt64)
  | .array xs => (4, xs.length.toUInt64)
  | .map kvs => (5, kvs.length.toUInt64)
  | .simpleBool b => (7, if b then 21 else 20)
def payloadOf : CborVal → List UInt8
  | .bytes b => b.data.toList
  | .text b => b.data.toList
  | .array xs => encListSpec xs
  | .map kvs => encMapSpec kvs
  | _ => []
theorem encSpec_eq_head (v : CborVal) :
    encSpec v = encHeadSpec (headOf v).1 (headOf v).2 ++ payloadOf v := by
  cases v <;> simp [encSpec, headOf, payloadOf]
theorem headOf_major_lt (v : CborVal) : (headOf v).1.toNat < 8 := by cases v <;> simp [headOf]
/-- One item body reads back the value whose head and payload it was given, when the nested
reader reads back every value nested in it. -/
theorem decBody_enc {textOk : ByteArray → Bool} {strict : Bool} {dec : List UInt8 → Option (CborVal × List UInt8)}
    (v : CborVal) (rest : List UInt8) (hw : wfVal textOk strict v = true)
    (hdec : ∀ x r, (encSpec x).length ≤ (payloadOf v).length → wfVal textOk strict x = true →
      dec (encSpec x ++ r) = some (x, r)) :
    decBody textOk strict dec (headOf v).1 (headOf v).2 (payloadOf v ++ rest) = some (v, rest) := by
  cases v with
  | uint n => rfl
  | nint n => rfl
  | bytes b =>
    simp only [wfVal, decide_eq_true_eq] at hw; have hsz : b.data.toList.length = b.size := Array.length_toList
    have hle : b.size ≤ (b.data.toList ++ rest).length := by simp [hsz]
    have htake : takeBytes b.size (b.data.toList ++ rest) = b := by
      apply byteArray_eq_of_toList
      rw [takeBytes_data, List.take_left' hsz]
    simp only [headOf, payloadOf]; unfold decBody
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, toNat_toUInt64 hw,
      ite_eq_left hle, htake, List.drop_left' hsz]
  | text b =>
    simp only [wfVal, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hsz : b.data.toList.length = b.size := Array.length_toList
    have hle : b.size ≤ (b.data.toList ++ rest).length := by simp [hsz]
    have htake : takeBytes b.size (b.data.toList ++ rest) = b := by
      apply byteArray_eq_of_toList
      rw [takeBytes_data, List.take_left' hsz]
    simp only [headOf, payloadOf]; unfold decBody
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl, toNat_toUInt64 hw.1, htake, ite_eq_left ⟨hle, hw.2⟩, List.drop_left' hsz]
  | array xs =>
    simp only [wfVal, Bool.and_eq_true, decide_eq_true_eq] at hw; simp only [headOf, payloadOf] at hdec ⊢
    unfold decBody; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_left rfl, toNat_toUInt64 hw.1,
      decItemsWith_enc xs rest (fun x hx r =>
        hdec x r (encSpec_length_le_of_mem hx) (wfList_mem hw.2 hx))]
    rfl
  | map kvs =>
    simp only [wfVal, Bool.and_eq_true, decide_eq_true_eq] at hw; simp only [headOf, payloadOf] at hdec ⊢
    unfold decBody; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, toNat_toUInt64 hw.1,
      decPairsWith_enc kvs none rest (fun p hp r =>
        ⟨hdec p.1 r (encSpec_length_le_of_mem_map hp).1 (wfMap_mem hw.2 hp).1,
          hdec p.2 r (encSpec_length_le_of_mem_map hp).2 (wfMap_mem hw.2 hp).2⟩) hw.2]
    rfl
  | simpleBool b => cases b <;> rfl
/-- **Decoder completeness.** A value well formed at the decoder's strictness is read back from
its encoding, on every suffix, at any fuel covering the encoding's length. -/
theorem decSpecAt_enc (textOk : ByteArray → Bool) (strict : Bool) :
    ∀ (fuel : Nat) (v : CborVal) (rest : List UInt8),
      (encSpec v).length ≤ fuel → wfVal textOk strict v = true →
      decSpecAt textOk strict fuel (encSpec v ++ rest) = some (v, rest)
  | 0, v, _, hf, _ => absurd (Nat.lt_of_lt_of_le (encSpec_pos v) hf) (Nat.lt_irrefl 0)
  | fuel + 1, v, rest, hf, hw => by
    have hpos := encHeadSpec_pos (headOf v).1 (headOf v).2; rw [encSpec_eq_head v, List.length_append] at hf
    unfold decSpecAt; rw [encSpec_eq_head v, List.append_assoc,
      decHeadSpec_encHeadSpec _ _ _ (headOf_major_lt v)]
    exact decBody_enc v rest hw (fun x r hx hwx =>
      decSpecAt_enc textOk strict fuel x r
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (Nat.lt_of_le_of_lt hx (Nat.lt_add_of_pos_left hpos)) hf)) hwx)
/-- Decode a whole byte list: one canonical item and nothing after it. -/
def decodeSpec (bs : List UInt8) : Option CborVal :=
  match decSpecAt isValidUtf8 true (bs.length + 1) bs with
  | some (v, []) => some v
  | _ => none
theorem decodeSpec_encSpec (v : CborVal) (hc : CanonicalCbor v = true) :
    decodeSpec (encSpec v) = some v := by
  have h := decSpecAt_enc isValidUtf8 true ((encSpec v).length + 1) v [] (Nat.le_succ _) hc; rw [List.append_nil] at h
  simp [decodeSpec, h]
theorem decodeSpec_sound {bs : List UInt8} {v : CborVal} (h : decodeSpec bs = some v) :
    CanonicalCbor v = true ∧ encSpec v = bs := by
  unfold decodeSpec at h; cases hd : decSpecAt isValidUtf8 true (bs.length + 1) bs with
  | none => simp [hd] at h
  | some p =>
    obtain ⟨w, r⟩ := p; cases r with
    | nil =>
      simp only [hd, Option.some.injEq] at h; subst h
      obtain ⟨hbs, hw⟩ := decSpecAt_sound isValidUtf8 true _ bs w [] hd; rw [List.append_nil] at hbs
      exact ⟨hw, hbs.symm⟩
    | cons _ _ => simp [hd] at h
/-- **Injectivity of the reasoning-tier encoder** on values within width, on every suffix. -/
theorem encSpec_injective {v₁ v₂ : CborVal} (h₁ : WithinWidth v₁ = true)
    (h₂ : WithinWidth v₂ = true) (h : encSpec v₁ = encSpec v₂) : v₁ = v₂ := by
  have d1 := decSpecAt_enc (fun _ => true) false (encSpec v₁).length v₁ [] (Nat.le_refl _) h₁
  have d2 := decSpecAt_enc (fun _ => true) false (encSpec v₁).length v₂ [] (by rw [h]; exact Nat.le_refl _) h₂
  rw [h] at d1 d2; rw [d1] at d2; cases d2; rfl

/-! ## 5. The execution tier: a `ByteArray` writer -/
/-- Push `k` big-endian bytes of `v`. -/
def pushBe (acc : ByteArray) : Nat → Nat → ByteArray
  | 0, _ => acc
  | k + 1, v => (pushBe acc k (v / 256)).push (UInt8.ofNat v)
theorem pushBe_data (acc : ByteArray) : ∀ (k v : Nat),
    (pushBe acc k v).data.toList = acc.data.toList ++ beNat k v
  | 0, _ => by simp [pushBe, beNat]
  | k + 1, v => by simp [pushBe, beNat, pushBe_data acc k]
/-- Push the shortest-width head. -/
def pushHead (acc : ByteArray) (major : UInt8) (n : UInt64) : ByteArray :=
  if n.toNat < 24 then acc.push (headByte major n.toNat)
  else if n.toNat < 256 then pushBe (acc.push (headByte major 24)) 1 n.toNat
  else if n.toNat < 65536 then pushBe (acc.push (headByte major 25)) 2 n.toNat
  else if n.toNat < 4294967296 then pushBe (acc.push (headByte major 26)) 4 n.toNat
  else pushBe (acc.push (headByte major 27)) 8 n.toNat
theorem pushHead_data (acc : ByteArray) (major : UInt8) (n : UInt64) :
    (pushHead acc major n).data.toList = acc.data.toList ++ encHeadSpec major n := by
  unfold pushHead encHeadSpec
  split
  · simp
  · split
    · simp [pushBe_data]
    · split
      · simp [pushBe_data]
      · split <;> simp [pushBe_data]
mutual
/-- **The execution-tier encoder**: append the encoding of a value to a buffer. -/
def pushDetCbor (acc : ByteArray) : CborVal → ByteArray
  | .uint n => pushHead acc 0 n
  | .nint n => pushHead acc 1 n
  | .bytes b => pushHead acc 2 b.size.toUInt64 ++ b
  | .text b => pushHead acc 3 b.size.toUInt64 ++ b
  | .array xs => pushListCbor (pushHead acc 4 xs.length.toUInt64) xs
  | .map kvs => pushMapCbor (pushHead acc 5 kvs.length.toUInt64) kvs
  | .simpleBool b => pushHead acc 7 (if b then 21 else 20)
def pushListCbor (acc : ByteArray) : List CborVal → ByteArray
  | [] => acc
  | x :: xs => pushListCbor (pushDetCbor acc x) xs
def pushMapCbor (acc : ByteArray) : List (CborVal × CborVal) → ByteArray
  | [] => acc
  | (k, v) :: rest => pushMapCbor (pushDetCbor (pushDetCbor acc k) v) rest
end
mutual
theorem pushDetCbor_data : ∀ (v : CborVal) (acc : ByteArray),
    (pushDetCbor acc v).data.toList = acc.data.toList ++ encSpec v
  | .uint n, acc => by rw [pushDetCbor, pushHead_data, encSpec]
  | .nint n, acc => by rw [pushDetCbor, pushHead_data, encSpec]
  | .bytes b, acc => by
    rw [pushDetCbor, ByteArray.data_append, Array.toList_append, pushHead_data, encSpec,
      List.append_assoc]
  | .text b, acc => by
    rw [pushDetCbor, ByteArray.data_append, Array.toList_append, pushHead_data, encSpec,
      List.append_assoc]
  | .array xs, acc => by rw [pushDetCbor, pushListCbor_data xs, pushHead_data, encSpec, List.append_assoc]
  | .map kvs, acc => by rw [pushDetCbor, pushMapCbor_data kvs, pushHead_data, encSpec, List.append_assoc]
  | .simpleBool b, acc => by rw [pushDetCbor, pushHead_data, encSpec]
theorem pushListCbor_data : ∀ (xs : List CborVal) (acc : ByteArray),
    (pushListCbor acc xs).data.toList = acc.data.toList ++ encListSpec xs
  | [], acc => by simp [pushListCbor, encListSpec]
  | x :: xs, acc => by rw [pushListCbor, pushListCbor_data xs, pushDetCbor_data x, encListSpec, List.append_assoc]
theorem pushMapCbor_data : ∀ (kvs : List (CborVal × CborVal)) (acc : ByteArray),
    (pushMapCbor acc kvs).data.toList = acc.data.toList ++ encMapSpec kvs
  | [], acc => by simp [pushMapCbor, encMapSpec]
  | (k, v) :: rest, acc => by
    rw [pushMapCbor, pushMapCbor_data rest, pushDetCbor_data v, pushDetCbor_data k, encMapSpec,
      List.append_assoc, List.append_assoc]
end
/-- **Encode** a value as deterministic CBOR. -/
def encodeDetCbor (v : CborVal) : ByteArray := pushDetCbor ByteArray.empty v
theorem encodeDetCbor_data (v : CborVal) : (encodeDetCbor v).data.toList = encSpec v := by
  rw [encodeDetCbor, pushDetCbor_data]; rfl

/-! ## 6. The execution tier: a `ByteArray` cursor -/
/-- Read `k` big-endian bytes at `off`. -/
def readBe (b : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, off, acc => readBe b k (off + 1) (acc * 256 + (byteAt b off).toNat)
theorem readBe_eq (b : ByteArray) : ∀ (k off acc : Nat), k ≤ b.size - off →
    readBe b k off acc =
      ((b.data.toList.drop off).take k).foldl (fun a x => a * 256 + x.toNat) acc
  | 0, _, _, _ => by simp [readBe]
  | k + 1, off, acc, h => by
    have hoff : off < b.size := by omega
    rw [readBe, readBe_eq b k (off + 1) _ (by omega), drop_byteAt b off hoff, List.take_succ_cons,
      List.foldl_cons]
def readArg (b : ByteArray) (k lo off : Nat) : Option (Nat × Nat) :=
  if k ≤ b.size - off ∧ lo ≤ readBe b k off 0 then some (readBe b k off 0, off + k) else none
theorem toList_length (b : ByteArray) : b.data.toList.length = b.size := Array.length_toList
theorem readArg_eq (b : ByteArray) (k lo off : Nat) :
    decArg k lo (b.data.toList.drop off) =
      (readArg b k lo off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold decArg readArg; simp only [List.length_drop, toList_length]
  by_cases hk : k ≤ b.size - off
  · have hbe : readBe b k off 0 = ofBe ((b.data.toList.drop off).take k) := readBe_eq b k off 0 hk; rw [hbe]
    by_cases hlo : lo ≤ ofBe ((b.data.toList.drop off).take k)
    · rw [ite_eq_left ⟨hk, hlo⟩, ite_eq_left ⟨hk, hlo⟩]; simp [List.drop_drop]
    · rw [ite_eq_right (fun h => hlo h.2), ite_eq_right (fun h => hlo h.2)]
      rfl
  · rw [ite_eq_right (fun h => hk h.1), ite_eq_right (fun h => hk h.1)]
    rfl
theorem readArg_bound {b : ByteArray} {k lo off v off' : Nat} (hoff : off ≤ b.size)
    (h : readArg b k lo off = some (v, off')) : off ≤ off' ∧ off' ≤ b.size := by
  unfold readArg at h
  split at h
  · rename_i hc
    cases h; omega
  · cases h
/-- **The head cursor**: the head at `off`, and the offset after it. -/
def readHeadAt (b : ByteArray) (off : Nat) : Option (UInt8 × UInt64 × Nat) :=
  if off < b.size then
    if (byteAt b off).toNat % 32 < 24 then
      some (UInt8.ofNat ((byteAt b off).toNat / 32), UInt64.ofNat ((byteAt b off).toNat % 32),
        off + 1)
    else
      match argWidth ((byteAt b off).toNat % 32) with
      | none => none
      | some (k, lo) =>
        (readArg b k lo (off + 1)).map
          fun p => (UInt8.ofNat ((byteAt b off).toNat / 32), UInt64.ofNat p.1, p.2)
  else none
theorem readHeadAt_eq (b : ByteArray) (off : Nat) :
    decHeadSpec (b.data.toList.drop off) =
      (readHeadAt b off).map (fun p => (p.1, p.2.1, b.data.toList.drop p.2.2)) := by
  unfold readHeadAt
  by_cases h : off < b.size
  · rw [ite_eq_left h, drop_byteAt b off h]; simp only [decHeadSpec]
    by_cases hai : (byteAt b off).toNat % 32 < 24
    · rw [ite_eq_left hai, ite_eq_left hai]; rfl
    · rw [ite_eq_right hai, ite_eq_right hai]; cases hw : argWidth ((byteAt b off).toNat % 32) with
      | none => rfl
      | some kl =>
        obtain ⟨k, lo⟩ := kl; simp only []; rw [readArg_eq b k lo (off + 1)]; cases readArg b k lo (off + 1) <;> rfl
  · rw [ite_eq_right h, List.drop_eq_nil_of_le (by rw [toList_length]; omega)]; rfl
theorem readHeadAt_bound {b : ByteArray} {off : Nat} {major : UInt8} {n : UInt64} {off' : Nat}
    (h : readHeadAt b off = some (major, n, off')) : off < off' ∧ off' ≤ b.size := by
  unfold readHeadAt at h
  by_cases hlt : off < b.size
  · rw [ite_eq_left hlt] at h
    by_cases hai : (byteAt b off).toNat % 32 < 24
    · rw [ite_eq_left hai] at h; cases h; omega
    · rw [ite_eq_right hai] at h; cases hw : argWidth ((byteAt b off).toNat % 32) with
      | none => simp [hw] at h
      | some kl =>
        obtain ⟨k, lo⟩ := kl; simp only [hw] at h; obtain ⟨⟨v, o⟩, hr, he⟩ := Option.map_eq_some_iff.1 h; cases he
        have := readArg_bound (by omega : off + 1 ≤ b.size) hr; omega
  · rw [ite_eq_right hlt] at h; cases h
/-- Read `c` items with an offset reader, accumulating; the stack does not grow with `c`. -/
def readItemsWith (rd : Nat → Option (CborVal × Nat)) :
    Nat → Nat → List CborVal → Option (List CborVal × Nat)
  | 0, off, acc => some (acc.reverse, off)
  | c + 1, off, acc =>
    match rd off with
    | none => none
    | some (x, off') => readItemsWith rd c off' (x :: acc)
theorem readItemsWith_eq {L : List UInt8} {dec : List UInt8 → Option (CborVal × List UInt8)}
    {rd : Nat → Option (CborVal × Nat)}
    (href : ∀ off, dec (L.drop off) = (rd off).map (fun p => (p.1, L.drop p.2))) :
    ∀ (c off : Nat) (acc : List CborVal),
      (readItemsWith rd c off acc).map (fun p => (p.1, L.drop p.2)) =
        (decItemsWith dec c (L.drop off)).map (fun p => (acc.reverse ++ p.1, p.2))
  | 0, off, acc => by simp [readItemsWith, decItemsWith]
  | c + 1, off, acc => by unfold readItemsWith decItemsWith; rw [href off]; cases hrd : rd off with
    | none => rfl
    | some p =>
      obtain ⟨x, off'⟩ := p; simp only [Option.map_some]; rw [readItemsWith_eq href c off' (x :: acc)]
      cases decItemsWith dec c (L.drop off') with
      | none => rfl
      | some q => simp [List.reverse_cons, List.append_assoc]
theorem readItemsWith_bound {size : Nat} {rd : Nat → Option (CborVal × Nat)}
    (hb : ∀ off v off', rd off = some (v, off') → off ≤ off' ∧ off' ≤ size) :
    ∀ (c off : Nat) (acc : List CborVal) (xs : List CborVal) (off' : Nat), off ≤ size →
      readItemsWith rd c off acc = some (xs, off') → off ≤ off' ∧ off' ≤ size
  | 0, off, acc, xs, off', hoff, h => by simp only [readItemsWith, Option.some.injEq, Prod.mk.injEq] at h; omega
  | c + 1, off, acc, xs, off', hoff, h => by unfold readItemsWith at h; cases hrd : rd off with
    | none => simp [hrd] at h
    | some p =>
      obtain ⟨x, o1⟩ := p; simp only [hrd] at h; have h1 := hb off x o1 hrd
      have h2 := readItemsWith_bound hb c o1 _ xs off' h1.2 h; omega
/-- The key at `[s, e)` sorts strictly after the previous key's span, compared in place. -/
def spanOk (b : ByteArray) (prev : Option (Nat × Nat)) (s e : Nat) : Bool :=
  match prev with
  | none => true
  | some (ps, pe) => lexLtGo b b (pe - ps + 1) ps pe s e
/-- Read `c` key/value pairs, checking key order on the input bytes themselves. -/
def readPairsWith (b : ByteArray) (rd : Nat → Option (CborVal × Nat)) :
    Nat → Option (Nat × Nat) → Nat → List (CborVal × CborVal) →
      Option (List (CborVal × CborVal) × Nat)
  | 0, _, off, acc => some (acc.reverse, off)
  | c + 1, prev, off, acc =>
    match rd off with
    | none => none
    | some (k, o1) =>
      if spanOk b prev off o1 then
        match rd o1 with
        | none => none
        | some (v, o2) => readPairsWith b rd c (some (off, o1)) o2 ((k, v) :: acc)
      else none
/-- The previous key as the spec carries it (its encoding) and as the cursor carries it (its
span in the input). -/
def PrevRel (L : List UInt8) (size : Nat) : Option (List UInt8) → Option (Nat × Nat) → Prop
  | none, none => True
  | some p, some (s, e) => e ≤ size ∧ (L.drop s).take (e - s) = p
  | _, _ => False
theorem span_eq_enc {b : ByteArray} {off o1 : Nat} {k : CborVal}
    (hle : off ≤ o1) (hsz : o1 ≤ b.size)
    (h : b.data.toList.drop off = encSpec k ++ b.data.toList.drop o1) :
    (b.data.toList.drop off).take (o1 - off) = encSpec k := by
  have hlen := congrArg List.length h; simp only [List.length_drop, List.length_append, toList_length] at hlen; rw [h]
  exact List.take_left' (by omega)
theorem spanOk_eq {b : ByteArray} {prev : Option (List UInt8)} {pspan : Option (Nat × Nat)}
    (hp : PrevRel b.data.toList b.size prev pspan) {off o1 : Nat} {k : CborVal}
    (hle : off ≤ o1) (hsz : o1 ≤ b.size)
    (h : b.data.toList.drop off = encSpec k ++ b.data.toList.drop o1) :
    spanOk b pspan off o1 = keyOrderOk true prev (encSpec k) := by
  cases prev with
  | none =>
    cases pspan with
    | none => rfl
    | some _ => exact absurd hp id
  | some p =>
    cases pspan with
    | none => exact absurd hp id
    | some se =>
      obtain ⟨ps, pe⟩ := se; obtain ⟨hpe, hslice⟩ := hp; simp only [spanOk, keyOrderOk, Bool.not_true, Bool.false_or]
      rw [lexLtGo_eq b b _ ps pe off o1 hpe hsz (by omega), hslice, span_eq_enc hle hsz h]
theorem readPairsWith_eq (b : ByteArray) {dec : List UInt8 → Option (CborVal × List UInt8)}
    {rd : Nat → Option (CborVal × Nat)}
    (href : ∀ off, dec (b.data.toList.drop off) =
      (rd off).map (fun p => (p.1, b.data.toList.drop p.2)))
    (hb : ∀ off v off', rd off = some (v, off') → off ≤ off' ∧ off' ≤ b.size)
    (hs : ∀ bs v rest, dec bs = some (v, rest) → bs = encSpec v ++ rest) :
    ∀ (c : Nat) (prev : Option (List UInt8)) (pspan : Option (Nat × Nat)) (off : Nat)
      (acc : List (CborVal × CborVal)), PrevRel b.data.toList b.size prev pspan →
      (readPairsWith b rd c pspan off acc).map (fun p => (p.1, b.data.toList.drop p.2)) =
        (decPairsWith true dec c prev (b.data.toList.drop off)).map
          (fun p => (acc.reverse ++ p.1, p.2))
  | 0, prev, pspan, off, acc, _ => by simp [readPairsWith, decPairsWith]
  | c + 1, prev, pspan, off, acc, hp => by
    unfold readPairsWith decPairsWith; have hd := href off; cases hrd : rd off with
    | none =>
      rw [hrd] at hd; rw [hd]; rfl
    | some p =>
      obtain ⟨k, o1⟩ := p; rw [hrd] at hd; rw [hd]; simp only [Option.map_some]; have hbk := hb off k o1 hrd
      have hsk := hs _ k _ hd; rw [spanOk_eq hp hbk.1 hbk.2 hsk]
      by_cases hord : keyOrderOk true prev (encSpec k) = true
      · rw [ite_eq_left hord, ite_eq_left hord]; have hd2 := href o1; cases hrd2 : rd o1 with
        | none =>
          rw [hrd2] at hd2; rw [hd2]; rfl
        | some q =>
          obtain ⟨v, o2⟩ := q; rw [hrd2] at hd2; rw [hd2]; simp only [Option.map_some]
          have hp' : PrevRel b.data.toList b.size (some (encSpec k)) (some (off, o1)) :=
            ⟨hbk.2, span_eq_enc hbk.1 hbk.2 hsk⟩
          rw [readPairsWith_eq b href hb hs c _ _ o2 ((k, v) :: acc) hp']
          cases decPairsWith true dec c (some (encSpec k)) (b.data.toList.drop o2) with
          | none => rfl
          | some r => simp [List.reverse_cons, List.append_assoc]
      · rw [ite_eq_right hord, ite_eq_right hord]; rfl
theorem readPairsWith_bound {b : ByteArray} {rd : Nat → Option (CborVal × Nat)}
    (hb : ∀ off v off', rd off = some (v, off') → off ≤ off' ∧ off' ≤ b.size) :
    ∀ (c : Nat) (pspan : Option (Nat × Nat)) (off : Nat) (acc kvs : List (CborVal × CborVal))
      (off' : Nat), off ≤ b.size →
      readPairsWith b rd c pspan off acc = some (kvs, off') → off ≤ off' ∧ off' ≤ b.size
  | 0, _, off, acc, kvs, off', hoff, h => by simp only [readPairsWith, Option.some.injEq, Prod.mk.injEq] at h; omega
  | c + 1, pspan, off, acc, kvs, off', hoff, h => by unfold readPairsWith at h; cases hrd : rd off with
    | none => simp [hrd] at h
    | some p =>
      obtain ⟨k, o1⟩ := p; simp only [hrd] at h
      split at h
      · cases hrd2 : rd o1 with
        | none => simp [hrd2] at h
        | some q =>
          obtain ⟨v, o2⟩ := q; simp only [hrd2] at h; have h1 := hb off k o1 hrd; have h2 := hb o1 v o2 hrd2
          have h3 := readPairsWith_bound hb c _ o2 _ kvs off' h2.2 h; omega
      · cases h
/-- One item after its head at `off`, given the cursor for nested items. Byte and text payloads
are copied out with one `extract`; nothing else is. -/
def readBody (b : ByteArray) (rd : Nat → Option (CborVal × Nat)) (major : UInt8) (n : UInt64)
    (off : Nat) : Option (CborVal × Nat) :=
  if major = 0 then some (.uint n, off)
  else if major = 1 then some (.nint n, off)
  else if major = 2 then
    if n.toNat ≤ b.size - off then some (.bytes (b.extract off (off + n.toNat)), off + n.toNat)
    else none
  else if major = 3 then
    if n.toNat ≤ b.size - off ∧ isValidUtf8 (b.extract off (off + n.toNat)) = true then
      some (.text (b.extract off (off + n.toNat)), off + n.toNat)
    else none
  else if major = 4 then
    (readItemsWith rd n.toNat off []).map fun p => (.array p.1, p.2)
  else if major = 5 then
    (readPairsWith b rd n.toNat none off []).map fun p => (.map p.1, p.2)
  else if major = 7 then
    if n = 20 then some (.simpleBool false, off)
    else if n = 21 then some (.simpleBool true, off)
    else none
  else none
theorem extract_eq_takeBytes (b : ByteArray) (off k : Nat) :
    b.extract off (off + k) = takeBytes k (b.data.toList.drop off) := by
  apply byteArray_eq_of_toList
  rw [takeBytes_data, ByteArray.data_extract, Array.toList_extract]
  show List.take (off + k - off) (List.drop off b.data.toList) = _; rw [Nat.add_sub_cancel_left]
theorem readBody_eq (b : ByteArray) {dec : List UInt8 → Option (CborVal × List UInt8)}
    {rd : Nat → Option (CborVal × Nat)}
    (href : ∀ off, dec (b.data.toList.drop off) =
      (rd off).map (fun p => (p.1, b.data.toList.drop p.2)))
    (hb : ∀ off v off', rd off = some (v, off') → off ≤ off' ∧ off' ≤ b.size)
    (hs : ∀ bs v rest, dec bs = some (v, rest) → bs = encSpec v ++ rest)
    (major : UInt8) (n : UInt64) (off : Nat) :
    decBody isValidUtf8 true dec major n (b.data.toList.drop off) =
      (readBody b rd major n off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold decBody readBody; simp only [List.length_drop, toList_length]
  by_cases m0 : major = 0
  · rw [ite_eq_left m0, ite_eq_left m0]; rfl
  rw [ite_eq_right m0, ite_eq_right m0]
  by_cases m1 : major = 1
  · rw [ite_eq_left m1, ite_eq_left m1]; rfl
  rw [ite_eq_right m1, ite_eq_right m1]
  by_cases m2 : major = 2
  · rw [ite_eq_left m2, ite_eq_left m2]
    by_cases hl : n.toNat ≤ b.size - off
    · rw [ite_eq_left hl, ite_eq_left hl, extract_eq_takeBytes]; simp [List.drop_drop]
    · rw [ite_eq_right hl, ite_eq_right hl]; rfl
  rw [ite_eq_right m2, ite_eq_right m2]
  by_cases m3 : major = 3
  · rw [ite_eq_left m3, ite_eq_left m3, extract_eq_takeBytes]
    by_cases hl : n.toNat ≤ b.size - off ∧
        isValidUtf8 (takeBytes n.toNat (b.data.toList.drop off)) = true
    · rw [ite_eq_left hl, ite_eq_left hl]; simp [List.drop_drop]
    · rw [ite_eq_right hl, ite_eq_right hl]; rfl
  rw [ite_eq_right m3, ite_eq_right m3]
  by_cases m4 : major = 4
  · rw [ite_eq_left m4, ite_eq_left m4]; have h := readItemsWith_eq href n.toNat off []
    cases hx : readItemsWith rd n.toNat off [] with
    | none =>
      rw [hx] at h; cases hy : decItemsWith dec n.toNat (b.data.toList.drop off) with
      | none => rfl
      | some q => rw [hy] at h; cases h
    | some p =>
      rw [hx] at h; cases hy : decItemsWith dec n.toNat (b.data.toList.drop off) with
      | none => rw [hy] at h; cases h
      | some q =>
        rw [hy] at h; simp only [Option.map_some, List.reverse_nil, List.nil_append, Option.some.injEq,
          Prod.mk.injEq] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, CborVal.array.injEq]; exact ⟨h.1.symm, h.2.symm⟩
  rw [ite_eq_right m4, ite_eq_right m4]
  by_cases m5 : major = 5
  · rw [ite_eq_left m5, ite_eq_left m5]; have h := readPairsWith_eq b href hb hs n.toNat none none off [] trivial
    cases hx : readPairsWith b rd n.toNat none off [] with
    | none =>
      rw [hx] at h; cases hy : decPairsWith true dec n.toNat none (b.data.toList.drop off) with
      | none => rfl
      | some q => rw [hy] at h; cases h
    | some p =>
      rw [hx] at h; cases hy : decPairsWith true dec n.toNat none (b.data.toList.drop off) with
      | none => rw [hy] at h; cases h
      | some q =>
        rw [hy] at h; simp only [Option.map_some, List.reverse_nil, List.nil_append, Option.some.injEq,
          Prod.mk.injEq] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, CborVal.map.injEq]; exact ⟨h.1.symm, h.2.symm⟩
  rw [ite_eq_right m5, ite_eq_right m5]
  by_cases m7 : major = 7
  · rw [ite_eq_left m7, ite_eq_left m7]
    by_cases n20 : n = 20
    · rw [ite_eq_left n20, ite_eq_left n20]; rfl
    · rw [ite_eq_right n20, ite_eq_right n20]
      by_cases n21 : n = 21
      · rw [ite_eq_left n21, ite_eq_left n21]; rfl
      · rw [ite_eq_right n21, ite_eq_right n21]; rfl
  · rw [ite_eq_right m7, ite_eq_right m7]; rfl
theorem readBody_bound {b : ByteArray} {rd : Nat → Option (CborVal × Nat)}
    (hb : ∀ off v off', rd off = some (v, off') → off ≤ off' ∧ off' ≤ b.size)
    {major : UInt8} {n : UInt64} {off : Nat} {v : CborVal} {off' : Nat} (hoff : off ≤ b.size)
    (h : readBody b rd major n off = some (v, off')) : off ≤ off' ∧ off' ≤ b.size := by
  unfold readBody at h
  by_cases m0 : major = 0
  · rw [ite_eq_left m0] at h; cases h; omega
  rw [ite_eq_right m0] at h
  by_cases m1 : major = 1
  · rw [ite_eq_left m1] at h; cases h; omega
  rw [ite_eq_right m1] at h
  by_cases m2 : major = 2
  · rw [ite_eq_left m2] at h
    split at h
    · cases h; omega
    · cases h
  rw [ite_eq_right m2] at h
  by_cases m3 : major = 3
  · rw [ite_eq_left m3] at h
    split at h
    · rename_i hc; cases h; omega
    · cases h
  rw [ite_eq_right m3] at h
  by_cases m4 : major = 4
  · rw [ite_eq_left m4] at h; obtain ⟨⟨xs, o⟩, hi, he⟩ := Option.map_eq_some_iff.1 h; cases he
    exact readItemsWith_bound hb n.toNat off [] xs _ hoff hi
  rw [ite_eq_right m4] at h
  by_cases m5 : major = 5
  · rw [ite_eq_left m5] at h; obtain ⟨⟨kvs, o⟩, hi, he⟩ := Option.map_eq_some_iff.1 h; cases he
    exact readPairsWith_bound hb n.toNat none off [] kvs _ hoff hi
  rw [ite_eq_right m5] at h
  by_cases m7 : major = 7
  · rw [ite_eq_left m7] at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · cases h
  · rw [ite_eq_right m7] at h; cases h
/-- **The execution-tier decoder**: one item at `off`, and the offset after it. -/
def readDetCborAt : Nat → ByteArray → Nat → Option (CborVal × Nat)
  | 0, _, _ => none
  | fuel + 1, b, off =>
    match readHeadAt b off with
    | none => none
    | some (major, n, off1) => readBody b (readDetCborAt fuel b) major n off1
theorem readDetCborAt_bound (b : ByteArray) : ∀ (fuel off : Nat) (v : CborVal) (off' : Nat),
    readDetCborAt fuel b off = some (v, off') → off ≤ off' ∧ off' ≤ b.size
  | 0, _, _, _, h => by simp [readDetCborAt] at h
  | fuel + 1, off, v, off', h => by unfold readDetCborAt at h; cases hh : readHeadAt b off with
    | none => simp [hh] at h
    | some t =>
      obtain ⟨major, n, off1⟩ := t; simp only [hh] at h; have h1 := readHeadAt_bound hh
      have h2 := readBody_bound (readDetCborAt_bound b fuel) h1.2 h; omega
/-- **The cursor refines the reasoning-tier decoder** at every fuel and offset. -/
theorem readDetCborAt_eq (b : ByteArray) : ∀ (fuel off : Nat),
    decSpecAt isValidUtf8 true fuel (b.data.toList.drop off) =
      (readDetCborAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2))
  | 0, _ => rfl
  | fuel + 1, off => by unfold decSpecAt readDetCborAt; rw [readHeadAt_eq b off]; cases hh : readHeadAt b off with
    | none => rfl
    | some t =>
      obtain ⟨major, n, off1⟩ := t; simp only [Option.map_some]
      exact readBody_eq b (readDetCborAt_eq b fuel) (readDetCborAt_bound b fuel)
        (fun bs v rest h => (decSpecAt_sound isValidUtf8 true fuel bs v rest h).1) major n off1
/-- **Decode** a whole buffer: one canonical item and nothing after it. -/
def decodeDetCbor (b : ByteArray) : Option CborVal :=
  match readDetCborAt (b.size + 1) b 0 with
  | some (v, off) => if off = b.size then some v else none
  | none => none
theorem decodeDetCbor_eq_spec (b : ByteArray) : decodeDetCbor b = decodeSpec b.data.toList := by
  have hr := readDetCborAt_eq b (b.size + 1) 0; rw [List.drop_zero] at hr; unfold decodeDetCbor decodeSpec
  rw [toList_length, hr]; cases hrd : readDetCborAt (b.size + 1) b 0 with
  | none => rfl
  | some p =>
    obtain ⟨v, off⟩ := p; have hbd := readDetCborAt_bound b _ 0 v off hrd; simp only [Option.map_some]
    by_cases ho : off = b.size
    · have hnil : b.data.toList.drop off = [] :=
        List.drop_eq_nil_of_le (by rw [toList_length]; omega)
      rw [ite_eq_left ho, hnil]
    · have hne : b.data.toList.drop off ≠ [] := by
        intro hn; rw [List.drop_eq_nil_iff, toList_length] at hn; omega
      rw [ite_eq_right ho]; cases hd : b.data.toList.drop off with
      | nil => exact absurd hd hne
      | cons _ _ => rfl

/-! ## 7. The deterministic bijection -/
/-- **Roundtrip.** A canonical value decodes from its encoding. -/
theorem decodeDetCbor_encodeDetCbor (v : CborVal) (hc : CanonicalCbor v = true) :
    decodeDetCbor (encodeDetCbor v) = some v := by
  rw [decodeDetCbor_eq_spec, encodeDetCbor_data]; exact decodeSpec_encSpec v hc
/-- **Decoder canonicality.** Whatever decodes is canonical. -/
theorem decodeDetCbor_canonical {b : ByteArray} {v : CborVal} (h : decodeDetCbor b = some v) :
    CanonicalCbor v = true := by
  rw [decodeDetCbor_eq_spec] at h; exact (decodeSpec_sound h).1
/-- **Reject non-minimal.** Whatever decodes re-encodes to exactly the input bytes. -/
theorem decodeDetCbor_encode_of_some {b : ByteArray} {v : CborVal}
    (h : decodeDetCbor b = some v) : encodeDetCbor v = b := by
  rw [decodeDetCbor_eq_spec] at h; apply byteArray_eq_of_toList
  rw [encodeDetCbor_data]; exact (decodeSpec_sound h).2
/-- No two byte strings decode to the same value. -/
theorem decodeDetCbor_unique {b₁ b₂ : ByteArray} {v : CborVal} (h₁ : decodeDetCbor b₁ = some v)
    (h₂ : decodeDetCbor b₂ = some v) : b₁ = b₂ := by
  rw [← decodeDetCbor_encode_of_some h₁, ← decodeDetCbor_encode_of_some h₂]
/-- **Injectivity.** No two values within width encode to the same bytes. The width bound is
necessary: see the module note. -/
theorem encodeDetCbor_injective (v₁ v₂ : CborVal) (h₁ : WithinWidth v₁ = true)
    (h₂ : WithinWidth v₂ = true) (h : encodeDetCbor v₁ = encodeDetCbor v₂) : v₁ = v₂ := by
  apply encSpec_injective h₁ h₂; rw [← encodeDetCbor_data, ← encodeDetCbor_data, h]
theorem encodeDetCbor_injective_canonical (v₁ v₂ : CborVal) (h₁ : CanonicalCbor v₁ = true)
    (h₂ : CanonicalCbor v₂ = true) (h : encodeDetCbor v₁ = encodeDetCbor v₂) : v₁ = v₂ := by
  have d1 := decodeDetCbor_encodeDetCbor v₁ h₁; rw [h, decodeDetCbor_encodeDetCbor v₂ h₂] at d1
  exact (Option.some.inj d1).symm
mutual
theorem wfVal_lax : ∀ (v : CborVal), wfVal isValidUtf8 true v = true → wfVal (fun _ => true) false v = true
  | .uint _, _ => rfl
  | .nint _, _ => rfl
  | .bytes _, h => h
  | .text b, h => by
    simp only [wfVal, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, trivial⟩
  | .array xs, h => by
    simp only [wfVal, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, wfList_lax xs h.2⟩
  | .map kvs, h => by
    simp only [wfVal, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, wfMap_lax kvs none none h.2⟩
  | .simpleBool _, _ => rfl
theorem wfList_lax : ∀ (xs : List CborVal), wfList isValidUtf8 true xs = true → wfList (fun _ => true) false xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [wfList, Bool.and_eq_true] at h ⊢
    exact ⟨wfVal_lax x h.1, wfList_lax xs h.2⟩
theorem wfMap_lax : ∀ (kvs : List (CborVal × CborVal)) (prev prev' : Option (List UInt8)),
    wfMap isValidUtf8 true prev kvs = true → wfMap (fun _ => true) false prev' kvs = true
  | [], _, _, _ => rfl
  | (k, v) :: rest, prev, prev', h => by
    simp only [wfMap, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨by simp [keyOrderOk], wfVal_lax k h.1.1.2⟩, wfVal_lax v h.1.2⟩,
      wfMap_lax rest _ _ h.2⟩
end
/-- A canonical value is within width. -/
theorem canonical_withinWidth {v : CborVal} (h : CanonicalCbor v = true) : WithinWidth v = true :=
  wfVal_lax v h
theorem keyOrderOk_some {p cur : List UInt8} (h : keyOrderOk true (some p) cur = true) :
    lexLtList p cur = true := by
  simpa [keyOrderOk] using h
theorem wfMap_sorted : ∀ (kvs : List (CborVal × CborVal)) (prev : Option (List UInt8)),
    wfMap isValidUtf8 true prev kvs = true →
      (∀ p, prev = some p → ∀ q ∈ kvs, lexLtList p (encSpec q.1) = true) ∧
        kvs.Pairwise (fun a c => lexLtList (encSpec a.1) (encSpec c.1) = true)
  | [], _, _ => ⟨fun _ _ _ h => (by cases h), List.Pairwise.nil⟩
  | (k, v) :: rest, prev, hw => by
    simp only [wfMap, Bool.and_eq_true] at hw; obtain ⟨ih1, ih2⟩ := wfMap_sorted rest (some (encSpec k)) hw.2
    refine ⟨?_, List.pairwise_cons.2 ⟨fun q hq => ih1 _ rfl q hq, ih2⟩⟩
    intro p hp q hq; subst hp; have hpk : lexLtList p (encSpec k) = true := keyOrderOk_some hw.1.1.1
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hpk
    · exact lexLtList_trans _ _ _ hpk (ih1 _ rfl q hq)
/-- **A canonical map is strictly sorted** by the bytewise order of its encoded keys: every
pair of entries, not only adjacent ones. -/
theorem canonicalMap_sorted {kvs : List (CborVal × CborVal)}
    (h : CanonicalCbor (.map kvs) = true) :
    kvs.Pairwise (fun a c => lexLtBytes (encodeDetCbor a.1) (encodeDetCbor c.1) = true) := by
  simp only [CanonicalCbor, wfVal, Bool.and_eq_true] at h; refine (wfMap_sorted kvs none h.2).2.imp ?_
  intro a c hac; rw [lexLtBytes_eq, encodeDetCbor_data, encodeDetCbor_data]; exact hac
/-- **A canonical map has no duplicate key.** -/
theorem canonicalMap_keys_nodup {kvs : List (CborVal × CborVal)}
    (h : CanonicalCbor (.map kvs) = true) : (kvs.map (·.1)).Nodup := by
  rw [List.Nodup, List.pairwise_map]; refine (canonicalMap_sorted h).imp ?_
  intro a c hac heq; rw [heq, lexLtBytes_irrefl] at hac; cases hac

/-! ## 8. Arrays sorted by a byte key -/
theorem pairwise_getElem?_rel {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {i j : Nat} {x y : α},
      l[i]? = some x → l[j]? = some y → i < j → R x y
  | [], _, i, j, x, y, hi, _, _ => by simp at hi
  | a :: l, hp, i, j, x, y, hi, hj, hij => by cases j with
    | zero => omega
    | succ j =>
      rw [List.getElem?_cons_succ] at hj
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at hi
        cases hi; exact (List.pairwise_cons.1 hp).1 y (List.mem_of_getElem? hj)
      | succ i =>
        rw [List.getElem?_cons_succ] at hi
        exact pairwise_getElem?_rel (List.pairwise_cons.1 hp).2 hi hj (by omega)
theorem find?_of_sorted {α : Type} {key : α → ByteArray} :
    ∀ {l : List α}, l.Pairwise (fun x y => lexLtBytes (key x) (key y) = true) →
      ∀ {i : Nat} {e : α}, l[i]? = some e → l.find? (fun x => decide (key x = key e)) = some e
  | [], _, i, e, h => by simp at h
  | a :: l, hp, i, e, h => by cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      cases h; simp
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      have hlt := (List.pairwise_cons.1 hp).1 e (List.mem_of_getElem? h)
      have hne : decide (key a = key e) = false := by
        apply decide_eq_false
        intro hb; rw [hb, lexLtBytes_irrefl] at hlt; cases hlt
      simp only [List.find?_cons, hne]
      exact find?_of_sorted (List.pairwise_cons.1 hp).2 h
/-- Binary search for the entry with byte key `k` in the window `[lo, hi)`. -/
def bsearchFuel {α : Type} (key : α → ByteArray) (a : Array α) (k : ByteArray) :
    Nat → Nat → Nat → Option α
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      match a[(lo + hi) / 2]? with
      | none => none
      | some e =>
        if lexLtBytes (key e) k then bsearchFuel key a k fuel ((lo + hi) / 2 + 1) hi
        else if lexLtBytes k (key e) then bsearchFuel key a k fuel lo ((lo + hi) / 2)
        else some e
    else none
/-- `O(log n)` search of an array strictly sorted by `lexLtBytes` on `key`. -/
def sortedSearch {α : Type} (key : α → ByteArray) (a : Array α) (k : ByteArray) : Option α :=
  bsearchFuel key a k (a.size + 1) 0 a.size
theorem bsearchFuel_eq_find {α : Type} (key : α → ByteArray) (a : Array α) (k : ByteArray)
    (hs : a.toList.Pairwise (fun x y => lexLtBytes (key x) (key y) = true)) :
    ∀ (fuel lo hi : Nat), hi ≤ a.size → hi - lo < fuel →
      (∀ (i : Nat) (e : α), a.toList[i]? = some e → (i < lo ∨ hi ≤ i) → key e ≠ k) →
      bsearchFuel key a k fuel lo hi = a.toList.find? (fun e => decide (key e = k))
  | 0, _, _, _, hf, _ => by omega
  | fuel + 1, lo, hi, hhi, hf, hout => by
    unfold bsearchFuel
    by_cases hlt : lo < hi
    · rw [ite_eq_left hlt]
      have hmid : (lo + hi) / 2 < a.size := by omega
      obtain ⟨e, he⟩ : ∃ e, a[(lo + hi) / 2]? = some e :=
        ⟨a[(lo + hi) / 2], getElem?_pos a _ hmid⟩
      have hel : a.toList[(lo + hi) / 2]? = some e := by rw [Array.getElem?_toList]; exact he
      simp only [he]
      by_cases hk : lexLtBytes (key e) k = true
      · rw [ite_eq_left hk]; refine bsearchFuel_eq_find key a k hs fuel _ hi hhi (by omega) ?_
        intro i x hx hcase
        rcases hcase with hi' | hi'
        · by_cases hlo : i < lo
          · exact hout i x hx (Or.inl hlo)
          · intro hxk
            by_cases him : i = (lo + hi) / 2
            · subst him; rw [hel] at hx; cases hx; rw [hxk, lexLtBytes_irrefl] at hk; cases hk
            · have hxe : lexLtBytes (key x) (key e) = true :=
                pairwise_getElem?_rel hs hx hel (by omega)
              have := lexLtBytes_trans hxe hk; rw [hxk, lexLtBytes_irrefl] at this; cases this
        · exact hout i x hx (Or.inr hi')
      · rw [ite_eq_right hk]
        by_cases hk2 : lexLtBytes k (key e) = true
        · rw [ite_eq_left hk2]; refine bsearchFuel_eq_find key a k hs fuel lo _ (by omega) (by omega) ?_
          intro i x hx hcase
          rcases hcase with hi' | hi'
          · exact hout i x hx (Or.inl hi')
          · by_cases hhi' : hi ≤ i
            · exact hout i x hx (Or.inr hhi')
            · intro hxk
              by_cases him : i = (lo + hi) / 2
              · subst him; rw [hel] at hx; cases hx; rw [hxk, lexLtBytes_irrefl] at hk2; cases hk2
              · have hxe : lexLtBytes (key e) (key x) = true :=
                  pairwise_getElem?_rel hs hel hx (by omega)
                have := lexLtBytes_trans hk2 hxe; rw [hxk, lexLtBytes_irrefl] at this; cases this
        · rw [ite_eq_right hk2]; have hke : key e = k :=
            lexLtBytes_total (Bool.not_eq_true _ ▸ hk) (Bool.not_eq_true _ ▸ hk2)
          subst hke; exact (find?_of_sorted hs hel).symm
    · rw [ite_eq_right hlt]
      symm; rw [List.find?_eq_none]
      intro x hx; obtain ⟨i, hi', hget⟩ := List.mem_iff_getElem.1 hx
      have hx' : a.toList[i]? = some x := by rw [List.getElem?_eq_getElem hi', hget]
      have hne := hout i x hx' (by omega); simpa using hne
/-- **The binary search is the linear search** on an array strictly sorted by byte key. -/
theorem sortedSearch_eq_find {α : Type} (key : α → ByteArray) (a : Array α) (k : ByteArray)
    (hs : a.toList.Pairwise (fun x y => lexLtBytes (key x) (key y) = true)) :
    sortedSearch key a k = a.toList.find? (fun e => decide (key e = k)) := by
  refine bsearchFuel_eq_find key a k hs (a.size + 1) 0 a.size (Nat.le_refl _) (by omega) ?_
  intro i e he hcase
  rcases hcase with h0 | hsz
  · omega
  · have hlt : i < a.toList.length := (List.getElem?_eq_some_iff.1 he).1
    simp at hlt; omega
/-- Adjacent keys strictly ascending: one pass. -/
def sortedByKeyB {α : Type} (key : α → ByteArray) : List α → Bool
  | a :: b :: rest => lexLtBytes (key a) (key b) && sortedByKeyB key (b :: rest)
  | _ => true
theorem sortedByKeyB_sound {α : Type} (key : α → ByteArray) :
    ∀ (l : List α), sortedByKeyB key l = true →
      l.Pairwise (fun x y => lexLtBytes (key x) (key y) = true)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: rest, h => by
    simp only [sortedByKeyB, Bool.and_eq_true] at h; have ih := sortedByKeyB_sound key (b :: rest) h.2
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · exact lexLtBytes_trans h.1 ((List.pairwise_cons.1 ih).1 y hy)
/-- A prefix sorts before its extensions, and the first differing byte decides. -/
example : sortedByKeyB id [⟨#[1]⟩, ⟨#[1, 0]⟩, ⟨#[1, 0, 7]⟩, ⟨#[2]⟩] = true := by decide +kernel

/-! ## 9. Decidable equality -/
mutual
def CborVal.beq : CborVal → CborVal → Bool
  | .uint a, y => match y with | .uint b => a == b | _ => false
  | .nint a, y => match y with | .nint b => a == b | _ => false
  | .bytes a, y => match y with | .bytes b => decide (a = b) | _ => false
  | .text a, y => match y with | .text b => decide (a = b) | _ => false
  | .array a, y => match y with | .array b => beqList a b | _ => false
  | .map a, y => match y with | .map b => beqMap a b | _ => false
  | .simpleBool a, y => match y with | .simpleBool b => a == b | _ => false
def beqList : List CborVal → List CborVal → Bool
  | [], ys => ys.isEmpty
  | x :: xs, ys => match ys with | y :: ys' => x.beq y && beqList xs ys' | [] => false
def beqMap : List (CborVal × CborVal) → List (CborVal × CborVal) → Bool
  | [], ys => ys.isEmpty
  | (k, v) :: xs, ys =>
    match ys with
    | (k', v') :: ys' => k.beq k' && v.beq v' && beqMap xs ys'
    | [] => false
end
mutual
theorem CborVal.eq_of_beq : ∀ (a b : CborVal), a.beq b = true → a = b
  | .uint a, y, h => by cases y <;> simp [CborVal.beq] at h; rw [h]
  | .nint a, y, h => by cases y <;> simp [CborVal.beq] at h; rw [h]
  | .bytes a, y, h => by cases y <;> simp [CborVal.beq] at h; rw [h]
  | .text a, y, h => by cases y <;> simp [CborVal.beq] at h; rw [h]
  | .array a, y, h => by cases y <;> simp [CborVal.beq] at h; rw [eq_of_beqList a _ h]
  | .map a, y, h => by cases y <;> simp [CborVal.beq] at h; rw [eq_of_beqMap a _ h]
  | .simpleBool a, y, h => by cases y <;> simp [CborVal.beq] at h; rw [h]
theorem eq_of_beqList : ∀ (a b : List CborVal), beqList a b = true → a = b
  | [], ys, h => by simp only [beqList] at h; exact (List.isEmpty_iff.1 h).symm
  | x :: xs, ys, h => by cases ys with
    | nil => simp [beqList] at h
    | cons y ys' =>
      simp only [beqList, Bool.and_eq_true] at h; rw [CborVal.eq_of_beq x y h.1, eq_of_beqList xs ys' h.2]
theorem eq_of_beqMap : ∀ (a b : List (CborVal × CborVal)), beqMap a b = true → a = b
  | [], ys, h => by simp only [beqMap] at h; exact (List.isEmpty_iff.1 h).symm
  | (k, v) :: xs, ys, h => by cases ys with
    | nil => simp [beqMap] at h
    | cons y ys' =>
      obtain ⟨k', v'⟩ := y; simp only [beqMap, Bool.and_eq_true] at h
      rw [CborVal.eq_of_beq k k' h.1.1, CborVal.eq_of_beq v v' h.1.2, eq_of_beqMap xs ys' h.2]
end
mutual
theorem CborVal.beq_refl : ∀ (a : CborVal), a.beq a = true
  | .uint _ => by simp [CborVal.beq]
  | .nint _ => by simp [CborVal.beq]
  | .bytes _ => by simp [CborVal.beq]
  | .text _ => by simp [CborVal.beq]
  | .array a => by simp [CborVal.beq, beqList_refl a]
  | .map a => by simp [CborVal.beq, beqMap_refl a]
  | .simpleBool _ => by simp [CborVal.beq]
theorem beqList_refl : ∀ (a : List CborVal), beqList a a = true
  | [] => rfl
  | x :: xs => by simp [beqList, CborVal.beq_refl x, beqList_refl xs]
theorem beqMap_refl : ∀ (a : List (CborVal × CborVal)), beqMap a a = true
  | [] => rfl
  | (k, v) :: xs => by simp [beqMap, CborVal.beq_refl k, CborVal.beq_refl v, beqMap_refl xs]
end
instance : DecidableEq CborVal := fun a b =>
  if h : a.beq b = true then isTrue (CborVal.eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ CborVal.beq_refl a))

end Obend.Codec.DetCbor
end
