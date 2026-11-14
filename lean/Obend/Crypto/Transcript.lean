module
/-
# Obend.Crypto.Transcript — Fenzi-Safe, Instance-Bound 256-Bit Domain-Separated Fiat–Shamir Transcript

Eliminates critical 2026 Fiat–Shamir and field-aliasing vulnerabilities at the Lean type level:
1. **Fenzi Attack on Program-Generated Circuits (`ePrint 2026/1838`) & Statement Grinding (`InstanceBound`)**:
   `Transcript` is indexed by `TranscriptPhase` (`.unseeded | .relationBound | .instanceBound`):
   - `Transcript.newUnseeded : ByteArray → Transcript .unseeded`
   - `bindRelation : String → ByteArray → ByteArray → Transcript .unseeded → Transcript .relationBound`
     is the **sole entry constructor** producing `.relationBound` (`Transcript.mk` is `private`).
   - `bindInstance : [TranscriptEncode ι] → ι → Transcript .relationBound → BoundTranscript ι`
     is the **sole entry constructor** producing `Transcript .instanceBound` and `BoundTranscript ι`,
     preventing commitment/sum `0`-grinding before challenge squeezing.
   - `absorbMsg`, `squeezeChallenge256`, `squeezeGoldilocks`, and `squeezeGoldilocksExt2` require
     `[CanSqueezeTranscript phase]` (inhabited ONLY for `.instanceBound`;
     squeezing from `.unseeded` or `.relationBound` before `bindInstance` is a compile-time Lean type error).
2. **Canonical Goldilocks Field Lift (`CanonicalLift`, `canonicalLift?`)**:
   Rejects non-canonical `n ≥ goldilocksPrime` witnesses (`0` vs `p = 2^64 - 2^32 + 1` alias).
3. **Bounded Collision Carrier (`BoundedCollision`) & Constructive Collision Extraction**:
   Replaces pigeonhole-vacuous unbounded `¬ Collision H` with `BoundedCollision H maxBytes`
   (`Nonempty (HashCollisionWitness H maxBytes)`) and `0 Classical` collision extractors.
4. **Collision-Free Canonical Framing (`encodeFrame_injective`, `encodePointBytes_injective`, `encodeSignedIntBytes_injective`)**:
   Unconditional self-delimiting LEB128 length-prefixed framing with zero boundary or sign ambiguity.
-/
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes
public import Obend.Crypto.Multilinear
public import Obend.Judge.Computational

public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Apps.ZkNtt
open Obend.Judge.Computational

set_option autoImplicit false

/-! ## 1. Self-Delimiting LEB128 Length-Prefixed Framing, Length Bounds & Unconditional Injectivity -/

/-- Fuel-bounded LEB128 variable-length natural encoding:
    continuation bytes have high bit set (`≥ 128`), final byte has `< 128`. -/
@[expose] def leb128Aux : Nat → Nat → List UInt8
  | 0, v => [UInt8.ofNat (v % 128)]
  | fuel + 1, v =>
    if v < 128 then [UInt8.ofNat v]
    else UInt8.ofNat (128 + v % 128) :: leb128Aux fuel (v / 128)

/-- Canonical self-delimiting LEB128 encoding of `n : Nat`. -/
@[expose] def leb128 (n : Nat) : List UInt8 := leb128Aux n n

theorem leb128Aux_length_le_of_lt_two_pow :
    ∀ (k fuel v : Nat), v < 2 ^ k → (leb128Aux fuel v).length ≤ k + 1
  | 0, fuel, v, hv => by
    have hv0 : v = 0 := by simp at hv; exact hv
    subst hv0
    cases fuel <;> simp [leb128Aux]
  | _ + 1, 0, _, _ => by
    simp [leb128Aux]
  | k + 1, fuel + 1, v, hv => by
    simp only [leb128Aux]
    split
    · simp
    · simp only [List.length_cons]
      have hdiv : v / 128 < 2 ^ k := by
        rw [Nat.pow_succ] at hv
        omega
      have ih := leb128Aux_length_le_of_lt_two_pow k fuel (v / 128) hdiv
      omega

/-- Every `n < 2 ^ k` encodes in at most `k + 1` LEB128 bytes. -/
theorem leb128_length_le_of_lt_two_pow {n k : Nat} (hn : n < 2 ^ k) :
    (leb128 n).length ≤ k + 1 :=
  leb128Aux_length_le_of_lt_two_pow k n n hn

theorem leb128Aux_length_le_fuel : ∀ (fuel v : Nat), (leb128Aux fuel v).length ≤ fuel + 1
  | 0, _ => by simp [leb128Aux]
  | fuel + 1, v => by
    simp only [leb128Aux]
    split
    · simp
    · simp only [List.length_cons]
      have ih := leb128Aux_length_le_fuel fuel (v / 128)
      omega

theorem leb128_length_le_succ (n : Nat) : (leb128 n).length ≤ n + 1 :=
  leb128Aux_length_le_fuel n n

theorem uint8_toNat_lt_256_of_lt {k : Nat} (hk : k < 256) :
    (UInt8.ofNat k).toNat = k := by
  rw [UInt8.toNat_ofNat']
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  rw [h8]
  exact Nat.mod_eq_of_lt hk

theorem leb128Aux_prefix_inj :
    ∀ {f₁ f₂ n₁ n₂ : Nat} {r₁ r₂ : List UInt8},
      n₁ ≤ f₁ → n₂ ≤ f₂ →
      leb128Aux f₁ n₁ ++ r₁ = leb128Aux f₂ n₂ ++ r₂ →
      n₁ = n₂ ∧ r₁ = r₂
  | 0, 0, n₁, n₂, r₁, r₂, hn₁, hn₂, h => by
    have z₁ : n₁ = 0 := by omega
    have z₂ : n₂ = 0 := by omega
    subst z₁ z₂
    simp only [leb128Aux, List.singleton_append, List.cons.injEq] at h
    exact ⟨rfl, h.2⟩
  | 0, f₂ + 1, n₁, n₂, r₁, r₂, hn₁, _, h => by
    have z₁ : n₁ = 0 := by omega
    subst z₁
    simp only [leb128Aux, List.singleton_append] at h
    if hlt : n₂ < 128 then
      simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat 0).toNat = (UInt8.ofNat n₂).toNat := congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by decide), uint8_toNat_lt_256_of_lt (by omega)] at hb
      exact ⟨hb, h.2⟩
    else
      simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat 0).toNat = (UInt8.ofNat (128 + n₂ % 128)).toNat :=
        congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by decide), uint8_toNat_lt_256_of_lt (by omega)] at hb
      omega
  | f₁ + 1, 0, n₁, n₂, r₁, r₂, _, hn₂, h => by
    have z₂ : n₂ = 0 := by omega
    subst z₂
    simp only [leb128Aux, List.singleton_append] at h
    if hlt : n₁ < 128 then
      simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat n₁).toNat = (UInt8.ofNat 0).toNat := congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by decide)] at hb
      exact ⟨hb, h.2⟩
    else
      simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat (128 + n₁ % 128)).toNat = (UInt8.ofNat 0).toNat :=
        congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by decide)] at hb
      omega
  | f₁ + 1, f₂ + 1, n₁, n₂, r₁, r₂, hn₁, hn₂, h => by
    simp only [leb128Aux] at h
    if h₁ : n₁ < 128 then
      if h₂ : n₂ < 128 then
        simp only [h₁, h₂, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
        have hb : (UInt8.ofNat n₁).toNat = (UInt8.ofNat n₂).toNat := congrArg UInt8.toNat h.1
        rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
        exact ⟨hb, h.2⟩
      else
        simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
        have hb : (UInt8.ofNat n₁).toNat = (UInt8.ofNat (128 + n₂ % 128)).toNat :=
          congrArg UInt8.toNat h.1
        rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
        omega
    else
      if h₂ : n₂ < 128 then
        simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
        have hb : (UInt8.ofNat (128 + n₁ % 128)).toNat = (UInt8.ofNat n₂).toNat :=
          congrArg UInt8.toNat h.1
        rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
        omega
      else
        simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
        have hb : (UInt8.ofNat (128 + n₁ % 128)).toNat = (UInt8.ofNat (128 + n₂ % 128)).toNat :=
          congrArg UInt8.toNat h.1
        rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
        have hq₁ : n₁ / 128 ≤ f₁ := by omega
        have hq₂ : n₂ / 128 ≤ f₂ := by omega
        obtain ⟨hdiv, hrest⟩ := leb128Aux_prefix_inj hq₁ hq₂ h.2
        exact ⟨by omega, hrest⟩

theorem leb128_prefix_inj {n₁ n₂ : Nat} {r₁ r₂ : List UInt8}
    (h : leb128 n₁ ++ r₁ = leb128 n₂ ++ r₂) : n₁ = n₂ ∧ r₁ = r₂ :=
  leb128Aux_prefix_inj (Nat.le_refl n₁) (Nat.le_refl n₂) h

/-- Length-prefixed byte field: `leb128(len(xs)) ‖ xs`. -/
@[expose] def encodeListField (xs : List UInt8) : List UInt8 :=
  leb128 xs.length ++ xs

theorem encodeListField_prefix_inj {a₁ a₂ r₁ r₂ : List UInt8}
    (h : encodeListField a₁ ++ r₁ = encodeListField a₂ ++ r₂) :
    a₁ = a₂ ∧ r₁ = r₂ := by
  simp only [encodeListField, List.append_assoc] at h
  obtain ⟨hlen, htail⟩ := leb128_prefix_inj h
  exact List.append_inj htail hlen

theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := by
  cases a with
  | mk da =>
    cases b with
    | mk db =>
      congr 1
      exact Array.toList_inj.mp h

/-- Canonical length-prefixed 3-field domain frame `len(a) ‖ a ‖ len(b) ‖ b ‖ len(c) ‖ c`. -/
@[expose] def encodeFrameList (a b c : List UInt8) : List UInt8 :=
  encodeListField a ++ encodeListField b ++ encodeListField c

/-- Canonical length-prefixed 3-field `ByteArray` frame. -/
@[expose] def encodeFrame (a b c : ByteArray) : ByteArray :=
  Native.bytesOfList (encodeFrameList a.data.toList b.data.toList c.data.toList)

theorem encodeFrameList_injective {a₁ b₁ c₁ a₂ b₂ c₂ : List UInt8}
    (h : encodeFrameList a₁ b₁ c₁ = encodeFrameList a₂ b₂ c₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  simp only [encodeFrameList, List.append_assoc] at h
  obtain ⟨ha, hbc⟩ := encodeListField_prefix_inj h
  obtain ⟨hb, hcRaw⟩ := encodeListField_prefix_inj hbc
  obtain ⟨hc, _⟩ :=
    encodeListField_prefix_inj (r₁ := []) (r₂ := []) (by simpa [List.append_nil] using hcRaw)
  exact ⟨ha, hb, hc⟩

/-- **Domain-Separation Framing Injectivity (`encodeFrame_injective`)**:
    Canonical length-prefixed framing has zero boundary collision ambiguity across
    all `ByteArray` triples `(a, b, c)`, regardless of payload byte lengths. -/
theorem encodeFrame_injective {a₁ b₁ c₁ a₂ b₂ c₂ : ByteArray}
    (h : encodeFrame a₁ b₁ c₁ = encodeFrame a₂ b₂ c₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  have hl : (encodeFrame a₁ b₁ c₁).data.toList = (encodeFrame a₂ b₂ c₂).data.toList :=
    congrArg (fun x => x.data.toList) h
  simp only [encodeFrame, Native.bytesOfList_toList] at hl
  obtain ⟨ha, hb, hc⟩ := encodeFrameList_injective hl
  exact ⟨byteArray_eq_of_toList_eq ha, byteArray_eq_of_toList_eq hb, byteArray_eq_of_toList_eq hc⟩

/-- Encode a `String` as LEB128-delimited Unicode scalar values (`Char.toNat`). -/
def encodeStringCodepoints (s : String) : ByteArray :=
  Native.bytesOfList (s.toList.flatMap fun c => leb128 c.toNat)

/-- Canonical Fenzi relation-binding prefix framing `(protocolId, canonicalRelBytes, publicIoBytes)`. -/
def canonicalPrefix (protocolId : String) (canonicalRelBytes publicIoBytes : ByteArray) : ByteArray :=
  encodeFrame (encodeStringCodepoints protocolId) canonicalRelBytes publicIoBytes

/-- **Fenzi Prefix Injectivity (`bindRelation_injective_prefix`)**:
    Equal `canonicalPrefix` frames imply identical encoded protocol identifiers,
    identical materialized relation descriptors, and identical public I/O payloads. -/
theorem bindRelation_injective_prefix
    {p₁ p₂ : String} {rel₁ rel₂ io₁ io₂ : ByteArray}
    (h : canonicalPrefix p₁ rel₁ io₁ = canonicalPrefix p₂ rel₂ io₂) :
    encodeStringCodepoints p₁ = encodeStringCodepoints p₂ ∧ rel₁ = rel₂ ∧ io₁ = io₂ :=
  encodeFrame_injective h

/-! ## 2. Canonical Goldilocks Field Lift & Bounded Hash Collision Carrier -/

/-- Canonical integer-to-Goldilocks field lift predicate (`n < goldilocksPrime`).
    Prevents the `0` vs `p = 2^64 - 2^32 + 1` modular wrap-around alias. -/
@[expose] def CanonicalLift (n : Nat) : Prop :=
  n < goldilocksPrime

/-- Executable canonical field-lift range check (`n < goldilocksPrime`). -/
def checkCanonicalLift (n : Nat) : Bool :=
  decide (n < goldilocksPrime)

theorem checkCanonicalLift_iff (n : Nat) :
    checkCanonicalLift n = true ↔ CanonicalLift n := by
  simp [checkCanonicalLift, CanonicalLift]

/-- Lift a verified `< goldilocksPrime` natural into `Goldilocks` without modular wrap-around. -/
@[expose] def liftCanonical (n : Nat) (h : CanonicalLift n) : Goldilocks :=
  ⟨n, h⟩

theorem liftCanonical_injective {a b : Nat} (ha : CanonicalLift a) (hb : CanonicalLift b)
    (h : liftCanonical a ha = liftCanonical b hb) : a = b :=
  congrArg Goldilocks.val h

/-- Partial canonical field lift: returns `none` whenever `n ≥ goldilocksPrime`
    (refusing `n = goldilocksPrime`, which `Goldilocks.ofNat` would silently map to `0`). -/
@[expose] def canonicalLift? (n : Nat) : Option Goldilocks :=
  if h : n < goldilocksPrime then some ⟨n, h⟩ else none

theorem canonicalLift?_eq_some_iff (n : Nat) (x : Goldilocks) :
    canonicalLift? n = some x ↔ ∃ h : CanonicalLift n, x = liftCanonical n h := by
  unfold canonicalLift?
  if h : n < goldilocksPrime then
    simp only [h, ↓reduceDIte, Option.some.injEq]
    exact ⟨fun hx => ⟨h, hx.symm⟩, fun ⟨_, hx⟩ => hx.symm⟩
  else
    simp only [h, ↓reduceDIte, reduceCtorEq, false_iff]
    rintro ⟨hc, _⟩
    exact h hc

theorem canonicalLift?_injective {a b : Nat} {x : Goldilocks}
    (ha : canonicalLift? a = some x) (hb : canonicalLift? b = some x) : a = b := by
  obtain ⟨hca, rfl⟩ := (canonicalLift?_eq_some_iff a x).1 ha
  obtain ⟨hcb, heq⟩ := (canonicalLift?_eq_some_iff b _).1 hb
  exact liftCanonical_injective hca hcb heq

theorem canonicalLift?_refuses_ge_prime {n : Nat} (h : goldilocksPrime ≤ n) :
    canonicalLift? n = none := by
  unfold canonicalLift?
  have hNotLt : ¬ n < goldilocksPrime := by omega
  simp [hNotLt]

example : canonicalLift? goldilocksPrime = none := rfl

/-- **Domain-Bounded Hash Collision Predicate (`BoundedCollision`)**:
    Asserts the existence of a `HashCollisionWitness H maxBytes` (`msgA.length ≤ maxBytes`,
    `msgB.length ≤ maxBytes`, `msgA ≠ msgB`, `ofBE (H msgA) = ofBE (H msgB)`).
    Unlike unbounded `Collision H` (which is trivially `True` by pigeonhole on any fixed-width hash),
    `¬ BoundedCollision H maxBytes` is genuinely satisfiable on bounded preimage domains. -/
@[expose] def BoundedCollision (H : Hash) (maxBytes : Nat) : Prop :=
  Nonempty (HashCollisionWitness H maxBytes)

theorem boundedCollision_iff_collisionAmong (H : Hash) (maxBytes : Nat) :
    BoundedCollision H maxBytes ↔ CollisionAmong H (fun m => m.length ≤ maxBytes) := by
  constructor
  · rintro ⟨w⟩
    exact w.toCollisionAmong
  · rintro ⟨a, b, ha, hb, hne, heq⟩
    exact ⟨⟨a, b, ha, hb, hne, heq⟩⟩

theorem boundedCollision_mono {H : Hash} {b₁ b₂ : Nat} (hle : b₁ ≤ b₂)
    (hc : BoundedCollision H b₁) : BoundedCollision H b₂ := by
  rcases hc with ⟨w⟩
  exact ⟨⟨w.msgA, w.msgB, Nat.le_trans w.lenA hle, Nat.le_trans w.lenB hle, w.distinct, w.sameDigest⟩⟩

theorem boundedCollision_imp_collision {H : Hash} {maxBytes : Nat}
    (hc : BoundedCollision H maxBytes) : Collision H := by
  rcases hc with ⟨w⟩
  exact w.toCollision

/-! ## 3. Canonical Encodings for Field Elements, Evaluation Points & Signed Lattice Syndromes -/

/-- Encode a canonical `Goldilocks` element as 8 big-endian bytes (`val < p < 2^64 = 256^8`). -/
def encodeGoldilocksBytes (x : Goldilocks) : ByteArray :=
  Native.bytesOfList (be 8 x.val)

theorem encodeGoldilocksBytes_injective {x y : Goldilocks}
    (h : encodeGoldilocksBytes x = encodeGoldilocksBytes y) : x = y := by
  have hl : (encodeGoldilocksBytes x).data.toList = (encodeGoldilocksBytes y).data.toList :=
    congrArg (fun b => b.data.toList) h
  simp only [encodeGoldilocksBytes, Native.bytesOfList_toList] at hl
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hx : x.val < 256 ^ 8 := h8 ▸ Goldilocks.val_lt_two_pow_64 x
  have hy : y.val < 256 ^ 8 := h8 ▸ Goldilocks.val_lt_two_pow_64 y
  exact Goldilocks.ext (be_injective hx hy hl)

/-- Encode a `GoldilocksExt2` element as 16 big-endian bytes (`be 8 c0 ‖ be 8 c1`). -/
def encodeGoldilocksExt2Bytes (z : GoldilocksExt2) : ByteArray :=
  Native.bytesOfList (be 8 z.c0.val ++ be 8 z.c1.val)

theorem encodeGoldilocksExt2Bytes_injective {z₁ z₂ : GoldilocksExt2}
    (h : encodeGoldilocksExt2Bytes z₁ = encodeGoldilocksExt2Bytes z₂) : z₁ = z₂ := by
  have hl : (encodeGoldilocksExt2Bytes z₁).data.toList = (encodeGoldilocksExt2Bytes z₂).data.toList :=
    congrArg (fun b => b.data.toList) h
  simp only [encodeGoldilocksExt2Bytes, Native.bytesOfList_toList] at hl
  obtain ⟨hc0, hc1⟩ := List.append_inj hl (by simp)
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  exact GoldilocksExt2.ext
    (Goldilocks.ext (be_injective (h8 ▸ Goldilocks.val_lt_two_pow_64 z₁.c0)
                                  (h8 ▸ Goldilocks.val_lt_two_pow_64 z₂.c0) hc0))
    (Goldilocks.ext (be_injective (h8 ▸ Goldilocks.val_lt_two_pow_64 z₁.c1)
                                  (h8 ▸ Goldilocks.val_lt_two_pow_64 z₂.c1) hc1))

/-- Canonical length-prefixed encoding of an evaluation point `pt : List Goldilocks`. -/
def encodeGoldilocksList (xs : List Goldilocks) : List UInt8 :=
  leb128 xs.length ++ xs.flatMap (fun x => be 8 x.val)

/-- Canonical `ByteArray` encoding of an evaluation point `pt : List Goldilocks`. -/
def encodePointBytes (pt : List Goldilocks) : ByteArray :=
  Native.bytesOfList (encodeGoldilocksList pt)

private theorem flatMap_be8_inj :
    ∀ {xs ys : List Goldilocks},
      xs.length = ys.length →
      xs.flatMap (fun x => be 8 x.val) = ys.flatMap (fun x => be 8 x.val) →
      xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [List.flatMap_cons] at h
    obtain ⟨hhead, htail⟩ := List.append_inj h (by simp)
    have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
    have hxy : x = y := Goldilocks.ext
      (be_injective (h8 ▸ Goldilocks.val_lt_two_pow_64 x)
                    (h8 ▸ Goldilocks.val_lt_two_pow_64 y) hhead)
    rw [hxy, flatMap_be8_inj hlen htail]

theorem encodePointBytes_injective {p₁ p₂ : List Goldilocks}
    (h : encodePointBytes p₁ = encodePointBytes p₂) : p₁ = p₂ := by
  have hl : (encodePointBytes p₁).data.toList = (encodePointBytes p₂).data.toList :=
    congrArg (fun b => b.data.toList) h
  simp only [encodePointBytes, encodeGoldilocksList, Native.bytesOfList_toList] at hl
  obtain ⟨hlen, hbody⟩ := leb128_prefix_inj hl
  exact flatMap_be8_inj hlen hbody

/-- Sign-preserving self-delimiting encoding of `z : Int` (`0x00 ‖ leb128 n` vs `0x01 ‖ leb128 n`). -/
def encodeSignedInt : Int → List UInt8
  | Int.ofNat n => (0x00 : UInt8) :: leb128 n
  | Int.negSucc n => (0x01 : UInt8) :: leb128 n

theorem encodeSignedInt_prefix_inj {z₁ z₂ : Int} {r₁ r₂ : List UInt8}
    (h : encodeSignedInt z₁ ++ r₁ = encodeSignedInt z₂ ++ r₂) :
    z₁ = z₂ ∧ r₁ = r₂ := by
  cases z₁ with
  | ofNat n₁ =>
    cases z₂ with
    | ofNat n₂ =>
      simp only [encodeSignedInt, List.cons_append, List.cons.injEq] at h
      obtain ⟨hn, hr⟩ := leb128_prefix_inj h.2
      exact ⟨congrArg Int.ofNat hn, hr⟩
    | negSucc n₂ =>
      simp [encodeSignedInt] at h
  | negSucc n₁ =>
    cases z₂ with
    | ofNat n₂ =>
      simp [encodeSignedInt] at h
    | negSucc n₂ =>
      simp only [encodeSignedInt, List.cons_append, List.cons.injEq] at h
      obtain ⟨hn, hr⟩ := leb128_prefix_inj h.2
      exact ⟨congrArg Int.negSucc hn, hr⟩

/-- Canonical length-prefixed encoding of a signed integer vector `zs : List Int`. -/
def encodeSignedIntList (zs : List Int) : List UInt8 :=
  leb128 zs.length ++ zs.flatMap encodeSignedInt

/-- Canonical sign-injective `ByteArray` encoding of `zs : List Int` (e.g. Ajtai syndromes). -/
def encodeSignedIntBytes (zs : List Int) : ByteArray :=
  Native.bytesOfList (encodeSignedIntList zs)

private theorem flatMap_encodeSignedInt_inj :
    ∀ {xs ys : List Int},
      xs.length = ys.length →
      xs.flatMap encodeSignedInt = ys.flatMap encodeSignedInt →
      xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [List.flatMap_cons] at h
    obtain ⟨hxy, htail⟩ := encodeSignedInt_prefix_inj h
    rw [hxy, flatMap_encodeSignedInt_inj hlen htail]

theorem encodeSignedIntBytes_injective {xs ys : List Int}
    (h : encodeSignedIntBytes xs = encodeSignedIntBytes ys) : xs = ys := by
  have hl : (encodeSignedIntBytes xs).data.toList = (encodeSignedIntBytes ys).data.toList :=
    congrArg (fun b => b.data.toList) h
  simp only [encodeSignedIntBytes, encodeSignedIntList, Native.bytesOfList_toList] at hl
  obtain ⟨hlen, hbody⟩ := leb128_prefix_inj hl
  exact flatMap_encodeSignedInt_inj hlen hbody

/-- Canonical byte serialization class for statement/commitment instances bound into `Transcript`. -/
class TranscriptEncode (ι : Type) where
  encodeTranscriptBytes : ι → ByteArray

/-- Lawful injective byte serialization for statement/commitment instances. -/
class LawfulTranscriptEncode (ι : Type) extends TranscriptEncode ι where
  encodeTranscriptBytes_injective :
    ∀ {a b : ι}, encodeTranscriptBytes a = encodeTranscriptBytes b → a = b

instance : LawfulTranscriptEncode ByteArray where
  encodeTranscriptBytes b := b
  encodeTranscriptBytes_injective h := h

instance : LawfulTranscriptEncode Nat where
  encodeTranscriptBytes n := Native.bytesOfList (leb128 n)
  encodeTranscriptBytes_injective {a b} h := by
    have hl : (Native.bytesOfList (leb128 a)).data.toList =
              (Native.bytesOfList (leb128 b)).data.toList :=
      congrArg (fun x => x.data.toList) h
    simp only [Native.bytesOfList_toList] at hl
    exact (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa [List.append_nil] using hl)).1

instance : LawfulTranscriptEncode Goldilocks where
  encodeTranscriptBytes := encodeGoldilocksBytes
  encodeTranscriptBytes_injective := encodeGoldilocksBytes_injective

instance : LawfulTranscriptEncode GoldilocksExt2 where
  encodeTranscriptBytes := encodeGoldilocksExt2Bytes
  encodeTranscriptBytes_injective := encodeGoldilocksExt2Bytes_injective

instance : LawfulTranscriptEncode (List Goldilocks) where
  encodeTranscriptBytes := encodePointBytes
  encodeTranscriptBytes_injective := encodePointBytes_injective

instance : LawfulTranscriptEncode (List Int) where
  encodeTranscriptBytes := encodeSignedIntBytes
  encodeTranscriptBytes_injective := encodeSignedIntBytes_injective

instance {α β : Type} [TranscriptEncode α] [TranscriptEncode β] : TranscriptEncode (α × β) where
  encodeTranscriptBytes p :=
    encodeFrame
      (TranscriptEncode.encodeTranscriptBytes p.1)
      (TranscriptEncode.encodeTranscriptBytes p.2)
      ByteArray.empty

instance {α β : Type} [LawfulTranscriptEncode α] [LawfulTranscriptEncode β] :
    LawfulTranscriptEncode (α × β) where
  encodeTranscriptBytes_injective {p₁ p₂} h := by
    obtain ⟨h1, h2, _⟩ := encodeFrame_injective h
    exact Prod.ext
      (LawfulTranscriptEncode.encodeTranscriptBytes_injective h1)
      (LawfulTranscriptEncode.encodeTranscriptBytes_injective h2)

/-! ## 4. CSHAKE256 32-Byte Sponge Primitives & Domain Customizations -/

/-- `"OBEND.CRYPTO.FS.SEED/v1"` in ASCII. -/
def fsSeedCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x53, 0x45, 0x45, 0x44, 0x2f, 0x76, 0x31]

/-- `"OBEND.CRYPTO.FS.BIND/v1"` in ASCII. -/
def fsBindCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x42, 0x49, 0x4e, 0x44, 0x2f, 0x76, 0x31]

/-- `"OBEND.CRYPTO.FS.INSTANCE/v1"` in ASCII. -/
def fsInstanceCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x49, 0x4e, 0x53, 0x54, 0x41, 0x4e, 0x43, 0x45,
   0x2f, 0x76, 0x31]

/-- `"OBEND.CRYPTO.FS.ABSORB/v1"` in ASCII. -/
def fsAbsorbCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x41, 0x42, 0x53, 0x4f, 0x52, 0x42, 0x2f, 0x76, 0x31]

/-- `"OBEND.CRYPTO.FS.SQUEEZE/v1"` in ASCII. -/
def fsSqueezeCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x53, 0x51, 0x55, 0x45, 0x45, 0x5a, 0x45, 0x2f, 0x76, 0x31]

/-- `"OBEND.CRYPTO.FS.RATCHET/v1"` in ASCII. -/
def fsRatchetCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x52, 0x41, 0x54, 0x43, 0x48, 0x45, 0x54, 0x2f, 0x76, 0x31]

/-- Squeeze an exact 32-byte `ByteArray` from `cshake256Bytes customization input`. -/
@[expose] def cshake32ByteArray (customization input : List UInt8) : ByteArray :=
  Native.bytesOfList (cshake256Bytes customization input)

theorem cshake32ByteArray_size (customization input : List UInt8) :
    (cshake32ByteArray customization input).size = 32 := by
  unfold cshake32ByteArray
  rw [Fast.size_eq_length, Native.bytesOfList_toList, cshake256Bytes_length]

/-- Preimage list hashed during `bindRelation`. -/
def bindPreimageList (seed : ByteArray) (protocolId : String)
    (canonicalRelBytes publicIoBytes : ByteArray) : List UInt8 :=
  encodeListField seed.data.toList ++
    (canonicalPrefix protocolId canonicalRelBytes publicIoBytes).data.toList

theorem bindPreimageList_injective
    {s₁ s₂ : ByteArray} {p₁ p₂ : String} {r₁ r₂ io₁ io₂ : ByteArray}
    (h : bindPreimageList s₁ p₁ r₁ io₁ = bindPreimageList s₂ p₂ r₂ io₂) :
    s₁ = s₂ ∧ encodeStringCodepoints p₁ = encodeStringCodepoints p₂ ∧ r₁ = r₂ ∧ io₁ = io₂ := by
  unfold bindPreimageList at h
  obtain ⟨hs, hpref⟩ := encodeListField_prefix_inj h
  have hprefBA : canonicalPrefix p₁ r₁ io₁ = canonicalPrefix p₂ r₂ io₂ :=
    byteArray_eq_of_toList_eq hpref
  obtain ⟨hp, hr, hio⟩ := bindRelation_injective_prefix hprefBA
  exact ⟨byteArray_eq_of_toList_eq hs, hp, hr, hio⟩

/-- Preimage list hashed during `bindInstance`. -/
def instancePreimageList (relState : ByteArray) (stepCount : Nat) (instBytes : ByteArray) :
    List UInt8 :=
  encodeFrameList relState.data.toList (leb128 stepCount) instBytes.data.toList

theorem instancePreimageList_injective
    {s₁ s₂ : ByteArray} {c₁ c₂ : Nat} {i₁ i₂ : ByteArray}
    (h : instancePreimageList s₁ c₁ i₁ = instancePreimageList s₂ c₂ i₂) :
    s₁ = s₂ ∧ c₁ = c₂ ∧ i₁ = i₂ := by
  unfold instancePreimageList at h
  obtain ⟨hs, hcRaw, hi⟩ := encodeFrameList_injective h
  obtain ⟨hc, _⟩ := leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa [List.append_nil] using hcRaw)
  exact ⟨byteArray_eq_of_toList_eq hs, hc, byteArray_eq_of_toList_eq hi⟩

/-- Type-level state machine preventing Fiat–Shamir challenge generation prior to
    materialized relation binding (`Fenzi ePrint 2026/1838`) and statement/commitment
    instance binding (`.instanceBound`). -/
inductive TranscriptPhase where
  | unseeded
  | relationBound
  | instanceBound
  deriving DecidableEq, Repr

/-- Typeclass witnessing that a `TranscriptPhase` has completed BOTH Fenzi relation binding
    AND public-instance/initial-commitment binding (`phase = .instanceBound`).
    Both `.unseeded` and `.relationBound` intentionally have NO instance, rejecting premature
    Fiat–Shamir challenge squeezes before `bindInstance` at compile time. -/
class CanSqueezeTranscript (phase : TranscriptPhase) : Type where
  is_instanceBound : phase = .instanceBound

instance : CanSqueezeTranscript .instanceBound where
  is_instanceBound := rfl

/-- Squeeze capability is held by **exactly** the `.instanceBound` phase: every earlier phase
    (`.unseeded`, `.relationBound`) is refused, closing the premature Fiat–Shamir squeeze
    (pre-instance-binding grinding) channel. -/
theorem canSqueeze_nonempty_iff (phase : TranscriptPhase) :
    Nonempty (CanSqueezeTranscript phase) ↔ phase = .instanceBound := by
  constructor
  · rintro ⟨⟨h⟩⟩; exact h
  · intro h; exact ⟨⟨h⟩⟩

/-- Any phase other than `.instanceBound` refuses challenge squeezes. -/
theorem not_canSqueeze_of_ne {phase : TranscriptPhase} (hp : phase ≠ .instanceBound) :
    ¬ Nonempty (CanSqueezeTranscript phase) :=
  fun h => hp ((canSqueeze_nonempty_iff phase).1 h)

/-! ## 5. Phase-Indexed Fenzi-Safe `Transcript` & `BoundTranscript` (Constructor-Sealed Boundary) -/

/-- Phase-indexed 256-bit Fiat–Shamir sponge transcript.
    `private mk ::` seals the constructor inside `Obend.Crypto.Transcript`; external callers
    can ONLY transition `.unseeded → .relationBound` via `bindRelation` and
    `.relationBound → .instanceBound` via `bindInstance`. -/
structure Transcript (phase : TranscriptPhase) where
  private mk ::
  state : ByteArray
  state_len : state.size = 32
  stepCount : Nat

instance {phase : TranscriptPhase} : DecidableEq (Transcript phase) := fun a b =>
  if h : a.state = b.state ∧ a.stepCount = b.stepCount then
    isTrue (by
      cases a; cases b
      simp only at h
      rcases h with ⟨hs, hc⟩
      subst hs hc
      rfl)
  else
    isFalse (fun heq => by
      subst heq
      exact h ⟨rfl, rfl⟩)

/-- Constructor-sealed witness indexing a `Transcript .instanceBound` by the exact statement/commitment
    instance `inst : ι` absorbed via `bindInstance` (`private mk ::` prevents swapping `inst`). -/
structure BoundTranscript {ι : Type} (inst : ι) where
  private mk ::
  transcript : Transcript .instanceBound
  deriving DecidableEq

/-- Recover the bound instance `inst` from `BoundTranscript inst`. -/
@[expose] def BoundTranscript.inst {ι : Type} {i : ι} (_ : BoundTranscript i) : ι := i

/-- Initialize a fresh `.unseeded` transcript from an optional context nonce/seed. -/
def Transcript.newUnseeded (contextSeed : ByteArray := ByteArray.empty) : Transcript .unseeded :=
  Transcript.mk
    (cshake32ByteArray fsSeedCustomization contextSeed.data.toList)
    (cshake32ByteArray_size _ _)
    0

/-- **The Sole Entry Constructor Producing `.relationBound` (`bindRelation`)**:
    Hashes the unseeded state together with the canonical length-prefixed framing of
    `(protocolId, canonicalRelBytes, publicIoBytes)` via full 256-bit cSHAKE256 before
    any Fiat–Shamir challenge can be squeezed (`Fenzi 2026/1838` Theorem 5.5 defense). -/
def bindRelation (protocolId : String) (canonicalRelBytes : ByteArray) (publicIoBytes : ByteArray)
    (tr : Transcript .unseeded) : Transcript .relationBound :=
  let pre := bindPreimageList tr.state protocolId canonicalRelBytes publicIoBytes
  Transcript.mk
    (cshake32ByteArray fsBindCustomization pre)
    (cshake32ByteArray_size _ _)
    1

theorem bindRelation_state_eq (protocolId : String)
    (canonicalRelBytes publicIoBytes : ByteArray) (tr : Transcript .unseeded) :
    (bindRelation protocolId canonicalRelBytes publicIoBytes tr).state =
      cshake32ByteArray fsBindCustomization
        (bindPreimageList tr.state protocolId canonicalRelBytes publicIoBytes) := by
  unfold bindRelation
  rfl

/-- **Constructive Statement-Binding Extractor (`extractBindRelationCollision`, `0 Classical`)**:
    Two `bindRelation` calls yielding identical 32-byte sponge states either bound the exact same
    `(seed, protocolId, canonicalRelBytes, publicIoBytes)` tuple, or constructively yield a
    `HashCollisionWitness` on `cshake256Bytes fsBindCustomization`. -/
def extractBindRelationOrEq
    (tr₁ tr₂ : Transcript .unseeded)
    (p₁ p₂ : String) (rel₁ rel₂ io₁ io₂ : ByteArray)
    (hState : (bindRelation p₁ rel₁ io₁ tr₁).state = (bindRelation p₂ rel₂ io₂ tr₂).state) :
    PSum
      (tr₁.state = tr₂.state ∧
       encodeStringCodepoints p₁ = encodeStringCodepoints p₂ ∧
       rel₁ = rel₂ ∧ io₁ = io₂)
      (HashCollisionWitness (cshake256Bytes fsBindCustomization)
        (Nat.max (bindPreimageList tr₁.state p₁ rel₁ io₁).length
                 (bindPreimageList tr₂.state p₂ rel₂ io₂).length)) :=
  let pre₁ := bindPreimageList tr₁.state p₁ rel₁ io₁
  let pre₂ := bindPreimageList tr₂.state p₂ rel₂ io₂
  if hpre : pre₁ = pre₂ then
    .inl (bindPreimageList_injective hpre)
  else
    .inr
      { msgA := pre₁
        msgB := pre₂
        lenA := Nat.le_max_left _ _
        lenB := Nat.le_max_right _ _
        distinct := hpre
        sameDigest := by
          rw [bindRelation_state_eq, bindRelation_state_eq] at hState
          have hlist : (cshake32ByteArray fsBindCustomization pre₁).data.toList =
                       (cshake32ByteArray fsBindCustomization pre₂).data.toList :=
            congrArg (fun b => b.data.toList) hState
          simp only [cshake32ByteArray, Native.bytesOfList_toList] at hlist
          exact congrArg ofBE hlist }

/-- **Cryptographic Statement Binding (`bindRelation_binds_or_collides`)**:
    Two `bindRelation` invocations yielding identical 32-byte sponge states either bound
    the exact same `(seed, protocolId, canonicalRelBytes, publicIoBytes)` tuple, or witness
    a bounded 256-bit collision in cSHAKE256 under `fsBindCustomization`. -/
theorem bindRelation_binds_or_collides
    {tr₁ tr₂ : Transcript .unseeded}
    {p₁ p₂ : String} {rel₁ rel₂ io₁ io₂ : ByteArray}
    (hState : (bindRelation p₁ rel₁ io₁ tr₁).state = (bindRelation p₂ rel₂ io₂ tr₂).state) :
    (tr₁.state = tr₂.state ∧
     encodeStringCodepoints p₁ = encodeStringCodepoints p₂ ∧
     rel₁ = rel₂ ∧ io₁ = io₂) ∨
    BoundedCollision (cshake256Bytes fsBindCustomization)
      (Nat.max (bindPreimageList tr₁.state p₁ rel₁ io₁).length
               (bindPreimageList tr₂.state p₂ rel₂ io₂).length) := by
  cases extractBindRelationOrEq tr₁ tr₂ p₁ p₂ rel₁ rel₂ io₁ io₂ hState with
  | inl heq => exact .inl heq
  | inr w => exact .inr ⟨w⟩

/-- **The Sole Entry Constructor Producing `BoundTranscript inst` & `.instanceBound` (`bindInstance`)**:
    Absorbs the statement/commitment instance `inst` (such as `(comm, numVars, claimedSum)`) into
    a `.relationBound` transcript under `fsInstanceCustomization` before round challenges are squeezed. -/
def bindInstance {ι : Type} [TranscriptEncode ι] (inst : ι)
    (tr : Transcript .relationBound) : BoundTranscript inst :=
  let pre := instancePreimageList tr.state tr.stepCount (TranscriptEncode.encodeTranscriptBytes inst)
  BoundTranscript.mk
    (Transcript.mk
      (cshake32ByteArray fsInstanceCustomization pre)
      (cshake32ByteArray_size _ _)
      (tr.stepCount + 1))

theorem bindInstance_inst {ι : Type} [TranscriptEncode ι] (inst : ι)
    (tr : Transcript .relationBound) :
    (bindInstance inst tr).inst = inst := rfl

theorem bindInstance_state_eq {ι : Type} [TranscriptEncode ι] (inst : ι)
    (tr : Transcript .relationBound) :
    (bindInstance inst tr).transcript.state =
      cshake32ByteArray fsInstanceCustomization
        (instancePreimageList tr.state tr.stepCount (TranscriptEncode.encodeTranscriptBytes inst)) := by
  unfold bindInstance; rfl

/-- **Constructive Instance-Binding Extractor (`extractBindInstanceOrEq`, `0 Classical`)**:
    Two `bindInstance` invocations producing the same 32-byte `.instanceBound` state either bound
    the exact same `(tr, inst)` pair or constructively exhibit a bounded `HashCollisionWitness`. -/
def extractBindInstanceOrEq {ι : Type} [LawfulTranscriptEncode ι]
    (inst₁ inst₂ : ι) (tr₁ tr₂ : Transcript .relationBound)
    (hState : (bindInstance inst₁ tr₁).transcript.state =
              (bindInstance inst₂ tr₂).transcript.state) :
    PSum
      (tr₁ = tr₂ ∧ inst₁ = inst₂)
      (HashCollisionWitness (cshake256Bytes fsInstanceCustomization)
        (Nat.max
          (instancePreimageList tr₁.state tr₁.stepCount
            (TranscriptEncode.encodeTranscriptBytes inst₁)).length
          (instancePreimageList tr₂.state tr₂.stepCount
            (TranscriptEncode.encodeTranscriptBytes inst₂)).length)) :=
  let pre₁ := instancePreimageList tr₁.state tr₁.stepCount
    (TranscriptEncode.encodeTranscriptBytes inst₁)
  let pre₂ := instancePreimageList tr₂.state tr₂.stepCount
    (TranscriptEncode.encodeTranscriptBytes inst₂)
  if hpre : pre₁ = pre₂ then
    .inl (by
      obtain ⟨hs, hc, hi⟩ := instancePreimageList_injective hpre
      have htr : tr₁ = tr₂ := by
        cases tr₁; cases tr₂
        simp only at hs hc
        subst hs hc
        rfl
      exact ⟨htr, LawfulTranscriptEncode.encodeTranscriptBytes_injective hi⟩)
  else
    .inr
      { msgA := pre₁
        msgB := pre₂
        lenA := Nat.le_max_left _ _
        lenB := Nat.le_max_right _ _
        distinct := hpre
        sameDigest := by
          rw [bindInstance_state_eq, bindInstance_state_eq] at hState
          have hlist : (cshake32ByteArray fsInstanceCustomization pre₁).data.toList =
                       (cshake32ByteArray fsInstanceCustomization pre₂).data.toList :=
            congrArg (fun b => b.data.toList) hState
          simp only [cshake32ByteArray, Native.bytesOfList_toList] at hlist
          exact congrArg ofBE hlist }

theorem bindInstance_binds_or_collides {ι : Type} [LawfulTranscriptEncode ι]
    {inst₁ inst₂ : ι} {tr₁ tr₂ : Transcript .relationBound}
    (hState : (bindInstance inst₁ tr₁).transcript.state =
              (bindInstance inst₂ tr₂).transcript.state) :
    (tr₁ = tr₂ ∧ inst₁ = inst₂) ∨
    BoundedCollision (cshake256Bytes fsInstanceCustomization)
      (Nat.max
        (instancePreimageList tr₁.state tr₁.stepCount
          (TranscriptEncode.encodeTranscriptBytes inst₁)).length
        (instancePreimageList tr₂.state tr₂.stepCount
          (TranscriptEncode.encodeTranscriptBytes inst₂)).length) := by
  cases extractBindInstanceOrEq inst₁ inst₂ tr₁ tr₂ hState with
  | inl heq => exact .inl heq
  | inr w => exact .inr ⟨w⟩

/-- Absorb a labeled prover message into a seeded (`.relationBound` or `.instanceBound`) transcript.
    Unseeded transcripts are rejected by the Lean typechecker. -/
def absorbMsg {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (label : ByteArray) (msgBytes : ByteArray)
    (tr : Transcript phase) : Transcript phase :=
  let frame := encodeFrameList tr.state.data.toList label.data.toList
    (leb128 tr.stepCount ++ msgBytes.data.toList)
  Transcript.mk
    (cshake32ByteArray fsAbsorbCustomization frame)
    (cshake32ByteArray_size _ _)
    (tr.stepCount + 1)

theorem absorbMsg_state_eq {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (label msgBytes : ByteArray) (tr : Transcript phase) :
    (absorbMsg label msgBytes tr).state =
      cshake32ByteArray fsAbsorbCustomization
        (encodeFrameList tr.state.data.toList label.data.toList
          (leb128 tr.stepCount ++ msgBytes.data.toList)) := by
  unfold absorbMsg; rfl

/-- Constructive collision-or-equality extractor for `absorbMsg` (`0 Classical`). -/
def extractAbsorbMsgOrEq {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (l₁ m₁ l₂ m₂ : ByteArray) (tr₁ tr₂ : Transcript phase)
    (hState : (absorbMsg l₁ m₁ tr₁).state = (absorbMsg l₂ m₂ tr₂).state) :
    PSum
      (tr₁ = tr₂ ∧ l₁ = l₂ ∧ m₁ = m₂)
      (HashCollisionWitness (cshake256Bytes fsAbsorbCustomization)
        (Nat.max
          (encodeFrameList tr₁.state.data.toList l₁.data.toList
            (leb128 tr₁.stepCount ++ m₁.data.toList)).length
          (encodeFrameList tr₂.state.data.toList l₂.data.toList
            (leb128 tr₂.stepCount ++ m₂.data.toList)).length)) :=
  let f₁ := encodeFrameList tr₁.state.data.toList l₁.data.toList
    (leb128 tr₁.stepCount ++ m₁.data.toList)
  let f₂ := encodeFrameList tr₂.state.data.toList l₂.data.toList
    (leb128 tr₂.stepCount ++ m₂.data.toList)
  if hf : f₁ = f₂ then
    .inl (by
      obtain ⟨hs, hl, hcm⟩ := encodeFrameList_injective hf
      obtain ⟨hc, hm⟩ := leb128_prefix_inj hcm
      have hsBA := byteArray_eq_of_toList_eq hs
      have htr : tr₁ = tr₂ := by
        cases tr₁; cases tr₂
        simp only at hsBA hc
        subst hsBA hc
        rfl
      exact ⟨htr, byteArray_eq_of_toList_eq hl, byteArray_eq_of_toList_eq hm⟩)
  else
    .inr
      { msgA := f₁
        msgB := f₂
        lenA := Nat.le_max_left _ _
        lenB := Nat.le_max_right _ _
        distinct := hf
        sameDigest := by
          rw [absorbMsg_state_eq, absorbMsg_state_eq] at hState
          have hlist : (cshake32ByteArray fsAbsorbCustomization f₁).data.toList =
                       (cshake32ByteArray fsAbsorbCustomization f₂).data.toList :=
            congrArg (fun b => b.data.toList) hState
          simp only [cshake32ByteArray, Native.bytesOfList_toList] at hlist
          exact congrArg ofBE hlist }

/-- Squeeze a full 32-byte (256-bit) challenge and ratchet a seeded sponge state.
    Defeats 1-felt ($2^{15.5}$-bit) truncation bugs by preserving all 256 bits of entropy. -/
def squeezeChallenge256 {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (tr : Transcript phase) :
    { out : ByteArray // out.size = 32 } × Transcript phase :=
  let payload := encodeListField tr.state.data.toList ++ leb128 tr.stepCount
  let outBytes := cshake32ByteArray fsSqueezeCustomization payload
  let hOut : outBytes.size = 32 := cshake32ByteArray_size _ _
  let nextState := cshake32ByteArray fsRatchetCustomization
    (encodeListField tr.state.data.toList ++ encodeListField outBytes.data.toList)
  (⟨outBytes, hOut⟩, Transcript.mk nextState (cshake32ByteArray_size _ _) (tr.stepCount + 1))

/-- Squeeze a single 64-bit canonical `Goldilocks` challenge reduced from 128 bits (16 bytes)
    of cSHAKE256 output (bias $< 2^{-64}$). -/
def squeezeGoldilocks {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (tr : Transcript phase) :
    Goldilocks × Transcript phase :=
  let (⟨bytes, _⟩, tr') := squeezeChallenge256 tr
  let limb128 := ofBE (bytes.data.toList.take 16)
  (Goldilocks.ofNat limb128, tr')

/-- Squeeze a 128-bit challenge pair in `GoldilocksExt2` ($\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2-7)$)
    using all 32 bytes (two independent 128-bit halves reduced modulo $p$). -/
def squeezeGoldilocksExt2 {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (tr : Transcript phase) :
    GoldilocksExt2 × Transcript phase :=
  let (⟨bytes, _⟩, tr') := squeezeChallenge256 tr
  let list32 := bytes.data.toList
  let lo128 := ofBE (list32.take 16)
  let hi128 := ofBE (list32.drop 16)
  (⟨Goldilocks.ofNat lo128, Goldilocks.ofNat hi128⟩, tr')

end Obend.Crypto
end
