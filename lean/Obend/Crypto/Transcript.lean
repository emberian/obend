module
/-
# Obend.Crypto.Transcript — Fenzi-Safe, Full-256-Bit Domain-Separated Fiat–Shamir Transcript

Eliminates two critical 2026 soundness vulnerabilities at the Lean type level:
1. **Fenzi Attack on Program-Generated Circuits (`ePrint 2026/1838`)**:
   Delayed statement binding on dynamically generated R1CS/CCS/DPR relations allows concrete
   hash diagonalization. Here `Transcript` is indexed by `TranscriptPhase`:
   - `Transcript.newUnseeded : ByteArray → Transcript .unseeded`
   - `bindRelation : String → ByteArray → ByteArray → Transcript .unseeded → Transcript .relationBound`
     is the **sole entry constructor** producing `.relationBound` (`Transcript.mk` is `private`).
   - `absorbMsg`, `squeezeChallenge256`, `squeezeGoldilocks`, and `squeezeGoldilocksExt2`
     accept **only** `Transcript .relationBound`: squeezing a Fiat–Shamir challenge before
     binding the materialized relation descriptor is a **compile-time Lean type error**.
2. **1-Felt ($2^{15.5}$-Bit) Digest-Weld Truncation**:
   Every `Transcript` carries a full 32-byte (`256`-bit) cSHAKE256 sponge state
   (`state : ByteArray`, `state_len : state.size = 32`), backed by `Obend.Digest.Cshake256`.
3. **Collision-Free Canonical Framing (`encodeFrame_injective`, `bindRelation_injective_prefix`)**:
   Unconditional self-delimiting LEB128 length-prefixed framing guarantees zero boundary ambiguity
   across arbitrary-length `(protocolId, canonicalRelBytes, publicIoBytes)` triples.
-/
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes
public import Obend.Crypto.Multilinear

@[expose] public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Self-Delimiting LEB128 Length-Prefixed Framing & Unconditional Injectivity -/

/-- Fuel-bounded LEB128 variable-length natural encoding:
    continuation bytes have high bit set (`≥ 128`), final byte has `< 128`. -/
def leb128Aux : Nat → Nat → List UInt8
  | 0, v => [UInt8.ofNat (v % 128)]
  | fuel + 1, v =>
    if v < 128 then [UInt8.ofNat v]
    else UInt8.ofNat (128 + v % 128) :: leb128Aux fuel (v / 128)

/-- Canonical self-delimiting LEB128 encoding of `n : Nat`. -/
def leb128 (n : Nat) : List UInt8 := leb128Aux n n

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
    by_cases hlt : n₂ < 128
    · simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat 0).toNat = (UInt8.ofNat n₂).toNat := congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by decide), uint8_toNat_lt_256_of_lt (by omega)] at hb
      exact ⟨hb, h.2⟩
    · simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat 0).toNat = (UInt8.ofNat (128 + n₂ % 128)).toNat :=
        congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by decide), uint8_toNat_lt_256_of_lt (by omega)] at hb
      omega
  | f₁ + 1, 0, n₁, n₂, r₁, r₂, _, hn₂, h => by
    have z₂ : n₂ = 0 := by omega
    subst z₂
    simp only [leb128Aux, List.singleton_append] at h
    by_cases hlt : n₁ < 128
    · simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat n₁).toNat = (UInt8.ofNat 0).toNat := congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by decide)] at hb
      exact ⟨hb, h.2⟩
    · simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat (128 + n₁ % 128)).toNat = (UInt8.ofNat 0).toNat :=
        congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by decide)] at hb
      omega
  | f₁ + 1, f₂ + 1, n₁, n₂, r₁, r₂, hn₁, hn₂, h => by
    simp only [leb128Aux] at h
    by_cases h₁ : n₁ < 128 <;> by_cases h₂ : n₂ < 128
    · simp only [h₁, h₂, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat n₁).toNat = (UInt8.ofNat n₂).toNat := congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
      exact ⟨hb, h.2⟩
    · simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat n₁).toNat = (UInt8.ofNat (128 + n₂ % 128)).toNat :=
        congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
      omega
    · simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb : (UInt8.ofNat (128 + n₁ % 128)).toNat = (UInt8.ofNat n₂).toNat :=
        congrArg UInt8.toNat h.1
      rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
      omega
    · simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
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
def encodeListField (xs : List UInt8) : List UInt8 :=
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
def encodeFrameList (a b c : List UInt8) : List UInt8 :=
  encodeListField a ++ encodeListField b ++ encodeListField c

/-- Canonical length-prefixed 3-field `ByteArray` frame. -/
def encodeFrame (a b c : ByteArray) : ByteArray :=
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

/-! ## 2. CSHAKE256 32-Byte Sponge Primitives & Domain Customizations -/

/-- `"OBEND.CRYPTO.FS.SEED/v1"` in ASCII. -/
def fsSeedCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x53, 0x45, 0x45, 0x44, 0x2f, 0x76, 0x31]

/-- `"OBEND.CRYPTO.FS.BIND/v1"` in ASCII. -/
def fsBindCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x46, 0x53, 0x2e, 0x42, 0x49, 0x4e, 0x44, 0x2f, 0x76, 0x31]

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
def cshake32ByteArray (customization input : List UInt8) : ByteArray :=
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

/-- Type-level state machine preventing Fiat–Shamir challenge generation prior to
    materialized relation & public-I/O binding (`Fenzi ePrint 2026/1838`). -/
inductive TranscriptPhase where
  | unseeded
  | relationBound
  deriving DecidableEq, Repr

end Obend.Crypto
end

/-! ## 3. Phase-Indexed Fenzi-Safe `Transcript` (Constructor-Sealed Module Boundary) -/

public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-- Phase-indexed 256-bit Fiat–Shamir sponge transcript.
    `private mk ::` seals the constructor inside `Obend.Crypto.Transcript`; external callers
    can ONLY transition `.unseeded → .relationBound` through `bindRelation`. -/
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

/-- **Cryptographic Statement Binding (`bindRelation_binds_or_collides`)**:
    Two `bindRelation` invocations yielding identical 32-byte sponge states either bound
    the exact same `(seed, protocolId, canonicalRelBytes, publicIoBytes)` tuple, or witness
    an explicit 256-bit collision in cSHAKE256 under `fsBindCustomization`. -/
theorem bindRelation_binds_or_collides
    {tr₁ tr₂ : Transcript .unseeded}
    {p₁ p₂ : String} {rel₁ rel₂ io₁ io₂ : ByteArray}
    (hState : (bindRelation p₁ rel₁ io₁ tr₁).state = (bindRelation p₂ rel₂ io₂ tr₂).state) :
    (tr₁.state = tr₂.state ∧
     encodeStringCodepoints p₁ = encodeStringCodepoints p₂ ∧
     rel₁ = rel₂ ∧ io₁ = io₂) ∨
    Collision (cshake256Bytes fsBindCustomization) := by
  let pre₁ := bindPreimageList tr₁.state p₁ rel₁ io₁
  let pre₂ := bindPreimageList tr₂.state p₂ rel₂ io₂
  by_cases hpre : pre₁ = pre₂
  · exact .inl (bindPreimageList_injective hpre)
  · right
    rw [bindRelation_state_eq, bindRelation_state_eq] at hState
    have hlist : (cshake32ByteArray fsBindCustomization pre₁).data.toList =
                 (cshake32ByteArray fsBindCustomization pre₂).data.toList :=
      congrArg (fun b => b.data.toList) hState
    simp only [cshake32ByteArray, Native.bytesOfList_toList] at hlist
    exact ⟨pre₁, pre₂, hpre, congrArg ofBE hlist⟩

/-- Absorb a labeled prover message into a `.relationBound` transcript.
    Unseeded transcripts are rejected by the Lean typechecker. -/
def absorbMsg (label : ByteArray) (msgBytes : ByteArray)
    (tr : Transcript .relationBound) : Transcript .relationBound :=
  let frame := encodeFrameList tr.state.data.toList label.data.toList
    (leb128 tr.stepCount ++ msgBytes.data.toList)
  Transcript.mk
    (cshake32ByteArray fsAbsorbCustomization frame)
    (cshake32ByteArray_size _ _)
    (tr.stepCount + 1)

/-- Squeeze a full 32-byte (256-bit) challenge and ratchet the `.relationBound` sponge state.
    Defeats 1-felt ($2^{15.5}$-bit) truncation bugs by preserving all 256 bits of entropy. -/
def squeezeChallenge256 (tr : Transcript .relationBound) :
    { out : ByteArray // out.size = 32 } × Transcript .relationBound :=
  let payload := encodeListField tr.state.data.toList ++ leb128 tr.stepCount
  let outBytes := cshake32ByteArray fsSqueezeCustomization payload
  let hOut : outBytes.size = 32 := cshake32ByteArray_size _ _
  let nextState := cshake32ByteArray fsRatchetCustomization
    (encodeListField tr.state.data.toList ++ encodeListField outBytes.data.toList)
  (⟨outBytes, hOut⟩, Transcript.mk nextState (cshake32ByteArray_size _ _) (tr.stepCount + 1))

/-- Squeeze a single 64-bit canonical `Goldilocks` challenge reduced from 128 bits (16 bytes)
    of cSHAKE256 output (bias $< 2^{-64}$). -/
def squeezeGoldilocks (tr : Transcript .relationBound) :
    Goldilocks × Transcript .relationBound :=
  let (⟨bytes, _⟩, tr') := squeezeChallenge256 tr
  let limb128 := ofBE (bytes.data.toList.take 16)
  (Goldilocks.ofNat limb128, tr')

/-- Squeeze a 128-bit challenge pair in `GoldilocksExt2` ($\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2-7)$)
    using all 32 bytes (two independent 128-bit halves reduced modulo $p$). -/
def squeezeGoldilocksExt2 (tr : Transcript .relationBound) :
    GoldilocksExt2 × Transcript .relationBound :=
  let (⟨bytes, _⟩, tr') := squeezeChallenge256 tr
  let list32 := bytes.data.toList
  let lo128 := ofBE (list32.take 16)
  let hi128 := ofBE (list32.drop 16)
  (⟨Goldilocks.ofNat lo128, Goldilocks.ofNat hi128⟩, tr')

end Obend.Crypto
end
