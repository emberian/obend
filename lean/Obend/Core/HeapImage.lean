module
/-
# Obend.Core.HeapImage — Orthogonal `Core4` Heap & Yielded-Continuation Persistence

Canonical two-tier (`Spec` `List UInt8` + `Exec` `ByteArray` push/cursor via `@[csimp]`) binary
image persistence and 256-bit `cSHAKE256` content addressing for `Obend.Core.Machine.State`:
1. Bijective wire codec (`decodeHeapImage_encodeHeapImage`, `encodeHeapImage_injective`) over all
   `Primitive` (18), `Term` (25), `RuntimeValue` (8), `Cell` (3), `Frame` (13), `Refusal` (9),
   `Control` (7), and `State` constructors with `0 sorry`, `0 axiom`, and `0 Classical.choice`.
2. 256-bit `cSHAKE256` CIDs (`heapImageCid_binds_or_collides`, `heapImageCid_binds_or_extract_collision`).
3. Multi-yield persisted continuation equivalence (`rehydrate_resume_steps_eq`).
-/
public import Obend.Core.Machine
public import Obend.Core.Digest
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes

public section
namespace Obend.Core.HeapImage

open Obend.Core.Term
open Obend.Core.Machine
open Obend.Digest.HashBytes
open Obend.Core.Digest (Digest256 DigestWords4 ExactCollisionPair)

set_option autoImplicit false

/-! ## 1. Magic Header & Canonical Unbounded Base-128 Varints -/

/-- 8-byte ASCII magic header `"OBHIMG01"` identifying canonical Core4 heap images. -/
def heapImageMagic : List UInt8 :=
  [0x4f, 0x42, 0x48, 0x49, 0x4d, 0x47, 0x30, 0x31]

def heapImageMagicBytes : ByteArray := ⟨heapImageMagic.toArray⟩

theorem heapImageMagicBytes_toList : heapImageMagicBytes.data.toList = heapImageMagic := by
  simp [heapImageMagicBytes, heapImageMagic]

/-- Read 256-bit big-endian hash output from a 32-byte `Hash` (exposed for downstream modules). -/
@[expose] def hashBytesToDigest256 (H : Hash) (msg : List UInt8) : Digest256 :=
  BitVec.ofNat 256 (ofBE (H msg))

/-- Canonical unbounded varint encoder: 7 payload bits per byte; continuation bytes require a
    strictly positive quotient `n / 128 > 0`, ruling out non-minimal trailing zero bytes. -/
def encVarNat (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (128 + n % 128) :: encVarNat (n / 128)
termination_by n
decreasing_by omega

private theorem encVarNat_step (n : Nat) :
    encVarNat n = if n < 128 then [UInt8.ofNat n]
      else UInt8.ofNat (128 + n % 128) :: encVarNat (n / 128) := by
  rw [encVarNat]

theorem encVarNat_pos (n : Nat) : 0 < (encVarNat n).length := by
  rw [encVarNat_step]; split <;> simp

/-- Reasoning-tier canonical varint decoder with explicit fuel. -/
def decVarNat : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else
      match decVarNat fuel rest with
      | some (hi, rest') =>
        if 0 < hi then some (hi * 128 + (b.toNat - 128), rest') else none
      | none => none

theorem decVarNat_encVarNat (n : Nat) :
    ∀ (fuel : Nat) (rest : List UInt8),
      (encVarNat n).length ≤ fuel →
      decVarNat fuel (encVarNat n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro fuel rest hlen
    rw [encVarNat_step] at hlen ⊢
    by_cases hlt : n < 128
    · rw [ite_eq_left hlt] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
        have hb : (UInt8.ofNat n).toNat = n := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        dsimp only [List.cons_append, List.nil_append, decVarNat]
        rw [hb, ite_eq_left hlt]
    · rw [ite_eq_right hlt] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
        simp only [List.length_cons] at hlen
        have hb : (UInt8.ofNat (128 + n % 128)).toNat = 128 + n % 128 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hnot : ¬ (128 + n % 128 < 128) := by omega
        have hdiv_lt : n / 128 < n := by omega
        have hdiv_pos : 0 < n / 128 := by omega
        have hrec := ih (n / 128) hdiv_lt f rest (by omega)
        have hval : n / 128 * 128 + (128 + n % 128 - 128) = n := by omega
        dsimp only [List.cons_append, decVarNat]
        rw [hb, ite_eq_right hnot, hrec]
        dsimp only
        rw [ite_eq_left hdiv_pos, hval]

theorem decVarNat_sound :
    ∀ (fuel : Nat) (bs : List UInt8) (n : Nat) (rest : List UInt8),
      decVarNat fuel bs = some (n, rest) → bs = encVarNat n ++ rest
  | 0, _, _, _, h => by simp [decVarNat] at h
  | _ + 1, [], _, _, h => by simp [decVarNat] at h
  | fuel + 1, b :: tail, n, rest, h => by
    have hb256 : b.toNat < 256 := b.toNat_lt
    dsimp only [decVarNat] at h
    by_cases hlt : b.toNat < 128
    · rw [ite_eq_left hlt] at h
      cases h
      have henc : encVarNat b.toNat = [b] := by
        rw [encVarNat_step, ite_eq_left hlt, UInt8.ofNat_toNat]
      rw [henc]; rfl
    · rw [ite_eq_right hlt] at h
      cases hrec : decVarNat fuel tail with
      | none => simp [hrec] at h
      | some p =>
        obtain ⟨hi, r'⟩ := p
        rw [hrec] at h
        dsimp only at h
        by_cases hpos : 0 < hi
        · rw [ite_eq_left hpos] at h
          obtain ⟨hn, hr'⟩ := Prod.mk.inj (Option.some.inj h)
          have ih := decVarNat_sound fuel tail hi r' hrec
          have hge : ¬ (n < 128) := by omega
          have hmod : 128 + n % 128 = b.toNat := by omega
          have hdiv : n / 128 = hi := by omega
          have henc : encVarNat n = b :: encVarNat hi := by
            rw [encVarNat_step n, ite_eq_right hge, hmod, UInt8.ofNat_toNat, hdiv]
          rw [← hr', ih, henc]; rfl
        · rw [ite_eq_right hpos] at h; cases h

/-! ## 2. Choice-Free RFC 3629 UTF-8 Scalar Framing (`0 Classical.choice`) -/

def mkValidChar? (v : Nat) : Option Char :=
  if (Char.ofNat v).toNat = v then some (Char.ofNat v) else none

theorem mkValidChar?_toNat (c : Char) : mkValidChar? c.toNat = some c := by
  unfold mkValidChar?; simp [Char.ofNat_toNat]

theorem mkValidChar?_sound {v : Nat} {c : Char} (h : mkValidChar? v = some c) :
    c.toNat = v := by
  unfold mkValidChar? at h
  by_cases heq : (Char.ofNat v).toNat = v
  · rw [ite_eq_left heq] at h; cases h; exact heq
  · rw [ite_eq_right heq] at h; cases h

def checkUtf8Min (lo v : Nat) (rest : List UInt8) : Option (Char × List UInt8) :=
  if lo ≤ v then (mkValidChar? v).map (·, rest) else none

private theorem checkUtf8Min_encode (lo : Nat) (c : Char) (rest : List UInt8)
    (hlo : lo ≤ c.toNat) :
    checkUtf8Min lo c.toNat rest = some (c, rest) := by
  unfold checkUtf8Min
  rw [ite_eq_left hlo, mkValidChar?_toNat c]
  rfl

private theorem checkUtf8Min_sound {lo v : Nat} {rest : List UInt8} {c : Char} {r' : List UInt8}
    (h : checkUtf8Min lo v rest = some (c, r')) :
    lo ≤ v ∧ c.toNat = v ∧ r' = rest := by
  unfold checkUtf8Min at h
  by_cases hlo : lo ≤ v
  · rw [ite_eq_left hlo] at h
    obtain ⟨ch, hch, heq⟩ := Option.map_eq_some_iff.1 h
    cases heq
    exact ⟨hlo, mkValidChar?_sound hch, rfl⟩
  · rw [ite_eq_right hlo] at h; cases h

/-- Decode one minimal-width UTF-8 codepoint matching `String.utf8EncodeChar`. -/
def utf8DecodeOne : List UInt8 → Option (Char × List UInt8)
  | [] => none
  | b0 :: rest =>
    if b0.toNat ≤ 127 then
      checkUtf8Min 0 b0.toNat rest
    else if 192 ≤ b0.toNat ∧ b0.toNat < 224 then
      match rest with
      | b1 :: rest1 =>
        if 128 ≤ b1.toNat ∧ b1.toNat < 192 then
          checkUtf8Min 128 ((b0.toNat - 192) * 64 + (b1.toNat - 128)) rest1
        else none
      | [] => none
    else if 224 ≤ b0.toNat ∧ b0.toNat < 240 then
      match rest with
      | b1 :: b2 :: rest2 =>
        if 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧ 128 ≤ b2.toNat ∧ b2.toNat < 192 then
          checkUtf8Min 2048
            ((b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128)) rest2
        else none
      | _ => none
    else if 240 ≤ b0.toNat ∧ b0.toNat < 248 then
      match rest with
      | b1 :: b2 :: b3 :: rest3 =>
        if 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧ 128 ≤ b2.toNat ∧ b2.toNat < 192 ∧
            128 ≤ b3.toNat ∧ b3.toNat < 192 then
          checkUtf8Min 65536
            ((b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 +
              (b2.toNat - 128) * 64 + (b3.toNat - 128)) rest3
        else none
      | _ => none
    else none

private theorem char_val_lt (c : Char) : c.toNat < 0x110000 := by
  rcases c.valid with h | ⟨_, h⟩
  · exact Nat.lt_trans h (by decide)
  · exact h

theorem utf8DecodeOne_encodeChar (c : Char) (rest : List UInt8) :
    utf8DecodeOne (String.utf8EncodeChar c ++ rest) = some (c, rest) := by
  have hmax := char_val_lt c
  dsimp [String.utf8EncodeChar]
  by_cases h1 : c.toNat ≤ 127
  · rw [ite_eq_left h1]
    have hb0 : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    dsimp only [List.cons_append, List.nil_append, utf8DecodeOne]
    rw [hb0, ite_eq_left h1]
    exact checkUtf8Min_encode 0 c rest (Nat.zero_le _)
  · rw [ite_eq_right h1]
    by_cases h2 : c.toNat ≤ 2047
    · rw [ite_eq_left h2]
      have hb0 : (UInt8.ofNat (c.toNat / 64 % 32 + 192)).toNat = c.toNat / 64 % 32 + 192 := by
        rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have hb1 : (UInt8.ofNat (c.toNat % 64 + 128)).toNat = c.toNat % 64 + 128 := by
        rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have hv : (c.toNat / 64 % 32 + 192 - 192) * 64 + (c.toNat % 64 + 128 - 128) = c.toNat := by
        omega
      dsimp only [List.cons_append, List.nil_append, utf8DecodeOne]
      rw [hb0, hb1, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
        ite_eq_left ⟨by omega, by omega⟩, hv]
      exact checkUtf8Min_encode 128 c rest (by omega)
    · rw [ite_eq_right h2]
      by_cases h3 : c.toNat ≤ 65535
      · rw [ite_eq_left h3]
        have hb0 : (UInt8.ofNat (c.toNat / 4096 % 16 + 224)).toNat = c.toNat / 4096 % 16 + 224 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hb1 : (UInt8.ofNat (c.toNat / 64 % 64 + 128)).toNat = c.toNat / 64 % 64 + 128 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hb2 : (UInt8.ofNat (c.toNat % 64 + 128)).toNat = c.toNat % 64 + 128 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hv : (c.toNat / 4096 % 16 + 224 - 224) * 4096 +
            (c.toNat / 64 % 64 + 128 - 128) * 64 + (c.toNat % 64 + 128 - 128) = c.toNat := by
          omega
        dsimp only [List.cons_append, List.nil_append, utf8DecodeOne]
        rw [hb0, hb1, hb2, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega, by omega, by omega⟩, hv]
        exact checkUtf8Min_encode 2048 c rest (by omega)
      · rw [ite_eq_right h3]
        have hb0 : (UInt8.ofNat (c.toNat / 262144 % 8 + 240)).toNat = c.toNat / 262144 % 8 + 240 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hb1 : (UInt8.ofNat (c.toNat / 4096 % 64 + 128)).toNat = c.toNat / 4096 % 64 + 128 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hb2 : (UInt8.ofNat (c.toNat / 64 % 64 + 128)).toNat = c.toNat / 64 % 64 + 128 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hb3 : (UInt8.ofNat (c.toNat % 64 + 128)).toNat = c.toNat % 64 + 128 := by
          rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hv : (c.toNat / 262144 % 8 + 240 - 240) * 262144 +
            (c.toNat / 4096 % 64 + 128 - 128) * 4096 +
            (c.toNat / 64 % 64 + 128 - 128) * 64 + (c.toNat % 64 + 128 - 128) = c.toNat := by
          omega
        dsimp only [List.cons_append, List.nil_append, utf8DecodeOne]
        rw [hb0, hb1, hb2, hb3, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
          ite_eq_left ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, hv]
        exact checkUtf8Min_encode 65536 c rest (by omega)

private theorem utf8EncodeChar_eq_val (c : Char) (v : Nat) (hv : c.toNat = v) :
    String.utf8EncodeChar c =
      if v ≤ 127 then [UInt8.ofNat v]
      else if v ≤ 2047 then [UInt8.ofNat (v / 64 % 32 + 192), UInt8.ofNat (v % 64 + 128)]
      else if v ≤ 65535 then
        [UInt8.ofNat (v / 4096 % 16 + 224), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)]
      else
        [UInt8.ofNat (v / 262144 % 8 + 240), UInt8.ofNat (v / 4096 % 64 + 128),
          UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] := by
  cases c with
  | mk val valid =>
    change val.toNat = v at hv
    subst hv
    rfl

theorem utf8DecodeOne_sound {bs : List UInt8} {c : Char} {rest : List UInt8}
    (h : utf8DecodeOne bs = some (c, rest)) :
    bs = String.utf8EncodeChar c ++ rest ∧ rest.length < bs.length := by
  have hmax := char_val_lt c
  cases bs with
  | nil => simp [utf8DecodeOne] at h
  | cons b0 tail =>
    dsimp only [utf8DecodeOne] at h
    by_cases c1 : b0.toNat ≤ 127
    · rw [ite_eq_left c1] at h
      obtain ⟨_, hv, rfl⟩ := checkUtf8Min_sound h
      refine ⟨?_, by simp⟩
      rw [utf8EncodeChar_eq_val c _ hv, ite_eq_left c1, UInt8.ofNat_toNat]; rfl
    · rw [ite_eq_right c1] at h
      by_cases c2 : 192 ≤ b0.toNat ∧ b0.toNat < 224
      · rw [ite_eq_left c2] at h
        cases tail with
        | nil => simp at h
        | cons b1 rest1 =>
          dsimp only at h
          by_cases cb1 : 128 ≤ b1.toNat ∧ b1.toNat < 192
          · rw [ite_eq_left cb1] at h
            obtain ⟨hlo, hv, rfl⟩ := checkUtf8Min_sound h
            refine ⟨?_, by simp; omega⟩
            rw [utf8EncodeChar_eq_val c _ hv, ite_eq_right (by omega), ite_eq_left (by omega)]
            have e0 : UInt8.ofNat (((b0.toNat - 192) * 64 + (b1.toNat - 128)) / 64 % 32 + 192) = b0 := by
              apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
            have e1 : UInt8.ofNat (((b0.toNat - 192) * 64 + (b1.toNat - 128)) % 64 + 128) = b1 := by
              apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
            rw [e0, e1]; rfl
          · rw [ite_eq_right cb1] at h; cases h
      · rw [ite_eq_right c2] at h
        by_cases c3 : 224 ≤ b0.toNat ∧ b0.toNat < 240
        · rw [ite_eq_left c3] at h
          cases tail with
          | nil => simp at h
          | cons b1 tail1 =>
            cases tail1 with
            | nil => simp at h
            | cons b2 rest2 =>
              dsimp only at h
              by_cases cb12 : 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧ 128 ≤ b2.toNat ∧ b2.toNat < 192
              · rw [ite_eq_left cb12] at h
                obtain ⟨hlo, hv, rfl⟩ := checkUtf8Min_sound h
                refine ⟨?_, by simp; omega⟩
                rw [utf8EncodeChar_eq_val c _ hv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
                have e0 : UInt8.ofNat (((b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128)) / 4096 % 16 + 224) = b0 := by
                  apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
                have e1 : UInt8.ofNat (((b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128)) / 64 % 64 + 128) = b1 := by
                  apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
                have e2 : UInt8.ofNat (((b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128)) % 64 + 128) = b2 := by
                  apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
                rw [e0, e1, e2]; rfl
              · rw [ite_eq_right cb12] at h; cases h
        · rw [ite_eq_right c3] at h
          by_cases c4 : 240 ≤ b0.toNat ∧ b0.toNat < 248
          · rw [ite_eq_left c4] at h
            cases tail with
            | nil => simp at h
            | cons b1 tail1 =>
              cases tail1 with
              | nil => simp at h
              | cons b2 tail2 =>
                cases tail2 with
                | nil => simp at h
                | cons b3 rest3 =>
                  dsimp only at h
                  by_cases cb123 : 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧ 128 ≤ b2.toNat ∧ b2.toNat < 192 ∧
                      128 ≤ b3.toNat ∧ b3.toNat < 192
                  · rw [ite_eq_left cb123] at h
                    obtain ⟨hlo, hv, rfl⟩ := checkUtf8Min_sound h
                    rw [hv] at hmax
                    refine ⟨?_, by simp; omega⟩
                    rw [utf8EncodeChar_eq_val c _ hv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
                    have e0 : UInt8.ofNat (((b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128)) / 262144 % 8 + 240) = b0 := by
                      apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
                    have e1 : UInt8.ofNat (((b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128)) / 4096 % 64 + 128) = b1 := by
                      apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
                    have e2 : UInt8.ofNat (((b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128)) / 64 % 64 + 128) = b2 := by
                      apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
                    have e3 : UInt8.ofNat (((b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128)) % 64 + 128) = b3 := by
                      apply UInt8.toNat_inj.1; rw [UInt8.toNat_ofNat']; omega
                    rw [e0, e1, e2, e3]; rfl
                  · rw [ite_eq_right cb123] at h; cases h
          · rw [ite_eq_right c4] at h; cases h

/-- Decode an entire UTF-8 byte list into `List Char` with explicit fuel. -/
def utf8DecodeAll : Nat → List UInt8 → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b :: rest =>
    match utf8DecodeOne (b :: rest) with
    | some (c, rest') => (utf8DecodeAll fuel rest').map (c :: ·)
    | none => none

private theorem utf8EncodeChar_pos (c : Char) : 0 < (String.utf8EncodeChar c).length := by
  dsimp [String.utf8EncodeChar]
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem utf8DecodeAll_encode :
    ∀ (cs : List Char) (fuel : Nat),
      (cs.flatMap String.utf8EncodeChar).length ≤ fuel →
      utf8DecodeAll fuel (cs.flatMap String.utf8EncodeChar) = some cs
  | [], fuel, _ => by cases fuel <;> rfl
  | c :: cs, 0, h => by
    have hpos := utf8EncodeChar_pos c
    simp only [List.flatMap_cons, List.length_append] at h
    omega
  | c :: cs, fuel + 1, h => by
    have hpos := utf8EncodeChar_pos c
    have htot : (String.utf8EncodeChar c).length + (cs.flatMap String.utf8EncodeChar).length ≤ fuel + 1 := by
      simpa only [List.flatMap_cons, List.length_append] using h
    have hrest : (cs.flatMap String.utf8EncodeChar).length ≤ fuel := by omega
    simp only [List.flatMap_cons]
    cases hce : String.utf8EncodeChar c ++ cs.flatMap String.utf8EncodeChar with
    | nil =>
      have hl := congrArg List.length hce
      simp only [List.length_append, List.length_nil] at hl
      omega
    | cons b tail =>
      unfold utf8DecodeAll
      rw [← hce, utf8DecodeOne_encodeChar c (cs.flatMap String.utf8EncodeChar)]
      simp [utf8DecodeAll_encode cs fuel hrest]

theorem utf8DecodeAll_sound :
    ∀ (fuel : Nat) (bs : List UInt8) (cs : List Char),
      utf8DecodeAll fuel bs = some cs → cs.flatMap String.utf8EncodeChar = bs
  | _, [], cs, h => by simp [utf8DecodeAll] at h; subst h; rfl
  | 0, _ :: _, _, h => by simp [utf8DecodeAll] at h
  | fuel + 1, b :: tail, cs, h => by
    unfold utf8DecodeAll at h
    cases hone : utf8DecodeOne (b :: tail) with
    | none => simp [hone] at h
    | some p =>
      obtain ⟨c, rest'⟩ := p
      simp only [hone] at h
      obtain ⟨cs', hall, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hbs, _⟩ := utf8DecodeOne_sound hone
      have ih := utf8DecodeAll_sound fuel rest' cs' hall
      simp [List.flatMap_cons, ih, ← hbs]

private theorem string_eq_of_toByteArray {s₁ s₂ : String}
    (h : s₁.toByteArray = s₂.toByteArray) : s₁ = s₂ := by
  cases s₁; cases s₂
  dsimp only at h
  subst h; rfl

private theorem ofList_toByteArray (cs : List Char) :
    (String.ofList cs).toByteArray = cs.utf8Encode := rfl

private theorem utf8Encode_toList (cs : List Char) :
    cs.utf8Encode.data.toList = cs.flatMap String.utf8EncodeChar := by
  simp [List.utf8Encode]

/-- Decode a UTF-8 `ByteArray` into `String` with zero `Classical.choice`. -/
def decodeUtf8Bytes (b : ByteArray) : Option String :=
  (utf8DecodeAll b.size b.data.toList).map String.ofList

theorem decodeUtf8Bytes_toByteArray (s : String) :
    decodeUtf8Bytes s.toByteArray = some s := by
  rcases s.isValidUTF8 with ⟨cs, hcs⟩
  unfold decodeUtf8Bytes
  have hlist : s.toByteArray.data.toList = cs.flatMap String.utf8EncodeChar := by
    rw [hcs, utf8Encode_toList]
  have hsz : (cs.flatMap String.utf8EncodeChar).length = s.toByteArray.size := by
    rw [← hlist, Array.length_toList]; rfl
  rw [hlist, ← hsz, utf8DecodeAll_encode cs _ (Nat.le_refl _)]
  simp only [Option.map_some, Option.some.injEq]
  apply string_eq_of_toByteArray
  rw [ofList_toByteArray, hcs]

theorem decodeUtf8Bytes_sound {b : ByteArray} {s : String}
    (h : decodeUtf8Bytes b = some s) : s.toByteArray = b := by
  unfold decodeUtf8Bytes at h
  obtain ⟨cs, hall, rfl⟩ := Option.map_eq_some_iff.1 h
  have hflat := utf8DecodeAll_sound b.size b.data.toList cs hall
  apply ByteArray.ext
  apply Array.toList_inj.1
  rw [ofList_toByteArray, utf8Encode_toList]
  exact hflat

/-- Length-framed string encoding: `varint(utf8ByteLen) ++ utf8Bytes`. -/
def encStrSpec (s : String) : List UInt8 :=
  encVarNat s.toByteArray.size ++ s.toByteArray.data.toList

def decStrSpec (fuel : Nat) (bs : List UInt8) : Option (String × List UInt8) :=
  match decVarNat fuel bs with
  | none => none
  | some (len, rest) =>
    if len ≤ rest.length then
      match decodeUtf8Bytes ⟨(rest.take len).toArray⟩ with
      | some s => some (s, rest.drop len)
      | none => none
    else none

theorem decStrSpec_encStrSpec (s : String) (fuel : Nat) (rest : List UInt8)
    (hf : (encStrSpec s).length ≤ fuel) :
    decStrSpec fuel (encStrSpec s ++ rest) = some (s, rest) := by
  unfold encStrSpec at hf ⊢
  simp only [List.length_append] at hf
  have hsz : s.toByteArray.data.toList.length = s.toByteArray.size := Array.length_toList
  unfold decStrSpec
  rw [List.append_assoc, decVarNat_encVarNat _ fuel _ (by omega)]
  dsimp only
  have hle : s.toByteArray.size ≤ (s.toByteArray.data.toList ++ rest).length := by simp [hsz]
  rw [ite_eq_left hle]
  have hba : (⟨((s.toByteArray.data.toList ++ rest).take s.toByteArray.size).toArray⟩ : ByteArray) =
      s.toByteArray := by
    apply ByteArray.ext; apply Array.toList_inj.1
    dsimp only
    exact List.take_left' hsz
  rw [hba, decodeUtf8Bytes_toByteArray s]
  dsimp only
  rw [List.drop_left' hsz]

theorem decStrSpec_sound {fuel : Nat} {bs : List UInt8} {s : String} {rest : List UInt8}
    (h : decStrSpec fuel bs = some (s, rest)) : bs = encStrSpec s ++ rest := by
  unfold decStrSpec at h
  cases hv : decVarNat fuel bs with
  | none => simp [hv] at h
  | some p =>
    obtain ⟨len, r0⟩ := p
    simp only [hv] at h
    split at h
    · next hle =>
      cases hu : decodeUtf8Bytes ⟨(r0.take len).toArray⟩ with
      | none => simp [hu] at h
      | some s' =>
        simp only [hu, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hbs := decVarNat_sound fuel bs len r0 hv
        have hba := decodeUtf8Bytes_sound hu
        have hdata : s'.toByteArray.data.toList = r0.take len := by rw [hba]
        have hlen : s'.toByteArray.size = len := by
          rw [hba]; simp [ByteArray.size, List.length_take, Nat.min_eq_left hle]
        rw [hbs, encStrSpec, hlen, hdata, List.append_assoc, List.take_append_drop]
    · cases h

/-! ## 3. Reasoning-Tier Encoder & Decoder for All `Core.Machine` Carriers -/

/-- Exhaustive tag mapping for all 18 `Core.Term.Primitive` constructors. -/
def primTag : Primitive → UInt8
  | .add => 0 | .multiply => 1 | .equal => 2 | .conjunction => 3 | .labelEqual => 4
  | .subtract => 5 | .divide => 6 | .less => 7 | .lessEqual => 8 | .modulo => 9
  | .bitAnd => 10 | .bitOr => 11 | .bitXor => 12 | .shl => 13 | .lshr => 14
  | .ashr => 15 | .slt => 16 | .qmul32 => 17

def primOfTag (b : UInt8) : Option Primitive :=
  match b.toNat with
  | 0 => some .add | 1 => some .multiply | 2 => some .equal | 3 => some .conjunction
  | 4 => some .labelEqual | 5 => some .subtract | 6 => some .divide | 7 => some .less
  | 8 => some .lessEqual | 9 => some .modulo | 10 => some .bitAnd | 11 => some .bitOr
  | 12 => some .bitXor | 13 => some .shl | 14 => some .lshr | 15 => some .ashr
  | 16 => some .slt | 17 => some .qmul32 | _ => none

theorem primOfTag_primTag (p : Primitive) : primOfTag (primTag p) = some p := by
  cases p <;> rfl

theorem primOfTag_sound {b : UInt8} {p : Primitive} (h : primOfTag b = some p) :
    primTag p = b := by
  have hb := b.toNat_lt
  unfold primOfTag at h
  split at h <;> cases h <;> (apply UInt8.toNat_inj.1; simp [primTag]; omega)

/-- Encode a list of strings with length prefix. -/
def encNamesSpec (names : List String) : List UInt8 :=
  encVarNat names.length ++ names.flatMap encStrSpec

def decNamesN (fuel : Nat) : Nat → List UInt8 → Option (List String × List UInt8)
  | 0, rest => some ([], rest)
  | c + 1, bs => do
    let (s, r1) ← decStrSpec fuel bs
    let (ss, r2) ← decNamesN fuel c r1
    pure (s :: ss, r2)

def decNamesSpec (fuel : Nat) (bs : List UInt8) : Option (List String × List UInt8) := do
  let (count, r0) ← decVarNat fuel bs
  decNamesN fuel count r0

/-- Encode a list of heap addresses (`Environment`) with length prefix. -/
def encAddrsSpec (addrs : List Address) : List UInt8 :=
  encVarNat addrs.length ++ addrs.flatMap encVarNat

def decAddrsN (fuel : Nat) : Nat → List UInt8 → Option (List Address × List UInt8)
  | 0, rest => some ([], rest)
  | c + 1, bs => do
    let (a, r1) ← decVarNat fuel bs
    let (as, r2) ← decAddrsN fuel c r1
    pure (a :: as, r2)

def decAddrsSpec (fuel : Nat) (bs : List UInt8) : Option (List Address × List UInt8) := do
  let (count, r0) ← decVarNat fuel bs
  decAddrsN fuel count r0

/-- Encode named heap field bindings `List (String × Address)`. -/
def encNamedAddrsSpec (fields : List (String × Address)) : List UInt8 :=
  encVarNat fields.length ++ fields.flatMap (fun p => encStrSpec p.1 ++ encVarNat p.2)

def decNamedAddrsN (fuel : Nat) : Nat → List UInt8 → Option (List (String × Address) × List UInt8)
  | 0, rest => some ([], rest)
  | c + 1, bs => do
    let (name, r1) ← decStrSpec fuel bs
    let (addr, r2) ← decVarNat fuel r1
    let (others, r3) ← decNamedAddrsN fuel c r2
    pure ((name, addr) :: others, r3)

def decNamedAddrsSpec (fuel : Nat) (bs : List UInt8) :
    Option (List (String × Address) × List UInt8) := do
  let (count, r0) ← decVarNat fuel bs
  decNamedAddrsN fuel count r0

def encBoolByte (b : Bool) : UInt8 := if b then 1 else 0

def decBoolByte (b : UInt8) : Option Bool :=
  if b = 0 then some false else if b = 1 then some true else none

theorem decBoolByte_encBoolByte (b : Bool) : decBoolByte (encBoolByte b) = some b := by
  cases b <;> rfl

theorem decBoolByte_sound {byte : UInt8} {b : Bool} (h : decBoolByte byte = some b) :
    encBoolByte b = byte := by
  unfold decBoolByte at h
  by_cases h0 : byte = 0
  · subst h0; simp at h; subst h; rfl
  · rw [ite_eq_right h0] at h
    by_cases h1 : byte = 1
    · subst h1; simp at h; subst h; rfl
    · rw [ite_eq_right h1] at h; cases h

mutual
/-- Structural encoder for all 25 `Obend.Core.Term.Term` constructors. -/
def encTermSpec : Term → List UInt8
  | .hole n σ => (0 : UInt8) :: (encVarNat n ++ encTermsSpec σ)
  | .bound idx => (1 : UInt8) :: encVarNat idx
  | .lam body => (2 : UInt8) :: encTermSpec body
  | .app fn arg => (3 : UInt8) :: (encTermSpec fn ++ encTermSpec arg)
  | .mix lo hi => (4 : UInt8) :: (encTermSpec lo ++ encTermSpec hi)
  | .fix spec inh => (5 : UInt8) :: (encTermSpec spec ++ encTermSpec inh)
  | .specification metaT extT => (6 : UInt8) :: (encTermSpec metaT ++ encTermSpec extT)
  | .prototype spec tgt => (7 : UInt8) :: (encTermSpec spec ++ encTermSpec tgt)
  | .reflect tgt => (8 : UInt8) :: encTermSpec tgt
  | .metadata spec => (9 : UInt8) :: encTermSpec spec
  | .project tgt => (10 : UInt8) :: encTermSpec tgt
  | .nat v => (11 : UInt8) :: encVarNat v
  | .boolean b => [12, encBoolByte b]
  | .label s => (13 : UInt8) :: encStrSpec s
  | .binary p l r => (14 : UInt8) :: primTag p :: (encTermSpec l ++ encTermSpec r)
  | .extend inh fs => (15 : UInt8) :: (encTermSpec inh ++ encFieldsSpec fs)
  | .record fs => (16 : UInt8) :: encFieldsSpec fs
  | .get tgt name => (17 : UInt8) :: (encStrSpec name ++ encTermSpec tgt)
  | .ifZero v z s => (18 : UInt8) :: (encTermSpec v ++ encTermSpec z ++ encTermSpec s)
  | .inject tag pay => (19 : UInt8) :: (encStrSpec tag ++ encTermSpec pay)
  | .case scrut arms => (20 : UInt8) :: (encTermSpec scrut ++ encFieldsSpec arms)
  | .ifBool c t f => (21 : UInt8) :: (encTermSpec c ++ encTermSpec t ++ encTermSpec f)
  | .perform plan => (22 : UInt8) :: encTermSpec plan
  | .done v => (23 : UInt8) :: encTermSpec v
  | .split tgt names fn => (24 : UInt8) :: (encNamesSpec names ++ encTermSpec tgt ++ encTermSpec fn)
termination_by structural t => t

def encFieldsSpec : List (String × Term) → List UInt8
  | [] => [0]
  | (name, body) :: rest => (1 : UInt8) :: (encStrSpec name ++ encTermSpec body ++ encFieldsSpec rest)
termination_by structural fs => fs

def encTermsSpec : List Term → List UInt8
  | [] => [0]
  | t :: rest => (1 : UInt8) :: (encTermSpec t ++ encTermsSpec rest)
termination_by structural ts => ts
end

mutual
def decTermSpec : Nat → List UInt8 → Option (Term × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, tag :: rest =>
    match tag.toNat with
    | 0 => do
      let (n, r1) ← decVarNat fuel rest
      let (σ, r2) ← decTermsSpec fuel r1
      pure (.hole n σ, r2)
    | 1 => do
      let (idx, r1) ← decVarNat fuel rest
      pure (.bound idx, r1)
    | 2 => do
      let (body, r1) ← decTermSpec fuel rest
      pure (.lam body, r1)
    | 3 => do
      let (fn, r1) ← decTermSpec fuel rest
      let (arg, r2) ← decTermSpec fuel r1
      pure (.app fn arg, r2)
    | 4 => do
      let (lo, r1) ← decTermSpec fuel rest
      let (hi, r2) ← decTermSpec fuel r1
      pure (.mix lo hi, r2)
    | 5 => do
      let (sp, r1) ← decTermSpec fuel rest
      let (inh, r2) ← decTermSpec fuel r1
      pure (.fix sp inh, r2)
    | 6 => do
      let (m, r1) ← decTermSpec fuel rest
      let (e, r2) ← decTermSpec fuel r1
      pure (.specification m e, r2)
    | 7 => do
      let (sp, r1) ← decTermSpec fuel rest
      let (tgt, r2) ← decTermSpec fuel r1
      pure (.prototype sp tgt, r2)
    | 8 => do
      let (tgt, r1) ← decTermSpec fuel rest
      pure (.reflect tgt, r1)
    | 9 => do
      let (sp, r1) ← decTermSpec fuel rest
      pure (.metadata sp, r1)
    | 10 => do
      let (tgt, r1) ← decTermSpec fuel rest
      pure (.project tgt, r1)
    | 11 => do
      let (v, r1) ← decVarNat fuel rest
      pure (.nat v, r1)
    | 12 =>
      match rest with
      | b :: r1 => do
        let bv ← decBoolByte b
        pure (.boolean bv, r1)
      | [] => none
    | 13 => do
      let (s, r1) ← decStrSpec fuel rest
      pure (.label s, r1)
    | 14 =>
      match rest with
      | pb :: r0 => do
        let p ← primOfTag pb
        let (l, r1) ← decTermSpec fuel r0
        let (r, r2) ← decTermSpec fuel r1
        pure (.binary p l r, r2)
      | [] => none
    | 15 => do
      let (inh, r1) ← decTermSpec fuel rest
      let (fs, r2) ← decFieldsSpec fuel r1
      pure (.extend inh fs, r2)
    | 16 => do
      let (fs, r1) ← decFieldsSpec fuel rest
      pure (.record fs, r1)
    | 17 => do
      let (name, r1) ← decStrSpec fuel rest
      let (tgt, r2) ← decTermSpec fuel r1
      pure (.get tgt name, r2)
    | 18 => do
      let (v, r1) ← decTermSpec fuel rest
      let (z, r2) ← decTermSpec fuel r1
      let (s, r3) ← decTermSpec fuel r2
      pure (.ifZero v z s, r3)
    | 19 => do
      let (lbl, r1) ← decStrSpec fuel rest
      let (pay, r2) ← decTermSpec fuel r1
      pure (.inject lbl pay, r2)
    | 20 => do
      let (scrut, r1) ← decTermSpec fuel rest
      let (arms, r2) ← decFieldsSpec fuel r1
      pure (.case scrut arms, r2)
    | 21 => do
      let (c, r1) ← decTermSpec fuel rest
      let (t, r2) ← decTermSpec fuel r1
      let (f, r3) ← decTermSpec fuel r2
      pure (.ifBool c t f, r3)
    | 22 => do
      let (plan, r1) ← decTermSpec fuel rest
      pure (.perform plan, r1)
    | 23 => do
      let (v, r1) ← decTermSpec fuel rest
      pure (.done v, r1)
    | 24 => do
      let (names, r1) ← decNamesSpec fuel rest
      let (tgt, r2) ← decTermSpec fuel r1
      let (fn, r3) ← decTermSpec fuel r2
      pure (.split tgt names fn, r3)
    | _ => none

def decFieldsSpec : Nat → List UInt8 → Option (List (String × Term) × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, tag :: rest =>
    match tag.toNat with
    | 0 => some ([], rest)
    | 1 => do
      let (name, r1) ← decStrSpec fuel rest
      let (body, r2) ← decTermSpec fuel r1
      let (others, r3) ← decFieldsSpec fuel r2
      pure ((name, body) :: others, r3)
    | _ => none

def decTermsSpec : Nat → List UInt8 → Option (List Term × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, tag :: rest =>
    match tag.toNat with
    | 0 => some ([], rest)
    | 1 => do
      let (t, r1) ← decTermSpec fuel rest
      let (others, r2) ← decTermsSpec fuel r1
      pure (t :: others, r2)
    | _ => none
end

def encClosureSpec (cl : Closure) : List UInt8 :=
  encTermSpec cl.term ++ encAddrsSpec cl.environment

def decClosureSpec (fuel : Nat) (bs : List UInt8) : Option (Closure × List UInt8) := do
  let (t, r1) ← decTermSpec fuel bs
  let (env, r2) ← decAddrsSpec fuel r1
  pure (⟨t, env⟩, r2)

/-- Encoder for all 8 `RuntimeValue` constructors. -/
def encValueSpec : RuntimeValue → List UInt8
  | .closure body env => (0 : UInt8) :: (encTermSpec body ++ encAddrsSpec env)
  | .natural v => (1 : UInt8) :: encVarNat v
  | .boolean b => [2, encBoolByte b]
  | .label s => (3 : UInt8) :: encStrSpec s
  | .record fs => (4 : UInt8) :: encNamedAddrsSpec fs
  | .specification m e => (5 : UInt8) :: (encVarNat m ++ encVarNat e)
  | .prototype sp tgt => (6 : UInt8) :: (encVarNat sp ++ encVarNat tgt)
  | .variant lbl pay => (7 : UInt8) :: (encStrSpec lbl ++ encVarNat pay)

def decValueSpec (fuel : Nat) : List UInt8 → Option (RuntimeValue × List UInt8)
  | [] => none
  | tag :: rest =>
    match tag.toNat with
    | 0 => do
      let (body, r1) ← decTermSpec fuel rest
      let (env, r2) ← decAddrsSpec fuel r1
      pure (.closure body env, r2)
    | 1 => do
      let (v, r1) ← decVarNat fuel rest
      pure (.natural v, r1)
    | 2 =>
      match rest with
      | b :: r1 => do
        let bv ← decBoolByte b
        pure (.boolean bv, r1)
      | [] => none
    | 3 => do
      let (s, r1) ← decStrSpec fuel rest
      pure (.label s, r1)
    | 4 => do
      let (fs, r1) ← decNamedAddrsSpec fuel rest
      pure (.record fs, r1)
    | 5 => do
      let (m, r1) ← decVarNat fuel rest
      let (e, r2) ← decVarNat fuel r1
      pure (.specification m e, r2)
    | 6 => do
      let (sp, r1) ← decVarNat fuel rest
      let (tgt, r2) ← decVarNat fuel r1
      pure (.prototype sp tgt, r2)
    | 7 => do
      let (lbl, r1) ← decStrSpec fuel rest
      let (pay, r2) ← decVarNat fuel r1
      pure (.variant lbl pay, r2)
    | _ => none

/-- Encoder for all 3 `Cell` constructors (`suspended | evaluating | cached`). -/
def encCellSpec : Cell → List UInt8
  | .suspended orig => (0 : UInt8) :: encClosureSpec orig
  | .evaluating orig => (1 : UInt8) :: encClosureSpec orig
  | .cached orig val => (2 : UInt8) :: (encClosureSpec orig ++ encValueSpec val)

def decCellSpec (fuel : Nat) : List UInt8 → Option (Cell × List UInt8)
  | [] => none
  | tag :: rest =>
    match tag.toNat with
    | 0 => do
      let (orig, r1) ← decClosureSpec fuel rest
      pure (.suspended orig, r1)
    | 1 => do
      let (orig, r1) ← decClosureSpec fuel rest
      pure (.evaluating orig, r1)
    | 2 => do
      let (orig, r1) ← decClosureSpec fuel rest
      let (val, r2) ← decValueSpec fuel r1
      pure (.cached orig val, r2)
    | _ => none

/-- Non-mutual encoder for all 13 `Frame` continuation constructors. -/
def encFrameSpec : Frame → List UInt8
  | .argument t env => (0 : UInt8) :: (encTermSpec t ++ encAddrsSpec env)
  | .update addr => (1 : UInt8) :: encVarNat addr
  | .field name => (2 : UInt8) :: encStrSpec name
  | .reflect => [3]
  | .metadata => [4]
  | .project => [5]
  | .extend fs env => (6 : UInt8) :: (encFieldsSpec fs ++ encAddrsSpec env)
  | .condition z s env => (7 : UInt8) :: (encTermSpec z ++ encTermSpec s ++ encAddrsSpec env)
  | .binaryLeft p r env => (8 : UInt8) :: primTag p :: (encTermSpec r ++ encAddrsSpec env)
  | .binaryRight p l => (9 : UInt8) :: primTag p :: encValueSpec l
  | .case arms env => (10 : UInt8) :: (encFieldsSpec arms ++ encAddrsSpec env)
  | .ifBool wt wf env => (11 : UInt8) :: (encTermSpec wt ++ encTermSpec wf ++ encAddrsSpec env)
  | .split names fn env => (12 : UInt8) :: (encNamesSpec names ++ encTermSpec fn ++ encAddrsSpec env)

def decFrameSpec (fuel : Nat) : List UInt8 → Option (Frame × List UInt8)
  | [] => none
  | tag :: rest =>
    match tag.toNat with
    | 0 => do
      let (t, r1) ← decTermSpec fuel rest
      let (env, r2) ← decAddrsSpec fuel r1
      pure (.argument t env, r2)
    | 1 => do
      let (addr, r1) ← decVarNat fuel rest
      pure (.update addr, r1)
    | 2 => do
      let (name, r1) ← decStrSpec fuel rest
      pure (.field name, r1)
    | 3 => some (.reflect, rest)
    | 4 => some (.metadata, rest)
    | 5 => some (.project, rest)
    | 6 => do
      let (fs, r1) ← decFieldsSpec fuel rest
      let (env, r2) ← decAddrsSpec fuel r1
      pure (.extend fs env, r2)
    | 7 => do
      let (z, r1) ← decTermSpec fuel rest
      let (s, r2) ← decTermSpec fuel r1
      let (env, r3) ← decAddrsSpec fuel r2
      pure (.condition z s env, r3)
    | 8 =>
      match rest with
      | pb :: r0 => do
        let p ← primOfTag pb
        let (r, r1) ← decTermSpec fuel r0
        let (env, r2) ← decAddrsSpec fuel r1
        pure (.binaryLeft p r env, r2)
      | [] => none
    | 9 =>
      match rest with
      | pb :: r0 => do
        let p ← primOfTag pb
        let (l, r1) ← decValueSpec fuel r0
        pure (.binaryRight p l, r1)
      | [] => none
    | 10 => do
      let (arms, r1) ← decFieldsSpec fuel rest
      let (env, r2) ← decAddrsSpec fuel r1
      pure (.case arms env, r2)
    | 11 => do
      let (wt, r1) ← decTermSpec fuel rest
      let (wf, r2) ← decTermSpec fuel r1
      let (env, r3) ← decAddrsSpec fuel r2
      pure (.ifBool wt wf env, r3)
    | 12 => do
      let (names, r1) ← decNamesSpec fuel rest
      let (fn, r2) ← decTermSpec fuel r1
      let (env, r3) ← decAddrsSpec fuel r2
      pure (.split names fn env, r3)
    | _ => none

def refusalTag : Refusal → UInt8
  | .unbound => 0 | .missingCell => 1 | .missingField => 2 | .wrongValue => 3
  | .invalidUpdate => 4 | .capacity => 5 | .missingArm => 6 | .sharedEffect => 7
  | .unresolvedHole => 8

def refusalOfTag (b : UInt8) : Option Refusal :=
  match b.toNat with
  | 0 => some .unbound | 1 => some .missingCell | 2 => some .missingField
  | 3 => some .wrongValue | 4 => some .invalidUpdate | 5 => some .capacity
  | 6 => some .missingArm | 7 => some .sharedEffect | 8 => some .unresolvedHole
  | _ => none

theorem refusalOfTag_refusalTag (r : Refusal) : refusalOfTag (refusalTag r) = some r := by
  cases r <;> rfl

theorem refusalOfTag_sound {b : UInt8} {r : Refusal} (h : refusalOfTag b = some r) :
    refusalTag r = b := by
  have hb := b.toNat_lt
  unfold refusalOfTag at h
  split at h <;> cases h <;> (apply UInt8.toNat_inj.1; simp [refusalTag]; omega)

/-- Encoder for all 7 `Control` constructors (including `.yielded plan`). -/
def encControlSpec : Control → List UInt8
  | .evaluate t env => (0 : UInt8) :: (encTermSpec t ++ encAddrsSpec env)
  | .enter addr => (1 : UInt8) :: encVarNat addr
  | .blackhole addr => (2 : UInt8) :: encVarNat addr
  | .returned val => (3 : UInt8) :: encValueSpec val
  | .complete val => (4 : UInt8) :: encValueSpec val
  | .refused reason => [5, refusalTag reason]
  | .yielded plan => (6 : UInt8) :: encVarNat plan

def decControlSpec (fuel : Nat) : List UInt8 → Option (Control × List UInt8)
  | [] => none
  | tag :: rest =>
    match tag.toNat with
    | 0 => do
      let (t, r1) ← decTermSpec fuel rest
      let (env, r2) ← decAddrsSpec fuel r1
      pure (.evaluate t env, r2)
    | 1 => do
      let (addr, r1) ← decVarNat fuel rest
      pure (.enter addr, r1)
    | 2 => do
      let (addr, r1) ← decVarNat fuel rest
      pure (.blackhole addr, r1)
    | 3 => do
      let (val, r1) ← decValueSpec fuel rest
      pure (.returned val, r1)
    | 4 => do
      let (val, r1) ← decValueSpec fuel rest
      pure (.complete val, r1)
    | 5 =>
      match rest with
      | rb :: r1 => do
        let reason ← refusalOfTag rb
        pure (.refused reason, r1)
      | [] => none
    | 6 => do
      let (plan, r1) ← decVarNat fuel rest
      pure (.yielded plan, r1)
    | _ => none

def decManySpec {α : Type} (dec : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, rest => some ([], rest)
  | c + 1, bs => do
    let (x, r1) ← dec bs
    let (xs, r2) ← decManySpec dec c r1
    pure (x :: xs, r2)

/-- Complete canonical reasoning-tier image of `Core.Machine.State`. -/
def encStateSpec (s : State) : List UInt8 :=
  heapImageMagic ++ encVarNat s.heap.size ++ s.heap.toList.flatMap encCellSpec ++
    encControlSpec s.control ++ encVarNat s.stack.length ++ s.stack.flatMap encFrameSpec

def decStateSpec (bs : List UInt8) : Option State :=
  let fuel := bs.length + 1
  if bs.take 8 = heapImageMagic then
    let r0 := bs.drop 8
    match decVarNat fuel r0 with
    | none => none
    | some (cellCount, r1) =>
      match decManySpec (decCellSpec fuel) cellCount r1 with
      | none => none
      | some (cells, r2) =>
        match decControlSpec fuel r2 with
        | none => none
        | some (ctrl, r3) =>
          match decVarNat fuel r3 with
          | none => none
          | some (frameCount, r4) =>
            match decManySpec (decFrameSpec fuel) frameCount r4 with
            | some (frames, []) => some ⟨cells.toArray, ctrl, frames⟩
            | _ => none
  else none

/-! ## 4. Round-Trip & Canonical Soundness Proofs (`0 Classical`, `0 sorry`) -/

private theorem length_le_flatMap_bytes {α : Type} (enc : α → List UInt8) :
    ∀ (xs : List α) (x : α), x ∈ xs → (enc x).length ≤ (xs.flatMap enc).length
  | [], _, h => by cases h
  | y :: ys, x, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have ih := length_le_flatMap_bytes enc ys x h
      simp only [List.flatMap_cons, List.length_append]; omega

theorem decNamesN_enc :
    ∀ (names : List String) (fuel : Nat) (rest : List UInt8),
      (names.flatMap encStrSpec).length ≤ fuel →
      decNamesN fuel names.length (names.flatMap encStrSpec ++ rest) = some (names, rest)
  | [], _, rest, _ => rfl
  | name :: others, fuel, rest, hf => by
    simp only [List.flatMap_cons, List.length_append] at hf
    simp [decNamesN, List.append_assoc,
      decStrSpec_encStrSpec name fuel _ (by omega),
      decNamesN_enc others fuel rest (by omega)]

theorem decNamesSpec_enc (names : List String) (fuel : Nat) (rest : List UInt8)
    (hf : (encNamesSpec names).length ≤ fuel) :
    decNamesSpec fuel (encNamesSpec names ++ rest) = some (names, rest) := by
  unfold encNamesSpec at hf ⊢
  simp only [List.length_append] at hf
  unfold decNamesSpec
  rw [List.append_assoc]; simp only [bind, Option.bind]
  rw [decVarNat_encVarNat names.length fuel _ (by omega)]
  exact decNamesN_enc names fuel rest (by omega)

theorem decNamesN_sound (fuel : Nat) :
    ∀ (c : Nat) (bs : List UInt8) (names : List String) (rest : List UInt8),
      decNamesN fuel c bs = some (names, rest) →
      bs = names.flatMap encStrSpec ++ rest ∧ names.length = c
  | 0, bs, names, rest, h => by
    simp only [decNamesN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | c + 1, bs, names, rest, h => by
    simp only [decNamesN, bind, Option.bind] at h
    cases hs : decStrSpec fuel bs with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨s, r1⟩ := p; simp only [hs] at h
      cases hr : decNamesN fuel c r1 with
      | none => simp [hr] at h
      | some q =>
        obtain ⟨ss, r2⟩ := q; simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := decStrSpec_sound hs
        obtain ⟨h2, hlen⟩ := decNamesN_sound fuel c r1 ss r2 hr
        exact ⟨by rw [h1, h2, List.flatMap_cons, List.append_assoc], by simp [hlen]⟩

theorem decNamesSpec_sound {fuel : Nat} {bs : List UInt8} {names : List String} {rest : List UInt8}
    (h : decNamesSpec fuel bs = some (names, rest)) : bs = encNamesSpec names ++ rest := by
  simp only [decNamesSpec, bind, Option.bind] at h
  cases hc : decVarNat fuel bs with
  | none => simp [hc] at h
  | some p =>
    obtain ⟨cnt, r0⟩ := p; simp only [hc] at h
    have h0 := decVarNat_sound fuel bs cnt r0 hc
    obtain ⟨h1, hlen⟩ := decNamesN_sound fuel cnt r0 names rest h
    rw [h0, h1, encNamesSpec, hlen, List.append_assoc]

theorem decAddrsN_enc :
    ∀ (addrs : List Address) (fuel : Nat) (rest : List UInt8),
      (addrs.flatMap encVarNat).length ≤ fuel →
      decAddrsN fuel addrs.length (addrs.flatMap encVarNat ++ rest) = some (addrs, rest)
  | [], _, rest, _ => rfl
  | a :: others, fuel, rest, hf => by
    simp only [List.flatMap_cons, List.length_append] at hf
    simp [decAddrsN, List.append_assoc,
      decVarNat_encVarNat a fuel _ (by omega),
      decAddrsN_enc others fuel rest (by omega)]

theorem decAddrsSpec_enc (addrs : List Address) (fuel : Nat) (rest : List UInt8)
    (hf : (encAddrsSpec addrs).length ≤ fuel) :
    decAddrsSpec fuel (encAddrsSpec addrs ++ rest) = some (addrs, rest) := by
  unfold encAddrsSpec at hf ⊢
  simp only [List.length_append] at hf
  unfold decAddrsSpec
  rw [List.append_assoc]; simp only [bind, Option.bind]
  rw [decVarNat_encVarNat addrs.length fuel _ (by omega)]
  exact decAddrsN_enc addrs fuel rest (by omega)

theorem decAddrsN_sound (fuel : Nat) :
    ∀ (c : Nat) (bs : List UInt8) (addrs : List Address) (rest : List UInt8),
      decAddrsN fuel c bs = some (addrs, rest) →
      bs = addrs.flatMap encVarNat ++ rest ∧ addrs.length = c
  | 0, bs, addrs, rest, h => by
    simp only [decAddrsN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | c + 1, bs, addrs, rest, h => by
    simp only [decAddrsN, bind, Option.bind] at h
    cases ha : decVarNat fuel bs with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨a, r1⟩ := p; simp only [ha] at h
      cases hr : decAddrsN fuel c r1 with
      | none => simp [hr] at h
      | some q =>
        obtain ⟨as, r2⟩ := q; simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := decVarNat_sound fuel bs a r1 ha
        obtain ⟨h2, hlen⟩ := decAddrsN_sound fuel c r1 as r2 hr
        exact ⟨by rw [h1, h2, List.flatMap_cons, List.append_assoc], by simp [hlen]⟩

theorem decAddrsSpec_sound {fuel : Nat} {bs : List UInt8} {addrs : List Address} {rest : List UInt8}
    (h : decAddrsSpec fuel bs = some (addrs, rest)) : bs = encAddrsSpec addrs ++ rest := by
  simp only [decAddrsSpec, bind, Option.bind] at h
  cases hc : decVarNat fuel bs with
  | none => simp [hc] at h
  | some p =>
    obtain ⟨cnt, r0⟩ := p; simp only [hc] at h
    have h0 := decVarNat_sound fuel bs cnt r0 hc
    obtain ⟨h1, hlen⟩ := decAddrsN_sound fuel cnt r0 addrs rest h
    rw [h0, h1, encAddrsSpec, hlen, List.append_assoc]

theorem decNamedAddrsN_enc :
    ∀ (fs : List (String × Address)) (fuel : Nat) (rest : List UInt8),
      (fs.flatMap (fun p => encStrSpec p.1 ++ encVarNat p.2)).length ≤ fuel →
      decNamedAddrsN fuel fs.length
        (fs.flatMap (fun p => encStrSpec p.1 ++ encVarNat p.2) ++ rest) = some (fs, rest)
  | [], _, rest, _ => rfl
  | (name, addr) :: others, fuel, rest, hf => by
    simp only [List.flatMap_cons, List.length_append] at hf
    simp [decNamedAddrsN, List.append_assoc,
      decStrSpec_encStrSpec name fuel _ (by omega),
      decVarNat_encVarNat addr fuel _ (by omega),
      decNamedAddrsN_enc others fuel rest (by omega)]

theorem decNamedAddrsSpec_enc (fs : List (String × Address)) (fuel : Nat) (rest : List UInt8)
    (hf : (encNamedAddrsSpec fs).length ≤ fuel) :
    decNamedAddrsSpec fuel (encNamedAddrsSpec fs ++ rest) = some (fs, rest) := by
  unfold encNamedAddrsSpec at hf ⊢
  simp only [List.length_append] at hf
  unfold decNamedAddrsSpec
  rw [List.append_assoc]; simp only [bind, Option.bind]
  rw [decVarNat_encVarNat fs.length fuel _ (by omega)]
  exact decNamedAddrsN_enc fs fuel rest (by omega)

theorem decNamedAddrsN_sound (fuel : Nat) :
    ∀ (c : Nat) (bs : List UInt8) (fs : List (String × Address)) (rest : List UInt8),
      decNamedAddrsN fuel c bs = some (fs, rest) →
      bs = fs.flatMap (fun p => encStrSpec p.1 ++ encVarNat p.2) ++ rest ∧ fs.length = c
  | 0, bs, fs, rest, h => by
    simp only [decNamedAddrsN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | c + 1, bs, fs, rest, h => by
    simp only [decNamedAddrsN, bind, Option.bind] at h
    cases hs : decStrSpec fuel bs with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨name, r1⟩ := p; simp only [hs] at h
      cases ha : decVarNat fuel r1 with
      | none => simp [ha] at h
      | some q =>
        obtain ⟨addr, r2⟩ := q; simp only [ha] at h
        cases hr : decNamedAddrsN fuel c r2 with
        | none => simp [hr] at h
        | some w =>
          obtain ⟨others, r3⟩ := w; simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have h1 := decStrSpec_sound hs
          have h2 := decVarNat_sound fuel r1 addr r2 ha
          obtain ⟨h3, hlen⟩ := decNamedAddrsN_sound fuel c r2 others r3 hr
          exact ⟨by rw [h1, h2, h3, List.flatMap_cons, List.append_assoc, List.append_assoc],
            by simp [hlen]⟩

theorem decNamedAddrsSpec_sound {fuel : Nat} {bs : List UInt8}
    {fs : List (String × Address)} {rest : List UInt8}
    (h : decNamedAddrsSpec fuel bs = some (fs, rest)) : bs = encNamedAddrsSpec fs ++ rest := by
  simp only [decNamedAddrsSpec, bind, Option.bind] at h
  cases hc : decVarNat fuel bs with
  | none => simp [hc] at h
  | some p =>
    obtain ⟨cnt, r0⟩ := p; simp only [hc] at h
    have h0 := decVarNat_sound fuel bs cnt r0 hc
    obtain ⟨h1, hlen⟩ := decNamedAddrsN_sound fuel cnt r0 fs rest h
    rw [h0, h1, encNamedAddrsSpec, hlen, List.append_assoc]

private theorem encTermSpec_pos (t : Term) : 0 < (encTermSpec t).length := by
  cases t <;> simp [encTermSpec]

mutual
theorem decTermSpec_enc :
    ∀ (t : Term) (fuel : Nat) (rest : List UInt8),
      (encTermSpec t).length ≤ fuel →
      decTermSpec fuel (encTermSpec t ++ rest) = some (t, rest)
  | t, 0, _, hf => absurd (Nat.lt_of_lt_of_le (encTermSpec_pos t) hf) (Nat.lt_irrefl 0)
  | .hole n σ, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decVarNat_encVarNat n fuel _ (by omega), decTermsSpec_enc σ fuel rest (by omega)]
  | .bound idx, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decVarNat_encVarNat idx fuel rest (by omega)]
  | .lam body, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decTermSpec_enc body fuel rest (by omega)]
  | .app fn arg, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc fn fuel _ (by omega), decTermSpec_enc arg fuel rest (by omega)]
  | .mix lo hi, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc lo fuel _ (by omega), decTermSpec_enc hi fuel rest (by omega)]
  | .fix sp inh, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc sp fuel _ (by omega), decTermSpec_enc inh fuel rest (by omega)]
  | .specification m e, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc m fuel _ (by omega), decTermSpec_enc e fuel rest (by omega)]
  | .prototype sp tgt, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc sp fuel _ (by omega), decTermSpec_enc tgt fuel rest (by omega)]
  | .reflect tgt, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decTermSpec_enc tgt fuel rest (by omega)]
  | .metadata sp, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decTermSpec_enc sp fuel rest (by omega)]
  | .project tgt, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decTermSpec_enc tgt fuel rest (by omega)]
  | .nat v, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decVarNat_encVarNat v fuel rest (by omega)]
  | .boolean b, fuel + 1, rest, _ => by
    simp [encTermSpec, decTermSpec, decBoolByte_encBoolByte]
  | .label s, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decStrSpec_encStrSpec s fuel rest (by omega)]
  | .binary p l r, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc, primOfTag_primTag,
      decTermSpec_enc l fuel _ (by omega), decTermSpec_enc r fuel rest (by omega)]
  | .extend inh fs, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc inh fuel _ (by omega), decFieldsSpec_enc fs fuel rest (by omega)]
  | .record fs, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decFieldsSpec_enc fs fuel rest (by omega)]
  | .get tgt name, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decStrSpec_encStrSpec name fuel _ (by omega), decTermSpec_enc tgt fuel rest (by omega)]
  | .ifZero v z s, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc v fuel _ (by omega), decTermSpec_enc z fuel _ (by omega),
      decTermSpec_enc s fuel rest (by omega)]
  | .inject lbl pay, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decStrSpec_encStrSpec lbl fuel _ (by omega), decTermSpec_enc pay fuel rest (by omega)]
  | .case scrut arms, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc scrut fuel _ (by omega), decFieldsSpec_enc arms fuel rest (by omega)]
  | .ifBool c t f, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decTermSpec_enc c fuel _ (by omega), decTermSpec_enc t fuel _ (by omega),
      decTermSpec_enc f fuel rest (by omega)]
  | .perform plan, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decTermSpec_enc plan fuel rest (by omega)]
  | .done v, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons] at hf
    simp [encTermSpec, decTermSpec, decTermSpec_enc v fuel rest (by omega)]
  | .split tgt names fn, fuel + 1, rest, hf => by
    simp only [encTermSpec, List.length_cons, List.length_append] at hf
    simp [encTermSpec, decTermSpec, List.append_assoc,
      decNamesSpec_enc names fuel _ (by omega), decTermSpec_enc tgt fuel _ (by omega),
      decTermSpec_enc fn fuel rest (by omega)]
termination_by structural t => t

theorem decFieldsSpec_enc :
    ∀ (fs : List (String × Term)) (fuel : Nat) (rest : List UInt8),
      (encFieldsSpec fs).length ≤ fuel →
      decFieldsSpec fuel (encFieldsSpec fs ++ rest) = some (fs, rest)
  | fs, 0, _, hf => by cases fs <;> simp [encFieldsSpec] at hf
  | [], _ + 1, rest, _ => rfl
  | (name, body) :: others, fuel + 1, rest, hf => by
    simp only [encFieldsSpec, List.length_cons, List.length_append] at hf
    simp [encFieldsSpec, decFieldsSpec, List.append_assoc,
      decStrSpec_encStrSpec name fuel _ (by omega),
      decTermSpec_enc body fuel _ (by omega),
      decFieldsSpec_enc others fuel rest (by omega)]
termination_by structural fs => fs

theorem decTermsSpec_enc :
    ∀ (ts : List Term) (fuel : Nat) (rest : List UInt8),
      (encTermsSpec ts).length ≤ fuel →
      decTermsSpec fuel (encTermsSpec ts ++ rest) = some (ts, rest)
  | ts, 0, _, hf => by cases ts <;> simp [encTermsSpec] at hf
  | [], _ + 1, rest, _ => rfl
  | t :: others, fuel + 1, rest, hf => by
    simp only [encTermsSpec, List.length_cons, List.length_append] at hf
    simp [encTermsSpec, decTermsSpec, List.append_assoc,
      decTermSpec_enc t fuel _ (by omega),
      decTermsSpec_enc others fuel rest (by omega)]
termination_by structural ts => ts
end

private theorem uint8_of_toNat_eq {b : UInt8} {k : Nat} (h : b.toNat = k) : b = UInt8.ofNat k := by
  rw [← h, UInt8.ofNat_toNat]

mutual
theorem decTermSpec_sound :
    ∀ (fuel : Nat) (bs : List UInt8) (t : Term) (rest : List UInt8),
      decTermSpec fuel bs = some (t, rest) → bs = encTermSpec t ++ rest
  | 0, _, _, _, h => by simp [decTermSpec] at h
  | _ + 1, [], _, _, h => by simp [decTermSpec] at h
  | fuel + 1, tag :: r0, t, rest, h => by
    simp only [decTermSpec] at h
    split at h
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨n, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermsSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨σ, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decVarNat_sound fuel r0 n r1 h1, decTermsSpec_sound fuel r1 σ r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨idx, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ht, decVarNat_sound fuel r0 idx r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨body, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ht, decTermSpec_sound fuel r0 body r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨fn, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨arg, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 fn r1 h1, decTermSpec_sound fuel r1 arg r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨lo, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨hi, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 lo r1 h1, decTermSpec_sound fuel r1 hi r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨sp, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨inh, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 sp r1 h1, decTermSpec_sound fuel r1 inh r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨m, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨e, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 m r1 h1, decTermSpec_sound fuel r1 e r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨sp, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨tgt, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 sp r1 h1, decTermSpec_sound fuel r1 tgt r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨tgt, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decTermSpec_sound fuel r0 tgt r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨sp, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decTermSpec_sound fuel r0 sp r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨tgt, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decTermSpec_sound fuel r0 tgt r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨v, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 v r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      cases r0 with
      | nil => simp at h
      | cons b r1 =>
        simp only [bind, Option.bind] at h
        cases hb : decBoolByte b with
        | none => simp [hb] at h
        | some bv =>
          simp only [hb, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, ← decBoolByte_sound hb]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decStrSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨s, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decStrSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      cases r0 with
      | nil => simp at h
      | cons pb r0' =>
        simp only [bind, Option.bind] at h
        cases hp : primOfTag pb with
        | none => simp [hp] at h
        | some p =>
          simp only [hp] at h
          cases h1 : decTermSpec fuel r0' with
          | none => simp [h1] at h
          | some p1 =>
            obtain ⟨l, r1⟩ := p1; simp only [h1] at h
            cases h2 : decTermSpec fuel r1 with
            | none => simp [h2] at h
            | some p2 =>
              obtain ⟨r, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [ht, ← primOfTag_sound hp, decTermSpec_sound fuel r0' l r1 h1,
                decTermSpec_sound fuel r1 r r2 h2]
              simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨inh, r1⟩ := p1; simp only [h1] at h
        cases h2 : decFieldsSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨fs, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 inh r1 h1, decFieldsSpec_sound fuel r1 fs r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decFieldsSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨fs, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decFieldsSpec_sound fuel r0 fs r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decStrSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨name, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨tgt, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decStrSpec_sound h1, decTermSpec_sound fuel r1 tgt r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨v, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨z, r2⟩ := p2; simp only [h2] at h
          cases h3 : decTermSpec fuel r2 with
          | none => simp [h3] at h
          | some p3 =>
            obtain ⟨s, r3⟩ := p3; simp only [h3, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [ht, decTermSpec_sound fuel r0 v r1 h1, decTermSpec_sound fuel r1 z r2 h2,
              decTermSpec_sound fuel r2 s r3 h3]
            simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decStrSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨lbl, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨pay, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decStrSpec_sound h1, decTermSpec_sound fuel r1 pay r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨scrut, r1⟩ := p1; simp only [h1] at h
        cases h2 : decFieldsSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨arms, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 scrut r1 h1, decFieldsSpec_sound fuel r1 arms r2 h2]
          simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨c, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨wt, r2⟩ := p2; simp only [h2] at h
          cases h3 : decTermSpec fuel r2 with
          | none => simp [h3] at h
          | some p3 =>
            obtain ⟨wf, r3⟩ := p3; simp only [h3, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [ht, decTermSpec_sound fuel r0 c r1 h1, decTermSpec_sound fuel r1 wt r2 h2,
              decTermSpec_sound fuel r2 wf r3 h3]
            simp [encTermSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨plan, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decTermSpec_sound fuel r0 plan r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨v, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decTermSpec_sound fuel r0 v r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decNamesSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨names, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨tgt, r2⟩ := p2; simp only [h2] at h
          cases h3 : decTermSpec fuel r2 with
          | none => simp [h3] at h
          | some p3 =>
            obtain ⟨fn, r3⟩ := p3; simp only [h3, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [ht, decNamesSpec_sound h1, decTermSpec_sound fuel r1 tgt r2 h2,
              decTermSpec_sound fuel r2 fn r3 h3]
            simp [encTermSpec, List.append_assoc]
    · cases h

theorem decFieldsSpec_sound :
    ∀ (fuel : Nat) (bs : List UInt8) (fs : List (String × Term)) (rest : List UInt8),
      decFieldsSpec fuel bs = some (fs, rest) → bs = encFieldsSpec fs ++ rest
  | 0, _, _, _, h => by simp [decFieldsSpec] at h
  | _ + 1, [], _, _, h => by simp [decFieldsSpec] at h
  | fuel + 1, tag :: r0, fs, rest, h => by
    simp only [decFieldsSpec] at h
    split at h
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rw [ht]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      simp only [bind, Option.bind] at h
      cases h1 : decStrSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨name, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨body, r2⟩ := p2; simp only [h2] at h
          cases h3 : decFieldsSpec fuel r2 with
          | none => simp [h3] at h
          | some p3 =>
            obtain ⟨others, r3⟩ := p3; simp only [h3, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [ht, decStrSpec_sound h1, decTermSpec_sound fuel r1 body r2 h2,
              decFieldsSpec_sound fuel r2 others r3 h3]
            simp [encFieldsSpec, List.append_assoc]
    · cases h

theorem decTermsSpec_sound :
    ∀ (fuel : Nat) (bs : List UInt8) (ts : List Term) (rest : List UInt8),
      decTermsSpec fuel bs = some (ts, rest) → bs = encTermsSpec ts ++ rest
  | 0, _, _, _, h => by simp [decTermsSpec] at h
  | _ + 1, [], _, _, h => by simp [decTermsSpec] at h
  | fuel + 1, tag :: r0, ts, rest, h => by
    simp only [decTermsSpec] at h
    split at h
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rw [ht]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨t, r1⟩ := p1; simp only [h1] at h
        cases h2 : decTermsSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨others, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 t r1 h1, decTermsSpec_sound fuel r1 others r2 h2]
          simp [encTermsSpec, List.append_assoc]
    · cases h
end

theorem decClosureSpec_enc (cl : Closure) (fuel : Nat) (rest : List UInt8)
    (hf : (encClosureSpec cl).length ≤ fuel) :
    decClosureSpec fuel (encClosureSpec cl ++ rest) = some (cl, rest) := by
  unfold encClosureSpec at hf ⊢
  simp only [List.length_append] at hf
  simp [decClosureSpec, List.append_assoc,
    decTermSpec_enc cl.term fuel _ (by omega),
    decAddrsSpec_enc cl.environment fuel rest (by omega)]

theorem decClosureSpec_sound {fuel : Nat} {bs : List UInt8} {cl : Closure} {rest : List UInt8}
    (h : decClosureSpec fuel bs = some (cl, rest)) : bs = encClosureSpec cl ++ rest := by
  simp only [decClosureSpec, bind, Option.bind] at h
  cases h1 : decTermSpec fuel bs with
  | none => simp [h1] at h
  | some p1 =>
    obtain ⟨t, r1⟩ := p1; simp only [h1] at h
    cases h2 : decAddrsSpec fuel r1 with
    | none => simp [h2] at h
    | some p2 =>
      obtain ⟨env, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [decTermSpec_sound fuel bs t r1 h1, decAddrsSpec_sound h2, encClosureSpec, List.append_assoc]

theorem decValueSpec_enc (v : RuntimeValue) (fuel : Nat) (rest : List UInt8)
    (hf : (encValueSpec v).length ≤ fuel) :
    decValueSpec fuel (encValueSpec v ++ rest) = some (v, rest) := by
  cases v with
  | closure body env =>
    simp only [encValueSpec, List.length_cons, List.length_append] at hf
    simp [encValueSpec, decValueSpec, List.append_assoc,
      decTermSpec_enc body fuel _ (by omega), decAddrsSpec_enc env fuel rest (by omega)]
  | natural n =>
    simp only [encValueSpec, List.length_cons] at hf
    simp [encValueSpec, decValueSpec, decVarNat_encVarNat n fuel rest (by omega)]
  | boolean b =>
    simp [encValueSpec, decValueSpec, decBoolByte_encBoolByte]
  | label s =>
    simp only [encValueSpec, List.length_cons] at hf
    simp [encValueSpec, decValueSpec, decStrSpec_encStrSpec s fuel rest (by omega)]
  | record fs =>
    simp only [encValueSpec, List.length_cons] at hf
    simp [encValueSpec, decValueSpec, decNamedAddrsSpec_enc fs fuel rest (by omega)]
  | specification m e =>
    simp only [encValueSpec, List.length_cons, List.length_append] at hf
    simp [encValueSpec, decValueSpec, List.append_assoc,
      decVarNat_encVarNat m fuel _ (by omega), decVarNat_encVarNat e fuel rest (by omega)]
  | prototype sp tgt =>
    simp only [encValueSpec, List.length_cons, List.length_append] at hf
    simp [encValueSpec, decValueSpec, List.append_assoc,
      decVarNat_encVarNat sp fuel _ (by omega), decVarNat_encVarNat tgt fuel rest (by omega)]
  | variant lbl pay =>
    simp only [encValueSpec, List.length_cons, List.length_append] at hf
    simp [encValueSpec, decValueSpec, List.append_assoc,
      decStrSpec_encStrSpec lbl fuel _ (by omega), decVarNat_encVarNat pay fuel rest (by omega)]

theorem decValueSpec_sound {fuel : Nat} {bs : List UInt8} {v : RuntimeValue} {rest : List UInt8}
    (h : decValueSpec fuel bs = some (v, rest)) : bs = encValueSpec v ++ rest := by
  cases bs with
  | nil => simp [decValueSpec] at h
  | cons tag r0 =>
    simp only [decValueSpec] at h
    split at h
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨body, r1⟩ := p1; simp only [h1] at h
        cases h2 : decAddrsSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨env, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 body r1 h1, decAddrsSpec_sound h2]
          simp [encValueSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 => simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 _ _ h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      cases r0 with
      | nil => simp at h
      | cons b r1 =>
        simp only [bind, Option.bind] at h
        cases hb : decBoolByte b with
        | none => simp [hb] at h
        | some bv => simp only [hb, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, ← decBoolByte_sound hb]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decStrSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 => simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decStrSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decNamedAddrsSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 => simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decNamedAddrsSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decVarNat fuel p1.2 with
        | none => simp [h2] at h
        | some p2 => simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 p1.1 p1.2 h1, decVarNat_sound fuel p1.2 p2.1 p2.2 h2]; simp [encValueSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decVarNat fuel p1.2 with
        | none => simp [h2] at h
        | some p2 => simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 p1.1 p1.2 h1, decVarNat_sound fuel p1.2 p2.1 p2.2 h2]; simp [encValueSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decStrSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decVarNat fuel p1.2 with
        | none => simp [h2] at h
        | some p2 => simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decStrSpec_sound h1, decVarNat_sound fuel p1.2 p2.1 p2.2 h2]; simp [encValueSpec, List.append_assoc]
    · cases h

theorem decCellSpec_enc (c : Cell) (fuel : Nat) (rest : List UInt8)
    (hf : (encCellSpec c).length ≤ fuel) :
    decCellSpec fuel (encCellSpec c ++ rest) = some (c, rest) := by
  cases c with
  | suspended orig =>
    simp only [encCellSpec, List.length_cons] at hf
    simp [encCellSpec, decCellSpec, decClosureSpec_enc orig fuel rest (by omega)]
  | evaluating orig =>
    simp only [encCellSpec, List.length_cons] at hf
    simp [encCellSpec, decCellSpec, decClosureSpec_enc orig fuel rest (by omega)]
  | cached orig val =>
    simp only [encCellSpec, List.length_cons, List.length_append] at hf
    simp [encCellSpec, decCellSpec, List.append_assoc,
      decClosureSpec_enc orig fuel _ (by omega), decValueSpec_enc val fuel rest (by omega)]

theorem decCellSpec_sound {fuel : Nat} {bs : List UInt8} {c : Cell} {rest : List UInt8}
    (h : decCellSpec fuel bs = some (c, rest)) : bs = encCellSpec c ++ rest := by
  cases bs with
  | nil => simp [decCellSpec] at h
  | cons tag r0 =>
    simp only [decCellSpec] at h
    split at h
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decClosureSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨orig, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decClosureSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decClosureSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨orig, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decClosureSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decClosureSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨orig, r1⟩ := p1; simp only [h1] at h
        cases h2 : decValueSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨val, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decClosureSpec_sound h1, decValueSpec_sound h2]; simp [encCellSpec, List.append_assoc]
    · cases h

theorem decFrameSpec_enc (fr : Frame) (fuel : Nat) (rest : List UInt8)
    (hf : (encFrameSpec fr).length ≤ fuel) :
    decFrameSpec fuel (encFrameSpec fr ++ rest) = some (fr, rest) := by
  cases fr with
  | argument t env =>
    simp only [encFrameSpec, List.length_cons, List.length_append] at hf
    simp [encFrameSpec, decFrameSpec, List.append_assoc,
      decTermSpec_enc t fuel _ (by omega), decAddrsSpec_enc env fuel rest (by omega)]
  | update addr =>
    simp only [encFrameSpec, List.length_cons] at hf
    simp [encFrameSpec, decFrameSpec, decVarNat_encVarNat addr fuel rest (by omega)]
  | field name =>
    simp only [encFrameSpec, List.length_cons] at hf
    simp [encFrameSpec, decFrameSpec, decStrSpec_encStrSpec name fuel rest (by omega)]
  | reflect => simp [encFrameSpec, decFrameSpec]
  | metadata => simp [encFrameSpec, decFrameSpec]
  | project => simp [encFrameSpec, decFrameSpec]
  | extend fs env =>
    simp only [encFrameSpec, List.length_cons, List.length_append] at hf
    simp [encFrameSpec, decFrameSpec, List.append_assoc,
      decFieldsSpec_enc fs fuel _ (by omega), decAddrsSpec_enc env fuel rest (by omega)]
  | condition z s env =>
    simp only [encFrameSpec, List.length_cons, List.length_append] at hf
    simp [encFrameSpec, decFrameSpec, List.append_assoc,
      decTermSpec_enc z fuel _ (by omega), decTermSpec_enc s fuel _ (by omega),
      decAddrsSpec_enc env fuel rest (by omega)]
  | binaryLeft p r env =>
    simp only [encFrameSpec, List.length_cons, List.length_append] at hf
    simp [encFrameSpec, decFrameSpec, List.append_assoc, primOfTag_primTag,
      decTermSpec_enc r fuel _ (by omega), decAddrsSpec_enc env fuel rest (by omega)]
  | binaryRight p l =>
    simp only [encFrameSpec, List.length_cons] at hf
    simp [encFrameSpec, decFrameSpec, primOfTag_primTag,
      decValueSpec_enc l fuel rest (by omega)]
  | case arms env =>
    simp only [encFrameSpec, List.length_cons, List.length_append] at hf
    simp [encFrameSpec, decFrameSpec, List.append_assoc,
      decFieldsSpec_enc arms fuel _ (by omega), decAddrsSpec_enc env fuel rest (by omega)]
  | ifBool wt wf env =>
    simp only [encFrameSpec, List.length_cons, List.length_append] at hf
    simp [encFrameSpec, decFrameSpec, List.append_assoc,
      decTermSpec_enc wt fuel _ (by omega), decTermSpec_enc wf fuel _ (by omega),
      decAddrsSpec_enc env fuel rest (by omega)]
  | split names fn env =>
    simp only [encFrameSpec, List.length_cons, List.length_append] at hf
    simp [encFrameSpec, decFrameSpec, List.append_assoc,
      decNamesSpec_enc names fuel _ (by omega), decTermSpec_enc fn fuel _ (by omega),
      decAddrsSpec_enc env fuel rest (by omega)]

theorem decFrameSpec_sound {fuel : Nat} {bs : List UInt8} {fr : Frame} {rest : List UInt8}
    (h : decFrameSpec fuel bs = some (fr, rest)) : bs = encFrameSpec fr ++ rest := by
  cases bs with
  | nil => simp [decFrameSpec] at h
  | cons tag r0 =>
    simp only [decFrameSpec] at h
    split at h
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨t, r1⟩ := p1; simp only [h1] at h
        cases h2 : decAddrsSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨env, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 t r1 h1, decAddrsSpec_sound h2]
          simp [encFrameSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 => simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 _ _ h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decStrSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 => simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decStrSpec_sound h1]; rfl
    · next htag => have ht := uint8_of_toNat_eq htag; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht]; rfl
    · next htag => have ht := uint8_of_toNat_eq htag; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht]; rfl
    · next htag => have ht := uint8_of_toNat_eq htag; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decFieldsSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decAddrsSpec fuel p1.2 with
        | none => simp [h2] at h
        | some p2 => simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decFieldsSpec_sound fuel r0 p1.1 p1.2 h1, decAddrsSpec_sound h2]; simp [encFrameSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decTermSpec fuel p1.2 with
        | none => simp [h2] at h
        | some p2 =>
          simp only [h2] at h
          cases h3 : decAddrsSpec fuel p2.2 with
          | none => simp [h3] at h
          | some p3 => simp only [h3, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decTermSpec_sound fuel r0 p1.1 p1.2 h1, decTermSpec_sound fuel p1.2 p2.1 p2.2 h2, decAddrsSpec_sound h3]; simp [encFrameSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      cases r0 with
      | nil => simp at h
      | cons pb r0' =>
        simp only [bind, Option.bind] at h
        cases hp : primOfTag pb with
        | none => simp [hp] at h
        | some p =>
          simp only [hp] at h
          cases h1 : decTermSpec fuel r0' with
          | none => simp [h1] at h
          | some p1 =>
            simp only [h1] at h
            cases h2 : decAddrsSpec fuel p1.2 with
            | none => simp [h2] at h
            | some p2 => simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, ← primOfTag_sound hp, decTermSpec_sound fuel r0' p1.1 p1.2 h1, decAddrsSpec_sound h2]; simp [encFrameSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      cases r0 with
      | nil => simp at h
      | cons pb r0' =>
        simp only [bind, Option.bind] at h
        cases hp : primOfTag pb with
        | none => simp [hp] at h
        | some p =>
          simp only [hp] at h
          cases h1 : decValueSpec fuel r0' with
          | none => simp [h1] at h
          | some p1 => simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, ← primOfTag_sound hp, decValueSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decFieldsSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decAddrsSpec fuel p1.2 with
        | none => simp [h2] at h
        | some p2 => simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decFieldsSpec_sound fuel r0 p1.1 p1.2 h1, decAddrsSpec_sound h2]; simp [encFrameSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decTermSpec fuel p1.2 with
        | none => simp [h2] at h
        | some p2 =>
          simp only [h2] at h
          cases h3 : decAddrsSpec fuel p2.2 with
          | none => simp [h3] at h
          | some p3 => simp only [h3, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decTermSpec_sound fuel r0 p1.1 p1.2 h1, decTermSpec_sound fuel p1.2 p2.1 p2.2 h2, decAddrsSpec_sound h3]; simp [encFrameSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decNamesSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        simp only [h1] at h
        cases h2 : decTermSpec fuel p1.2 with
        | none => simp [h2] at h
        | some p2 =>
          simp only [h2] at h
          cases h3 : decAddrsSpec fuel p2.2 with
          | none => simp [h3] at h
          | some p3 => simp only [h3, pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [ht, decNamesSpec_sound h1, decTermSpec_sound fuel p1.2 p2.1 p2.2 h2, decAddrsSpec_sound h3]; simp [encFrameSpec, List.append_assoc]
    · cases h

theorem decControlSpec_enc (ctrl : Control) (fuel : Nat) (rest : List UInt8)
    (hf : (encControlSpec ctrl).length ≤ fuel) :
    decControlSpec fuel (encControlSpec ctrl ++ rest) = some (ctrl, rest) := by
  cases ctrl with
  | evaluate t env =>
    simp only [encControlSpec, List.length_cons, List.length_append] at hf
    simp [encControlSpec, decControlSpec, List.append_assoc,
      decTermSpec_enc t fuel _ (by omega), decAddrsSpec_enc env fuel rest (by omega)]
  | enter addr =>
    simp only [encControlSpec, List.length_cons] at hf
    simp [encControlSpec, decControlSpec, decVarNat_encVarNat addr fuel rest (by omega)]
  | blackhole addr =>
    simp only [encControlSpec, List.length_cons] at hf
    simp [encControlSpec, decControlSpec, decVarNat_encVarNat addr fuel rest (by omega)]
  | returned val =>
    simp only [encControlSpec, List.length_cons] at hf
    simp [encControlSpec, decControlSpec, decValueSpec_enc val fuel rest (by omega)]
  | complete val =>
    simp only [encControlSpec, List.length_cons] at hf
    simp [encControlSpec, decControlSpec, decValueSpec_enc val fuel rest (by omega)]
  | refused reason =>
    simp [encControlSpec, decControlSpec, refusalOfTag_refusalTag]
  | yielded plan =>
    simp only [encControlSpec, List.length_cons] at hf
    simp [encControlSpec, decControlSpec, decVarNat_encVarNat plan fuel rest (by omega)]

theorem decControlSpec_sound {fuel : Nat} {bs : List UInt8} {ctrl : Control} {rest : List UInt8}
    (h : decControlSpec fuel bs = some (ctrl, rest)) : bs = encControlSpec ctrl ++ rest := by
  cases bs with
  | nil => simp [decControlSpec] at h
  | cons tag r0 =>
    simp only [decControlSpec] at h
    split at h
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decTermSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨t, r1⟩ := p1; simp only [h1] at h
        cases h2 : decAddrsSpec fuel r1 with
        | none => simp [h2] at h
        | some p2 =>
          obtain ⟨env, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ht, decTermSpec_sound fuel r0 t r1 h1, decAddrsSpec_sound h2]
          simp [encControlSpec, List.append_assoc]
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨addr, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 addr r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨addr, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 addr r1 h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decValueSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨val, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decValueSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decValueSpec fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨val, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decValueSpec_sound h1]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag
      cases r0 with
      | nil => simp at h
      | cons rb r1 =>
        simp only [bind, Option.bind] at h
        cases hr : refusalOfTag rb with
        | none => simp [hr] at h
        | some reason =>
          simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; rw [ht, ← refusalOfTag_sound hr]; rfl
    · next htag =>
      have ht := uint8_of_toNat_eq htag; simp only [bind, Option.bind] at h
      cases h1 : decVarNat fuel r0 with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨plan, r1⟩ := p1; simp only [h1, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rw [ht, decVarNat_sound fuel r0 plan r1 h1]; rfl
    · cases h

theorem decManySpec_enc {α : Type} (dec : List UInt8 → Option (α × List UInt8))
    (enc : α → List UInt8) :
    ∀ (items : List α) (rest : List UInt8),
      (∀ x ∈ items, ∀ r, dec (enc x ++ r) = some (x, r)) →
      decManySpec dec items.length (items.flatMap enc ++ rest) = some (items, rest)
  | [], rest, _ => rfl
  | x :: xs, rest, each => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decManySpec, bind, Option.bind]
    rw [each x List.mem_cons_self]
    simp only []
    rw [decManySpec_enc dec enc xs rest (fun y hy => each y (List.mem_cons_of_mem _ hy))]
    rfl

theorem decManySpec_sound {α : Type} {dec : List UInt8 → Option (α × List UInt8)}
    {enc : α → List UInt8}
    (hsound : ∀ bs x r, dec bs = some (x, r) → bs = enc x ++ r) :
    ∀ (c : Nat) (bs : List UInt8) (items : List α) (rest : List UInt8),
      decManySpec dec c bs = some (items, rest) →
      bs = items.flatMap enc ++ rest ∧ items.length = c
  | 0, bs, items, rest, h => by
    simp only [decManySpec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | c + 1, bs, items, rest, h => by
    simp only [decManySpec, bind, Option.bind] at h
    cases h1 : dec bs with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨x, r1⟩ := p1; simp only [h1] at h
      cases h2 : decManySpec dec c r1 with
      | none => simp [h2] at h
      | some p2 =>
        obtain ⟨xs, r2⟩ := p2; simp only [h2, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have e1 := hsound bs x r1 h1
        obtain ⟨e2, hlen⟩ := decManySpec_sound hsound c r1 xs r2 h2
        exact ⟨by rw [e1, e2, List.flatMap_cons, List.append_assoc], by simp [hlen]⟩

theorem decStateSpec_encStateSpec (s : State) :
    decStateSpec (encStateSpec s) = some s := by
  rcases s with ⟨heap, ctrl, stack⟩
  have hmag : heapImageMagic.length = 8 := rfl
  have hshape : encStateSpec ⟨heap, ctrl, stack⟩ =
      heapImageMagic ++ (encVarNat heap.size ++ (heap.toList.flatMap encCellSpec ++
        (encControlSpec ctrl ++ (encVarNat stack.length ++ stack.flatMap encFrameSpec)))) := by
    simp [encStateSpec, List.append_assoc]
  have hlen : (encStateSpec ⟨heap, ctrl, stack⟩).length =
      8 + ((encVarNat heap.size).length + ((heap.toList.flatMap encCellSpec).length +
        ((encControlSpec ctrl).length + ((encVarNat stack.length).length +
          (stack.flatMap encFrameSpec).length)))) := by
    rw [hshape]; simp [hmag]
  unfold decStateSpec
  generalize hfuel : (encStateSpec ⟨heap, ctrl, stack⟩).length + 1 = fuel
  have htake : (encStateSpec ⟨heap, ctrl, stack⟩).take 8 = heapImageMagic := by
    rw [hshape, List.take_left' hmag]
  have hdrop : (encStateSpec ⟨heap, ctrl, stack⟩).drop 8 =
      encVarNat heap.size ++ (heap.toList.flatMap encCellSpec ++
        (encControlSpec ctrl ++ (encVarNat stack.length ++ stack.flatMap encFrameSpec))) := by
    rw [hshape, List.drop_left' hmag]
  rw [ite_eq_left htake]; dsimp only; rw [hdrop]
  rw [decVarNat_encVarNat heap.size fuel _ (by omega)]; dsimp only
  have hcells : ∀ c ∈ heap.toList, ∀ r, decCellSpec fuel (encCellSpec c ++ r) = some (c, r) := by
    intro c hc r
    apply decCellSpec_enc
    have := length_le_flatMap_bytes encCellSpec heap.toList c hc
    omega
  rw [show heap.size = heap.toList.length by simp]
  rw [decManySpec_enc (decCellSpec fuel) encCellSpec heap.toList _ hcells]; dsimp only
  rw [decControlSpec_enc ctrl fuel _ (by omega)]; dsimp only
  rw [decVarNat_encVarNat stack.length fuel _ (by omega)]; dsimp only
  have hframes : ∀ fr ∈ stack, ∀ r, decFrameSpec fuel (encFrameSpec fr ++ r) = some (fr, r) := by
    intro fr hfr r
    apply decFrameSpec_enc
    have := length_le_flatMap_bytes encFrameSpec stack fr hfr
    omega
  have hstk := decManySpec_enc (decFrameSpec fuel) encFrameSpec stack [] hframes
  rw [List.append_nil] at hstk
  simp [hstk]

theorem decStateSpec_sound {bs : List UInt8} {s : State} (h : decStateSpec bs = some s) :
    encStateSpec s = bs := by
  unfold decStateSpec at h
  generalize (bs.length + 1) = fuel at h
  split at h
  · next hmag =>
    dsimp only at h
    cases h1 : decVarNat fuel (bs.drop 8) with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨cellCnt, r1⟩ := p1; simp only [h1] at h
      cases h2 : decManySpec (decCellSpec fuel) cellCnt r1 with
      | none => simp [h2] at h
      | some p2 =>
        obtain ⟨cells, r2⟩ := p2; simp only [h2] at h
        cases h3 : decControlSpec fuel r2 with
        | none => simp [h3] at h
        | some p3 =>
          obtain ⟨ctrl, r3⟩ := p3; simp only [h3] at h
          cases h4 : decVarNat fuel r3 with
          | none => simp [h4] at h
          | some p4 =>
            obtain ⟨frameCnt, r4⟩ := p4; simp only [h4] at h
            cases h5 : decManySpec (decFrameSpec fuel) frameCnt r4 with
            | none => simp [h5] at h
            | some p5 =>
              obtain ⟨frames, r5⟩ := p5
              cases r5 with
              | cons _ _ => simp [h5] at h
              | nil =>
                simp only [h5, Option.some.injEq] at h
                subst h
                have e1 := decVarNat_sound fuel (bs.drop 8) cellCnt r1 h1
                obtain ⟨e2, hclen⟩ :=
                  decManySpec_sound (fun _ _ _ => decCellSpec_sound) cellCnt r1 cells r2 h2
                have e3 := decControlSpec_sound h3
                have e4 := decVarNat_sound fuel r3 frameCnt r4 h4
                obtain ⟨e5, hflen⟩ :=
                  decManySpec_sound (fun _ _ _ => decFrameSpec_sound) frameCnt r4 frames [] h5
                rw [List.append_nil] at e5
                have htot : bs = heapImageMagic ++ bs.drop 8 := by
                  rw [← hmag, List.take_append_drop]
                rw [htot, e1, e2, e3, e4, e5, ← hclen, ← hflen]
                simp [encStateSpec, List.append_assoc]
  · cases h

/-! ## 5. Unboxed `ByteArray` Execution Tier (Push Writer + Offset Cursor Reader + `@[csimp]`) -/

/-- Append canonical base-128 varint bytes directly into a `ByteArray` buffer. -/
def pushVarNat (out : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then out.push (UInt8.ofNat n)
  else pushVarNat (out.push (UInt8.ofNat (128 + n % 128))) (n / 128)
termination_by n
decreasing_by omega

theorem pushVarNat_toList (n : Nat) :
    ∀ (out : ByteArray), (pushVarNat out n).data.toList = out.data.toList ++ encVarNat n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro out
    rw [pushVarNat, encVarNat_step]
    by_cases hlt : n < 128
    · rw [ite_eq_left hlt, ite_eq_left hlt, Obend.Digest.Cshake256.Fast.push_data]
    · rw [ite_eq_right hlt, ite_eq_right hlt, ih (n / 128) (by omega),
        Obend.Digest.Cshake256.Fast.push_data, List.append_assoc, List.singleton_append]

def pushStr (out : ByteArray) (s : String) : ByteArray :=
  pushVarNat out s.toByteArray.size ++ s.toByteArray

theorem pushStr_toList (out : ByteArray) (s : String) :
    (pushStr out s).data.toList = out.data.toList ++ encStrSpec s := by
  simp [pushStr, encStrSpec, pushVarNat_toList, ByteArray.data_append, List.append_assoc]

def pushNames (out : ByteArray) (names : List String) : ByteArray :=
  names.foldl pushStr (pushVarNat out names.length)

private theorem foldl_push_eq {α : Type} (pushFn : ByteArray → α → ByteArray)
    (specFn : α → List UInt8)
    (hpush : ∀ b x, (pushFn b x).data.toList = b.data.toList ++ specFn x) :
    ∀ (xs : List α) (out : ByteArray),
      (xs.foldl pushFn out).data.toList = out.data.toList ++ xs.flatMap specFn
  | [], out => by simp
  | x :: xs, out => by
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [foldl_push_eq pushFn specFn hpush xs (pushFn out x), hpush, List.append_assoc]

theorem pushNames_toList (out : ByteArray) (names : List String) :
    (pushNames out names).data.toList = out.data.toList ++ encNamesSpec names := by
  unfold pushNames encNamesSpec
  rw [foldl_push_eq pushStr encStrSpec pushStr_toList, pushVarNat_toList, List.append_assoc]

def pushAddrs (out : ByteArray) (addrs : List Address) : ByteArray :=
  addrs.foldl pushVarNat (pushVarNat out addrs.length)

theorem pushAddrs_toList (out : ByteArray) (addrs : List Address) :
    (pushAddrs out addrs).data.toList = out.data.toList ++ encAddrsSpec addrs := by
  unfold pushAddrs encAddrsSpec
  rw [foldl_push_eq pushVarNat encVarNat (fun b x => pushVarNat_toList x b),
    pushVarNat_toList, List.append_assoc]

def pushNamedAddrs (out : ByteArray) (fs : List (String × Address)) : ByteArray :=
  fs.foldl (fun acc p => pushVarNat (pushStr acc p.1) p.2) (pushVarNat out fs.length)

theorem pushNamedAddrs_toList (out : ByteArray) (fs : List (String × Address)) :
    (pushNamedAddrs out fs).data.toList = out.data.toList ++ encNamedAddrsSpec fs := by
  unfold pushNamedAddrs encNamedAddrsSpec
  rw [foldl_push_eq (fun acc (p : String × Address) => pushVarNat (pushStr acc p.1) p.2)
    (fun p => encStrSpec p.1 ++ encVarNat p.2)
    (fun acc p => by rw [pushVarNat_toList, pushStr_toList, List.append_assoc]),
    pushVarNat_toList, List.append_assoc]

mutual
def pushTerm (out : ByteArray) : Term → ByteArray
  | .hole n σ => pushTerms (pushVarNat (out.push 0) n) σ
  | .bound idx => pushVarNat (out.push 1) idx
  | .lam body => pushTerm (out.push 2) body
  | .app fn arg => pushTerm (pushTerm (out.push 3) fn) arg
  | .mix lo hi => pushTerm (pushTerm (out.push 4) lo) hi
  | .fix sp inh => pushTerm (pushTerm (out.push 5) sp) inh
  | .specification m e => pushTerm (pushTerm (out.push 6) m) e
  | .prototype sp tgt => pushTerm (pushTerm (out.push 7) sp) tgt
  | .reflect tgt => pushTerm (out.push 8) tgt
  | .metadata sp => pushTerm (out.push 9) sp
  | .project tgt => pushTerm (out.push 10) tgt
  | .nat v => pushVarNat (out.push 11) v
  | .boolean b => (out.push 12).push (encBoolByte b)
  | .label s => pushStr (out.push 13) s
  | .binary p l r => pushTerm (pushTerm ((out.push 14).push (primTag p)) l) r
  | .extend inh fs => pushFields (pushTerm (out.push 15) inh) fs
  | .record fs => pushFields (out.push 16) fs
  | .get tgt name => pushTerm (pushStr (out.push 17) name) tgt
  | .ifZero v z s => pushTerm (pushTerm (pushTerm (out.push 18) v) z) s
  | .inject lbl pay => pushTerm (pushStr (out.push 19) lbl) pay
  | .case scrut arms => pushFields (pushTerm (out.push 20) scrut) arms
  | .ifBool c t f => pushTerm (pushTerm (pushTerm (out.push 21) c) t) f
  | .perform plan => pushTerm (out.push 22) plan
  | .done v => pushTerm (out.push 23) v
  | .split tgt names fn => pushTerm (pushTerm (pushNames (out.push 24) names) tgt) fn
termination_by structural t => t

def pushFields (out : ByteArray) : List (String × Term) → ByteArray
  | [] => out.push 0
  | (name, body) :: rest => pushFields (pushTerm (pushStr (out.push 1) name) body) rest
termination_by structural fs => fs

def pushTerms (out : ByteArray) : List Term → ByteArray
  | [] => out.push 0
  | t :: rest => pushTerms (pushTerm (out.push 1) t) rest
termination_by structural ts => ts
end

mutual
theorem pushTerm_toList :
    ∀ (t : Term) (out : ByteArray),
      (pushTerm out t).data.toList = out.data.toList ++ encTermSpec t
  | .hole n σ, out => by
    simp [pushTerm, encTermSpec, pushTerms_toList, pushVarNat_toList, List.append_assoc]
  | .bound idx, out => by
    simp [pushTerm, encTermSpec, pushVarNat_toList, List.append_assoc]
  | .lam body, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .app fn arg, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .mix lo hi, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .fix sp inh, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .specification m e, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .prototype sp tgt, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .reflect tgt, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .metadata sp, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .project tgt, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .nat v, out => by
    simp [pushTerm, encTermSpec, pushVarNat_toList, List.append_assoc]
  | .boolean b, out => by
    simp [pushTerm, encTermSpec, List.append_assoc]
  | .label s, out => by
    simp [pushTerm, encTermSpec, pushStr_toList, List.append_assoc]
  | .binary p l r, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .extend inh fs, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, pushFields_toList, List.append_assoc]
  | .record fs, out => by
    simp [pushTerm, encTermSpec, pushFields_toList, List.append_assoc]
  | .get tgt name, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, pushStr_toList, List.append_assoc]
  | .ifZero v z s, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .inject lbl pay, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, pushStr_toList, List.append_assoc]
  | .case scrut arms, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, pushFields_toList, List.append_assoc]
  | .ifBool c t f, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .perform plan, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .done v, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, List.append_assoc]
  | .split tgt names fn, out => by
    simp [pushTerm, encTermSpec, pushTerm_toList, pushNames_toList, List.append_assoc]
termination_by structural t => t

theorem pushFields_toList :
    ∀ (fs : List (String × Term)) (out : ByteArray),
      (pushFields out fs).data.toList = out.data.toList ++ encFieldsSpec fs
  | [], out => by simp [pushFields, encFieldsSpec]
  | (name, body) :: rest, out => by
    simp [pushFields, encFieldsSpec, pushFields_toList, pushTerm_toList, pushStr_toList,
      List.append_assoc]
termination_by structural fs => fs

theorem pushTerms_toList :
    ∀ (ts : List Term) (out : ByteArray),
      (pushTerms out ts).data.toList = out.data.toList ++ encTermsSpec ts
  | [], out => by simp [pushTerms, encTermsSpec]
  | t :: rest, out => by
    simp [pushTerms, encTermsSpec, pushTerms_toList, pushTerm_toList, List.append_assoc]
termination_by structural ts => ts
end

def pushClosure (out : ByteArray) (cl : Closure) : ByteArray :=
  pushAddrs (pushTerm out cl.term) cl.environment

theorem pushClosure_toList (out : ByteArray) (cl : Closure) :
    (pushClosure out cl).data.toList = out.data.toList ++ encClosureSpec cl := by
  simp [pushClosure, encClosureSpec, pushAddrs_toList, pushTerm_toList, List.append_assoc]

def pushValue (out : ByteArray) : RuntimeValue → ByteArray
  | .closure body env => pushAddrs (pushTerm (out.push 0) body) env
  | .natural v => pushVarNat (out.push 1) v
  | .boolean b => (out.push 2).push (encBoolByte b)
  | .label s => pushStr (out.push 3) s
  | .record fs => pushNamedAddrs (out.push 4) fs
  | .specification m e => pushVarNat (pushVarNat (out.push 5) m) e
  | .prototype sp tgt => pushVarNat (pushVarNat (out.push 6) sp) tgt
  | .variant lbl pay => pushVarNat (pushStr (out.push 7) lbl) pay

theorem pushValue_toList (out : ByteArray) (v : RuntimeValue) :
    (pushValue out v).data.toList = out.data.toList ++ encValueSpec v := by
  cases v <;> simp [pushValue, encValueSpec, pushAddrs_toList, pushTerm_toList,
    pushVarNat_toList, pushStr_toList, pushNamedAddrs_toList, List.append_assoc]

def pushCell (out : ByteArray) : Cell → ByteArray
  | .suspended orig => pushClosure (out.push 0) orig
  | .evaluating orig => pushClosure (out.push 1) orig
  | .cached orig val => pushValue (pushClosure (out.push 2) orig) val

theorem pushCell_toList (out : ByteArray) (c : Cell) :
    (pushCell out c).data.toList = out.data.toList ++ encCellSpec c := by
  cases c <;> simp [pushCell, encCellSpec, pushClosure_toList, pushValue_toList,
    List.append_assoc]

def pushFrame (out : ByteArray) (fr : Frame) : ByteArray :=
  out ++ ⟨(encFrameSpec fr).toArray⟩

theorem pushFrame_toList (out : ByteArray) (fr : Frame) :
    (pushFrame out fr).data.toList = out.data.toList ++ encFrameSpec fr := by
  simp [pushFrame, ByteArray.data_append]

def pushControl (out : ByteArray) : Control → ByteArray
  | .evaluate t env => pushAddrs (pushTerm (out.push 0) t) env
  | .enter addr => pushVarNat (out.push 1) addr
  | .blackhole addr => pushVarNat (out.push 2) addr
  | .returned val => pushValue (out.push 3) val
  | .complete val => pushValue (out.push 4) val
  | .refused reason => (out.push 5).push (refusalTag reason)
  | .yielded plan => pushVarNat (out.push 6) plan

theorem pushControl_toList (out : ByteArray) (ctrl : Control) :
    (pushControl out ctrl).data.toList = out.data.toList ++ encControlSpec ctrl := by
  cases ctrl <;> simp [pushControl, encControlSpec, pushAddrs_toList, pushTerm_toList,
    pushVarNat_toList, pushValue_toList, List.append_assoc]

/-- Encode any `Core.Machine.State` (heap of cells, control, continuation frame stack) into its
    canonical `ByteArray` heap image. -/
def encodeHeapImage (s : State) : ByteArray :=
  let b0 := pushVarNat heapImageMagicBytes s.heap.size
  let b1 := s.heap.foldl pushCell b0
  let b2 := pushControl b1 s.control
  let b3 := pushVarNat b2 s.stack.length
  s.stack.foldl pushFrame b3

theorem encodeHeapImage_toList (s : State) :
    (encodeHeapImage s).data.toList = encStateSpec s := by
  unfold encodeHeapImage encStateSpec
  simp only [foldl_push_eq pushFrame encFrameSpec pushFrame_toList,
    pushVarNat_toList, pushControl_toList, ← Array.foldl_toList,
    foldl_push_eq pushCell encCellSpec pushCell_toList,
    heapImageMagicBytes_toList, List.append_assoc]

/-! ### Execution-Tier In-Place `ByteArray` Offset Cursor (`decodeHeapImageExec`) -/

@[inline] private def byteAtImg (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

private theorem drop_byteAtImg (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.data.toList.drop i = byteAtImg b i :: b.data.toList.drop (i + 1) := by
  have hl : i < b.data.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons hl]
  have hg : b.data.toList[i]'hl = b[i]'h := rfl
  rw [hg, byteAtImg, dite_eq_left h]

private theorem drop_nil_of_ge_size (b : ByteArray) (i : Nat) (h : ¬ i < b.size) :
    b.data.toList.drop i = [] := by
  apply List.drop_eq_nil_of_le
  rw [Array.length_toList]
  change b.size ≤ i
  omega

def readVarNatAt : Nat → ByteArray → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, b, off =>
    if off < b.size then
      let byte := byteAtImg b off
      if byte.toNat < 128 then some (byte.toNat, off + 1)
      else
        match readVarNatAt fuel b (off + 1) with
        | some (hi, off') =>
          if 0 < hi then some (hi * 128 + (byte.toNat - 128), off') else none
        | none => none
    else none

theorem readVarNatAt_eq (b : ByteArray) :
    ∀ (fuel off : Nat),
      decVarNat fuel (b.data.toList.drop off) =
        (readVarNatAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2))
  | 0, _ => rfl
  | fuel + 1, off => by
    unfold readVarNatAt
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
      dsimp only [decVarNat]
      by_cases hb : (byteAtImg b off).toNat < 128
      · rw [ite_eq_left hb, ite_eq_left hb]; rfl
      · rw [ite_eq_right hb, ite_eq_right hb, readVarNatAt_eq b fuel (off + 1)]
        cases readVarNatAt fuel b (off + 1) with
        | none => rfl
        | some p =>
          dsimp only [Option.map_some]
          split <;> rfl
    · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl

def readStrAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (String × Nat) :=
  match readVarNatAt fuel b off with
  | none => none
  | some (len, off1) =>
    if len ≤ b.size - off1 then
      match decodeUtf8Bytes (b.extract off1 (off1 + len)) with
      | some s => some (s, off1 + len)
      | none => none
    else none

theorem readStrAt_eq (b : ByteArray) (fuel off : Nat) :
    decStrSpec fuel (b.data.toList.drop off) =
      (readStrAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold decStrSpec readStrAt
  rw [readVarNatAt_eq b fuel off]
  cases readVarNatAt fuel b off with
  | none => rfl
  | some p =>
    obtain ⟨len, off1⟩ := p
    dsimp only [Option.map_some]
    have hlen_drop : (b.data.toList.drop off1).length = b.size - off1 := by
      simp [Array.length_toList]
    rw [hlen_drop]
    by_cases hle : len ≤ b.size - off1
    · rw [ite_eq_left hle, ite_eq_left hle]
      have hext : b.extract off1 (off1 + len) = ⟨((b.data.toList.drop off1).take len).toArray⟩ := by
        apply ByteArray.ext; apply Array.toList_inj.1
        rw [ByteArray.data_extract, Array.toList_extract]
        simp [Nat.add_sub_cancel_left]
      rw [hext]
      cases decodeUtf8Bytes ⟨((b.data.toList.drop off1).take len).toArray⟩ with
      | none => rfl
      | some s => simp [List.drop_drop, Nat.add_comm]
    · rw [ite_eq_right hle, ite_eq_right hle]; rfl

private theorem bind_cursor_eq {α β : Type} {L : List UInt8}
    {mSpec : Option (α × List UInt8)} {mExec : Option (α × Nat)}
    {kSpec : α × List UInt8 → Option (β × List UInt8)}
    {kExec : α × Nat → Option (β × Nat)}
    (hm : mSpec = mExec.map (fun p => (p.1, L.drop p.2)))
    (hk : ∀ a off, kSpec (a, L.drop off) = (kExec (a, off)).map (fun p => (p.1, L.drop p.2))) :
    (mSpec >>= kSpec) = (mExec >>= kExec).map (fun p => (p.1, L.drop p.2)) := by
  rw [hm]
  cases mExec with
  | none => rfl
  | some p => exact hk p.1 p.2

def readNamesNAt (fuel : Nat) (b : ByteArray) : Nat → Nat → List String → Option (List String × Nat)
  | 0, off, acc => some (acc.reverse, off)
  | c + 1, off, acc =>
    match readStrAt fuel b off with
    | none => none
    | some (s, off1) => readNamesNAt fuel b c off1 (s :: acc)

private theorem readNamesNAt_eq (b : ByteArray) (fuel : Nat) :
    ∀ (c off : Nat) (acc : List String),
      (readNamesNAt fuel b c off acc).map (fun p => (p.1, b.data.toList.drop p.2)) =
        (decNamesN fuel c (b.data.toList.drop off)).map (fun p => (acc.reverse ++ p.1, p.2))
  | 0, off, acc => by simp [readNamesNAt, decNamesN]
  | c + 1, off, acc => by
    unfold readNamesNAt decNamesN
    simp only [bind, Option.bind, readStrAt_eq b fuel off]
    cases readStrAt fuel b off with
    | none => rfl
    | some p =>
      obtain ⟨s, off1⟩ := p
      dsimp only [Option.map_some]
      rw [readNamesNAt_eq b fuel c off1 (s :: acc)]
      cases decNamesN fuel c (b.data.toList.drop off1) <;>
        simp [pure, List.reverse_cons, List.append_assoc]

def readNamesAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (List String × Nat) := do
  let (cnt, off1) ← readVarNatAt fuel b off
  readNamesNAt fuel b cnt off1 []

theorem readNamesAt_eq (b : ByteArray) (fuel off : Nat) :
    decNamesSpec fuel (b.data.toList.drop off) =
      (readNamesAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold decNamesSpec readNamesAt
  refine bind_cursor_eq (readVarNatAt_eq b fuel off) fun cnt off1 => ?_
  have h := readNamesNAt_eq b fuel cnt off1 []
  rw [h]; cases hd : decNamesN fuel cnt (b.data.toList.drop off1) <;> simp [hd]

def readAddrsNAt (fuel : Nat) (b : ByteArray) :
    Nat → Nat → List Address → Option (List Address × Nat)
  | 0, off, acc => some (acc.reverse, off)
  | c + 1, off, acc =>
    match readVarNatAt fuel b off with
    | none => none
    | some (a, off1) => readAddrsNAt fuel b c off1 (a :: acc)

private theorem readAddrsNAt_eq (b : ByteArray) (fuel : Nat) :
    ∀ (c off : Nat) (acc : List Address),
      (readAddrsNAt fuel b c off acc).map (fun p => (p.1, b.data.toList.drop p.2)) =
        (decAddrsN fuel c (b.data.toList.drop off)).map (fun p => (acc.reverse ++ p.1, p.2))
  | 0, off, acc => by simp [readAddrsNAt, decAddrsN]
  | c + 1, off, acc => by
    unfold readAddrsNAt decAddrsN
    simp only [bind, Option.bind, readVarNatAt_eq b fuel off]
    cases readVarNatAt fuel b off with
    | none => rfl
    | some p =>
      obtain ⟨a, off1⟩ := p
      dsimp only [Option.map_some]
      rw [readAddrsNAt_eq b fuel c off1 (a :: acc)]
      cases decAddrsN fuel c (b.data.toList.drop off1) <;>
        simp [pure, List.reverse_cons, List.append_assoc]

def readAddrsAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (List Address × Nat) := do
  let (cnt, off1) ← readVarNatAt fuel b off
  readAddrsNAt fuel b cnt off1 []

theorem readAddrsAt_eq (b : ByteArray) (fuel off : Nat) :
    decAddrsSpec fuel (b.data.toList.drop off) =
      (readAddrsAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold decAddrsSpec readAddrsAt
  refine bind_cursor_eq (readVarNatAt_eq b fuel off) fun cnt off1 => ?_
  have h := readAddrsNAt_eq b fuel cnt off1 []
  rw [h]; cases hd : decAddrsN fuel cnt (b.data.toList.drop off1) <;> simp [hd]

def readNamedAddrsNAt (fuel : Nat) (b : ByteArray) :
    Nat → Nat → List (String × Address) → Option (List (String × Address) × Nat)
  | 0, off, acc => some (acc.reverse, off)
  | c + 1, off, acc =>
    match readStrAt fuel b off with
    | none => none
    | some (name, off1) =>
      match readVarNatAt fuel b off1 with
      | none => none
      | some (addr, off2) => readNamedAddrsNAt fuel b c off2 ((name, addr) :: acc)

private theorem readNamedAddrsNAt_eq (b : ByteArray) (fuel : Nat) :
    ∀ (c off : Nat) (acc : List (String × Address)),
      (readNamedAddrsNAt fuel b c off acc).map (fun p => (p.1, b.data.toList.drop p.2)) =
        (decNamedAddrsN fuel c (b.data.toList.drop off)).map (fun p => (acc.reverse ++ p.1, p.2))
  | 0, off, acc => by simp [readNamedAddrsNAt, decNamedAddrsN]
  | c + 1, off, acc => by
    unfold readNamedAddrsNAt decNamedAddrsN
    simp only [bind, Option.bind, readStrAt_eq b fuel off]
    cases readStrAt fuel b off with
    | none => rfl
    | some p =>
      obtain ⟨name, off1⟩ := p
      dsimp only [Option.map_some]
      rw [readVarNatAt_eq b fuel off1]
      cases readVarNatAt fuel b off1 with
      | none => rfl
      | some q =>
        obtain ⟨addr, off2⟩ := q
        dsimp only [Option.map_some]
        rw [readNamedAddrsNAt_eq b fuel c off2 ((name, addr) :: acc)]
        cases decNamedAddrsN fuel c (b.data.toList.drop off2) <;>
          simp [pure, List.reverse_cons, List.append_assoc]

def readNamedAddrsAt (fuel : Nat) (b : ByteArray) (off : Nat) :
    Option (List (String × Address) × Nat) := do
  let (cnt, off1) ← readVarNatAt fuel b off
  readNamedAddrsNAt fuel b cnt off1 []

theorem readNamedAddrsAt_eq (b : ByteArray) (fuel off : Nat) :
    decNamedAddrsSpec fuel (b.data.toList.drop off) =
      (readNamedAddrsAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold decNamedAddrsSpec readNamedAddrsAt
  refine bind_cursor_eq (readVarNatAt_eq b fuel off) fun cnt off1 => ?_
  have h := readNamedAddrsNAt_eq b fuel cnt off1 []
  rw [h]; cases hd : decNamedAddrsN fuel cnt (b.data.toList.drop off1) <;> simp [hd]

mutual
def readTermAt : Nat → ByteArray → Nat → Option (Term × Nat)
  | 0, _, _ => none
  | fuel + 1, b, off =>
    if off < b.size then
      let tag := byteAtImg b off
      let off0 := off + 1
      match tag.toNat with
      | 0 => do
        let (n, o1) ← readVarNatAt fuel b off0
        let (σ, o2) ← readTermsAt fuel b o1
        pure (.hole n σ, o2)
      | 1 => do let (idx, o1) ← readVarNatAt fuel b off0; pure (.bound idx, o1)
      | 2 => do let (body, o1) ← readTermAt fuel b off0; pure (.lam body, o1)
      | 3 => do
        let (fn, o1) ← readTermAt fuel b off0
        let (arg, o2) ← readTermAt fuel b o1
        pure (.app fn arg, o2)
      | 4 => do
        let (lo, o1) ← readTermAt fuel b off0
        let (hi, o2) ← readTermAt fuel b o1
        pure (.mix lo hi, o2)
      | 5 => do
        let (sp, o1) ← readTermAt fuel b off0
        let (inh, o2) ← readTermAt fuel b o1
        pure (.fix sp inh, o2)
      | 6 => do
        let (m, o1) ← readTermAt fuel b off0
        let (e, o2) ← readTermAt fuel b o1
        pure (.specification m e, o2)
      | 7 => do
        let (sp, o1) ← readTermAt fuel b off0
        let (tgt, o2) ← readTermAt fuel b o1
        pure (.prototype sp tgt, o2)
      | 8 => do let (tgt, o1) ← readTermAt fuel b off0; pure (.reflect tgt, o1)
      | 9 => do let (sp, o1) ← readTermAt fuel b off0; pure (.metadata sp, o1)
      | 10 => do let (tgt, o1) ← readTermAt fuel b off0; pure (.project tgt, o1)
      | 11 => do let (v, o1) ← readVarNatAt fuel b off0; pure (.nat v, o1)
      | 12 =>
        if off0 < b.size then do
          let bv ← decBoolByte (byteAtImg b off0)
          pure (.boolean bv, off0 + 1)
        else none
      | 13 => do let (s, o1) ← readStrAt fuel b off0; pure (.label s, o1)
      | 14 =>
        if off0 < b.size then do
          let p ← primOfTag (byteAtImg b off0)
          let (l, o1) ← readTermAt fuel b (off0 + 1)
          let (r, o2) ← readTermAt fuel b o1
          pure (.binary p l r, o2)
        else none
      | 15 => do
        let (inh, o1) ← readTermAt fuel b off0
        let (fs, o2) ← readFieldsAt fuel b o1
        pure (.extend inh fs, o2)
      | 16 => do let (fs, o1) ← readFieldsAt fuel b off0; pure (.record fs, o1)
      | 17 => do
        let (name, o1) ← readStrAt fuel b off0
        let (tgt, o2) ← readTermAt fuel b o1
        pure (.get tgt name, o2)
      | 18 => do
        let (v, o1) ← readTermAt fuel b off0
        let (z, o2) ← readTermAt fuel b o1
        let (s, o3) ← readTermAt fuel b o2
        pure (.ifZero v z s, o3)
      | 19 => do
        let (lbl, o1) ← readStrAt fuel b off0
        let (pay, o2) ← readTermAt fuel b o1
        pure (.inject lbl pay, o2)
      | 20 => do
        let (scrut, o1) ← readTermAt fuel b off0
        let (arms, o2) ← readFieldsAt fuel b o1
        pure (.case scrut arms, o2)
      | 21 => do
        let (c, o1) ← readTermAt fuel b off0
        let (wt, o2) ← readTermAt fuel b o1
        let (wf, o3) ← readTermAt fuel b o2
        pure (.ifBool c wt wf, o3)
      | 22 => do let (plan, o1) ← readTermAt fuel b off0; pure (.perform plan, o1)
      | 23 => do let (v, o1) ← readTermAt fuel b off0; pure (.done v, o1)
      | 24 => do
        let (names, o1) ← readNamesAt fuel b off0
        let (tgt, o2) ← readTermAt fuel b o1
        let (fn, o3) ← readTermAt fuel b o2
        pure (.split tgt names fn, o3)
      | _ => none
    else none

def readFieldsAt : Nat → ByteArray → Nat → Option (List (String × Term) × Nat)
  | 0, _, _ => none
  | fuel + 1, b, off =>
    if off < b.size then
      match (byteAtImg b off).toNat with
      | 0 => some ([], off + 1)
      | 1 => do
        let (name, o1) ← readStrAt fuel b (off + 1)
        let (body, o2) ← readTermAt fuel b o1
        let (others, o3) ← readFieldsAt fuel b o2
        pure ((name, body) :: others, o3)
      | _ => none
    else none

def readTermsAt : Nat → ByteArray → Nat → Option (List Term × Nat)
  | 0, _, _ => none
  | fuel + 1, b, off =>
    if off < b.size then
      match (byteAtImg b off).toNat with
      | 0 => some ([], off + 1)
      | 1 => do
        let (t, o1) ← readTermAt fuel b (off + 1)
        let (others, o2) ← readTermsAt fuel b o1
        pure (t :: others, o2)
      | _ => none
    else none
end

mutual
theorem readTermAt_eq (b : ByteArray) :
    ∀ (fuel off : Nat),
      decTermSpec fuel (b.data.toList.drop off) =
        (readTermAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2))
  | 0, _ => rfl
  | fuel + 1, off => by
    unfold readTermAt
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
      dsimp only [decTermSpec]
      split
      · refine bind_cursor_eq (readVarNatAt_eq b fuel _) fun n o1 =>
          bind_cursor_eq (readTermsAt_eq b fuel o1) fun σ o2 => rfl
      · exact bind_cursor_eq (readVarNatAt_eq b fuel _) fun idx o1 => rfl
      · exact bind_cursor_eq (readTermAt_eq b fuel _) fun body o1 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun fn o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun arg o2 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun lo o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun hi o2 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun sp o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun inh o2 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun m o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun e o2 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun sp o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun tgt o2 => rfl
      · exact bind_cursor_eq (readTermAt_eq b fuel _) fun tgt o1 => rfl
      · exact bind_cursor_eq (readTermAt_eq b fuel _) fun sp o1 => rfl
      · exact bind_cursor_eq (readTermAt_eq b fuel _) fun tgt o1 => rfl
      · exact bind_cursor_eq (readVarNatAt_eq b fuel _) fun v o1 => rfl
      · by_cases h1 : off + 1 < b.size
        · rw [ite_eq_left h1, drop_byteAtImg b (off + 1) h1]; dsimp only
          cases decBoolByte (byteAtImg b (off + 1)) <;> rfl
        · rw [ite_eq_right h1, drop_nil_of_ge_size b (off + 1) h1]; rfl
      · exact bind_cursor_eq (readStrAt_eq b fuel _) fun s o1 => rfl
      · by_cases h1 : off + 1 < b.size
        · rw [ite_eq_left h1, drop_byteAtImg b (off + 1) h1]; dsimp only
          cases primOfTag (byteAtImg b (off + 1)) with
          | none => rfl
          | some p =>
            dsimp only [bind, Option.bind]
            refine bind_cursor_eq (readTermAt_eq b fuel (off + 1 + 1)) fun l o1 =>
              bind_cursor_eq (readTermAt_eq b fuel o1) fun r o2 => rfl
        · rw [ite_eq_right h1, drop_nil_of_ge_size b (off + 1) h1]; rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun inh o1 =>
          bind_cursor_eq (readFieldsAt_eq b fuel o1) fun fs o2 => rfl
      · exact bind_cursor_eq (readFieldsAt_eq b fuel _) fun fs o1 => rfl
      · refine bind_cursor_eq (readStrAt_eq b fuel _) fun name o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun tgt o2 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun v o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun z o2 =>
          bind_cursor_eq (readTermAt_eq b fuel o2) fun s o3 => rfl
      · refine bind_cursor_eq (readStrAt_eq b fuel _) fun lbl o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun pay o2 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun scrut o1 =>
          bind_cursor_eq (readFieldsAt_eq b fuel o1) fun arms o2 => rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun c o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun wt o2 =>
          bind_cursor_eq (readTermAt_eq b fuel o2) fun wf o3 => rfl
      · exact bind_cursor_eq (readTermAt_eq b fuel _) fun plan o1 => rfl
      · exact bind_cursor_eq (readTermAt_eq b fuel _) fun v o1 => rfl
      · refine bind_cursor_eq (readNamesAt_eq b fuel _) fun names o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun tgt o2 =>
          bind_cursor_eq (readTermAt_eq b fuel o2) fun fn o3 => rfl
      · rfl
    · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl

theorem readFieldsAt_eq (b : ByteArray) :
    ∀ (fuel off : Nat),
      decFieldsSpec fuel (b.data.toList.drop off) =
        (readFieldsAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2))
  | 0, _ => rfl
  | fuel + 1, off => by
    unfold readFieldsAt
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
      dsimp only [decFieldsSpec]
      split
      · rfl
      · refine bind_cursor_eq (readStrAt_eq b fuel _) fun name o1 =>
          bind_cursor_eq (readTermAt_eq b fuel o1) fun body o2 =>
          bind_cursor_eq (readFieldsAt_eq b fuel o2) fun others o3 => rfl
      · rfl
    · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl

theorem readTermsAt_eq (b : ByteArray) :
    ∀ (fuel off : Nat),
      decTermsSpec fuel (b.data.toList.drop off) =
        (readTermsAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2))
  | 0, _ => rfl
  | fuel + 1, off => by
    unfold readTermsAt
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
      dsimp only [decTermsSpec]
      split
      · rfl
      · refine bind_cursor_eq (readTermAt_eq b fuel _) fun t o1 =>
          bind_cursor_eq (readTermsAt_eq b fuel o1) fun others o2 => rfl
      · rfl
    · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl
end

def readClosureAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (Closure × Nat) := do
  let (t, o1) ← readTermAt fuel b off
  let (env, o2) ← readAddrsAt fuel b o1
  pure (⟨t, env⟩, o2)

theorem readClosureAt_eq (b : ByteArray) (fuel off : Nat) :
    decClosureSpec fuel (b.data.toList.drop off) =
      (readClosureAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) :=
  bind_cursor_eq (readTermAt_eq b fuel off) fun _ o1 =>
    bind_cursor_eq (readAddrsAt_eq b fuel o1) fun _ _ => rfl

def readValueAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (RuntimeValue × Nat) :=
  if off < b.size then
    let off0 := off + 1
    match (byteAtImg b off).toNat with
    | 0 => do
      let (body, o1) ← readTermAt fuel b off0
      let (env, o2) ← readAddrsAt fuel b o1
      pure (.closure body env, o2)
    | 1 => do let (v, o1) ← readVarNatAt fuel b off0; pure (.natural v, o1)
    | 2 =>
      if off0 < b.size then do
        let bv ← decBoolByte (byteAtImg b off0)
        pure (.boolean bv, off0 + 1)
      else none
    | 3 => do let (s, o1) ← readStrAt fuel b off0; pure (.label s, o1)
    | 4 => do let (fs, o1) ← readNamedAddrsAt fuel b off0; pure (.record fs, o1)
    | 5 => do
      let (m, o1) ← readVarNatAt fuel b off0
      let (e, o2) ← readVarNatAt fuel b o1
      pure (.specification m e, o2)
    | 6 => do
      let (sp, o1) ← readVarNatAt fuel b off0
      let (tgt, o2) ← readVarNatAt fuel b o1
      pure (.prototype sp tgt, o2)
    | 7 => do
      let (lbl, o1) ← readStrAt fuel b off0
      let (pay, o2) ← readVarNatAt fuel b o1
      pure (.variant lbl pay, o2)
    | _ => none
  else none

theorem readValueAt_eq (b : ByteArray) (fuel off : Nat) :
    decValueSpec fuel (b.data.toList.drop off) =
      (readValueAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold readValueAt
  by_cases hlt : off < b.size
  · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
    dsimp only [decValueSpec]
    split
    · refine bind_cursor_eq (readTermAt_eq b fuel _) fun body o1 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o1) fun env o2 => rfl
    · exact bind_cursor_eq (readVarNatAt_eq b fuel _) fun v o1 => rfl
    · by_cases h1 : off + 1 < b.size
      · rw [ite_eq_left h1, drop_byteAtImg b (off + 1) h1]; dsimp only
        cases decBoolByte (byteAtImg b (off + 1)) <;> rfl
      · rw [ite_eq_right h1, drop_nil_of_ge_size b (off + 1) h1]; rfl
    · exact bind_cursor_eq (readStrAt_eq b fuel _) fun s o1 => rfl
    · exact bind_cursor_eq (readNamedAddrsAt_eq b fuel _) fun fs o1 => rfl
    · refine bind_cursor_eq (readVarNatAt_eq b fuel _) fun m o1 =>
        bind_cursor_eq (readVarNatAt_eq b fuel o1) fun e o2 => rfl
    · refine bind_cursor_eq (readVarNatAt_eq b fuel _) fun sp o1 =>
        bind_cursor_eq (readVarNatAt_eq b fuel o1) fun tgt o2 => rfl
    · refine bind_cursor_eq (readStrAt_eq b fuel _) fun lbl o1 =>
        bind_cursor_eq (readVarNatAt_eq b fuel o1) fun pay o2 => rfl
    · rfl
  · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl

def readCellAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (Cell × Nat) :=
  if off < b.size then
    let off0 := off + 1
    match (byteAtImg b off).toNat with
    | 0 => do let (orig, o1) ← readClosureAt fuel b off0; pure (.suspended orig, o1)
    | 1 => do let (orig, o1) ← readClosureAt fuel b off0; pure (.evaluating orig, o1)
    | 2 => do
      let (orig, o1) ← readClosureAt fuel b off0
      let (val, o2) ← readValueAt fuel b o1
      pure (.cached orig val, o2)
    | _ => none
  else none

theorem readCellAt_eq (b : ByteArray) (fuel off : Nat) :
    decCellSpec fuel (b.data.toList.drop off) =
      (readCellAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold readCellAt
  by_cases hlt : off < b.size
  · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
    dsimp only [decCellSpec]
    split
    · exact bind_cursor_eq (readClosureAt_eq b fuel _) fun _ _ => rfl
    · exact bind_cursor_eq (readClosureAt_eq b fuel _) fun _ _ => rfl
    · refine bind_cursor_eq (readClosureAt_eq b fuel _) fun _ o1 =>
        bind_cursor_eq (readValueAt_eq b fuel o1) fun _ _ => rfl
    · rfl
  · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl

def readFrameAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (Frame × Nat) :=
  if off < b.size then
    let off0 := off + 1
    match (byteAtImg b off).toNat with
    | 0 => do
      let (t, o1) ← readTermAt fuel b off0
      let (env, o2) ← readAddrsAt fuel b o1
      pure (.argument t env, o2)
    | 1 => do let (addr, o1) ← readVarNatAt fuel b off0; pure (.update addr, o1)
    | 2 => do let (name, o1) ← readStrAt fuel b off0; pure (.field name, o1)
    | 3 => some (.reflect, off0)
    | 4 => some (.metadata, off0)
    | 5 => some (.project, off0)
    | 6 => do
      let (fs, o1) ← readFieldsAt fuel b off0
      let (env, o2) ← readAddrsAt fuel b o1
      pure (.extend fs env, o2)
    | 7 => do
      let (z, o1) ← readTermAt fuel b off0
      let (s, o2) ← readTermAt fuel b o1
      let (env, o3) ← readAddrsAt fuel b o2
      pure (.condition z s env, o3)
    | 8 =>
      if off0 < b.size then do
        let p ← primOfTag (byteAtImg b off0)
        let (r, o1) ← readTermAt fuel b (off0 + 1)
        let (env, o2) ← readAddrsAt fuel b o1
        pure (.binaryLeft p r env, o2)
      else none
    | 9 =>
      if off0 < b.size then do
        let p ← primOfTag (byteAtImg b off0)
        let (l, o1) ← readValueAt fuel b (off0 + 1)
        pure (.binaryRight p l, o1)
      else none
    | 10 => do
      let (arms, o1) ← readFieldsAt fuel b off0
      let (env, o2) ← readAddrsAt fuel b o1
      pure (.case arms env, o2)
    | 11 => do
      let (wt, o1) ← readTermAt fuel b off0
      let (wf, o2) ← readTermAt fuel b o1
      let (env, o3) ← readAddrsAt fuel b o2
      pure (.ifBool wt wf env, o3)
    | 12 => do
      let (names, o1) ← readNamesAt fuel b off0
      let (fn, o2) ← readTermAt fuel b o1
      let (env, o3) ← readAddrsAt fuel b o2
      pure (.split names fn env, o3)
    | _ => none
  else none

theorem readFrameAt_eq (b : ByteArray) (fuel off : Nat) :
    decFrameSpec fuel (b.data.toList.drop off) =
      (readFrameAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold readFrameAt
  by_cases hlt : off < b.size
  · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
    dsimp only [decFrameSpec]
    split
    · refine bind_cursor_eq (readTermAt_eq b fuel _) fun t o1 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o1) fun env o2 => rfl
    · exact bind_cursor_eq (readVarNatAt_eq b fuel _) fun _ _ => rfl
    · exact bind_cursor_eq (readStrAt_eq b fuel _) fun _ _ => rfl
    · rfl
    · rfl
    · rfl
    · refine bind_cursor_eq (readFieldsAt_eq b fuel _) fun fs o1 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o1) fun env o2 => rfl
    · refine bind_cursor_eq (readTermAt_eq b fuel _) fun z o1 =>
        bind_cursor_eq (readTermAt_eq b fuel o1) fun s o2 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o2) fun env o3 => rfl
    · by_cases h1 : off + 1 < b.size
      · rw [ite_eq_left h1, drop_byteAtImg b (off + 1) h1]; dsimp only
        cases primOfTag (byteAtImg b (off + 1)) with
        | none => rfl
        | some p =>
          dsimp only [bind, Option.bind]
          refine bind_cursor_eq (readTermAt_eq b fuel (off + 1 + 1)) fun r o1 =>
            bind_cursor_eq (readAddrsAt_eq b fuel o1) fun env o2 => rfl
      · rw [ite_eq_right h1, drop_nil_of_ge_size b (off + 1) h1]; rfl
    · by_cases h1 : off + 1 < b.size
      · rw [ite_eq_left h1, drop_byteAtImg b (off + 1) h1]; dsimp only
        cases primOfTag (byteAtImg b (off + 1)) with
        | none => rfl
        | some p =>
          dsimp only [bind, Option.bind]
          exact bind_cursor_eq (readValueAt_eq b fuel (off + 1 + 1)) fun l o1 => rfl
      · rw [ite_eq_right h1, drop_nil_of_ge_size b (off + 1) h1]; rfl
    · refine bind_cursor_eq (readFieldsAt_eq b fuel _) fun arms o1 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o1) fun env o2 => rfl
    · refine bind_cursor_eq (readTermAt_eq b fuel _) fun wt o1 =>
        bind_cursor_eq (readTermAt_eq b fuel o1) fun wf o2 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o2) fun env o3 => rfl
    · refine bind_cursor_eq (readNamesAt_eq b fuel _) fun names o1 =>
        bind_cursor_eq (readTermAt_eq b fuel o1) fun fn o2 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o2) fun env o3 => rfl
    · rfl
  · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl

def readControlAt (fuel : Nat) (b : ByteArray) (off : Nat) : Option (Control × Nat) :=
  if off < b.size then
    let off0 := off + 1
    match (byteAtImg b off).toNat with
    | 0 => do
      let (t, o1) ← readTermAt fuel b off0
      let (env, o2) ← readAddrsAt fuel b o1
      pure (.evaluate t env, o2)
    | 1 => do let (addr, o1) ← readVarNatAt fuel b off0; pure (.enter addr, o1)
    | 2 => do let (addr, o1) ← readVarNatAt fuel b off0; pure (.blackhole addr, o1)
    | 3 => do let (val, o1) ← readValueAt fuel b off0; pure (.returned val, o1)
    | 4 => do let (val, o1) ← readValueAt fuel b off0; pure (.complete val, o1)
    | 5 =>
      if off0 < b.size then do
        let reason ← refusalOfTag (byteAtImg b off0)
        pure (.refused reason, off0 + 1)
      else none
    | 6 => do let (plan, o1) ← readVarNatAt fuel b off0; pure (.yielded plan, o1)
    | _ => none
  else none

theorem readControlAt_eq (b : ByteArray) (fuel off : Nat) :
    decControlSpec fuel (b.data.toList.drop off) =
      (readControlAt fuel b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  unfold readControlAt
  by_cases hlt : off < b.size
  · rw [ite_eq_left hlt, drop_byteAtImg b off hlt]
    dsimp only [decControlSpec]
    split
    · refine bind_cursor_eq (readTermAt_eq b fuel _) fun t o1 =>
        bind_cursor_eq (readAddrsAt_eq b fuel o1) fun env o2 => rfl
    · exact bind_cursor_eq (readVarNatAt_eq b fuel _) fun _ _ => rfl
    · exact bind_cursor_eq (readVarNatAt_eq b fuel _) fun _ _ => rfl
    · exact bind_cursor_eq (readValueAt_eq b fuel _) fun _ _ => rfl
    · exact bind_cursor_eq (readValueAt_eq b fuel _) fun _ _ => rfl
    · by_cases h1 : off + 1 < b.size
      · rw [ite_eq_left h1, drop_byteAtImg b (off + 1) h1]; dsimp only
        cases refusalOfTag (byteAtImg b (off + 1)) <;> rfl
      · rw [ite_eq_right h1, drop_nil_of_ge_size b (off + 1) h1]; rfl
    · exact bind_cursor_eq (readVarNatAt_eq b fuel _) fun _ _ => rfl
    · rfl
  · rw [ite_eq_right hlt, drop_nil_of_ge_size b off hlt]; rfl

def readManyAt {α : Type} (rd : Nat → Option (α × Nat)) :
    Nat → Nat → List α → Option (List α × Nat)
  | 0, off, acc => some (acc.reverse, off)
  | c + 1, off, acc =>
    match rd off with
    | none => none
    | some (x, off1) => readManyAt rd c off1 (x :: acc)

private theorem readManyAt_eq {α : Type} {L : List UInt8}
    {dec : List UInt8 → Option (α × List UInt8)} {rd : Nat → Option (α × Nat)}
    (href : ∀ off, dec (L.drop off) = (rd off).map (fun p => (p.1, L.drop p.2))) :
    ∀ (c off : Nat) (acc : List α),
      (readManyAt rd c off acc).map (fun p => (p.1, L.drop p.2)) =
        (decManySpec dec c (L.drop off)).map (fun p => (acc.reverse ++ p.1, p.2))
  | 0, off, acc => by simp [readManyAt, decManySpec]
  | c + 1, off, acc => by
    unfold readManyAt decManySpec
    simp only [bind, Option.bind, href off]
    cases rd off with
    | none => rfl
    | some p =>
      obtain ⟨x, off1⟩ := p
      dsimp only [Option.map_some]
      rw [readManyAt_eq href c off1 (x :: acc)]
      cases decManySpec dec c (L.drop off1) <;>
        simp [pure, List.reverse_cons, List.append_assoc]

private theorem readManyAt_bound {α : Type} {sz : Nat} {rd : Nat → Option (α × Nat)}
    (hb : ∀ off x off1, rd off = some (x, off1) → off ≤ off1 ∧ off1 ≤ sz) :
    ∀ (c off : Nat) (acc xs : List α) (off' : Nat),
      off ≤ sz → readManyAt rd c off acc = some (xs, off') → off ≤ off' ∧ off' ≤ sz
  | 0, off, acc, xs, off', hoff, h => by
    simp only [readManyAt, Option.some.injEq, Prod.mk.injEq] at h; omega
  | c + 1, off, acc, xs, off', _, h => by
    unfold readManyAt at h
    cases hrd : rd off with
    | none => simp [hrd] at h
    | some p =>
      obtain ⟨x, o1⟩ := p; simp only [hrd] at h
      have h1 := hb off x o1 hrd
      have h2 := readManyAt_bound hb c o1 _ xs off' h1.2 h
      omega

private theorem readVarNatAt_bound (b : ByteArray) :
    ∀ (fuel off n off1 : Nat), readVarNatAt fuel b off = some (n, off1) → off1 ≤ b.size
  | 0, _, _, _, h => by simp [readVarNatAt] at h
  | fuel + 1, off, n, off1, h => by
    unfold readVarNatAt at h
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt] at h
      dsimp only at h
      by_cases hb : (byteAtImg b off).toNat < 128
      · rw [ite_eq_left hb] at h; cases h; omega
      · rw [ite_eq_right hb] at h
        cases hr : readVarNatAt fuel b (off + 1) with
        | none => simp [hr] at h
        | some p =>
          rw [hr] at h; dsimp only at h
          by_cases hp0 : 0 < p.1
          · rw [ite_eq_left hp0] at h
            obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
            exact readVarNatAt_bound b fuel (off + 1) p.1 p.2 hr
          · rw [ite_eq_right hp0] at h; cases h
    · rw [ite_eq_right hlt] at h; cases h

private theorem readStrAt_bound (b : ByteArray) {fuel off : Nat} {s : String} {off1 : Nat}
    (h : readStrAt fuel b off = some (s, off1)) : off1 ≤ b.size := by
  unfold readStrAt at h
  cases hr : readVarNatAt fuel b off with
  | none => simp [hr] at h
  | some p =>
    obtain ⟨len, o1⟩ := p
    have ho1 := readVarNatAt_bound b fuel off len o1 hr
    rw [hr] at h; dsimp only at h
    by_cases hle : len ≤ b.size - o1
    · rw [ite_eq_left hle] at h
      cases hdec : decodeUtf8Bytes (b.extract o1 (o1 + len)) with
      | none => simp [hdec] at h
      | some str =>
        rw [hdec] at h; cases h; omega
    · rw [ite_eq_right hle] at h; cases h

private theorem readAddrsNAt_bound (b : ByteArray) (fuel : Nat) :
    ∀ (c off : Nat) (acc xs : List Address) (off1 : Nat),
      off ≤ b.size → readAddrsNAt fuel b c off acc = some (xs, off1) → off1 ≤ b.size
  | 0, off, acc, xs, off1, hoff, h => by simp [readAddrsNAt] at h; omega
  | c + 1, off, acc, xs, off1, _, h => by
    unfold readAddrsNAt at h
    cases hr : readVarNatAt fuel b off with
    | none => simp [hr] at h
    | some p =>
      rw [hr] at h
      exact readAddrsNAt_bound b fuel c p.2 _ xs off1 (readVarNatAt_bound b fuel off p.1 p.2 hr) h

private theorem readAddrsAt_bound (b : ByteArray) {fuel off : Nat} {xs : List Address} {off1 : Nat}
    (h : readAddrsAt fuel b off = some (xs, off1)) : off1 ≤ b.size := by
  unfold readAddrsAt at h; simp only [bind, Option.bind] at h
  cases hr : readVarNatAt fuel b off with
  | none => simp [hr] at h
  | some p => rw [hr] at h; dsimp only at h; exact readAddrsNAt_bound b fuel p.1 p.2 [] xs off1 (readVarNatAt_bound b fuel off p.1 p.2 hr) h

private theorem readNamedAddrsNAt_bound (b : ByteArray) (fuel : Nat) :
    ∀ (c off : Nat) (acc xs : List (String × Address)) (off1 : Nat),
      off ≤ b.size → readNamedAddrsNAt fuel b c off acc = some (xs, off1) → off1 ≤ b.size
  | 0, off, acc, xs, off1, hoff, h => by simp [readNamedAddrsNAt] at h; omega
  | c + 1, off, acc, xs, off1, _, h => by
    unfold readNamedAddrsNAt at h
    cases hs : readStrAt fuel b off with
    | none => simp [hs] at h
    | some p =>
      rw [hs] at h; dsimp only at h
      cases ha : readVarNatAt fuel b p.2 with
      | none => simp [ha] at h
      | some q =>
        rw [ha] at h; dsimp only at h
        exact readNamedAddrsNAt_bound b fuel c q.2 _ xs off1
          (readVarNatAt_bound b fuel p.2 q.1 q.2 ha) h

private theorem readNamedAddrsAt_bound (b : ByteArray) {fuel off : Nat}
    {xs : List (String × Address)} {off1 : Nat}
    (h : readNamedAddrsAt fuel b off = some (xs, off1)) : off1 ≤ b.size := by
  unfold readNamedAddrsAt at h; simp only [bind, Option.bind] at h
  cases hr : readVarNatAt fuel b off with
  | none => simp [hr] at h
  | some p =>
    rw [hr] at h; dsimp only at h
    exact readNamedAddrsNAt_bound b fuel p.1 p.2 [] xs off1
      (readVarNatAt_bound b fuel off p.1 p.2 hr) h

private theorem readNamesNAt_bound (b : ByteArray) (fuel : Nat) :
    ∀ (c off : Nat) (acc xs : List String) (off1 : Nat),
      off ≤ b.size → readNamesNAt fuel b c off acc = some (xs, off1) → off1 ≤ b.size
  | 0, off, acc, xs, off1, hoff, h => by simp [readNamesNAt] at h; omega
  | c + 1, off, acc, xs, off1, _, h => by
    unfold readNamesNAt at h
    cases hs : readStrAt fuel b off with
    | none => simp [hs] at h
    | some p => rw [hs] at h; exact readNamesNAt_bound b fuel c p.2 _ xs off1 (readStrAt_bound b hs) h

private theorem readNamesAt_bound (b : ByteArray) {fuel off : Nat} {xs : List String} {off1 : Nat}
    (h : readNamesAt fuel b off = some (xs, off1)) : off1 ≤ b.size := by
  unfold readNamesAt at h; simp only [bind, Option.bind] at h
  cases hr : readVarNatAt fuel b off with
  | none => simp [hr] at h
  | some p =>
    rw [hr] at h; dsimp only at h
    exact readNamesNAt_bound b fuel p.1 p.2 [] xs off1 (readVarNatAt_bound b fuel off p.1 p.2 hr) h

private theorem bind_bound {α β : Type} {sz : Nat}
    {m : Option (α × Nat)} {k : α × Nat → Option (β × Nat)} {y : β} {off' : Nat}
    (h : (m >>= k) = some (y, off'))
    (hk : ∀ a o1, m = some (a, o1) → k (a, o1) = some (y, off') → off' ≤ sz) : off' ≤ sz := by
  cases hm : m with
  | none => simp [hm, bind, Option.bind] at h
  | some p =>
    rcases p with ⟨a, o1⟩
    simp only [hm, bind, Option.bind] at h
    exact hk a o1 hm h

private theorem pure_bound {α : Type} {sz o1 off' : Nat} {x y : α}
    (ho1 : o1 ≤ sz) (h : (pure (x, o1) : Option (α × Nat)) = some (y, off')) : off' ≤ sz := by
  cases h; exact ho1

mutual
private theorem readTermAt_bound (b : ByteArray) :
    ∀ (fuel off : Nat) (t : Term) (off1 : Nat),
      readTermAt fuel b off = some (t, off1) → off1 ≤ b.size
  | 0, _, _, _, h => by simp [readTermAt] at h
  | fuel + 1, off, t, off1, h => by
    unfold readTermAt at h
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt] at h; dsimp only at h
      split at h
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun σ o2 h2 hp => pure_bound (readTermsAt_bound b fuel o1 σ o2 h2) hp
      · exact bind_bound h fun v o1 h1 hp => pure_bound (readVarNatAt_bound b fuel _ v o1 h1) hp
      · exact bind_bound h fun x o1 h1 hp => pure_bound (readTermAt_bound b fuel _ x o1 h1) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp
      · exact bind_bound h fun x o1 h1 hp => pure_bound (readTermAt_bound b fuel _ x o1 h1) hp
      · exact bind_bound h fun x o1 h1 hp => pure_bound (readTermAt_bound b fuel _ x o1 h1) hp
      · exact bind_bound h fun x o1 h1 hp => pure_bound (readTermAt_bound b fuel _ x o1 h1) hp
      · exact bind_bound h fun v o1 h1 hp => pure_bound (readVarNatAt_bound b fuel _ v o1 h1) hp
      · by_cases h1 : off + 1 < b.size
        · rw [ite_eq_left h1] at h; cases hb : decBoolByte (byteAtImg b (off + 1)) <;> simp [hb] at h; omega
        · rw [ite_eq_right h1] at h; cases h
      · exact bind_bound h fun _ o1 h1 hp => pure_bound (readStrAt_bound b h1) hp
      · by_cases h1 : off + 1 < b.size
        · rw [ite_eq_left h1] at h
          cases hp : primOfTag (byteAtImg b (off + 1)) with
          | none => simp [hp, bind, Option.bind] at h
          | some _ =>
            rw [hp] at h; dsimp only [bind, Option.bind] at h
            exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp' => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp'
        · rw [ite_eq_right h1] at h; cases h
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun fs o2 h2 hp => pure_bound (readFieldsAt_bound b fuel o1 fs o2 h2) hp
      · exact bind_bound h fun fs o1 h1 hp => pure_bound (readFieldsAt_bound b fuel _ fs o1 h1) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp
      · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ o2 _ h'' => bind_bound h'' fun x o3 h3 hp => pure_bound (readTermAt_bound b fuel o2 x o3 h3) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun x o2 h2 hp => pure_bound (readTermAt_bound b fuel o1 x o2 h2) hp
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun fs o2 h2 hp => pure_bound (readFieldsAt_bound b fuel o1 fs o2 h2) hp
      · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ o2 _ h'' => bind_bound h'' fun x o3 h3 hp => pure_bound (readTermAt_bound b fuel o2 x o3 h3) hp
      · exact bind_bound h fun x o1 h1 hp => pure_bound (readTermAt_bound b fuel _ x o1 h1) hp
      · exact bind_bound h fun x o1 h1 hp => pure_bound (readTermAt_bound b fuel _ x o1 h1) hp
      · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ o2 _ h'' => bind_bound h'' fun x o3 h3 hp => pure_bound (readTermAt_bound b fuel o2 x o3 h3) hp
      · cases h
    · rw [ite_eq_right hlt] at h; cases h

private theorem readFieldsAt_bound (b : ByteArray) :
    ∀ (fuel off : Nat) (fs : List (String × Term)) (off1 : Nat),
      readFieldsAt fuel b off = some (fs, off1) → off1 ≤ b.size
  | 0, _, _, _, h => by simp [readFieldsAt] at h
  | fuel + 1, off, fs, off1, h => by
    unfold readFieldsAt at h
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt] at h; dsimp only at h
      split at h
      · cases h; omega
      · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ o2 _ h'' => bind_bound h'' fun xs o3 h3 hp => pure_bound (readFieldsAt_bound b fuel o2 xs o3 h3) hp
      · cases h
    · rw [ite_eq_right hlt] at h; cases h

private theorem readTermsAt_bound (b : ByteArray) :
    ∀ (fuel off : Nat) (ts : List Term) (off1 : Nat),
      readTermsAt fuel b off = some (ts, off1) → off1 ≤ b.size
  | 0, _, _, _, h => by simp [readTermsAt] at h
  | fuel + 1, off, ts, off1, h => by
    unfold readTermsAt at h
    by_cases hlt : off < b.size
    · rw [ite_eq_left hlt] at h; dsimp only at h
      split at h
      · cases h; omega
      · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun xs o2 h2 hp => pure_bound (readTermsAt_bound b fuel o1 xs o2 h2) hp
      · cases h
    · rw [ite_eq_right hlt] at h; cases h
end

private theorem readValueAt_bound (b : ByteArray) {fuel off : Nat} {v : RuntimeValue} {off1 : Nat}
    (h : readValueAt fuel b off = some (v, off1)) : off1 ≤ b.size := by
  unfold readValueAt at h
  by_cases hlt : off < b.size
  · rw [ite_eq_left hlt] at h; dsimp only at h
    split at h
    · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ h2 hp => pure_bound (readAddrsAt_bound b h2) hp
    · exact bind_bound h fun n o1 h1 hp => pure_bound (readVarNatAt_bound b fuel _ n o1 h1) hp
    · by_cases h1 : off + 1 < b.size
      · rw [ite_eq_left h1] at h; cases hb : decBoolByte (byteAtImg b (off + 1)) <;> simp [hb] at h; omega
      · rw [ite_eq_right h1] at h; cases h
    · exact bind_bound h fun _ _ h1 hp => pure_bound (readStrAt_bound b h1) hp
    · exact bind_bound h fun _ _ h1 hp => pure_bound (readNamedAddrsAt_bound b h1) hp
    · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun e o2 h2 hp => pure_bound (readVarNatAt_bound b fuel o1 e o2 h2) hp
    · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun t o2 h2 hp => pure_bound (readVarNatAt_bound b fuel o1 t o2 h2) hp
    · exact bind_bound h fun _ o1 _ h' => bind_bound h' fun p o2 h2 hp => pure_bound (readVarNatAt_bound b fuel o1 p o2 h2) hp
    · cases h
  · rw [ite_eq_right hlt] at h; cases h

private theorem readFrameAt_bound (b : ByteArray) {fuel off : Nat} {fr : Frame} {off1 : Nat}
    (h : readFrameAt fuel b off = some (fr, off1)) : off ≤ off1 ∧ off1 ≤ b.size := by
  have hd := readFrameAt_eq b fuel off
  rw [h] at hd; dsimp only [Option.map_some] at hd
  have hs := decFrameSpec_sound hd
  have hlen := congrArg List.length hs
  simp only [List.length_drop, Array.length_toList, List.length_append] at hlen
  have hdsz : b.data.size = b.size := rfl
  rw [hdsz] at hlen
  have hoff_lt : off < b.size := by
    unfold readFrameAt at h
    by_cases hlt : off < b.size
    · exact hlt
    · rw [ite_eq_right hlt] at h; cases h
  have hsz : off1 ≤ b.size := by
    unfold readFrameAt at h
    rw [ite_eq_left hoff_lt] at h; dsimp only at h
    split at h
    · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ h2 hp => pure_bound (readAddrsAt_bound b h2) hp
    · exact bind_bound h fun a o1 h1 hp => pure_bound (readVarNatAt_bound b fuel _ a o1 h1) hp
    · exact bind_bound h fun _ _ h1 hp => pure_bound (readStrAt_bound b h1) hp
    · cases h; omega
    · cases h; omega
    · cases h; omega
    · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ h2 hp => pure_bound (readAddrsAt_bound b h2) hp
    · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ _ h'' => bind_bound h'' fun _ _ h3 hp => pure_bound (readAddrsAt_bound b h3) hp
    · by_cases h1 : off + 1 < b.size
      · rw [ite_eq_left h1] at h
        cases hp : primOfTag (byteAtImg b (off + 1)) with
        | none => simp [hp, bind, Option.bind] at h
        | some _ =>
          rw [hp] at h; dsimp only [bind, Option.bind] at h
          exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ h2 hp' => pure_bound (readAddrsAt_bound b h2) hp'
      · rw [ite_eq_right h1] at h; cases h
    · by_cases h1 : off + 1 < b.size
      · rw [ite_eq_left h1] at h
        cases hp : primOfTag (byteAtImg b (off + 1)) with
        | none => simp [hp, bind, Option.bind] at h
        | some _ =>
          rw [hp] at h; dsimp only [bind, Option.bind] at h
          exact bind_bound h fun _ _ h1' hp' => pure_bound (readValueAt_bound b h1') hp'
      · rw [ite_eq_right h1] at h; cases h
    · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ h2 hp => pure_bound (readAddrsAt_bound b h2) hp
    · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ _ h'' => bind_bound h'' fun _ _ h3 hp => pure_bound (readAddrsAt_bound b h3) hp
    · exact bind_bound h fun _ _ _ h' => bind_bound h' fun _ _ _ h'' => bind_bound h'' fun _ _ h3 hp => pure_bound (readAddrsAt_bound b h3) hp
    · cases h
  omega

/-- **Execution-tier `ByteArray` heap image decoder**: reads in place by offset cursor with
    tail-recursive accumulators and zero whole-image `List UInt8` conversion. -/
def decodeHeapImageExec (b : ByteArray) : Option State :=
  let fuel := b.size + 1
  if decide (8 ≤ b.size) && decide (b.extract 0 8 = heapImageMagicBytes) then
    match readVarNatAt fuel b 8 with
    | none => none
    | some (cellCount, o1) =>
      match readManyAt (readCellAt fuel b) cellCount o1 [] with
      | none => none
      | some (cells, o2) =>
        match readControlAt fuel b o2 with
        | none => none
        | some (ctrl, o3) =>
          match readVarNatAt fuel b o3 with
          | none => none
          | some (frameCount, o4) =>
            match readManyAt (readFrameAt fuel b) frameCount o4 [] with
            | some (frames, o5) =>
              if o5 = b.size then some ⟨cells.toArray, ctrl, frames⟩ else none
            | none => none
  else none

/-- Reasoning-tier specification decoder over `List UInt8`. -/
def decodeHeapImage (bs : ByteArray) : Option State :=
  decStateSpec bs.data.toList

theorem decodeHeapImageExec_eq (b : ByteArray) :
    decodeHeapImageExec b = decodeHeapImage b := by
  unfold decodeHeapImage decodeHeapImageExec decStateSpec
  have hlen : b.data.toList.length = b.size := Array.length_toList
  rw [hlen]
  generalize b.size + 1 = fuel
  have hmag_iff : (decide (8 ≤ b.size) && decide (b.extract 0 8 = heapImageMagicBytes)) =
      decide (b.data.toList.take 8 = heapImageMagic) := by
    by_cases h8 : 8 ≤ b.size
    · have hex : (b.extract 0 8).data.toList = b.data.toList.take 8 := by
        rw [ByteArray.data_extract, Array.toList_extract]; simp
      simp only [h8, decide_true, Bool.true_and]
      by_cases hm : b.extract 0 8 = heapImageMagicBytes
      · have hml : b.data.toList.take 8 = heapImageMagic := by
          rw [← hex, hm, heapImageMagicBytes_toList]
        simp [hm, hml]
      · have hml : b.data.toList.take 8 ≠ heapImageMagic := by
          intro hc; apply hm; apply ByteArray.ext; apply Array.toList_inj.1
          rw [hex, hc, heapImageMagicBytes_toList]
        simp [hm, hml]
    · have hml : b.data.toList.take 8 ≠ heapImageMagic := by
        intro hc; have hl := congrArg List.length hc
        simp [List.length_take, hlen, heapImageMagic] at hl; omega
      simp [h8, hml]
  by_cases hm : b.data.toList.take 8 = heapImageMagic
  · have hmB : (decide (8 ≤ b.size) && decide (b.extract 0 8 = heapImageMagicBytes)) = true := by
      rw [hmag_iff]; exact decide_eq_true hm
    rw [hmB, ite_eq_left rfl, ite_eq_left hm]
    dsimp only
    rw [readVarNatAt_eq b fuel 8]
    cases hr1 : readVarNatAt fuel b 8 with
    | none => rfl
    | some p1 =>
      obtain ⟨cellCount, o1⟩ := p1
      dsimp only [Option.map_some]
      have hmCells := readManyAt_eq (readCellAt_eq b fuel) cellCount o1 []
      cases hmc : readManyAt (readCellAt fuel b) cellCount o1 [] with
      | none =>
        rw [hmc] at hmCells
        cases hd : decManySpec (decCellSpec fuel) cellCount (b.data.toList.drop o1) with
        | none => rfl
        | some _ => rw [hd] at hmCells; cases hmCells
      | some p2 =>
        obtain ⟨cells, o2⟩ := p2
        rw [hmc] at hmCells
        cases hdCells : decManySpec (decCellSpec fuel) cellCount (b.data.toList.drop o1) with
        | none => rw [hdCells] at hmCells; cases hmCells
        | some q2 =>
          rw [hdCells] at hmCells
          simp only [Option.map_some, List.reverse_nil, List.nil_append, Option.some.injEq,
            Prod.mk.injEq] at hmCells
          obtain ⟨rfl, hq2⟩ := hmCells
          dsimp only
          rw [← hq2, readControlAt_eq b fuel o2]
          cases hr3 : readControlAt fuel b o2 with
          | none => rfl
          | some p3 =>
            obtain ⟨ctrl, o3⟩ := p3
            dsimp only [Option.map_some]
            rw [readVarNatAt_eq b fuel o3]
            cases hr4 : readVarNatAt fuel b o3 with
            | none => rfl
            | some p4 =>
              obtain ⟨frameCount, o4⟩ := p4
              have ho4 : o4 ≤ b.size := readVarNatAt_bound b fuel o3 frameCount o4 hr4
              dsimp only [Option.map_some]
              have hmFrames := readManyAt_eq (readFrameAt_eq b fuel) frameCount o4 []
              cases hmf : readManyAt (readFrameAt fuel b) frameCount o4 [] with
              | none =>
                rw [hmf] at hmFrames
                cases hd : decManySpec (decFrameSpec fuel) frameCount (b.data.toList.drop o4) with
                | none => rfl
                | some _ => rw [hd] at hmFrames; cases hmFrames
              | some p5 =>
                obtain ⟨frames, o5⟩ := p5
                have ho5 : o5 ≤ b.size :=
                  (readManyAt_bound (fun _ _ _ h => readFrameAt_bound b h)
                    frameCount o4 [] frames o5 ho4 hmf).2
                rw [hmf] at hmFrames
                cases hdFrames : decManySpec (decFrameSpec fuel) frameCount (b.data.toList.drop o4) with
                | none => rw [hdFrames] at hmFrames; cases hmFrames
                | some q5 =>
                  rcases q5 with ⟨frames', rem⟩
                  rw [hdFrames] at hmFrames
                  simp only [Option.map_some, List.reverse_nil, List.nil_append, Option.some.injEq,
                    Prod.mk.injEq] at hmFrames
                  obtain ⟨rfl, hq5⟩ := hmFrames
                  dsimp only
                  rw [← hq5]
                  by_cases ho5eq : o5 = b.size
                  · rw [ite_eq_left ho5eq, drop_nil_of_ge_size b o5 (by omega)]
                  · rw [ite_eq_right ho5eq]
                    have hne : b.data.toList.drop o5 ≠ [] := by
                      intro hn; rw [List.drop_eq_nil_iff, hlen] at hn; omega
                    cases hd5 : b.data.toList.drop o5 with
                    | nil => exact absurd hd5 hne
                    | cons _ _ => rfl
  · have hmB : (decide (8 ≤ b.size) && decide (b.extract 0 8 = heapImageMagicBytes)) = false := by
      rw [hmag_iff]; exact decide_eq_false hm
    rw [hmB, ite_eq_right Bool.false_ne_true, ite_eq_right hm]

@[csimp] theorem decodeHeapImage_eq_exec : @decodeHeapImage = @decodeHeapImageExec := by
  funext b; exact (decodeHeapImageExec_eq b).symm

/-- **Exact Round-Trip (`0 sorry`, `0 Classical`).** Every `Core.Machine.State` — covering all 25
    `Term` constructors, 8 `RuntimeValue` constructors, 3 `Cell` states, 13 `Frame` constructors,
    and 7 `Control` states — decodes bit-identically from its encoded `ByteArray` image. -/
theorem decodeHeapImage_encodeHeapImage (s : State) :
    decodeHeapImage (encodeHeapImage s) = some s := by
  unfold decodeHeapImage
  rw [encodeHeapImage_toList]
  exact decStateSpec_encStateSpec s

/-- **Canonical Re-Encoding.** Any `ByteArray` accepted by `decodeHeapImage` re-encodes to the
    exact same `ByteArray` byte-for-byte. -/
theorem encodeHeapImage_of_decodeHeapImage {bs : ByteArray} {s : State}
    (h : decodeHeapImage bs = some s) : encodeHeapImage s = bs := by
  apply ByteArray.ext
  apply Array.toList_inj.1
  rw [encodeHeapImage_toList]
  exact decStateSpec_sound h

/-- No two distinct `ByteArray`s can decode to the same `Core.Machine.State`. -/
theorem decodeHeapImage_unique {bs₁ bs₂ : ByteArray} {s : State}
    (h₁ : decodeHeapImage bs₁ = some s) (h₂ : decodeHeapImage bs₂ = some s) : bs₁ = bs₂ := by
  rw [← encodeHeapImage_of_decodeHeapImage h₁, ← encodeHeapImage_of_decodeHeapImage h₂]

/-- **Total Canonical Injectivity.** Encoding `Core.Machine.State` to `ByteArray` is unconditionally
    injective across all states with zero width or well-formedness side conditions. -/
theorem encodeHeapImage_injective {s₁ s₂ : State}
    (h : encodeHeapImage s₁ = encodeHeapImage s₂) : s₁ = s₂ := by
  have d₁ := decodeHeapImage_encodeHeapImage s₁
  rw [h, decodeHeapImage_encodeHeapImage s₂] at d₁
  exact Option.some.inj d₁.symm

/-! ## 6. 256-Bit `cSHAKE256` Content-Addressed Heap Image CIDs -/

/-- Domain-separation customization `"OBEND.CORE.HEAP_IMAGE/v1"` as explicit UTF-8 bytes. -/
def heapImageCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x4f, 0x52, 0x45, 0x2e,
   0x48, 0x45, 0x41, 0x50, 0x5f, 0x49, 0x4d, 0x41, 0x47, 0x45, 0x2f, 0x76, 0x31]

/-- Deployed 256-bit `cSHAKE256` byte hash for heap images. -/
def heapImageHash : Hash :=
  Obend.Digest.Cshake256.cshake256Bytes heapImageCustomization

/-- Content-addressed 256-bit heap image CID parameterized by `H : Hash`. -/
def heapImageCidWith (H : Hash) (s : State) : Digest256 :=
  hashBytesToDigest256 H (encodeHeapImage s).data.toList

/-- Canonical 256-bit `cSHAKE256` content-addressed identifier (`BitVec 256`) of a `State`. -/
def heapImageCid (s : State) : Digest256 :=
  heapImageCidWith heapImageHash s

/-- Canonical 32-byte `ByteArray` representation of `heapImageCid`. -/
def heapImageCidBytes (s : State) : ByteArray :=
  (DigestWords4.ofDigest256 (heapImageCid s)).toByteArray32

theorem heapImageCidBytes_size (s : State) : (heapImageCidBytes s).size = 32 := by
  have h : (heapImageCidBytes s).data.toList.length = 32 := by
    simp [heapImageCidBytes, DigestWords4.toByteArray32_toList,
      DigestWords4.toDigest256_ofDigest256]
  simpa using h

theorem heapImageCidBytes_injective {s₁ s₂ : State}
    (h : heapImageCidBytes s₁ = heapImageCidBytes s₂) :
    heapImageCid s₁ = heapImageCid s₂ := by
  have hl := congrArg (fun b : ByteArray => b.data.toList) h
  simp only [heapImageCidBytes, DigestWords4.toByteArray32_toList,
    DigestWords4.toDigest256_ofDigest256] at hl
  exact Obend.Core.Digest.bytes32OfDigest256_injective hl

private theorem hashBytesToDigest256_eq_ofBE {H : Hash} {a b : List UInt8}
    (ha : (H a).length = 32) (hb : (H b).length = 32)
    (h : hashBytesToDigest256 H a = hashBytesToDigest256 H b) :
    ofBE (H a) = ofBE (H b) := by
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have lta : ofBE (H a) < 2 ^ 256 := by have := ofBE_lt (H a); rwa [ha, hpow] at this
  have ltb : ofBE (H b) < 2 ^ 256 := by have := ofBE_lt (H b); rwa [hb, hpow] at this
  have hh := congrArg BitVec.toNat h
  simpa only [hashBytesToDigest256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lta,
    Nat.mod_eq_of_lt ltb] using hh

/-- **Generic Heap Image CID Binding (`0 Classical`).** Equal 256-bit CIDs imply identical machine
    states or exhibit a concrete collision on the two encoded image preimages. -/
theorem heapImageCidWith_binds_or_collides (H : Hash) {s₁ s₂ : State}
    (hlen : (H (encodeHeapImage s₁).data.toList).length = 32 ∧
            (H (encodeHeapImage s₂).data.toList).length = 32)
    (h : heapImageCidWith H s₁ = heapImageCidWith H s₂) :
    s₁ = s₂ ∨ CollisionAmong H
      (fun pre => pre = (encodeHeapImage s₁).data.toList ∨
                  pre = (encodeHeapImage s₂).data.toList) := by
  if hImg : encodeHeapImage s₁ = encodeHeapImage s₂ then
    exact Or.inl (encodeHeapImage_injective hImg)
  else
    have hListNe : (encodeHeapImage s₁).data.toList ≠ (encodeHeapImage s₂).data.toList :=
      fun hl => hImg (ByteArray.ext (Array.toList_inj.1 hl))
    exact Or.inr ⟨_, _, .inl rfl, .inr rfl, hListNe,
      hashBytesToDigest256_eq_ofBE hlen.1 hlen.2 h⟩

/-- **`heapImageCid` Binds or Collides (`0 Classical`).** Two `Core.Machine.State` values sharing
    one 256-bit `cSHAKE256` CID are identical or witness an explicit `cSHAKE256` collision. -/
theorem heapImageCid_binds_or_collides {s₁ s₂ : State}
    (h : heapImageCid s₁ = heapImageCid s₂) :
    s₁ = s₂ ∨ CollisionAmong heapImageHash
      (fun pre => pre = (encodeHeapImage s₁).data.toList ∨
                  pre = (encodeHeapImage s₂).data.toList) :=
  heapImageCidWith_binds_or_collides heapImageHash
    ⟨by simp [heapImageHash], by simp [heapImageHash]⟩ h

/-- Constructive `Type`-valued `PSum` collision extractor (`0 Classical.choice`). -/
def heapImageCid_binds_or_extract_collision {s₁ s₂ : State}
    (h : heapImageCid s₁ = heapImageCid s₂) :
    PSum (s₁ = s₂)
      (ExactCollisionPair heapImageHash
        (encodeHeapImage s₁).data.toList (encodeHeapImage s₂).data.toList) :=
  if hImg : encodeHeapImage s₁ = encodeHeapImage s₂ then
    .inl (encodeHeapImage_injective hImg)
  else
    .inr ⟨fun hl => hImg (ByteArray.ext (Array.toList_inj.1 hl)),
      hashBytesToDigest256_eq_ofBE (by simp [heapImageHash]) (by simp [heapImageHash]) h⟩

/-- Refutable pole: under `Obend.Core.Digest.lengthHash`, two distinct states of equal byte width
    collide, proving `CollisionAmong` is non-vacuously inhabited on non-cryptographic hashes. -/
theorem lengthHash_heapImageCid_collides :
    let s₁ := initial (.nat 1)
    let s₂ := initial (.nat 2)
    s₁ ≠ s₂ ∧ heapImageCidWith Obend.Core.Digest.lengthHash s₁ =
      heapImageCidWith Obend.Core.Digest.lengthHash s₂ := by
  refine ⟨by intro h; have hc := congrArg State.control h; simp [initial] at hc, ?_⟩
  have hlenEq : (encodeHeapImage (initial (.nat 1))).data.toList.length =
      (encodeHeapImage (initial (.nat 2))).data.toList.length := by
    simp [encodeHeapImage_toList, encStateSpec, initial, encControlSpec, encTermSpec,
      encAddrsSpec, encVarNat]
  simp only [heapImageCidWith, hashBytesToDigest256, Obend.Core.Digest.lengthHash, hlenEq]

/-! ## 7. Orthogonal Continuation Checkpoint & Multi-Yield Resume Equivalence -/

/-- Persist a quiescent `Control.yielded planAddr` continuation to a content-addressed image
    envelope `(planAddr, cid, bytes)`. Refuses non-yielded running/terminal control states. -/
structure PersistedYieldImage where
  planAddr : Address
  cid : Digest256
  bytes : ByteArray
  deriving DecidableEq

def checkpointYielded (s : State) : Option PersistedYieldImage :=
  match s.control with
  | .yielded plan =>
    some { planAddr := plan, cid := heapImageCid s, bytes := encodeHeapImage s }
  | _ => none

/-- Rehydrate a `PersistedYieldImage` in a fresh process (verifying both canonical decoding and
    256-bit `cSHAKE256` CID integrity) and resume with `response`. -/
def rehydrateAndResume (img : PersistedYieldImage) (response : Term) : Option State :=
  match decodeHeapImage img.bytes with
  | some s =>
    if heapImageCid s == img.cid then
      resume response s
    else none
  | none => none

/-- Single-boundary checkpoint + verified rehydration equals in-memory `resume` identically. -/
theorem rehydrateAndResume_checkpointYielded {s : State} {plan : Address}
    (hy : s.control = .yielded plan) (response : Term) :
    ∃ img, checkpointYielded s = some img ∧
      img.planAddr = plan ∧
      rehydrateAndResume img response = resume response s ∧
      (resume response s).isSome = true := by
  refine ⟨{ planAddr := plan, cid := heapImageCid s, bytes := encodeHeapImage s }, ?_, rfl, ?_, ?_⟩
  · simp [checkpointYielded, hy]
  · simp [rehydrateAndResume, decodeHeapImage_encodeHeapImage]
  · simp [resume, hy]

/-- Iterate `stepRaw` exactly `k` steps from `s`. -/
def iterStepRaw : Nat → State → State
  | 0, s => s
  | k + 1, s => iterStepRaw k (stepRaw s)

/-- Iterated `stepRaw` from a rehydrated continuation agrees at every step count `k` with the
    un-checkpointed in-memory machine. -/
theorem rehydrate_resume_stepRaw_eq {s resumed : State} {img : PersistedYieldImage}
    {response : Term}
    (hck : checkpointYielded s = some img)
    (hres : resume response s = some resumed) :
    ∃ rehydrated, rehydrateAndResume img response = some rehydrated ∧
      ∀ k : Nat, iterStepRaw k rehydrated = iterStepRaw k resumed := by
  unfold checkpointYielded at hck
  cases hctrl : s.control <;> simp [hctrl] at hck
  subst hck
  refine ⟨resumed, ?_, fun _ => rfl⟩
  simp [rehydrateAndResume, decodeHeapImage_encodeHeapImage, hres]

/-- One turn of a multi-yield interactive session: tick budget to run until the next yield (or
    completion), together with the external `perform` response supplied if the segment yields. -/
structure YieldTurn where
  ticks : Nat
  response : Term
  deriving Repr

/-- Multi-turn in-memory interactive session runner over `List YieldTurn`. -/
def runInMemorySession (limits : Limits) : State → List YieldTurn → List Address × Outcome
  | s, [] => ([], runBounded limits 0 s)
  | s, turn :: rest =>
    match runBounded limits turn.ticks s with
    | .yielded plan y =>
      match resume turn.response y with
      | some next =>
        let (plans, finalOut) := runInMemorySession limits next rest
        (plan :: plans, finalOut)
      | none => ([plan], .yielded plan y)
    | other => ([], other)

/-- Multi-turn orthogonal persisted session runner: at **every** yield boundary, serializes the
    entire heap + stack + `yielded` control to raw `ByteArray`, discards the live pointer,
    rehydrates from `ByteArray` in a fresh state, checks `heapImageCid`, and resumes. -/
def runPersistedSession (limits : Limits) : State → List YieldTurn → Option (List Address × Outcome)
  | s, [] => some ([], runBounded limits 0 s)
  | s, turn :: rest =>
    match runBounded limits turn.ticks s with
    | .yielded _plan y =>
      match checkpointYielded y with
      | none => none
      | some img =>
        match rehydrateAndResume img turn.response with
        | none => none
        | some rehydrated =>
          (runPersistedSession limits rehydrated rest).map fun p => (img.planAddr :: p.1, p.2)
    | other => some ([], other)

private theorem step_yielded_control {limits : Limits} {s y : State} {plan : Address}
    (h : step limits s = .yielded plan y) : y.control = .yielded plan := by
  unfold step at h
  cases hc : s.control
  · rw [hc] at h; dsimp only at h; split at h <;> cases h
  · rw [hc] at h; dsimp only at h; split at h <;> cases h
  · rw [hc] at h; cases h
  · rw [hc] at h; dsimp only at h; split at h <;> cases h
  · rw [hc] at h; cases h
  · rw [hc] at h; cases h
  · rw [hc] at h; simp only [Outcome.yielded.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hc

private theorem runBounded_yielded_control :
    ∀ (ticks : Nat) {limits : Limits} {s y : State} {plan : Address},
      runBounded limits ticks s = .yielded plan y → y.control = .yielded plan
  | 0, limits, s, y, plan, h => by
    unfold runBounded at h
    cases hc : s.control <;> simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h; exact hc
  | ticks + 1, limits, s, y, plan, h => by
    unfold runBounded at h
    cases hs : step limits s with
    | suspended reason next =>
      cases reason with
      | ticks =>
        simp only [hs] at h
        exact runBounded_yielded_control ticks h
      | capacity => simp [hs] at h
    | yielded p st =>
      simp only [hs, Outcome.yielded.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact step_yielded_control hs
    | finished _ _ | divergent _ _ | refused _ _ => simp [hs] at h

/-- **Orthogonal Continuation Checkpoint & Multi-Yield Resume Equivalence (`rehydrate_resume_steps_eq`).**
    Across arbitrary multi-yield `List YieldTurn` traces, checkpointing every `Control.yielded`
    state to `ByteArray`, verifying `heapImageCid`, rehydrating in a fresh process, and supplying
    each `perform` response yields the **exact same** sequence of yielded plan addresses and final
    `Outcome` as the un-checkpointed in-memory demand machine. -/
theorem rehydrate_resume_steps_eq (limits : Limits) :
    ∀ (turns : List YieldTurn) (s : State),
      runPersistedSession limits s turns = some (runInMemorySession limits s turns)
  | [], s => rfl
  | turn :: rest, s => by
    unfold runPersistedSession runInMemorySession
    cases hrun : runBounded limits turn.ticks s with
    | finished _ _ | suspended _ _ | divergent _ _ | refused _ _ => rfl
    | yielded plan y =>
      have hy : y.control = .yielded plan := runBounded_yielded_control turn.ticks hrun
      obtain ⟨img, hck, hplan, hreh, _⟩ := rehydrateAndResume_checkpointYielded hy turn.response
      simp only [hck, hreh, hplan]
      cases hres : resume turn.response y with
      | none => simp [resume, hy] at hres
      | some next =>
        dsimp only
        rw [rehydrate_resume_steps_eq limits rest next]
        rfl

/-- Tamper refusal: mutating the stored CID of a `PersistedYieldImage` is deterministically
    rejected by `rehydrateAndResume`. -/
theorem rehydrateAndResume_tampered_cid_refused {img : PersistedYieldImage} {s : State}
    (hdec : decodeHeapImage img.bytes = some s) (htamper : heapImageCid s ≠ img.cid)
    (response : Term) :
    rehydrateAndResume img response = none := by
  unfold rehydrateAndResume
  rw [hdec]
  dsimp only
  have hneq : (heapImageCid s == img.cid) = false := beq_false_of_ne htamper
  rw [hneq]
  rfl

/-! ## 8. Inhabitedness Witnesses: Open-Recursive Prototype, Lazy Thunks & Multi-Yield Trace -/

/-- Concrete state containing open-recursive `prototype`, `specification`, `suspended` + `evaluating`
    + `cached` heap cells, continuation `Frame`s, and `Control.yielded`, witnessing non-vacuity of
    every persistence carrier. -/
def sampleYieldedPrototypeState : State :=
  { heap := #[
      .suspended ⟨.prototype (.bound 0) (.record [("val", .nat 42)]), [1]⟩,
      .evaluating ⟨.specification (.label "meta") (.lam (.bound 0)), []⟩,
      .cached ⟨.nat 7, []⟩ (.prototype 0 1),
      .suspended ⟨.inject "ask" (.nat 99), [2]⟩
    ]
    control := .yielded 3
    stack := [
      .binaryLeft .add (.project (.bound 0)) [2],
      .case [("ok", .done (.bound 0))] [0]
    ] }

theorem sampleYieldedPrototype_roundTrip_and_resumes :
    decodeHeapImage (encodeHeapImage sampleYieldedPrototypeState) =
      some sampleYieldedPrototypeState ∧
    (∃ img, checkpointYielded sampleYieldedPrototypeState = some img ∧
      img.planAddr = 3 ∧
      (rehydrateAndResume img (.nat 5)).isSome = true) := by
  refine ⟨decodeHeapImage_encodeHeapImage _, ?_⟩
  obtain ⟨img, hck, hp, hreh, hsome⟩ :=
    rehydrateAndResume_checkpointYielded (s := sampleYieldedPrototypeState) (plan := 3) rfl (.nat 5)
  exact ⟨img, hck, hp, by rw [hreh]; exact hsome⟩

def twoYieldSumTerm : Term := .binary .add (.perform (.nat 10)) (.perform (.nat 20))

theorem yieldedPersisted_session_inhabited :
    let s₀ : State := ⟨#[], .yielded 0, [.binaryLeft .add (.nat 23) []]⟩
    let turns : List YieldTurn := [⟨0, .nat 19⟩, ⟨8, .nat 0⟩]
    ∃ finalState,
      runPersistedSession ⟨16, 16⟩ s₀ turns =
        some ([0], .finished (.natural 42) finalState) := by
  dsimp only
  rw [rehydrate_resume_steps_eq ⟨16, 16⟩ [⟨0, .nat 19⟩, ⟨8, .nat 0⟩]
    ⟨#[], .yielded 0, [.binaryLeft .add (.nat 23) []]⟩]
  refine ⟨⟨#[], .complete (.natural 42), []⟩, ?_⟩
  simp [runInMemorySession, resume, runBounded, step, stepRaw, valueTerm, scalarValue,
    primitiveResult]

end Obend.Core.HeapImage
end
