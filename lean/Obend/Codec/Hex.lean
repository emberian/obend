module
/-
# Obend.Codec.Hex — hexadecimal, one codec for the tree

A nibble is spelled as an ASCII byte (`hexNibbleByte`) or a `Char` (`hexNibbleChar`): lowercase,
and total in `n % 16`. A byte string is spelled two digits a byte, high nibble first:
`bytesToHexChars`, its `String` forms `bytesToHex` and `byteArrayToHex`, and `bytesToHexAscii` for
framing at the byte level. A number in a fixed number of digits is `natToHexChars`.

Two decoders, because the tree has two contracts:

- **strict**, lowercase only: `decodeHexNibble?`, `hexCharsToBytes?`, and on ASCII bytes
  `decodeHexNibbleByte?`, `hexAsciiToBytes?`. It accepts exactly what the encoder writes
  (`bytesToHexChars_of_hexCharsToBytes?`), so a byte string has one spelling. Commitments,
  content addresses and wire forms are read this way.
- **case-insensitive**: `decodeHexNibbleAnyCase?`, `hexCharsToBytesAnyCase?`, `hexCharsToNat?`,
  `isHexChar`, `isHexByte`. `A`–`F` are digits too, for text that other tools and people write:
  JSON `\u` escapes, `0x` literals, CLI arguments, disassembler dumps.
-/
public section

namespace Obend.Codec.Hex

set_option autoImplicit false

/-! ## Nibbles -/

/-- The lowercase hex digit of `n % 16` as an ASCII byte: `0`–`9` are 48–57, `a`–`f` 97–102. -/
@[expose] def hexNibbleByte (n : Nat) : UInt8 :=
  if n % 16 < 10 then (48 + n % 16).toUInt8 else (87 + n % 16).toUInt8

/-- The lowercase hex digit of `n % 16` as a `Char`. -/
@[expose] def hexNibbleChar (n : Nat) : Char :=
  if n % 16 < 10 then Char.ofNat (48 + n % 16) else Char.ofNat (87 + n % 16)

/-- The digit a lowercase hex `Char` spells. Anything else, `A`–`F` included, is `none`. -/
@[expose] def decodeHexNibble? (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

/-- The digit a hex `Char` of either case spells. -/
@[expose] def decodeHexNibbleAnyCase? (c : Char) : Option Nat :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55) else decodeHexNibble? c

/-- The digit a lowercase hex ASCII byte spells. -/
@[expose] def decodeHexNibbleByte? (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b.toNat ∧ b.toNat ≤ 102 then some (b.toNat - 87)
  else none

/-- A hex digit of either case. -/
abbrev isHexChar (c : Char) : Bool := (decodeHexNibbleAnyCase? c).isSome

/-- A lowercase hex digit. -/
abbrev isLowerHexChar (c : Char) : Bool := (decodeHexNibble? c).isSome

/-- An ASCII hex digit of either case: what may follow `\u` in a JSON string (RFC 8259 §7). -/
@[expose] def isHexByte (b : UInt8) : Bool :=
  (48 ≤ b.toNat && b.toNat ≤ 57) || (65 ≤ b.toNat && b.toNat ≤ 70) ||
    (97 ≤ b.toNat && b.toNat ≤ 102)

theorem hexNibbleChar_mod (n : Nat) : hexNibbleChar (n % 16) = hexNibbleChar n := by
  simp only [hexNibbleChar, Nat.mod_mod]

theorem hexNibbleByte_mod (n : Nat) : hexNibbleByte (n % 16) = hexNibbleByte n := by
  simp only [hexNibbleByte, Nat.mod_mod]

private theorem nibbleChar_laws : ∀ d : Fin 16,
    decodeHexNibble? (hexNibbleChar d.val) = some d.val ∧
      decodeHexNibbleAnyCase? (hexNibbleChar d.val) = some d.val := by
  decide

private theorem nibbleByte_laws : ∀ d : Fin 16,
    decodeHexNibbleByte? (hexNibbleByte d.val) = some d.val ∧ isHexByte (hexNibbleByte d.val) = true := by
  decide

@[simp] theorem decodeHexNibble?_hexNibbleChar (n : Nat) :
    decodeHexNibble? (hexNibbleChar n) = some (n % 16) := by
  rw [← hexNibbleChar_mod]; exact (nibbleChar_laws ⟨n % 16, Nat.mod_lt _ (by decide)⟩).1

@[simp] theorem decodeHexNibbleAnyCase?_hexNibbleChar (n : Nat) :
    decodeHexNibbleAnyCase? (hexNibbleChar n) = some (n % 16) := by
  rw [← hexNibbleChar_mod]; exact (nibbleChar_laws ⟨n % 16, Nat.mod_lt _ (by decide)⟩).2

@[simp] theorem decodeHexNibbleByte?_hexNibbleByte (n : Nat) :
    decodeHexNibbleByte? (hexNibbleByte n) = some (n % 16) := by
  rw [← hexNibbleByte_mod]; exact (nibbleByte_laws ⟨n % 16, Nat.mod_lt _ (by decide)⟩).1

@[simp] theorem isHexByte_hexNibbleByte (n : Nat) : isHexByte (hexNibbleByte n) = true := by
  rw [← hexNibbleByte_mod]; exact (nibbleByte_laws ⟨n % 16, Nat.mod_lt _ (by decide)⟩).2

/-- The strict decoder reads only digits the encoder writes. -/
theorem hexNibbleChar_of_decodeHexNibble? {c : Char} {d : Nat} (h : decodeHexNibble? c = some d) :
    d < 16 ∧ hexNibbleChar d = c := by
  unfold decodeHexNibble? at h
  by_cases h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · rw [ite_eq_left h1, Option.some.injEq] at h
    subst h
    have hm : (c.toNat - 48) % 16 = c.toNat - 48 := Nat.mod_eq_of_lt (by omega)
    have hlt : c.toNat - 48 < 10 := by omega
    have he : 48 + (c.toNat - 48) = c.toNat := by omega
    refine ⟨by omega, ?_⟩
    simp only [hexNibbleChar, hm, hlt, ↓reduceIte, he, Char.ofNat_toNat]
  · rw [ite_eq_right h1] at h
    by_cases h2 : 97 ≤ c.toNat ∧ c.toNat ≤ 102
    · rw [ite_eq_left h2, Option.some.injEq] at h
      subst h
      have hm : (c.toNat - 87) % 16 = c.toNat - 87 := Nat.mod_eq_of_lt (by omega)
      have hge : ¬ c.toNat - 87 < 10 := by omega
      have he : 87 + (c.toNat - 87) = c.toNat := by omega
      refine ⟨by omega, ?_⟩
      simp only [hexNibbleChar, hm, hge, ↓reduceIte, he, Char.ofNat_toNat]
    · rw [ite_eq_right h2] at h
      cases h

/-- The same on ASCII bytes. -/
theorem hexNibbleByte_of_decodeHexNibbleByte? {b : UInt8} {d : Nat}
    (h : decodeHexNibbleByte? b = some d) : d < 16 ∧ hexNibbleByte d = b := by
  unfold decodeHexNibbleByte? at h
  by_cases h1 : 48 ≤ b.toNat ∧ b.toNat ≤ 57
  · rw [ite_eq_left h1, Option.some.injEq] at h
    subst h
    have hm : (b.toNat - 48) % 16 = b.toNat - 48 := Nat.mod_eq_of_lt (by omega)
    have hlt : b.toNat - 48 < 10 := by omega
    have he : 48 + (b.toNat - 48) = b.toNat := by omega
    refine ⟨by omega, ?_⟩
    simp only [hexNibbleByte, hm, hlt, ↓reduceIte, he, Nat.toUInt8_eq, UInt8.ofNat_toNat]
  · rw [ite_eq_right h1] at h
    by_cases h2 : 97 ≤ b.toNat ∧ b.toNat ≤ 102
    · rw [ite_eq_left h2, Option.some.injEq] at h
      subst h
      have hm : (b.toNat - 87) % 16 = b.toNat - 87 := Nat.mod_eq_of_lt (by omega)
      have hge : ¬ b.toNat - 87 < 10 := by omega
      have he : 87 + (b.toNat - 87) = b.toNat := by omega
      refine ⟨by omega, ?_⟩
      simp only [hexNibbleByte, hm, hge, ↓reduceIte, he, Nat.toUInt8_eq, UInt8.ofNat_toNat]
    · rw [ite_eq_right h2] at h
      cases h

/-! ## Byte strings -/

/-- Two lowercase digits a byte, high nibble first. -/
@[expose] def bytesToHexChars (bs : List UInt8) : List Char :=
  bs.flatMap fun b => [hexNibbleChar (b.toNat / 16), hexNibbleChar (b.toNat % 16)]

theorem bytesToHexChars_cons (b : UInt8) (bs : List UInt8) :
    bytesToHexChars (b :: bs) =
      hexNibbleChar (b.toNat / 16) :: hexNibbleChar (b.toNat % 16) :: bytesToHexChars bs := rfl

/-- The same spelling in ASCII bytes. -/
@[expose] def bytesToHexAscii (bs : List UInt8) : List UInt8 :=
  bs.flatMap fun b => [hexNibbleByte (b.toNat / 16), hexNibbleByte (b.toNat % 16)]

theorem bytesToHexAscii_cons (b : UInt8) (bs : List UInt8) :
    bytesToHexAscii (b :: bs) =
      hexNibbleByte (b.toNat / 16) :: hexNibbleByte (b.toNat % 16) :: bytesToHexAscii bs := rfl

/-- Lowercase hex of a byte list. -/
abbrev bytesToHex (bs : List UInt8) : String := String.ofList (bytesToHexChars bs)

/-- One byte in exactly two lowercase digits. -/
abbrev byteToHex (b : UInt8) : String := bytesToHex [b]

/-- Lowercase hex of a `ByteArray`. -/
abbrev byteArrayToHex (b : ByteArray) : String := bytesToHex b.data.toList

/-- The bytes a lowercase hex spelling names; `none` on an odd length or any other character. -/
@[expose] def hexCharsToBytes? : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← decodeHexNibble? a
    let lo ← decodeHexNibble? b
    let tl ← hexCharsToBytes? rest
    some ((hi * 16 + lo).toUInt8 :: tl)
  | [_] => none

/-- The bytes a hex spelling of either case names. -/
@[expose] def hexCharsToBytesAnyCase? : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← decodeHexNibbleAnyCase? a
    let lo ← decodeHexNibbleAnyCase? b
    let tl ← hexCharsToBytesAnyCase? rest
    some ((hi * 16 + lo).toUInt8 :: tl)
  | [_] => none

/-- The bytes a lowercase hex spelling in ASCII bytes names. -/
@[expose] def hexAsciiToBytes? : List UInt8 → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← decodeHexNibbleByte? a
    let lo ← decodeHexNibbleByte? b
    let tl ← hexAsciiToBytes? rest
    some ((hi * 16 + lo).toUInt8 :: tl)
  | [_] => none

theorem bytesToHexChars_length (bs : List UInt8) : (bytesToHexChars bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [bytesToHexChars_cons, List.length_cons, ih]; omega

theorem bytesToHexAscii_length (bs : List UInt8) : (bytesToHexAscii bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [bytesToHexAscii_cons, List.length_cons, ih]; omega

theorem bytesToHex_length (bs : List UInt8) : (bytesToHex bs).length = 2 * bs.length := by
  rw [String.length_ofList, bytesToHexChars_length]

theorem byteArrayToHex_length (b : ByteArray) : (byteArrayToHex b).length = 2 * b.size := by
  rw [bytesToHex_length, Array.length_toList, ByteArray.size_data]

private theorem byte_of_nibbles (b : UInt8) : ((b.toNat / 16 % 16) * 16 + b.toNat % 16 % 16).toUInt8 = b := by
  have hb : b.toNat < 256 := b.toNat_lt
  have hs : (b.toNat / 16 % 16) * 16 + b.toNat % 16 % 16 = b.toNat := by omega
  rw [hs, Nat.toUInt8_eq, UInt8.ofNat_toNat]

@[simp] theorem hexCharsToBytes?_bytesToHexChars (bs : List UInt8) :
    hexCharsToBytes? (bytesToHexChars bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesToHexChars_cons, hexCharsToBytes?, decodeHexNibble?_hexNibbleChar, ih, bind,
      Option.bind, byte_of_nibbles]

@[simp] theorem hexCharsToBytesAnyCase?_bytesToHexChars (bs : List UInt8) :
    hexCharsToBytesAnyCase? (bytesToHexChars bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesToHexChars_cons, hexCharsToBytesAnyCase?, decodeHexNibbleAnyCase?_hexNibbleChar, ih,
      bind, Option.bind, byte_of_nibbles]

@[simp] theorem hexAsciiToBytes?_bytesToHexAscii (bs : List UInt8) :
    hexAsciiToBytes? (bytesToHexAscii bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesToHexAscii_cons, hexAsciiToBytes?, decodeHexNibbleByte?_hexNibbleByte, ih, bind,
      Option.bind, byte_of_nibbles]

@[simp] theorem hexCharsToBytes?_bytesToHex (bs : List UInt8) :
    hexCharsToBytes? (bytesToHex bs).toList = some bs := by
  rw [String.toList_ofList, hexCharsToBytes?_bytesToHexChars]

@[simp] theorem hexCharsToBytes?_byteArrayToHex (b : ByteArray) :
    hexCharsToBytes? (byteArrayToHex b).toList = some b.data.toList :=
  hexCharsToBytes?_bytesToHex b.data.toList

private theorem nibbles_of_byte {hi lo : Nat} (hhi : hi < 16) (hlo : lo < 16) :
    (hi * 16 + lo).toUInt8.toNat / 16 = hi ∧ (hi * 16 + lo).toUInt8.toNat % 16 = lo := by
  have hv : (hi * 16 + lo).toUInt8.toNat = hi * 16 + lo := by
    rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [hv]; exact ⟨by omega, by omega⟩

/-- **Canonical spelling.** What the strict decoder accepts is the encoder's spelling of what it
returns: a byte string has exactly one lowercase hex spelling. -/
theorem bytesToHexChars_of_hexCharsToBytes? :
    ∀ {cs : List Char} {bs : List UInt8}, hexCharsToBytes? cs = some bs → bytesToHexChars bs = cs
  | [], bs, h => by
    simp only [hexCharsToBytes?, Option.some.injEq] at h; subst h; rfl
  | a :: b :: rest, bs, h => by
    simp only [hexCharsToBytes?, bind, Option.bind] at h
    cases ha : decodeHexNibble? a with
    | none => simp only [ha] at h; cases h
    | some hi =>
      cases hb : decodeHexNibble? b with
      | none => simp only [ha, hb] at h; cases h
      | some lo =>
        cases ht : hexCharsToBytes? rest with
        | none => simp only [ha, hb, ht] at h; cases h
        | some tl =>
          simp only [ha, hb, ht, Option.some.injEq] at h
          subst h
          obtain ⟨hhi, rfl⟩ := hexNibbleChar_of_decodeHexNibble? ha
          obtain ⟨hlo, rfl⟩ := hexNibbleChar_of_decodeHexNibble? hb
          obtain ⟨e1, e2⟩ := nibbles_of_byte hhi hlo
          simp only [bytesToHexChars_cons, e1, e2, bytesToHexChars_of_hexCharsToBytes? ht]
  | [_], _, h => by simp only [hexCharsToBytes?] at h; cases h

/-- The same on ASCII bytes. -/
theorem bytesToHexAscii_of_hexAsciiToBytes? :
    ∀ {cs bs : List UInt8}, hexAsciiToBytes? cs = some bs → bytesToHexAscii bs = cs
  | [], bs, h => by
    simp only [hexAsciiToBytes?, Option.some.injEq] at h; subst h; rfl
  | a :: b :: rest, bs, h => by
    simp only [hexAsciiToBytes?, bind, Option.bind] at h
    cases ha : decodeHexNibbleByte? a with
    | none => simp only [ha] at h; cases h
    | some hi =>
      cases hb : decodeHexNibbleByte? b with
      | none => simp only [ha, hb] at h; cases h
      | some lo =>
        cases ht : hexAsciiToBytes? rest with
        | none => simp only [ha, hb, ht] at h; cases h
        | some tl =>
          simp only [ha, hb, ht, Option.some.injEq] at h
          subst h
          obtain ⟨hhi, rfl⟩ := hexNibbleByte_of_decodeHexNibbleByte? ha
          obtain ⟨hlo, rfl⟩ := hexNibbleByte_of_decodeHexNibbleByte? hb
          obtain ⟨e1, e2⟩ := nibbles_of_byte hhi hlo
          simp only [bytesToHexAscii_cons, e1, e2, bytesToHexAscii_of_hexAsciiToBytes? ht]
  | [_], _, h => by simp only [hexAsciiToBytes?] at h; cases h

theorem bytesToHexChars_injective {a b : List UInt8} (h : bytesToHexChars a = bytesToHexChars b) :
    a = b := by
  have := congrArg hexCharsToBytes? h
  rwa [hexCharsToBytes?_bytesToHexChars, hexCharsToBytes?_bytesToHexChars, Option.some.injEq] at this

/-- An odd number of ASCII digits names no byte string. -/
theorem hexAsciiToBytes?_of_odd : ∀ (xs : List UInt8), xs.length % 2 ≠ 0 → hexAsciiToBytes? xs = none
  | [], h => by simp at h
  | a :: b :: rest, h => by
    have hr : rest.length % 2 ≠ 0 := by simp only [List.length_cons] at h; omega
    simp only [hexAsciiToBytes?, hexAsciiToBytes?_of_odd rest hr, bind, Option.bind]
    cases decodeHexNibbleByte? a <;> cases decodeHexNibbleByte? b <;> rfl
  | [_], _ => rfl

/-! ## Numbers -/

/-- `n % 16 ^ w` in exactly `w` lowercase digits, most significant first. -/
def natToHexChars (w n : Nat) : List Char :=
  (List.range w).reverse.map fun i => hexNibbleChar (n >>> (4 * i))

theorem natToHexChars_length (w n : Nat) : (natToHexChars w n).length = w := by
  simp only [natToHexChars, List.length_map, List.length_reverse, List.length_range]

theorem natToHexChars_succ (w n : Nat) :
    natToHexChars (w + 1) n = hexNibbleChar (n >>> (4 * w)) :: natToHexChars w n := by
  simp [natToHexChars, List.range_succ]

/-- The number a hex spelling of either case names, most significant digit first; `none` on any
other character. -/
def hexCharsToNat? (cs : List Char) : Option Nat :=
  cs.foldlM (fun acc c => (decodeHexNibbleAnyCase? c).map (acc * 16 + ·)) 0

private theorem foldlM_natToHexChars (w n acc : Nat) :
    (natToHexChars w n).foldlM (fun acc c => (decodeHexNibbleAnyCase? c).map (acc * 16 + ·)) acc =
      some (acc * 16 ^ w + n % 16 ^ w) := by
  induction w generalizing acc with
  | zero => simp [natToHexChars, Nat.mod_one]
  | succ w ih =>
    rw [natToHexChars_succ, List.foldlM_cons, decodeHexNibbleAnyCase?_hexNibbleChar, Option.map_some]
    simp only [bind, Option.bind]
    rw [ih, Option.some.injEq]
    have hs : n >>> (4 * w) = n / 16 ^ w := by
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
    rw [hs, Nat.mod_pow_succ, Nat.pow_succ]
    generalize 16 ^ w = P
    generalize n / P % 16 = D
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 16 P, Nat.mul_comm D P]
    omega

/-- `natToHexChars w` spells `n % 16 ^ w`. -/
theorem hexCharsToNat?_natToHexChars (w n : Nat) :
    hexCharsToNat? (natToHexChars w n) = some (n % 16 ^ w) := by
  rw [hexCharsToNat?, foldlM_natToHexChars, Nat.zero_mul, Nat.zero_add]

example : hexCharsToBytes? "00ff7a".toList = some [0, 255, 122] := by decide
example : hexCharsToBytes? "00FF".toList = none ∧ hexCharsToBytesAnyCase? "00FF".toList = some [0, 255] := by
  decide
example : hexAsciiToBytes? [48, 102] = some [15] ∧ isHexByte 70 = true ∧ isHexByte 103 = false := by decide

end Obend.Codec.Hex

end
