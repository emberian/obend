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

/-! ## Stack-Safe & `ByteArray` `Exec` Refinements (`@[csimp]`) -/

/-- Single-pass tail-recursive hex `Char` encoder without per-byte 2-element list allocation. -/
def bytesToHexCharsRev : List UInt8 → List Char → List Char
  | [], acc => acc.reverse
  | b :: bs, acc =>
    bytesToHexCharsRev bs (hexNibbleChar (b.toNat % 16) :: hexNibbleChar (b.toNat / 16) :: acc)

theorem bytesToHexCharsRev_eq (bs : List UInt8) (acc : List Char) :
    bytesToHexCharsRev bs acc = acc.reverse ++ bytesToHexChars bs := by
  induction bs generalizing acc with
  | nil => simp [bytesToHexCharsRev, bytesToHexChars]
  | cons b bs ih =>
    simp only [bytesToHexCharsRev, ih, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, bytesToHexChars_cons]

def bytesToHexCharsExec (bs : List UInt8) : List Char := bytesToHexCharsRev bs []

@[csimp] theorem bytesToHexChars_eq_exec : @bytesToHexChars = @bytesToHexCharsExec := by
  funext bs
  simpa [bytesToHexCharsExec] using (bytesToHexCharsRev_eq bs []).symm

/-- Single-pass tail-recursive ASCII hex encoder without per-byte 2-element list allocation. -/
def bytesToHexAsciiRev : List UInt8 → List UInt8 → List UInt8
  | [], acc => acc.reverse
  | b :: bs, acc =>
    bytesToHexAsciiRev bs (hexNibbleByte (b.toNat % 16) :: hexNibbleByte (b.toNat / 16) :: acc)

theorem bytesToHexAsciiRev_eq (bs acc : List UInt8) :
    bytesToHexAsciiRev bs acc = acc.reverse ++ bytesToHexAscii bs := by
  induction bs generalizing acc with
  | nil => simp [bytesToHexAsciiRev, bytesToHexAscii]
  | cons b bs ih =>
    simp only [bytesToHexAsciiRev, ih, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, bytesToHexAscii_cons]

def bytesToHexAsciiExec (bs : List UInt8) : List UInt8 := bytesToHexAsciiRev bs []

@[csimp] theorem bytesToHexAscii_eq_exec : @bytesToHexAscii = @bytesToHexAsciiExec := by
  funext bs
  simpa [bytesToHexAsciiExec] using (bytesToHexAsciiRev_eq bs []).symm

/-- Direct `ByteArray` ASCII hex encoder (`0` intermediate `List` allocations). -/
def byteArrayToHexAsciiLoop (src : @& ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, dst => dst
  | fuel + 1, i, dst =>
    if h : i < src.size then
      let b := src[i]'h
      let dst' := (dst.push (hexNibbleByte (b.toNat >>> 4))).push (hexNibbleByte (b.toNat &&& 15))
      byteArrayToHexAsciiLoop src fuel (i + 1) dst'
    else dst

def byteArrayToHexAscii (src : @& ByteArray) : ByteArray :=
  byteArrayToHexAsciiLoop src src.size 0 (ByteArray.emptyWithCapacity (2 * src.size))

private theorem push_data_hex (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  cases b; simp [ByteArray.push]

theorem byteArrayToHexAsciiLoop_eq (src : ByteArray) :
    ∀ (fuel i : Nat) (dst : ByteArray), src.size - i ≤ fuel →
      (byteArrayToHexAsciiLoop src fuel i dst).data.toList =
        dst.data.toList ++ bytesToHexAscii (src.data.toList.drop i)
  | 0, i, dst, hf => by
    have hge : src.data.toList.length ≤ i := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    simp [byteArrayToHexAsciiLoop, List.drop_eq_nil_of_le hge, bytesToHexAscii]
  | fuel + 1, i, dst, hf => by
    unfold byteArrayToHexAsciiLoop
    by_cases h : i < src.size
    · have hl : i < src.data.toList.length := by
        rwa [Array.length_toList, ByteArray.size_data]
      have hdrop : src.data.toList.drop i = (src[i]'h) :: src.data.toList.drop (i + 1) :=
        List.drop_eq_getElem_cons hl
      have hhi : (src[i]'h).toNat >>> 4 = (src[i]'h).toNat / 16 := by
        rw [Nat.shiftRight_eq_div_pow]
      have hlo : ((src[i]'h).toNat &&& 15) = (src[i]'h).toNat % 16 := by
        change (src[i]'h).toNat &&& (2 ^ 4 - 1) = (src[i]'h).toNat % 2 ^ 4
        exact Nat.and_two_pow_sub_one_eq_mod _ 4
      simp only [h, ↓reduceDIte, byteArrayToHexAsciiLoop_eq src fuel (i + 1) _ (by omega),
        push_data_hex, hhi, hlo, hdrop, bytesToHexAscii_cons, List.append_assoc,
        List.cons_append, List.nil_append]
    · have hge : src.data.toList.length ≤ i := by
        rw [Array.length_toList, ByteArray.size_data]; omega
      simp [h, List.drop_eq_nil_of_le hge, bytesToHexAscii]

theorem byteArrayToHexAscii_toList (src : ByteArray) :
    (byteArrayToHexAscii src).data.toList = bytesToHexAscii src.data.toList := by
  have hemp : (ByteArray.emptyWithCapacity (2 * src.size)).data.toList = [] := rfl
  unfold byteArrayToHexAscii
  rw [byteArrayToHexAsciiLoop_eq src src.size 0 _ (by omega), hemp, List.drop_zero, List.nil_append]

/-- Stack-safe tail-recursive strict lowercase hex `Char` decoder. -/
def hexCharsToBytesLoop : List Char → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | [_], _ => none
  | a :: b :: rest, acc =>
    match decodeHexNibble? a, decodeHexNibble? b with
    | some hi, some lo => hexCharsToBytesLoop rest ((hi * 16 + lo).toUInt8 :: acc)
    | _, _ => none

theorem hexCharsToBytesLoop_eq : ∀ (cs : List Char) (acc : List UInt8),
    hexCharsToBytesLoop cs acc = (hexCharsToBytes? cs).map (acc.reverse ++ ·)
  | [], acc => by simp [hexCharsToBytesLoop, hexCharsToBytes?]
  | [_], _ => by simp [hexCharsToBytesLoop, hexCharsToBytes?]
  | a :: b :: rest, acc => by
    simp only [hexCharsToBytesLoop, hexCharsToBytes?, bind, Option.bind]
    cases decodeHexNibble? a with
    | none => rfl
    | some hi =>
      cases decodeHexNibble? b with
      | none => rfl
      | some lo =>
        dsimp only
        rw [hexCharsToBytesLoop_eq rest]
        cases hexCharsToBytes? rest <;> simp [List.reverse_cons, List.append_assoc]

def hexCharsToBytesExec? (cs : List Char) : Option (List UInt8) := hexCharsToBytesLoop cs []

@[csimp] theorem hexCharsToBytes?_eq_exec : @hexCharsToBytes? = @hexCharsToBytesExec? := by
  funext cs
  simpa [hexCharsToBytesExec?] using (hexCharsToBytesLoop_eq cs []).symm

/-- Stack-safe tail-recursive case-insensitive hex `Char` decoder. -/
def hexCharsToBytesAnyCaseLoop : List Char → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | [_], _ => none
  | a :: b :: rest, acc =>
    match decodeHexNibbleAnyCase? a, decodeHexNibbleAnyCase? b with
    | some hi, some lo => hexCharsToBytesAnyCaseLoop rest ((hi * 16 + lo).toUInt8 :: acc)
    | _, _ => none

theorem hexCharsToBytesAnyCaseLoop_eq : ∀ (cs : List Char) (acc : List UInt8),
    hexCharsToBytesAnyCaseLoop cs acc = (hexCharsToBytesAnyCase? cs).map (acc.reverse ++ ·)
  | [], acc => by simp [hexCharsToBytesAnyCaseLoop, hexCharsToBytesAnyCase?]
  | [_], _ => by simp [hexCharsToBytesAnyCaseLoop, hexCharsToBytesAnyCase?]
  | a :: b :: rest, acc => by
    simp only [hexCharsToBytesAnyCaseLoop, hexCharsToBytesAnyCase?, bind, Option.bind]
    cases decodeHexNibbleAnyCase? a with
    | none => rfl
    | some hi =>
      cases decodeHexNibbleAnyCase? b with
      | none => rfl
      | some lo =>
        dsimp only
        rw [hexCharsToBytesAnyCaseLoop_eq rest]
        cases hexCharsToBytesAnyCase? rest <;> simp [List.reverse_cons, List.append_assoc]

def hexCharsToBytesAnyCaseExec? (cs : List Char) : Option (List UInt8) :=
  hexCharsToBytesAnyCaseLoop cs []

@[csimp] theorem hexCharsToBytesAnyCase?_eq_exec :
    @hexCharsToBytesAnyCase? = @hexCharsToBytesAnyCaseExec? := by
  funext cs
  simpa [hexCharsToBytesAnyCaseExec?] using (hexCharsToBytesAnyCaseLoop_eq cs []).symm

/-- Stack-safe tail-recursive strict ASCII hex byte decoder. -/
def hexAsciiToBytesLoop : List UInt8 → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | [_], _ => none
  | a :: b :: rest, acc =>
    match decodeHexNibbleByte? a, decodeHexNibbleByte? b with
    | some hi, some lo => hexAsciiToBytesLoop rest ((hi * 16 + lo).toUInt8 :: acc)
    | _, _ => none

theorem hexAsciiToBytesLoop_eq : ∀ (bs acc : List UInt8),
    hexAsciiToBytesLoop bs acc = (hexAsciiToBytes? bs).map (acc.reverse ++ ·)
  | [], acc => by simp [hexAsciiToBytesLoop, hexAsciiToBytes?]
  | [_], _ => by simp [hexAsciiToBytesLoop, hexAsciiToBytes?]
  | a :: b :: rest, acc => by
    simp only [hexAsciiToBytesLoop, hexAsciiToBytes?, bind, Option.bind]
    cases decodeHexNibbleByte? a with
    | none => rfl
    | some hi =>
      cases decodeHexNibbleByte? b with
      | none => rfl
      | some lo =>
        dsimp only
        rw [hexAsciiToBytesLoop_eq rest]
        cases hexAsciiToBytes? rest <;> simp [List.reverse_cons, List.append_assoc]

def hexAsciiToBytesExec? (bs : List UInt8) : Option (List UInt8) := hexAsciiToBytesLoop bs []

@[csimp] theorem hexAsciiToBytes?_eq_exec : @hexAsciiToBytes? = @hexAsciiToBytesExec? := by
  funext bs
  simpa [hexAsciiToBytesExec?] using (hexAsciiToBytesLoop_eq bs []).symm

/-- Zero-`List` strict lowercase hex decoder directly over `ByteArray` into `ByteArray`. -/
def hexByteArrayStrictLoop (src : @& ByteArray) : Nat → Nat → ByteArray → Option ByteArray
  | 0, i, dst => if i == src.size then some dst else none
  | fuel + 1, i, dst =>
    if h2 : i + 1 < src.size then
      match decodeHexNibbleByte? (src[i]'(by omega)), decodeHexNibbleByte? (src[i + 1]'h2) with
      | some hi, some lo => hexByteArrayStrictLoop src fuel (i + 2) (dst.push (hi * 16 + lo).toUInt8)
      | _, _ => none
    else if i == src.size then some dst else none

def hexByteArrayStrict? (src : @& ByteArray) : Option ByteArray :=
  if src.size % 2 != 0 then none
  else hexByteArrayStrictLoop src (src.size / 2) 0 (ByteArray.emptyWithCapacity (src.size / 2))

theorem hexByteArrayStrictLoop_eq (src : ByteArray) :
    ∀ (fuel i : Nat) (dst : ByteArray), i ≤ src.size → src.size - i ≤ 2 * fuel →
      (hexByteArrayStrictLoop src fuel i dst).map (fun b => b.data.toList) =
        (hexAsciiToBytes? (src.data.toList.drop i)).map (dst.data.toList ++ ·)
  | 0, i, dst, hle, hf => by
    have heq : i = src.size := by omega
    subst heq
    have hnil : src.data.toList.drop src.size = [] :=
      List.drop_eq_nil_of_le (by rw [Array.length_toList, ByteArray.size_data]; exact Nat.le_refl _)
    simp [hexByteArrayStrictLoop, hnil, hexAsciiToBytes?]
  | fuel + 1, i, dst, hle, hf => by
    unfold hexByteArrayStrictLoop
    by_cases h2 : i + 1 < src.size
    · have hl0 : i < src.data.toList.length := by
        rw [Array.length_toList, ByteArray.size_data]; omega
      have hl1 : i + 1 < src.data.toList.length := by
        rw [Array.length_toList, ByteArray.size_data]; omega
      have hdrop0 : src.data.toList.drop i = (src[i]'(by omega)) :: src.data.toList.drop (i + 1) :=
        List.drop_eq_getElem_cons hl0
      have hdrop1 : src.data.toList.drop (i + 1) = (src[i + 1]'h2) :: src.data.toList.drop (i + 2) :=
        List.drop_eq_getElem_cons hl1
      simp only [h2, ↓reduceDIte, hdrop0, hdrop1, hexAsciiToBytes?, bind, Option.bind]
      cases decodeHexNibbleByte? (src[i]'(by omega)) with
      | none => rfl
      | some hi =>
        cases decodeHexNibbleByte? (src[i + 1]'h2) with
        | none => rfl
        | some lo =>
          dsimp only
          rw [hexByteArrayStrictLoop_eq src fuel (i + 2) _ (by omega) (by omega), push_data_hex]
          cases hexAsciiToBytes? (src.data.toList.drop (i + 2)) <;>
            simp [List.append_assoc]
    · simp only [h2, ↓reduceDIte]
      by_cases heq : i = src.size
      · subst heq
        have hnil : src.data.toList.drop src.size = [] :=
          List.drop_eq_nil_of_le (by rw [Array.length_toList, ByteArray.size_data]; exact Nat.le_refl _)
        simp [hnil, hexAsciiToBytes?]
      · have hl0 : i < src.data.toList.length := by
          rw [Array.length_toList, ByteArray.size_data]; omega
        have hdrop0 : src.data.toList.drop i = (src[i]'(by omega)) :: src.data.toList.drop (i + 1) :=
          List.drop_eq_getElem_cons hl0
        have hnil1 : src.data.toList.drop (i + 1) = [] :=
          List.drop_eq_nil_of_le (by rw [Array.length_toList, ByteArray.size_data]; omega)
        have hne_b : (i == src.size) = false := beq_eq_false_iff_ne.mpr heq
        simp [hne_b, hdrop0, hnil1, hexAsciiToBytes?]

theorem hexByteArrayStrict?_toList (src : ByteArray) :
    (hexByteArrayStrict? src).map (fun b => b.data.toList) = hexAsciiToBytes? src.data.toList := by
  unfold hexByteArrayStrict?
  by_cases hodd : src.size % 2 != 0
  · have hlen_odd : src.data.toList.length % 2 ≠ 0 := by
      rw [Array.length_toList]
      exact bne_iff_ne.mp hodd
    simp [hodd, hexAsciiToBytes?_of_odd _ hlen_odd]
  · have heven : src.size % 2 = 0 := Decidable.of_not_not (fun h => hodd (bne_iff_ne.mpr h))
    have hb : (src.size % 2 != 0) = false := bne_eq_false_iff_eq.mpr heven
    have hdiv : src.size - 0 ≤ 2 * (src.size / 2) := by
      have h := Nat.div_add_mod src.size 2
      omega
    have hemp : (ByteArray.emptyWithCapacity (src.size / 2)).data.toList = [] := rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte,
      hexByteArrayStrictLoop_eq src (src.size / 2) 0 _ (Nat.zero_le _) hdiv,
      List.drop_zero, hemp, List.nil_append, Option.map_id']

end Obend.Codec.Hex

end
