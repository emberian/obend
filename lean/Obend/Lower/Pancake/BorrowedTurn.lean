module
public import Obend.Lower.Pancake.DragonStyleShard

public section
namespace Obend.Lower.Pancake.BorrowedTurn

set_option autoImplicit false

/-- Bounded HTTP/1.1 appliance endpoint. Each descriptor carries one request with a
canonical 1..4-digit `Content-Length` header admitting binary bodies of `0` through
`maxPayload` (4096) bytes, with no leading-zero ambiguity. -/
def header : ByteArray := "POST /turn HTTP/1.1\r\nHost: appliance\r\nContent-Length: ".toUTF8
def delimiter : ByteArray := "\r\n\r\n".toUTF8
def maxPayload : Nat := 4096
def maxDigits : Nat := 4
def minFrameSize : Nat := header.size + 1 + delimiter.size
def maxFrameSize (maxLen : Nat) : Nat := header.size + maxDigits + delimiter.size + maxLen

theorem header_size_eq : header.size = 54 := by
  unfold header; simp only [String.toUTF8_eq_toByteArray]; rfl

theorem delimiter_size_eq : delimiter.size = 4 := by
  unfold delimiter; simp only [String.toUTF8_eq_toByteArray]; rfl

theorem minFrameSize_eq : minFrameSize = 59 := by
  simp [minFrameSize, header_size_eq, delimiter_size_eq]

theorem maxFrameSize_4096 : maxFrameSize maxPayload = 4158 := by
  simp [maxFrameSize, maxPayload, maxDigits, header_size_eq, delimiter_size_eq]

structure Lease where
  owner : UInt16
  epoch : UInt64
  slot : UInt16
  generation : UInt64
  deriving DecidableEq, Repr

structure View extends Lease where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- Generation rollover advances the epoch. At the end of both counters the slot retires. -/
def recycle (l : Lease) : Option Lease :=
  if l.generation.toNat < 2 ^ 64 - 1 then some { l with generation := l.generation + 1 }
  else if l.epoch.toNat < 2 ^ 64 - 1 then some { l with epoch := l.epoch + 1, generation := 0 }
  else none

def serial (l : Lease) : Nat := l.epoch.toNat * 2 ^ 64 + l.generation.toNat

theorem recycle_advances {a b : Lease} (h : recycle a = some b) : serial b = serial a + 1 := by
  unfold recycle at h
  split at h
  · cases h
    simp [serial, UInt64.toNat_add, Nat.mod_eq_of_lt (show a.generation.toNat + 1 < 2 ^ 64 by omega)]
    omega
  · split at h
    · cases h
      have hg := a.generation.toNat_lt
      simp [serial, UInt64.toNat_add, Nat.mod_eq_of_lt (show a.epoch.toNat + 1 < 2 ^ 64 by omega),
        Nat.add_mul]
      omega
    · contradiction

theorem recycle_retires_iff (l : Lease) :
    recycle l = none ↔ l.generation.toNat = 2 ^ 64 - 1 ∧ l.epoch.toNat = 2 ^ 64 - 1 := by
  have hg := l.generation.toNat_lt
  have he := l.epoch.toNat_lt
  unfold recycle
  split <;> rename_i h1
  · constructor
    · intro h; cases h
    · intro ⟨h, _⟩; omega
  · split <;> rename_i h2
    · constructor
      · intro h; cases h
      · intro ⟨_, h⟩; omega
    · constructor
      · intro _; omega
      · intro _; rfl

/-- Only metadata is produced. Reads validate against the current slot owner and extent. -/
def readByte (frame : ByteArray) (current : Lease) (v : View) (i : Nat) : Option UInt8 :=
  if decide (v.toLease = current ∧ v.offset + v.length ≤ frame.size ∧ i < v.length)
  then some frame[v.offset + i]! else none

theorem readByte_eq_some_iff (frame : ByteArray) (current : Lease) (v : View) (i : Nat) (b : UInt8) :
    readByte frame current v i = some b ↔
      v.toLease = current ∧ v.offset + v.length ≤ frame.size ∧ i < v.length ∧ b = frame[v.offset + i]! := by
  unfold readByte
  cases hd : decide (v.toLease = current ∧ v.offset + v.length ≤ frame.size ∧ i < v.length) with
  | false =>
    have hnot := of_decide_eq_false hd
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    intro ⟨h1, h2, h3, _⟩; exact hnot ⟨h1, h2, h3⟩
  | true =>
    have hok := of_decide_eq_true hd
    simp only [↓reduceIte, Option.some.injEq, hok, true_and, eq_comm]

inductive Later : Lease → Lease → Prop
  | once {a b} : recycle a = some b → Later a b
  | more {a b c} : Later a b → recycle b = some c → Later a c

theorem stale_never_resolves {a b : Lease} (h : Later a b) (frame : ByteArray) (off len i : Nat) :
    readByte frame b ⟨a, off, len⟩ i = none := by
  have lt : serial a < serial b := by
    induction h with
    | once h => rw [recycle_advances h]; omega
    | more _ h ih => rw [recycle_advances h]; omega
  have ne : a ≠ b := fun e => (Nat.ne_of_lt lt) (congrArg serial e)
  simp [readByte, ne]

/-- Compare in place. No body or header byte arrays are constructed by the parser. -/
def matchBytes (frame pat : ByteArray) (off : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => frame[off + n]? == pat[n]? && matchBytes frame pat off n

theorem matchBytes_iff (frame pat : ByteArray) (off n : Nat) :
    matchBytes frame pat off n = true ↔ ∀ i < n, frame[off + i]? = pat[i]? := by
  induction n with
  | zero => simp [matchBytes]
  | succ n ih =>
    simp only [matchBytes, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨last, prev⟩ i hi
      by_cases eq : i = n
      · simpa [eq] using last
      · exact prev i (by omega)
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

def isAsciiDigit (b : UInt8) : Bool :=
  decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- Scan up to `fuel` ASCII decimal digits starting at `frame[off + d]`. -/
def scanDigits (frame : ByteArray) (off : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, d, acc => (d, acc)
  | fuel + 1, d, acc =>
    match frame[off + d]? with
    | some b =>
      if isAsciiDigit b then
        scanDigits frame off fuel (d + 1) (acc * 10 + (b.toNat - 48))
      else (d, acc)
    | none => (d, acc)

theorem scanDigits_bounds (frame : ByteArray) (off fuel d acc : Nat) :
    d ≤ (scanDigits frame off fuel d acc).1 ∧
    (scanDigits frame off fuel d acc).1 ≤ d + fuel := by
  induction fuel generalizing d acc with
  | zero => simp [scanDigits]
  | succ fuel ih =>
    unfold scanDigits
    cases frame[off + d]? with
    | none => simp
    | some b =>
      cases hdig : isAsciiDigit b with
      | false => simp [hdig]
      | true =>
        simp only [hdig, ↓reduceIte]
        have h := ih (d + 1) (acc * 10 + (b.toNat - 48))
        omega

/-- Bounded HTTP/1.1 parser accepting `0 ≤ Content-Length ≤ maxLen` (`1..4` canonical digits,
no leading zeros except `"0"`), returning only borrowed `(offset, length)` metadata. -/
def parseWith (maxLen : Nat) (frame : ByteArray) (lease : Lease) : Option View :=
  if decide (minFrameSize ≤ frame.size ∧ frame.size ≤ maxFrameSize maxLen) &&
      matchBytes frame header 0 header.size then
    let (d, len) := scanDigits frame header.size maxDigits 0 0
    let off := header.size + d + delimiter.size
    if decide (1 ≤ d ∧ d ≤ maxDigits ∧ len ≤ maxLen ∧ frame.size = off + len) &&
        (decide (d = 1) || frame[header.size]! != 48) &&
        matchBytes frame delimiter (header.size + d) delimiter.size then
      some ⟨lease, off, len⟩
    else none
  else none

def parse (frame : ByteArray) (lease : Lease) : Option View :=
  parseWith maxPayload frame lease

theorem parseWith_eq_some_iff (maxLen : Nat) (frame : ByteArray) (lease : Lease) (v : View) :
    parseWith maxLen frame lease = some v ↔
      let (d, len) := scanDigits frame header.size maxDigits 0 0
      let off := header.size + d + delimiter.size
      minFrameSize ≤ frame.size ∧ frame.size ≤ maxFrameSize maxLen ∧
      (∀ i < header.size, frame[i]? = header[i]?) ∧
      1 ≤ d ∧ d ≤ maxDigits ∧ len ≤ maxLen ∧ frame.size = off + len ∧
      (d = 1 ∨ frame[header.size]! ≠ 48) ∧
      (∀ i < delimiter.size, frame[header.size + d + i]? = delimiter[i]?) ∧
      v = ⟨lease, off, len⟩ := by
  unfold parseWith
  dsimp only
  cases hpre : (decide (minFrameSize ≤ frame.size ∧ frame.size ≤ maxFrameSize maxLen) &&
      matchBytes frame header 0 header.size) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    intro ⟨hmin, hmax, hhdr, _⟩
    have h1 : decide (minFrameSize ≤ frame.size ∧ frame.size ≤ maxFrameSize maxLen) = true :=
      decide_eq_true ⟨hmin, hmax⟩
    have h2 : matchBytes frame header 0 header.size = true :=
      (matchBytes_iff frame header 0 header.size).mpr (by simpa using hhdr)
    simp [h1, h2] at hpre
  | true =>
    simp only [↓reduceIte]
    simp only [Bool.and_eq_true, decide_eq_true_eq, matchBytes_iff, Nat.zero_add] at hpre
    cases hpost : (decide (1 ≤ (scanDigits frame header.size maxDigits 0 0).1 ∧
        (scanDigits frame header.size maxDigits 0 0).1 ≤ maxDigits ∧
        (scanDigits frame header.size maxDigits 0 0).2 ≤ maxLen ∧
        frame.size = header.size + (scanDigits frame header.size maxDigits 0 0).1 + delimiter.size +
          (scanDigits frame header.size maxDigits 0 0).2) &&
        (decide ((scanDigits frame header.size maxDigits 0 0).1 = 1) || frame[header.size]! != 48) &&
        matchBytes frame delimiter (header.size + (scanDigits frame header.size maxDigits 0 0).1) delimiter.size) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
      intro ⟨_, _, _, hd1, hd4, hlen, hsz, hnz, hdel, _⟩
      have h1 : decide (1 ≤ (scanDigits frame header.size maxDigits 0 0).1 ∧
          (scanDigits frame header.size maxDigits 0 0).1 ≤ maxDigits ∧
          (scanDigits frame header.size maxDigits 0 0).2 ≤ maxLen ∧
          frame.size = header.size + (scanDigits frame header.size maxDigits 0 0).1 + delimiter.size +
            (scanDigits frame header.size maxDigits 0 0).2) = true :=
        decide_eq_true ⟨hd1, hd4, hlen, hsz⟩
      have h2 : (decide ((scanDigits frame header.size maxDigits 0 0).1 = 1) || frame[header.size]! != 48) = true := by
        rcases hnz with h | h
        · simp [h]
        · simp [bne_iff_ne, h]
      have h3 : matchBytes frame delimiter (header.size + (scanDigits frame header.size maxDigits 0 0).1) delimiter.size = true :=
        (matchBytes_iff ..).mpr hdel
      simp [h1, h2, h3] at hpost
    | true =>
      simp only [↓reduceIte, Option.some.injEq]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, matchBytes_iff] at hpost
      constructor
      · intro hv
        exact ⟨hpre.1.1, hpre.1.2, hpre.2, hpost.1.1.1, hpost.1.1.2.1, hpost.1.1.2.2.1,
          hpost.1.1.2.2.2, hpost.1.2, hpost.2, hv.symm⟩
      · intro h
        exact h.2.2.2.2.2.2.2.2.2.symm

theorem parseWith_sound {maxLen : Nat} {frame : ByteArray} {lease : Lease} {v : View}
    (h : parseWith maxLen frame lease = some v) :
    v.toLease = lease ∧ minFrameSize ≤ v.offset ∧ v.offset ≤ header.size + maxDigits + delimiter.size ∧
    v.length ≤ maxLen ∧ v.offset + v.length = frame.size ∧
    ∀ i, i < v.length → readByte frame lease v i = some frame[v.offset + i]! := by
  have hiff := (parseWith_eq_some_iff maxLen frame lease v).mp h
  dsimp only at hiff
  obtain ⟨_, _, _, hd1, hd4, hlen, hsz, _, _, rfl⟩ := hiff
  refine ⟨rfl, by unfold minFrameSize; dsimp only; omega, by dsimp only; omega, hlen, hsz.symm, fun i hi => ?_⟩
  exact (readByte_eq_some_iff ..).mpr ⟨rfl, by dsimp only at *; omega, hi, rfl⟩

theorem parse_sound {frame : ByteArray} {lease : Lease} {v : View} (h : parse frame lease = some v) :
    v.toLease = lease ∧ 59 ≤ v.offset ∧ v.offset ≤ 62 ∧ v.length ≤ maxPayload ∧
    v.offset + v.length = frame.size ∧
    ∀ i, i < v.length → readByte frame lease v i = some frame[v.offset + i]! := by
  have hs := parseWith_sound h
  rw [minFrameSize_eq, header_size_eq, delimiter_size_eq] at hs
  exact hs

theorem parse_header {frame : ByteArray} {lease : Lease} {v : View} (h : parse frame lease = some v) :
    (∀ i < header.size, frame[i]? = header[i]?) ∧
    (∀ i < delimiter.size, frame[v.offset - delimiter.size + i]? = delimiter[i]?) := by
  have hiff := (parseWith_eq_some_iff maxPayload frame lease v).mp h
  dsimp only at hiff
  obtain ⟨_, _, hhdr, _, _, _, _, _, hdel, rfl⟩ := hiff
  exact ⟨hhdr, by simpa [Nat.add_sub_cancel] using hdel⟩

theorem parseWith_rejects_short {maxLen : Nat} {frame : ByteArray} {lease : Lease}
    (h : frame.size < minFrameSize) : parseWith maxLen frame lease = none := by
  cases hp : parseWith maxLen frame lease with
  | none => rfl
  | some v =>
    have hiff := (parseWith_eq_some_iff maxLen frame lease v).mp hp
    omega

theorem parseWith_rejects_oversize {maxLen : Nat} {frame : ByteArray} {lease : Lease}
    (h : maxFrameSize maxLen < frame.size) : parseWith maxLen frame lease = none := by
  cases hp : parseWith maxLen frame lease with
  | none => rfl
  | some v =>
    have hiff := (parseWith_eq_some_iff maxLen frame lease v).mp hp
    omega

private def fixture : Lease := ⟨1, 2, 0, 3⟩
#guard (parseWith 4096 (header ++ "0\r\n\r\n".toUTF8) fixture) == some ⟨fixture, 59, 0⟩
#guard (parse (header ++ "0\r\n\r\n".toUTF8) fixture) == some ⟨fixture, 59, 0⟩
#guard (parse (header ++ "7\r\n\r\n0123456".toUTF8) fixture) == some ⟨fixture, 59, 7⟩
#guard (parse (header ++ "10\r\n\r\n0123456789".toUTF8) fixture) == some ⟨fixture, 60, 10⟩
#guard (parse (header ++ "00\r\n\r\n".toUTF8) fixture).isNone
#guard (parse (header ++ "07\r\n\r\n0123456".toUTF8) fixture).isNone
#guard (parse (header ++ "11\r\n\r\n0123456789".toUTF8) fixture).isNone
#guard (parse (header ++ "4097\r\n\r\n".toUTF8) fixture).isNone

end Obend.Lower.Pancake.BorrowedTurn
