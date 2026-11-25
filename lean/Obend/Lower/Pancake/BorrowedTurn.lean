module
public import Obend.Lower.Pancake.DragonStyleShard
import Obend.Tactic.Tooth

public section
namespace Obend.Lower.Pancake.BorrowedTurn

/-- A bounded HTTP/1.1 appliance endpoint. Each descriptor contains exactly one request.
The canonical two-digit length admits binary bodies of 10 through 99 bytes. -/
def header := "POST /turn HTTP/1.1\r\nHost: appliance\r\nContent-Length: ".toUTF8
def delimiter := "\r\n\r\n".toUTF8
def bodyOffset := header.size + 2 + delimiter.size

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
  if l.generation.toNat < 2^64-1 then some {l with generation := l.generation + 1}
  else if l.epoch.toNat < 2^64-1 then some {l with epoch := l.epoch+1, generation := 0}
  else none

def serial (l : Lease) := l.epoch.toNat * 2^64 + l.generation.toNat

theorem recycle_advances {a b : Lease} (h : recycle a = some b) : serial b = serial a + 1 := by
  unfold recycle at h
  split at h
  · cases h
    simp [serial, UInt64.toNat_add, Nat.mod_eq_of_lt (show a.generation.toNat + 1 < 2^64 by omega)]
    omega
  · split at h
    · cases h
      have hg := a.generation.toNat_lt
      simp [serial, UInt64.toNat_add, Nat.mod_eq_of_lt (show a.epoch.toNat + 1 < 2^64 by omega),
        Nat.add_mul]
      omega
    · contradiction

/-- Only metadata is produced. Reads validate against the current slot owner and extent. -/
def readByte (frame : ByteArray) (current : Lease) (v : View) (i : Nat) : Option UInt8 :=
  if v.toLease = current ∧ v.offset + v.length ≤ frame.size ∧ i < v.length
  then some frame[v.offset+i]! else none

inductive Later : Lease → Lease → Prop
  | once {a b} : recycle a = some b → Later a b
  | more {a b c} : Later a b → recycle b = some c → Later a c

theorem stale_never_resolves {a b} (h : Later a b) (frame : ByteArray) (off len i : Nat) :
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
  | n+1 => frame[off+n]? == pat[n]? && matchBytes frame pat off n

theorem matchBytes_iff (frame pat : ByteArray) (off n : Nat) :
    matchBytes frame pat off n = true ↔ ∀ i < n, frame[off+i]? = pat[i]? := by
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

def decimalLength (frame : ByteArray) :=
  (frame[header.size]!.toNat-48)*10 + (frame[header.size+1]!.toNat-48)

def validLength (frame : ByteArray) : Bool :=
  let a := frame[header.size]!.toNat
  let b := frame[header.size+1]!.toNat
  decide (49 ≤ a ∧ a ≤ 57 ∧ 48 ≤ b ∧ b ≤ 57 ∧ frame.size = bodyOffset + decimalLength frame)

def parse (frame : ByteArray) (lease : Lease) : Option View :=
  if bodyOffset + 10 ≤ frame.size ∧ frame.size ≤ bodyOffset + 99 ∧
    matchBytes frame header 0 header.size ∧ matchBytes frame delimiter (header.size+2) delimiter.size ∧
    validLength frame then some ⟨lease, bodyOffset, decimalLength frame⟩ else none

theorem parse_sound {frame lease v} (h : parse frame lease = some v) :
    v.toLease = lease ∧ v.offset = bodyOffset ∧ v.offset + v.length = frame.size ∧
    ∀ i, i < v.length → readByte frame lease v i = some frame[bodyOffset+i]! := by
  unfold parse at h
  split at h <;> try contradiction
  cases h
  simp_all [validLength,readByte]

theorem parse_header {frame lease v} (h : parse frame lease = some v) :
    (∀ i < header.size, frame[i]? = header[i]?) ∧
    (∀ i < delimiter.size, frame[header.size+2+i]? = delimiter[i]?) := by
  unfold parse at h
  split at h <;> try contradiction
  rename_i ok
  exact ⟨by simpa using (matchBytes_iff ..).mp ok.2.2.1,
    (matchBytes_iff ..).mp ok.2.2.2.1⟩

private def fixture : Lease := ⟨1,2,0,3⟩
#guard (parse (header ++ "10\r\n\r\n0123456789".toUTF8) fixture).isSome
#guard (parse (header ++ "11\r\n\r\n0123456789".toUTF8) fixture).isNone
example : recycle ⟨0, 0xffffffffffffffff, 0, 0xffffffffffffffff⟩ = none := by decide

#tooth stale_never_resolves by mutation readByte := fun frame _ v i => frame[v.offset+i]?

end Obend.Lower.Pancake.BorrowedTurn
