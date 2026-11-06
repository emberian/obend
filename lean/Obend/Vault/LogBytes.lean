module

/-
# Obend.Vault.LogBytes — the log read and written as bytes in place

`Obend.Vault.Log` reads and writes the log as a `List UInt8`: the shape its theorems are about. A
process reads the log as the `ByteArray` the file is, and reads each record at an offset into it,
copying out only the record's own bytes; it writes each record as a `ByteArray` pushed byte by byte.
The functions here are those, and each is proved to be its list twin, so every theorem of
`Obend.Vault.Log` and `Obend.Vault.Retention` is a theorem about what the process does:

* `encode_bytes_eq`: a record's bytes are `encodeRecord`'s, byte for byte;
* `parseOneAt_eq`, `parseFromAt_eq`, `parseLogAt_eq`: reading at an offset is reading the list
  dropped to that offset, and what is left is the list dropped to the offset reached;
* `holdsAt_eq`: a checkpoint holds against the bytes exactly when it holds against their list.

Reading at an offset costs the bytes read, not the bytes before them: the records after a checkpoint
are read without touching the records before it.
-/

public import Obend.Vault.Retention
public import Obend.Digest.Cshake256.Fast

@[expose] public section

namespace Obend.Vault.LogBytes

open Obend.Vault.Log
open Obend.Vault.Rehydration (genesisSentinel)
open Obend.Digest.Cshake256.Fast (pushList pushList_data empty_data)

set_option autoImplicit false

section Codec
variable (Hb : Bytes → Bytes)

/-- **A record's bytes**, pushed into a byte array: its header, the turn, the seal. -/
def encodeRecordBytes (r : Record) : ByteArray :=
  pushList (pushList (pushList ByteArray.empty (headerOf r)) r.payload) (be 32 (Hr Hb r.receipt))

theorem encode_bytes_eq (r : Record) : (encodeRecordBytes Hb r).data.toList = encodeRecord Hb r := by
  simp [encodeRecordBytes, pushList_data, encodeRecord]

/-- `n` bytes of `b` from `i` (fewer at its end), copied out. -/
def slice (b : ByteArray) (i n : Nat) : Bytes := (b.extract i (i + n)).data.toList

theorem slice_eq (b : ByteArray) (i n : Nat) : slice b i n = (b.data.toList.drop i).take n := by
  simp [slice, List.extract]

/-- **Read one record at `off`** (`parseOne` at an offset): the record and the offset after it. -/
def parseOneAt (prev : Option Nat) (b : ByteArray) (off : Nat) : Except Drop (Record × Nat) :=
  if off + 136 ≤ b.size then
    let h := slice b off 136
    if h.take 4 ≠ magic then .error .magic else
    let len := unbe ((h.drop 4).take 4)
    if off + 136 + (len + 32) ≤ b.size then
      let body := slice b (off + 136) (len + 32)
      let rc := fieldsOf ((h.drop 4).drop 4)
      let payload := body.take len
      if rc.effectsHash ≠ dig Hb payload then .error .digest
      else if unbe (body.drop len) ≠ Hr Hb rc then .error .seal
      else if prev.any (rc.prevHash ≠ ·) then .error .link
      else .ok (⟨rc, payload⟩, off + 136 + (len + 32))
    else .error .torn
  else .error .torn

theorem drop_drop' (L : Bytes) (a b : Nat) : (L.drop a).drop b = L.drop (a + b) := by
  rw [List.drop_drop]

theorem parseOneAt_eq (prev : Option Nat) (b : ByteArray) (off : Nat) :
    parseOne Hb prev (b.data.toList.drop off) =
      (parseOneAt Hb prev b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  unfold parseOne parseOneAt
  simp only [slice_eq]
  rw [← hs]
  generalize b.data.toList = L
  by_cases h1 : off + 136 ≤ L.length
  · have e1 : takeN 136 (L.drop off) = some ((L.drop off).take 136, L.drop (off + 136)) := by
      simp only [takeN, List.length_drop, List.drop_drop]; rw [if_pos (by omega)]
    rw [e1, if_pos h1]
    dsimp only
    split
    · rfl
    · generalize unbe ((((L.drop off).take 136).drop 4).take 4) = len
      by_cases h2 : off + 136 + (len + 32) ≤ L.length
      · have e2 : takeN (len + 32) (L.drop (off + 136)) =
            some ((L.drop (off + 136)).take (len + 32), L.drop (off + 136 + (len + 32))) := by
          simp only [takeN, List.length_drop, List.drop_drop]; rw [if_pos (by omega)]
        rw [e2, if_pos h2]
        dsimp only
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · rfl
      · have e2 : takeN (len + 32) (L.drop (off + 136)) = none := by
          simp only [takeN, List.length_drop]; rw [if_neg (by omega)]
        rw [e2, if_neg h2]; rfl
  · have e1 : takeN 136 (L.drop off) = none := by
      simp only [takeN, List.length_drop]; rw [if_neg (by omega)]
    rw [e1, if_neg h1]; rfl

theorem parseOneAt_ok {prev : Option Nat} {b : ByteArray} {off : Nat} {r : Record} {o : Nat}
    (h : parseOneAt Hb prev b off = .ok (r, o)) : off < o ∧ o ≤ b.size := by
  unfold parseOneAt at h
  split at h
  · simp only at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h; omega
      · cases h
  · cases h

/-- **Read records at an offset** while they parse and follow one another (`parseFrom` at an offset):
the records, the offset where the dropped tail starts, and why. -/
def parseFromAt (prev : Nat) (b : ByteArray) (off : Nat) : List Record × Nat × Option Drop :=
  if b.size ≤ off then ([], off, none) else
  match hp : parseOneAt Hb (some prev) b off with
  | .error d => ([], off, some d)
  | .ok (r, o) =>
    have := (parseOneAt_ok Hb hp).1
    let (qs, o', why) := parseFromAt (Hr Hb r.receipt) b o
    (r :: qs, o', why)
termination_by b.size - off

theorem parseFromAt_end {prev : Nat} {b : ByteArray} {off : Nat} (h : b.size ≤ off) :
    parseFromAt Hb prev b off = ([], off, none) := by
  rw [parseFromAt]; simp [h]

theorem parseFromAt_error {prev : Nat} {b : ByteArray} {off : Nat} {d : Drop} (h0 : ¬ b.size ≤ off)
    (h : parseOneAt Hb (some prev) b off = .error d) : parseFromAt Hb prev b off = ([], off, some d) := by
  rw [parseFromAt]
  simp only [h0, ↓reduceIte]
  split
  · rename_i d' h'
    rw [h] at h'; cases h'; rfl
  · rename_i r o h'
    rw [h] at h'; cases h'

theorem parseFromAt_ok {prev : Nat} {b : ByteArray} {off o : Nat} {r : Record}
    (h : parseOneAt Hb (some prev) b off = .ok (r, o)) :
    parseFromAt Hb prev b off =
      (r :: (parseFromAt Hb (Hr Hb r.receipt) b o).1, (parseFromAt Hb (Hr Hb r.receipt) b o).2) := by
  have h0 : ¬ b.size ≤ off := by have := parseOneAt_ok Hb h; omega
  rw [parseFromAt]
  simp only [h0, ↓reduceIte]
  split
  · rename_i d' h'
    rw [h] at h'; cases h'
  · rename_i r' o' h'
    rw [h] at h'; cases h'; rfl

theorem parseFromAt_eq (prev : Nat) (b : ByteArray) (off : Nat) :
    parseFrom Hb prev (b.data.toList.drop off) =
      ((parseFromAt Hb prev b off).1, b.data.toList.drop (parseFromAt Hb prev b off).2.1,
        (parseFromAt Hb prev b off).2.2) := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  by_cases h0 : b.size ≤ off
  · rw [parseFromAt_end Hb h0, List.drop_eq_nil_of_le (by omega), parseFrom_nil]
  · have hne : b.data.toList.drop off ≠ [] := by
      intro e; have := congrArg List.length e; simp only [List.length_drop, List.length_nil] at this; omega
    have hp := parseOneAt_eq Hb (some prev) b off
    cases e : parseOneAt Hb (some prev) b off with
    | error d =>
      rw [e] at hp
      rw [parseFrom_error Hb hne hp, parseFromAt_error Hb h0 e]
    | ok p =>
      obtain ⟨r, o⟩ := p
      rw [e] at hp
      have := (parseOneAt_ok Hb e).1
      rw [parseFrom_ok Hb hp, parseFromAt_ok Hb e, parseFromAt_eq (Hr Hb r.receipt) b o]
termination_by b.size - off

/-- **Read a log that may start with a checkpoint record**, at offsets (`Retention.parseLog`). -/
def parseLogAt (anchorOf : Bytes → Option Nat) (b : ByteArray) : List Record × Nat × Option Drop :=
  match parseOneAt Hb (some genesisSentinel) b 0 with
  | .ok (r, o) =>
    match anchorOf r.payload with
    | some a =>
      let (qs, o', why) := parseFromAt Hb a b o
      (r :: qs, o', why)
    | none => parseFromAt Hb genesisSentinel b 0
  | .error _ => parseFromAt Hb genesisSentinel b 0

theorem parseLogAt_eq (anchorOf : Bytes → Option Nat) (b : ByteArray) :
    Retention.parseLog Hb anchorOf b.data.toList =
      ((parseLogAt Hb anchorOf b).1, b.data.toList.drop (parseLogAt Hb anchorOf b).2.1,
        (parseLogAt Hb anchorOf b).2.2) := by
  have h0 := parseOneAt_eq Hb (some genesisSentinel) b 0
  have hf := parseFromAt_eq Hb genesisSentinel b 0
  simp only [List.drop_zero] at h0 hf
  unfold Retention.parseLog parseLogAt
  cases e : parseOneAt Hb (some genesisSentinel) b 0 with
  | error d => rw [e] at h0; rw [h0]; exact hf
  | ok p =>
    obtain ⟨r, o⟩ := p
    rw [e] at h0; rw [h0]
    simp only [Except.map]
    cases anchorOf r.payload with
    | none => exact hf
    | some a => simp only [parseFromAt_eq Hb a b o]

/-- **A checkpoint holds** against a log's bytes (`Checkpoint.holds`), reading only its last record. -/
def holdsAt {W : Type} (decW : Bytes → Option W) (ck : Checkpoint) (b : ByteArray) : Option W :=
  if ck.count = 0 then none else
  let s := b.extract ck.start ck.stop
  match parseOneAt Hb none s 0 with
  | .ok (r, o) =>
    if o = s.size then
      if Hr Hb r.receipt = ck.anchor ∧ r.receipt.newCommit = dig Hb ck.world then decW ck.world else none
    else none
  | .error _ => none

theorem holdsAt_eq {W : Type} (decW : Bytes → Option W) (ck : Checkpoint) (b : ByteArray) :
    ck.holds Hb decW b.data.toList = holdsAt Hb decW ck b := by
  have hx : (b.extract ck.start ck.stop).data.toList = (b.data.toList.drop ck.start).take (ck.stop - ck.start) := by
    simp [List.extract]
  have h0 := parseOneAt_eq Hb none (b.extract ck.start ck.stop) 0
  simp only [List.drop_zero, hx] at h0
  have hs : (b.extract ck.start ck.stop).data.toList.length = (b.extract ck.start ck.stop).size := Array.length_toList
  unfold Checkpoint.holds holdsAt
  by_cases hc : ck.count = 0
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    rw [h0]
    cases e : parseOneAt Hb none (b.extract ck.start ck.stop) 0 with
    | error d => rfl
    | ok p =>
      obtain ⟨r, o⟩ := p
      have hle := (parseOneAt_ok Hb e).2
      simp only [Except.map]
      by_cases ho : o = (b.extract ck.start ck.stop).size
      · rw [if_pos ho]
        have : (b.extract ck.start ck.stop).data.toList.drop o = [] := List.drop_eq_nil_of_le (by omega)
        rw [hx] at this; rw [this]
      · rw [if_neg ho]
        have : (b.extract ck.start ck.stop).data.toList.drop o ≠ [] := by
          intro e'; have := congrArg List.length e'; simp only [List.length_drop, List.length_nil] at this; omega
        rw [hx] at this
        split
        · rename_i r' h'
          simp only [Except.ok.injEq, Prod.mk.injEq] at h'
          exact absurd h'.2 this
        · rfl

end Codec

end Obend.Vault.LogBytes

end
