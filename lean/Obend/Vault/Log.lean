module
public import Obend.Vault.Rehydration
public import Obend.Digest.Cshake256.Fast
public import Obend.Vault.Cost

public section

/-
# Obend.Vault.Log — the log is truth, the state is a cache

A vault's world is a function of its log. The log is a file of RECORDS, each a receipt of Pillar 1
(`Obend.Vault.Rehydration.WitnessReceipt`: the digest of the record before it, the world's commitment
before and after the turn, and the digest of the turn) followed by the turn's bytes and a seal (the
digest of the receipt). Nothing else is truth: the world a process serves is `replay` of the log, a
checkpoint is a cache of a prefix's replay, and the files of the vault are what the turns rendered.

This module is generic in the world `W`, the step a turn's bytes make (`Machine.step`), the world's
canonical bytes (`Machine.encW`, whose digest is a receipt's commitment) and the byte digest `Hb`.
`Obend.Vault.Replay` instantiates it at the deployed entry.

* **Bytes.** `encodeRecord`: `OBL1`, the turn's length (4 bytes), the receipt's four fields (32 bytes
  each, big-endian), the turn, the seal. `parseOne` reads one record and refuses it by name
  (`Drop`): `torn` (the bytes end inside it), `magic`, `digest` (the turn is not the one its receipt
  names), `seal` (the receipt is not the one its seal names), `link` (it does not follow the record
  before it). `parseFrom` reads records while they parse and link, and returns the rest, the dropped
  tail, with the reason.
* **The log is Pillar 1's chain.** `log_wellLinked`: the receipts of a log a session wrote, newest
  first, are `wellLinked` at the genesis sentinel, the discipline `wellLinked_append` extends;
  `parseFrom_sound`: whatever bytes are read, the records recovered are linked and self-checking.
* **`state_eq_replay_log`**: a session (the world a process holds and the records it appended) reached
  by admitted turns from genesis holds `replay` of its log.
* **`recover_eq_replay_prefix`**: a crash at ANY byte of the log a session wrote recovers the replay of
  the longest prefix of whole records, which is a state the session served (`Reachable`), and names
  the rest as a torn tail. Byte truncation is the crash model: a process stopped, or a power loss on a
  device that writes a file's bytes in order.
* **`checkpoint_is_cache`**: recovering from a checkpoint the session wrote and replaying the records
  after it gives exactly what recovering from genesis gives, at every truncation of the log: a
  checkpoint can be dropped and nothing is lost. Its one premise is that the world's bytes decode to
  the world, which the writer checks before it writes a checkpoint.

Migration-time relinking (re-deriving a log under a new step) is out of scope here; a log is replayed
by the step that wrote it.
-/

namespace Obend.Vault.Log

open Obend.Vault.Rehydration (WitnessReceipt wellLinked genesisSentinel)

set_option autoImplicit false

abbrev Bytes := List UInt8

/-! ## Numbers as bytes -/

/-- `n` as `k` big-endian bytes (`n` mod `256 ^ k`). -/
def be : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => be k (n / 256) ++ [n.toUInt8]

/-- Big-endian bytes as a number. -/
def unbe (xs : Bytes) : Nat := xs.foldl (fun a b => a * 256 + b.toNat) 0

theorem be_length : ∀ k n, (be k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [be, be_length k]

theorem unbe_append_single (xs : Bytes) (b : UInt8) : unbe (xs ++ [b]) = unbe xs * 256 + b.toNat := by
  simp [unbe, List.foldl_append]

theorem unbe_be : ∀ k n, n < 256 ^ k → unbe (be k n) = n
  | 0, n, h => by simp at h; subst h; rfl
  | k + 1, n, h => by
    have hk : n / 256 < 256 ^ k := by
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [be, unbe_append_single, unbe_be k (n / 256) hk]
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]
    omega

theorem foldl_unbe_lt : ∀ (xs : Bytes) (a : Nat),
    xs.foldl (fun a b => a * 256 + b.toNat) a < (a + 1) * 256 ^ xs.length
  | [], a => by simp
  | b :: xs, a => by
    simp only [List.foldl_cons, List.length_cons]
    have ih := foldl_unbe_lt xs (a * 256 + b.toNat)
    have hb := b.toNat_lt
    calc _ < (a * 256 + b.toNat + 1) * 256 ^ xs.length := ih
      _ ≤ ((a + 1) * 256) * 256 ^ xs.length := Nat.mul_le_mul_right _ (by omega)
      _ = (a + 1) * 256 ^ (xs.length + 1) := by rw [Nat.pow_succ, Nat.mul_comm (256 ^ _) 256, Nat.mul_assoc]

theorem unbe_lt (xs : Bytes) : unbe xs < 256 ^ xs.length := by
  have := foldl_unbe_lt xs 0
  simpa [unbe] using this

/-- A field is a number below `bound`: 32 bytes. -/
def bound : Nat := 256 ^ 32

/-! ## The digest, receipts and records -/

section Hash
variable (Hb : Bytes → Bytes)

/-- A digest as a field: the first 32 bytes of `Hb`, as a number. -/
def dig (b : Bytes) : Nat := unbe ((Hb b).take 32)

theorem dig_lt (b : Bytes) : dig Hb b < bound := by
  unfold dig bound
  have h1 := unbe_lt ((Hb b).take 32)
  have h2 : ((Hb b).take 32).length ≤ 32 := by simp only [List.length_take]; exact Nat.min_le_left _ _
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)

/-- A receipt's four fields, 32 bytes each. -/
def receiptBytes (rc : WitnessReceipt) : Bytes :=
  be 32 rc.prevHash ++ (be 32 rc.oldCommit ++ (be 32 rc.newCommit ++ be 32 rc.effectsHash))

/-- **The receipt's digest**, the `H` of Pillar 1's `wellLinked`: a record's seal, and the next
record's `prevHash`. -/
def Hr (rc : WitnessReceipt) : Nat := dig Hb (receiptBytes rc)

end Hash

/-- One record of the log: its receipt and the turn's bytes. -/
structure Record where
  receipt : WitnessReceipt
  payload : Bytes
deriving DecidableEq, Repr

/-- The four bytes a record starts with, `OBL1`. -/
def magic : Bytes := [0x4f, 0x42, 0x4c, 0x31]

section Codec
variable (Hb : Bytes → Bytes)

/-- A record's header: the magic, the turn's length, the receipt (136 bytes). -/
def headerOf (r : Record) : Bytes := magic ++ (be 4 r.payload.length ++ receiptBytes r.receipt)

/-- **A record's bytes**: its header, the turn, the seal. -/
def encodeRecord (r : Record) : Bytes := headerOf r ++ (r.payload ++ be 32 (Hr Hb r.receipt))

/-- The bytes of records, in order. -/
def encodeAll : List Record → Bytes
  | [] => []
  | r :: rs => encodeRecord Hb r ++ encodeAll rs

/-- A record is WELL-FORMED: its fields fit in 32 bytes, its turn in a length of 4 bytes, and its
receipt names its turn's digest. -/
def Record.WF (r : Record) : Prop :=
  r.receipt.prevHash < bound ∧ r.receipt.oldCommit < bound ∧ r.receipt.newCommit < bound ∧
    r.receipt.effectsHash = dig Hb r.payload ∧ r.payload.length < 256 ^ 4

theorem headerOf_length (r : Record) : (headerOf r).length = 136 := by
  simp [headerOf, magic, receiptBytes, be_length]

theorem encodeRecord_length (r : Record) :
    (encodeRecord Hb r).length = 136 + (r.payload.length + 32) := by
  simp [encodeRecord, headerOf_length, be_length]

/-- `n` bytes and the rest, when there are `n`. -/
def takeN (n : Nat) (bs : Bytes) : Option (Bytes × Bytes) :=
  if n ≤ bs.length then some (bs.take n, bs.drop n) else none

theorem takeN_append (a b : Bytes) : takeN a.length (a ++ b) = some (a, b) := by
  simp [takeN]

theorem takeN_none {n : Nat} {bs : Bytes} (h : bs.length < n) : takeN n bs = none := by
  simp [takeN]; omega

/-- Why a record was not read. -/
inductive Drop
  /-- the bytes end inside it -/
  | torn
  /-- it does not start with `OBL1` -/
  | magic
  /-- its turn is not the one its receipt's `effectsHash` names -/
  | digest
  /-- its receipt is not the one its seal names -/
  | seal
  /-- its `prevHash` is not the digest of the record before it -/
  | link
deriving DecidableEq, Repr

/-- The receipt a header's bytes after the magic and the length carry. -/
def fieldsOf (h : Bytes) : WitnessReceipt :=
  let r1 := h.drop 32
  let r2 := r1.drop 32
  let r3 := r2.drop 32
  ⟨unbe (h.take 32), unbe (r1.take 32), unbe (r2.take 32), unbe (r3.take 32)⟩

/-- **Read one record**, following the receipt digest `prev` (none: any). All of its bytes are read
before anything is checked, so bytes that end inside a record are `torn` whatever they say. -/
def parseOne (prev : Option Nat) (bs : Bytes) : Except Drop (Record × Bytes) :=
  match takeN 136 bs with
  | none => .error .torn
  | some (h, rest) =>
    if h.take 4 ≠ magic then .error .magic else
    let len := unbe ((h.drop 4).take 4)
    match takeN (len + 32) rest with
    | none => .error .torn
    | some (body, rest') =>
      let rc := fieldsOf ((h.drop 4).drop 4)
      let payload := body.take len
      if rc.effectsHash ≠ dig Hb payload then .error .digest
      else if unbe (body.drop len) ≠ Hr Hb rc then .error .seal
      else if prev.any (rc.prevHash ≠ ·) then .error .link
      else .ok (⟨rc, payload⟩, rest')

theorem parseOne_ok_inv {prev : Option Nat} {bs rest : Bytes} {r : Record}
    (h : parseOne Hb prev bs = .ok (r, rest)) :
    rest.length < bs.length ∧ r.receipt.effectsHash = dig Hb r.payload ∧
      ∀ p, prev = some p → r.receipt.prevHash = p := by
  unfold parseOne at h
  cases e1 : takeN 136 bs with
  | none => rw [e1] at h; cases h
  | some x =>
    obtain ⟨hd, tl⟩ := x
    rw [e1] at h
    dsimp only at h
    have hl1 : tl.length + 136 ≤ bs.length := by
      simp only [takeN] at e1; split at e1
      · cases e1; simp only [List.length_drop]; omega
      · cases e1
    split at h
    · cases h
    · try dsimp only at h
      cases e2 : takeN (unbe ((hd.drop 4).take 4) + 32) tl with
      | none => rw [e2] at h; cases h
      | some y =>
        obtain ⟨bd, tl'⟩ := y
        rw [e2] at h
        dsimp only at h
        have hl2 : tl'.length ≤ tl.length := by
          simp only [takeN] at e2; split at e2
          · cases e2; simp only [List.length_drop]; omega
          · cases e2
        split at h
        · cases h
        · rename_i heff
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i hlink
              cases h
              refine ⟨by omega, by simpa using heff, ?_⟩
              intro p hp
              subst hp
              simpa using hlink

theorem parseOne_rest {prev : Option Nat} {bs rest : Bytes} {r : Record}
    (h : parseOne Hb prev bs = .ok (r, rest)) : rest.length < bs.length :=
  (parseOne_ok_inv Hb h).1

/-- **Read records** while they parse and follow one another, from the receipt digest `prev`: the
records, the bytes left (the dropped tail) and why the first of them was not read. -/
def parseFrom (prev : Nat) (bs : Bytes) : List Record × Bytes × Option Drop :=
  if bs = [] then ([], [], none) else
  match hp : parseOne Hb (some prev) bs with
  | .error d => ([], bs, some d)
  | .ok (r, rest) =>
    have := parseOne_rest Hb hp
    let (qs, tail, why) := parseFrom (Hr Hb r.receipt) rest
    (r :: qs, tail, why)
termination_by bs.length

theorem parseFrom_nil (prev : Nat) : parseFrom Hb prev [] = ([], [], none) := by
  rw [parseFrom]; simp

theorem parseFrom_error {prev : Nat} {bs : Bytes} {d : Drop} (hne : bs ≠ [])
    (h : parseOne Hb (some prev) bs = .error d) : parseFrom Hb prev bs = ([], bs, some d) := by
  rw [parseFrom]
  simp only [hne, ↓reduceIte]
  split
  · rename_i d' h'
    rw [h] at h'; cases h'; rfl
  · rename_i r rest h'
    rw [h] at h'; cases h'

theorem parseFrom_ok {prev : Nat} {bs rest : Bytes} {r : Record}
    (h : parseOne Hb (some prev) bs = .ok (r, rest)) :
    parseFrom Hb prev bs =
      ((r :: (parseFrom Hb (Hr Hb r.receipt) rest).1), (parseFrom Hb (Hr Hb r.receipt) rest).2) := by
  have hne : bs ≠ [] := by
    intro e; subst e; have := parseOne_rest Hb h; simp at this
  rw [parseFrom]
  simp only [hne, ↓reduceIte]
  split
  · rename_i d' h'
    rw [h] at h'; cases h'
  · rename_i r' rest' h'
    rw [h] at h'; cases h'; rfl

/-! ### A whole record reads as itself -/

theorem fieldsOf_receiptBytes {rc : WitnessReceipt} (h0 : rc.prevHash < bound)
    (h1 : rc.oldCommit < bound) (h2 : rc.newCommit < bound) (h3 : rc.effectsHash < bound) :
    fieldsOf (receiptBytes rc) = rc := by
  have l : ∀ n, (be 32 n).length = 32 := fun n => be_length 32 n
  simp only [fieldsOf, receiptBytes]
  rw [List.take_left' (l _), List.drop_left' (l _), List.take_left' (l _), List.drop_left' (l _),
    List.take_left' (l _), List.drop_left' (l _), List.take_of_length_le (Nat.le_of_eq (l _))]
  rw [unbe_be 32 _ h0, unbe_be 32 _ h1, unbe_be 32 _ h2, unbe_be 32 _ h3]

theorem Record.WF.eff_lt {r : Record} (h : r.WF Hb) : r.receipt.effectsHash < bound := by
  rw [h.2.2.2.1]; exact dig_lt Hb _

/-- **A whole, well-formed record reads as itself**, whatever follows it, when it follows `prev`. -/
theorem parseOne_encode {prev : Option Nat} {r : Record} (hwf : r.WF Hb)
    (hl : ∀ p, prev = some p → r.receipt.prevHash = p) (t : Bytes) :
    parseOne Hb prev (encodeRecord Hb r ++ t) = .ok (r, t) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hwf
  have hlen := headerOf_length r
  have e : encodeRecord Hb r ++ t = headerOf r ++ (r.payload ++ be 32 (Hr Hb r.receipt) ++ t) := by
    simp [encodeRecord]
  unfold parseOne
  rw [e, ← hlen, takeN_append]
  simp only
  have hm : (headerOf r).take 4 = magic := List.take_left' rfl
  have h4b : (be 4 r.payload.length).length = 4 := be_length 4 _
  have hd : (headerOf r).drop 4 = be 4 r.payload.length ++ receiptBytes r.receipt :=
    List.drop_left' rfl
  have hlenv : unbe (((headerOf r).drop 4).take 4) = r.payload.length := by
    rw [hd, List.take_left' h4b, unbe_be 4 _ h4]
  have hrc : ((headerOf r).drop 4).drop 4 = receiptBytes r.receipt := by
    rw [hd, List.drop_left' h4b]
  simp only [hm, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hlenv, hrc]
  have hbody : r.payload.length + 32 = (r.payload ++ be 32 (Hr Hb r.receipt)).length := by
    simp [be_length]
  rw [hbody, takeN_append]
  simp only
  have hfo : fieldsOf (receiptBytes r.receipt) = r.receipt :=
    fieldsOf_receiptBytes h0 h1 h2 (by rw [h3]; exact dig_lt Hb _)
  have hseal : unbe (be 32 (Hr Hb r.receipt)) = Hr Hb r.receipt := unbe_be 32 _ (dig_lt Hb _)
  rw [hfo, List.take_left' rfl, List.drop_left' rfl, hseal]
  cases prev with
  | none => simp [h3]
  | some p => simp [h3, hl p rfl]

/-- **A torn record is dropped as torn**: bytes that are a proper prefix of a well-formed record's
are refused `torn`, whatever they follow. -/
theorem parseOne_torn {prev : Option Nat} {r : Record} (hwf : r.WF Hb) {p q : Bytes}
    (hpq : p ++ q = encodeRecord Hb r) (hq : q ≠ []) : parseOne Hb prev p = .error .torn := by
  have hlen := headerOf_length r
  have hlt : p.length < (encodeRecord Hb r).length := by
    rw [← hpq, List.length_append]
    have : q.length ≠ 0 := by simpa using hq
    omega
  have hp : p = (encodeRecord Hb r).take p.length := by rw [← hpq]; simp
  unfold parseOne
  by_cases hsh : p.length < 136
  · rw [takeN_none hsh]
  · have hge : 136 ≤ p.length := by omega
    have hsplit : p = headerOf r ++ (r.payload ++ be 32 (Hr Hb r.receipt)).take (p.length - 136) := by
      have h' := hp
      rw [encodeRecord, List.take_append, hlen, List.take_of_length_le (by omega)] at h'
      exact h'
    rw [hsplit, ← hlen, takeN_append]
    simp only
    have hm : (headerOf r).take 4 = magic := List.take_left' rfl
    have h4b : (be 4 r.payload.length).length = 4 := be_length 4 _
    have hd : (headerOf r).drop 4 = be 4 r.payload.length ++ receiptBytes r.receipt :=
      List.drop_left' rfl
    have hlenv : unbe (((headerOf r).drop 4).take 4) = r.payload.length := by
      rw [hd, List.take_left' h4b, unbe_be 4 _ hwf.2.2.2.2]
    simp only [hm, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [hlenv]
    have hel := encodeRecord_length Hb r
    rw [takeN_none]
    simp only [List.length_take, List.length_append, be_length]
    omega

/-! ### Records that follow one another -/

/-- Records FOLLOW `prev`: each record's `prevHash` is the receipt digest of the one before it, the
first's is `prev`. -/
def Linked : Nat → List Record → Prop
  | _, [] => True
  | prev, r :: rs => r.receipt.prevHash = prev ∧ Linked (Hr Hb r.receipt) rs

/-- The receipt digest a log ends at (`prev` when it is empty). -/
def lastHash : Nat → List Record → Nat
  | prev, [] => prev
  | _, r :: rs => lastHash (Hr Hb r.receipt) rs

theorem lastHash_append (prev : Nat) (xs ys : List Record) :
    lastHash Hb prev (xs ++ ys) = lastHash Hb (lastHash Hb prev xs) ys := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem Linked_append (prev : Nat) (xs ys : List Record) :
    Linked Hb prev (xs ++ ys) ↔ Linked Hb prev xs ∧ Linked Hb (lastHash Hb prev xs) ys := by
  induction xs generalizing prev with
  | nil => simp [Linked, lastHash]
  | cons x xs ih =>
    simp only [List.cons_append, Linked, lastHash, ih]
    exact and_assoc.symm

theorem lastHash_lt {prev : Nat} (hp : prev < bound) (rs : List Record) : lastHash Hb prev rs < bound := by
  induction rs generalizing prev with
  | nil => exact hp
  | cons r rs ih => exact ih (dig_lt Hb _)

theorem encodeAll_append (xs ys : List Record) :
    encodeAll Hb (xs ++ ys) = encodeAll Hb xs ++ encodeAll Hb ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeAll, ih]

/-- **Whole records read back**: records that follow `prev`, each well-formed, read as themselves,
and reading goes on into what follows them from the digest they end at. -/
theorem parseFrom_encodeAll (rs : List Record) (prev : Nat) (hl : Linked Hb prev rs)
    (hwf : ∀ r ∈ rs, r.WF Hb) (t : Bytes) :
    parseFrom Hb prev (encodeAll Hb rs ++ t) =
      (rs ++ (parseFrom Hb (lastHash Hb prev rs) t).1, (parseFrom Hb (lastHash Hb prev rs) t).2) := by
  induction rs generalizing prev with
  | nil => rfl
  | cons r rs ih =>
    have h1 : parseOne Hb (some prev) (encodeRecord Hb r ++ (encodeAll Hb rs ++ t)) =
        .ok (r, encodeAll Hb rs ++ t) :=
      parseOne_encode Hb (hwf r (List.mem_cons_self ..)) (fun p hp => by cases hp; exact hl.1) _
    simp only [encodeAll, List.append_assoc]
    rw [parseFrom_ok Hb h1, ih _ hl.2 (fun x hx => hwf x (List.mem_cons_of_mem _ hx))]
    rfl

/-- The number of whole records in the first `k` bytes of a log. -/
def whole : List Record → Nat → Nat
  | [], _ => 0
  | r :: rs, k => if (encodeRecord Hb r).length ≤ k then whole rs (k - (encodeRecord Hb r).length) + 1 else 0

/-- The reason a dropped tail is named by: none when nothing was dropped, else `torn`. -/
def tornWhy (tail : Bytes) : Option Drop := if tail.isEmpty then none else some .torn

/-- **The crash at byte `k`**, at the level of bytes: the first `k` bytes of a log of well-formed
records that follow `prev` read as the records whole in them; the rest is dropped, as `torn`. -/
theorem parseFrom_take (rs : List Record) (prev : Nat) (hl : Linked Hb prev rs)
    (hwf : ∀ r ∈ rs, r.WF Hb) (k : Nat) :
    parseFrom Hb prev ((encodeAll Hb rs).take k) =
      (rs.take (whole Hb rs k),
        ((encodeAll Hb rs).take k).drop (encodeAll Hb (rs.take (whole Hb rs k))).length,
        tornWhy (((encodeAll Hb rs).take k).drop (encodeAll Hb (rs.take (whole Hb rs k))).length)) := by
  induction rs generalizing prev k with
  | nil => simp [encodeAll, whole, parseFrom_nil, tornWhy]
  | cons r rs ih =>
    have hr := hwf r (List.mem_cons_self ..)
    by_cases hk : (encodeRecord Hb r).length ≤ k
    · have hw : whole Hb (r :: rs) k = whole Hb rs (k - (encodeRecord Hb r).length) + 1 := by
        simp [whole, hk]
      have ht : (encodeAll Hb (r :: rs)).take k =
          encodeRecord Hb r ++ (encodeAll Hb rs).take (k - (encodeRecord Hb r).length) := by
        simp only [encodeAll, List.take_append, List.take_of_length_le hk]
      have h1 : parseOne Hb (some prev) (encodeRecord Hb r ++ (encodeAll Hb rs).take (k - (encodeRecord Hb r).length)) =
          .ok (r, (encodeAll Hb rs).take (k - (encodeRecord Hb r).length)) :=
        parseOne_encode Hb hr (fun p hp => by cases hp; exact hl.1) _
      rw [hw, ht, parseFrom_ok Hb h1, ih _ hl.2 (fun x hx => hwf x (List.mem_cons_of_mem _ hx))]
      simp [encodeAll]
    · have hw : whole Hb (r :: rs) k = 0 := by simp [whole, hk]
      have hk' : k < (encodeRecord Hb r).length := by omega
      have ht : (encodeAll Hb (r :: rs)).take k = (encodeRecord Hb r).take k := by
        have : k - (encodeRecord Hb r).length = 0 := by omega
        simp [encodeAll, List.take_append, this]
      rw [hw, ht]
      by_cases k0 : k = 0
      · subst k0; simp [parseFrom_nil, encodeAll, tornWhy]
      · have hne : (encodeRecord Hb r).take k ≠ [] := by
          rw [Ne, List.take_eq_nil_iff]
          rintro (h | h)
          · exact k0 h
          · rw [h] at hk'; simp at hk'
        have htorn : parseOne Hb (some prev) ((encodeRecord Hb r).take k) = .error .torn :=
          parseOne_torn Hb hr (List.take_append_drop k _) (by rw [Ne, List.drop_eq_nil_iff]; omega)
        rw [parseFrom_error Hb hne htorn]
        simp [encodeAll, tornWhy, hne]

/-- **Whatever bytes are read, what is recovered is linked and self-checking**: the records follow
`prev` and each names its turn's digest; nothing is read past a record that does not. -/
theorem parseFrom_sound (prev : Nat) (bs : Bytes) :
    Linked Hb prev (parseFrom Hb prev bs).1 ∧
      ∀ r ∈ (parseFrom Hb prev bs).1, r.receipt.effectsHash = dig Hb r.payload := by
  induction h : bs.length using Nat.strongRecOn generalizing prev bs with
  | ind n ih =>
    by_cases hne : bs = []
    · subst hne; simp [parseFrom_nil, Linked]
    · cases hp : parseOne Hb (some prev) bs with
      | error d => rw [parseFrom_error Hb hne hp]; simp [Linked]
      | ok x =>
        obtain ⟨r, rest⟩ := x
        rw [parseFrom_ok Hb hp]
        obtain ⟨hlt, heff, hpr⟩ := parseOne_ok_inv Hb hp
        obtain ⟨ih1, ih2⟩ := ih rest.length (h ▸ hlt) (Hr Hb r.receipt) rest rfl
        refine ⟨⟨hpr prev rfl, ih1⟩, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact heff
        · exact ih2 x hx

/-! ### The log is Pillar 1's chain -/

theorem lastHash_snoc (prev : Nat) (xs : List Record) (p : Record) :
    lastHash Hb prev (xs ++ [p]) = Hr Hb p.receipt := by
  rw [lastHash_append]; rfl

/-- **Records that follow the genesis sentinel are a well-linked receipt chain**: read newest first,
their receipts are `wellLinked` at the receipt digest `Hr` (`Obend.Vault.Rehydration.wellLinked`, the
discipline `wellLinked_append` extends and `chain_tamper_evident_or` binds). -/
theorem linked_genesis_iff (rs : List Record) :
    Linked Hb genesisSentinel rs ↔ wellLinked (Hr Hb) (rs.map (·.receipt)).reverse := by
  induction h : rs.length using Nat.strongRecOn generalizing rs with
  | ind n ih =>
    rcases List.eq_nil_or_concat rs with rfl | ⟨xs, p, rfl⟩
    · simp [Linked, wellLinked]
    · rw [List.concat_eq_append] at h ⊢
      rw [Linked_append]
      simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append]
      have hxs : xs.length < n := by rw [← h]; simp
      rcases List.eq_nil_or_concat xs with rfl | ⟨ys, q, rfl⟩
      · simp [Linked, lastHash, wellLinked]
      · rw [List.concat_eq_append] at hxs ⊢
        rw [lastHash_snoc]
        have ih' := ih _ hxs (ys ++ [q]) rfl
        simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append] at ih' ⊢
        simp only [wellLinked, Linked, and_true]
        rw [ih']
        exact and_comm

end Codec

/-! ## Replay, sessions and recovery -/

/-- What a log is replayed by: the step a turn's bytes make (a refusal leaves the world), with what it
says, and the world's canonical bytes, whose digest a receipt names as its commitment. -/
structure Machine (W O : Type) where
  step : W → Bytes → Except String (W × O)
  encW : W → Bytes

section Replay
variable {W O : Type} (Hb : Bytes → Bytes) (M : Machine W O)

/-- The world after a turn's bytes: the step's, or the same world when the step refuses them. -/
def stepB (w : W) (b : Bytes) : W :=
  match M.step w b with
  | .ok (w', _) => w'
  | .error _ => w

/-- **Replay**: the world after the turns of the records, in order, from `w`. -/
def replay (w : W) (rs : List Record) : W := rs.foldl (fun w r => stepB M w r.payload) w

theorem replay_append (w : W) (xs ys : List Record) :
    replay M w (xs ++ ys) = replay M (replay M w xs) ys := by
  simp [replay, List.foldl_append]

/-- **Admit a turn**: step the world by its bytes and, when the step admits them, the record to
append: the receipt following `prev`, from the world's commitment before to its commitment after. -/
def admit (w : W) (prev : Nat) (b : Bytes) : Except String (W × O × Record) :=
  if b.length < 256 ^ 4 then
    match M.step w b with
    | .ok (w', o) => .ok (w', o, ⟨⟨prev, dig Hb (M.encW w), dig Hb (M.encW w'), dig Hb b⟩, b⟩)
    | .error e => .error e
  else .error "a turn is under 4 GiB"

/-- **Admit, step by step**: a process that has stepped the turn (and knows the commitment of the world
it stepped from) builds the same record `admit` would. -/
theorem admit_of_step {w w' : W} {o : O} {prev : Nat} {b : Bytes} (hl : b.length < 256 ^ 4)
    (hs : M.step w b = .ok (w', o)) {oldC : Nat} (hc : oldC = dig Hb (M.encW w)) :
    admit Hb M w prev b = .ok (w', o, ⟨⟨prev, oldC, dig Hb (M.encW w'), dig Hb b⟩, b⟩) := by
  subst hc; simp [admit, hl, hs]

/-- A session: the world a process serves and the records it appended, oldest first. -/
structure Session (W : Type) where
  world : W
  log : List Record

/-- Admit a turn into a session: the record follows the session's last. -/
def Session.admit (S : Session W) (b : Bytes) : Except String (Session W) :=
  match Log.admit Hb M S.world (lastHash Hb genesisSentinel S.log) b with
  | .ok (w', _, r) => .ok ⟨w', S.log ++ [r]⟩
  | .error e => .error e

/-- The sessions a process passes through from the genesis world `w0`: genesis, then admitted turns. -/
inductive Reachable (w0 : W) : Session W → Prop
  | genesis : Reachable w0 ⟨w0, []⟩
  | admit {S S' : Session W} {b : Bytes} : Reachable w0 S → S.admit Hb M b = .ok S' → Reachable w0 S'

theorem admit_ok {w w' : W} {o : O} {prev : Nat} {b : Bytes} {r : Record}
    (h : Log.admit Hb M w prev b = .ok (w', o, r)) :
    M.step w b = .ok (w', o) ∧ r = ⟨⟨prev, dig Hb (M.encW w), dig Hb (M.encW w'), dig Hb b⟩, b⟩ ∧
      b.length < 256 ^ 4 := by
  unfold Log.admit at h
  split at h
  · split at h
    · rename_i w'' o'' hs
      cases h
      exact ⟨hs, rfl, by assumption⟩
    · cases h
  · cases h

theorem Session.admit_ok {S S' : Session W} {b : Bytes} (h : S.admit Hb M b = .ok S') :
    ∃ o, M.step S.world b = .ok (S'.world, o) ∧
      S'.log = S.log ++ [⟨⟨lastHash Hb genesisSentinel S.log, dig Hb (M.encW S.world),
        dig Hb (M.encW S'.world), dig Hb b⟩, b⟩] ∧ b.length < 256 ^ 4 := by
  unfold Session.admit at h
  split at h
  · rename_i w' o r ha
    cases h
    obtain ⟨hs, hr, hl⟩ := Log.admit_ok Hb M ha
    exact ⟨o, hs, by rw [hr], hl⟩
  · cases h

variable {Hb M}

/-- **`state_eq_replay_log`**: the world a session serves is the replay of its log from genesis. -/
theorem state_eq_replay_log {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) :
    S.world = replay M w0 S.log := by
  induction h with
  | genesis => rfl
  | admit _ ha ih =>
    obtain ⟨o, hs, hlog, _⟩ := Session.admit_ok Hb M ha
    rw [hlog, replay_append, ← ih]
    simp [replay, stepB, hs]

/-- The log of a session is well-formed and follows the genesis sentinel. -/
theorem log_sound {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) :
    Linked Hb genesisSentinel S.log ∧ ∀ r ∈ S.log, r.WF Hb := by
  induction h with
  | genesis => exact ⟨trivial, by simp⟩
  | admit _ ha ih =>
    obtain ⟨o, hs, hlog, hlen⟩ := Session.admit_ok Hb M ha
    rw [hlog, Linked_append]
    refine ⟨⟨ih.1, ?_, trivial⟩, ?_⟩
    · rfl
    · intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact ih.2 r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨lastHash_lt Hb (by decide) _, dig_lt Hb _, dig_lt Hb _, rfl, hlen⟩

/-- **The log a session wrote is Pillar 1's chain**: its receipts, newest first, are `wellLinked`. -/
theorem log_wellLinked {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) :
    wellLinked (Hr Hb) (S.log.map (·.receipt)).reverse :=
  (linked_genesis_iff Hb S.log).1 (log_sound h).1

/-- Every prefix of a session's log is the log of a session it passed through. -/
theorem prefix_reachable {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) (m : Nat) :
    Reachable Hb M w0 ⟨replay M w0 (S.log.take m), S.log.take m⟩ := by
  induction h generalizing m with
  | genesis => simpa [replay] using Reachable.genesis
  | @admit S S' b hS ha ih =>
    obtain ⟨o, hs, hlog, _⟩ := Session.admit_ok Hb M ha
    by_cases hm : m ≤ S.log.length
    · rw [hlog, List.take_append_of_le_length hm]
      exact ih m
    · rw [hlog, List.take_of_length_le (by simp; omega)]
      rw [← hlog, ← state_eq_replay_log (Reachable.admit hS ha)]
      exact Reachable.admit hS ha

/-- What recovery reads from a log's bytes: the world, how many records it replayed, the dropped
tail and why it was dropped. -/
structure Recovered (W : Type) where
  world : W
  count : Nat
  tail : Bytes
  why : Option Drop

variable (Hb M)

/-- **Recover from genesis**: replay the records read from the bytes, from the genesis world. -/
def recover (w0 : W) (bs : Bytes) : Recovered W :=
  let (qs, tail, why) := parseFrom Hb genesisSentinel bs
  ⟨replay M w0 qs, qs.length, tail, why⟩

variable {Hb M}

/-- **`recover_eq_replay_prefix`**: a crash at any byte `k` of the log a session wrote recovers the
replay of the longest prefix of whole records, a state the session served, and drops the rest of the
bytes, named `torn`. -/
theorem recover_eq_replay_prefix {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) (k : Nat) :
    let m := whole Hb S.log k
    let tail := ((encodeAll Hb S.log).take k).drop (encodeAll Hb (S.log.take m)).length
    recover Hb M w0 ((encodeAll Hb S.log).take k) = ⟨replay M w0 (S.log.take m), m, tail, tornWhy tail⟩ ∧
      Reachable Hb M w0 ⟨replay M w0 (S.log.take m), S.log.take m⟩ := by
  obtain ⟨hl, hwf⟩ := log_sound h
  refine ⟨?_, prefix_reachable h _⟩
  simp only [recover]
  rw [parseFrom_take Hb S.log genesisSentinel hl hwf k]
  have hm : whole Hb S.log k ≤ S.log.length := by
    clear hl hwf h
    induction S.log generalizing k with
    | nil => simp [whole]
    | cons r rs ih => simp only [whole]; split <;> simp [ih]
  simp [List.length_take, Nat.min_eq_left hm]

/-- The last record of a session's log commits to the world the session serves. -/
theorem newCommit_of_reachable {w0 w : W} {pre : List Record} {r : Record}
    (h : Reachable Hb M w0 ⟨w, pre ++ [r]⟩) : r.receipt.newCommit = dig Hb (M.encW w) := by
  generalize hS : (⟨w, pre ++ [r]⟩ : Session W) = S at h
  cases h with
  | genesis => simp at hS
  | @admit S0 S' b _ ha =>
    subst hS
    obtain ⟨o, hs, hlog, _⟩ := Session.admit_ok Hb M ha
    have h2 := (List.append_inj' hlog rfl).2
    simp only [List.cons.injEq, and_true] at h2
    rw [h2]

/-! ### Checkpoints -/

/-- A checkpoint: the world after the first `count` records (`world`, its bytes), the byte range of
the last of them (`start`, `stop`) and its receipt digest (`anchor`). -/
structure Checkpoint where
  count : Nat
  start : Nat
  stop : Nat
  anchor : Nat
  world : Bytes
deriving Repr

variable (Hb M)

/-- The checkpoint a session writes after the first `n` records of its log. -/
def checkpointAt (w0 : W) (rs : List Record) (n : Nat) : Checkpoint :=
  ⟨n, (encodeAll Hb (rs.take (n - 1))).length, (encodeAll Hb (rs.take n)).length,
    lastHash Hb genesisSentinel (rs.take n), M.encW (replay M w0 (rs.take n))⟩

/-- **A checkpoint holds** against a log's bytes when its last record is whole there, has its
receipt digest, and commits to the checkpoint's world bytes, which decode: the world it holds. -/
def Checkpoint.holds (decW : Bytes → Option W) (ck : Checkpoint) (bs : Bytes) : Option W :=
  if ck.count = 0 then none else
  match parseOne Hb none ((bs.drop ck.start).take (ck.stop - ck.start)) with
  | .ok (r, []) =>
    if Hr Hb r.receipt = ck.anchor ∧ r.receipt.newCommit = dig Hb ck.world then decW ck.world else none
  | _ => none

/-- **Recover from a checkpoint**: when it holds, its world and the records after it; otherwise
from genesis. -/
def recoverWith (decW : Bytes → Option W) (w0 : W) (ck : Checkpoint) (bs : Bytes) : Recovered W :=
  match ck.holds Hb decW bs with
  | some w =>
    let (qs, tail, why) := parseFrom Hb ck.anchor (bs.drop ck.stop)
    ⟨replay M w qs, ck.count + qs.length, tail, why⟩
  | none => recover Hb M w0 bs

variable {Hb M}

theorem drop_len_append (A B : Bytes) (x : Nat) : (A ++ B).drop (A.length + x) = B.drop x := by
  induction A with
  | nil => simp
  | cons a A ih => simp [Nat.add_right_comm]

theorem whole_le (rs : List Record) (k : Nat) : whole Hb rs k ≤ rs.length := by
  induction rs generalizing k with
  | nil => simp [whole]
  | cons r rs ih => simp only [whole]; split <;> simp [ih]

theorem whole_append (xs ys : List Record) {k : Nat} (hk : (encodeAll Hb xs).length ≤ k) :
    whole Hb (xs ++ ys) k = xs.length + whole Hb ys (k - (encodeAll Hb xs).length) := by
  induction xs generalizing k with
  | nil => simp [encodeAll]
  | cons x xs ih =>
    simp only [encodeAll, List.length_append] at hk
    simp only [List.cons_append, whole, show (encodeRecord Hb x).length ≤ k by omega, ↓reduceIte,
      List.length_cons]
    rw [ih (by omega)]
    simp only [encodeAll, List.length_append]
    have : k - (encodeRecord Hb x).length - (encodeAll Hb xs).length =
      k - ((encodeRecord Hb x).length + (encodeAll Hb xs).length) := by omega
    rw [this]; omega

/-- **`checkpoint_is_cache`**: at every truncation of the log a session wrote, recovering from a
checkpoint it wrote after `n` records gives exactly what recovering from genesis gives (the world,
the count, the dropped tail and its reason): the checkpoint can be dropped and nothing is lost. Its
premise is that the world's bytes decode to the world (`hcache`), which the writer checks. -/
theorem checkpoint_is_cache {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) {decW : Bytes → Option W}
    {n : Nat} (hn0 : 0 < n) (hn : n ≤ S.log.length)
    (hcache : decW (M.encW (replay M w0 (S.log.take n))) = some (replay M w0 (S.log.take n))) (k : Nat) :
    recoverWith Hb M decW w0 (checkpointAt Hb M w0 S.log n) ((encodeAll Hb S.log).take k) =
      recover Hb M w0 ((encodeAll Hb S.log).take k) := by
  obtain ⟨hl, hwf⟩ := log_sound h
  -- the log as the records before the checkpoint's last, that record, and the rest
  obtain ⟨pre, r, post, hsplit, hpre⟩ : ∃ pre r post, S.log = pre ++ r :: post ∧ pre.length = n - 1 := by
    refine ⟨S.log.take (n - 1), S.log[n - 1]'(by omega), S.log.drop n, ?_, by simp; omega⟩
    have : S.log.drop (n - 1) = S.log[n - 1]'(by omega) :: S.log.drop n := by
      rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
    rw [← this, List.take_append_drop]
  have htn : S.log.take n = pre ++ [r] := by
    rw [hsplit, show n = pre.length + 1 by omega, List.take_append, List.take_of_length_le (by omega)]
    simp
  have htn1 : S.log.take (n - 1) = pre := by
    rw [hsplit, ← hpre]; simp
  have hdropn : S.log.drop n = post := by
    rw [hsplit, show n = pre.length + 1 by omega]; simp
  have hB : encodeAll Hb S.log = encodeAll Hb pre ++ (encodeRecord Hb r ++ encodeAll Hb post) := by
    rw [hsplit, encodeAll_append]; rfl
  have hstart : (checkpointAt Hb M w0 S.log n).start = (encodeAll Hb pre).length := by
    simp [checkpointAt, htn1]
  have hstop : (checkpointAt Hb M w0 S.log n).stop =
      (encodeAll Hb pre).length + (encodeRecord Hb r).length := by
    simp [checkpointAt, htn, encodeAll_append, encodeAll]
  have hlinked := (Linked_append Hb _ _ _).1 (hsplit ▸ hl)
  have hr_wf : r.WF Hb := hwf r (by rw [hsplit]; simp)
  have hr_link : r.receipt.prevHash = lastHash Hb genesisSentinel pre := hlinked.2.1
  unfold recoverWith
  by_cases hk : (encodeAll Hb pre).length + (encodeRecord Hb r).length ≤ k
  · -- the checkpoint's last record is whole in the bytes: the checkpoint holds
    have hslice : (((encodeAll Hb S.log).take k).drop (checkpointAt Hb M w0 S.log n).start).take
        ((checkpointAt Hb M w0 S.log n).stop - (checkpointAt Hb M w0 S.log n).start) =
        encodeRecord Hb r ++ [] := by
      rw [hstart, hstop, hB, List.drop_take, List.drop_left' rfl, List.take_take, List.append_nil]
      rw [show min ((encodeAll Hb pre).length + (encodeRecord Hb r).length - (encodeAll Hb pre).length)
        (k - (encodeAll Hb pre).length) = (encodeRecord Hb r).length by omega]
      exact List.take_left' rfl
    have hholds : (checkpointAt Hb M w0 S.log n).holds Hb decW ((encodeAll Hb S.log).take k) =
        some (replay M w0 (S.log.take n)) := by
      unfold Checkpoint.holds
      rw [hslice, parseOne_encode Hb hr_wf (fun p hp => by cases hp)]
      have hn0' : (checkpointAt Hb M w0 S.log n).count ≠ 0 := by simp [checkpointAt]; omega
      simp only [hn0', ↓reduceIte]
      have hanc : Hr Hb r.receipt = (checkpointAt Hb M w0 S.log n).anchor := by
        simp [checkpointAt, htn, lastHash_snoc]
      have hcom : r.receipt.newCommit = dig Hb (checkpointAt Hb M w0 S.log n).world := by
        -- the record's commitment is the world's after it: the session's invariant
        have hrec := (prefix_reachable h n)
        rw [htn] at hrec
        simp only [checkpointAt, htn]
        exact newCommit_of_reachable hrec
      simp only [hanc, hcom, and_self, ↓reduceIte, checkpointAt]
      exact hcache
    rw [hholds]
    simp only
    -- the records after the checkpoint
    have hrest : ((encodeAll Hb S.log).take k).drop (checkpointAt Hb M w0 S.log n).stop =
        (encodeAll Hb post).take (k - ((encodeAll Hb pre).length + (encodeRecord Hb r).length)) := by
      rw [hstop, hB, List.drop_take, ← List.append_assoc, List.drop_left' (by simp)]
    have hanc : (checkpointAt Hb M w0 S.log n).anchor = lastHash Hb genesisSentinel (pre ++ [r]) := by
      simp [checkpointAt, htn]
    have hpost_l : Linked Hb (lastHash Hb genesisSentinel (pre ++ [r])) post := by
      rw [lastHash_snoc]; exact hlinked.2.2
    have hpost_wf : ∀ x ∈ post, x.WF Hb := fun x hx => hwf x (by rw [hsplit]; simp [hx])
    rw [hrest, hanc, parseFrom_take Hb post _ hpost_l hpost_wf]
    simp only [recover]
    have hl' : Linked Hb genesisSentinel ((pre ++ [r]) ++ post) := by
      rw [List.append_assoc]; exact hsplit ▸ hl
    have hB' : encodeAll Hb S.log = encodeAll Hb (pre ++ [r]) ++ encodeAll Hb post := by
      rw [hsplit, ← List.singleton_append, ← List.append_assoc, encodeAll_append]
    have hlen' : (encodeAll Hb (pre ++ [r])).length = (encodeAll Hb pre).length + (encodeRecord Hb r).length := by
      simp [encodeAll_append, encodeAll]
    rw [parseFrom_take Hb S.log genesisSentinel hl hwf k]
    have hw : whole Hb S.log k = (pre ++ [r]).length + whole Hb post (k - (encodeAll Hb (pre ++ [r])).length) := by
      rw [show S.log = (pre ++ [r]) ++ post by rw [hsplit]; simp]
      exact whole_append _ _ (by omega)
    simp only [Recovered.mk.injEq]
    rw [← hlen'] at hk ⊢
    have hsl : S.log = (pre ++ [r]) ++ post := by rw [hsplit]; simp
    have htw : S.log.take (whole Hb S.log k) =
        (pre ++ [r]) ++ post.take (whole Hb post (k - (encodeAll Hb (pre ++ [r])).length)) := by
      rw [hw, hsl, List.take_append, List.take_of_length_le (by simp)]
      congr 2; simp
    have htk : (encodeAll Hb S.log).take k =
        encodeAll Hb (pre ++ [r]) ++ (encodeAll Hb post).take (k - (encodeAll Hb (pre ++ [r])).length) := by
      rw [hB', List.take_append, List.take_of_length_le (by omega)]
    rw [htw, htk, htn, replay_append M w0 (pre ++ [r])]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [checkpointAt]; omega
    · rw [encodeAll_append Hb (pre ++ [r]), List.length_append, drop_len_append]
    · rw [encodeAll_append Hb (pre ++ [r]), List.length_append, drop_len_append]
  · -- the checkpoint's last record is not whole: it does not hold, and recovery is from genesis
    have hnot : (checkpointAt Hb M w0 S.log n).holds Hb decW ((encodeAll Hb S.log).take k) = none := by
      unfold Checkpoint.holds
      have hP := encodeRecord_length Hb r
      have hslice : (((encodeAll Hb S.log).take k).drop (checkpointAt Hb M w0 S.log n).start).take
          ((checkpointAt Hb M w0 S.log n).stop - (checkpointAt Hb M w0 S.log n).start) =
          (encodeRecord Hb r).take (k - (encodeAll Hb pre).length) := by
        rw [hstart, hstop, hB, List.drop_take, List.drop_left' rfl, List.take_take]
        rw [show min ((encodeAll Hb pre).length + (encodeRecord Hb r).length - (encodeAll Hb pre).length)
          (k - (encodeAll Hb pre).length) = k - (encodeAll Hb pre).length by omega]
        rw [List.take_append, show k - (encodeAll Hb pre).length - (encodeRecord Hb r).length = 0 by omega]
        simp
      have htorn : parseOne Hb none ((encodeRecord Hb r).take (k - (encodeAll Hb pre).length)) = .error .torn :=
        parseOne_torn Hb hr_wf (List.take_append_drop _ _) (by rw [Ne, List.drop_eq_nil_iff]; omega)
      have hc : (checkpointAt Hb M w0 S.log n).count ≠ 0 := by simp [checkpointAt]; omega
      simp only [hc, ↓reduceIte, hslice, htorn]
    rw [hnot]

end Replay

end Obend.Vault.Log

namespace Obend.Vault.Retention
open Obend.Vault.Log
open Obend.Vault.Rehydration (genesisSentinel)
/-- **Read a log that may be compacted**: when its first record follows genesis and its turn names an
ANCHOR (`anchorOf`: a checkpoint record, standing for a forgotten prefix that ended at that receipt
digest), the records after it follow the anchor; otherwise the log is read from genesis as ever
(`parseFrom`). -/
def parseLog (Hb : Bytes → Bytes) (anchorOf : Bytes → Option Nat) (bs : Bytes) : List Record × Bytes × Option Drop :=
  match parseOne Hb (some genesisSentinel) bs with
  | .ok (r, rest) =>
    match anchorOf r.payload with
    | some a =>
      let (qs, tail, why) := parseFrom Hb a rest
      (r :: qs, tail, why)
    | none => parseFrom Hb genesisSentinel bs
  | .error _ => parseFrom Hb genesisSentinel bs

end Obend.Vault.Retention

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

/-
# Byte-addressed log segments

The logical log is unchanged: the same records, checksums and receipt chain. Its bytes occupy
64 KiB files, with every file except the last full. The index is the byte address itself: division
selects a segment and remainder selects its byte. A checksummed index names the active segment.
Rollover clears the next block before publishing its index, then writes its payload; the preceding
segment is flushed first. An interrupted append leaves exactly a prefix, including a torn record.

`.obend/log` selects a generation atomically. Migration and compaction publish a complete new generation;
ordinary appends retain the generation and advance its active index only at segment boundaries. Old monolithic logs are read for migration.
`split_join`, `split_drop_join`, `holds_window` and `parse_window` connect the segmented byte windows
to the existing record/checkpoint semantics; no checksum or receipt check is bypassed.
-/


namespace Obend.Vault.SegmentLog
open Obend.Vault.Log Obend.Vault.LogBytes
set_option autoImplicit false

def capacity : Nat := 65536

/-- The specification of the physical segmentation, valid for every positive block size. -/
def split (n : Nat) (positive : 0 < n) (bs : Bytes) : List Bytes :=
  if bs.isEmpty then [] else bs.take n :: split n positive (bs.drop n)
termination_by bs.length
decreasing_by
  rename_i h
  have hn : bs ≠ [] := by simpa using h
  have hl := List.length_pos_iff.mpr hn
  simp only [List.length_drop]
  omega

theorem split_join (n : Nat) (positive : 0 < n) (bs : Bytes) :
    (split n positive bs).flatten = bs := by
  rw [split]
  split
  · rename_i h
    simpa using (List.isEmpty_iff.mp h).symm
  · simp only [List.flatten_cons, split_join n positive (bs.drop n), List.take_append_drop]
termination_by bs.length
decreasing_by
  rename_i h
  have hn : bs ≠ [] := by simpa using h
  have hl := List.length_pos_iff.mpr hn
  simp only [List.length_drop]
  omega

/-- Dropping whole files is dropping exactly that many block widths of logical bytes. -/
theorem split_drop_join (n : Nat) (positive : 0 < n) (bs : Bytes) (k : Nat) :
    ((split n positive bs).drop k).flatten = bs.drop (k * n) := by
  induction k generalizing bs with
  | zero => simpa using split_join n positive bs
  | succ k ih =>
    rw [split]
    split
    · rename_i h
      have e := List.isEmpty_iff.mp h
      simp [e]
    · simp only [List.drop_succ_cons, ih, List.drop_drop]
      congr 1
      simp [Nat.succ_mul, Nat.add_comm]

theorem split_take_join (n : Nat) (positive : 0 < n) (bs : Bytes) (k : Nat) :
    ((split n positive bs).take k).flatten = bs.take (k * n) := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
    rw [split]
    split
    · rename_i h
      have e := List.isEmpty_iff.mp h
      simp [e]
    · simp only [List.take_succ_cons, List.flatten_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm, List.take_add]

theorem split_drop (n : Nat) (positive : 0 < n) (bs : Bytes) (k : Nat) :
    (split n positive bs).drop k = split n positive (bs.drop (k * n)) := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
    rw [split]
    split
    · rename_i h
      have e := List.isEmpty_iff.mp h
      simp [e, split]
    · simp only [List.drop_succ_cons, ih, List.drop_drop]
      congr 1
      simp [Nat.succ_mul, Nat.add_comm]

/-- Concatenate the selected disk blocks with a unique byte-array accumulator. -/
def joinFrom (acc : ByteArray) : List ByteArray → ByteArray
  | [] => acc
  | b :: bs => joinFrom (acc ++ b) bs

theorem joinFrom_eq (acc : ByteArray) (bs : List ByteArray) :
    (joinFrom acc bs).data.toList = acc.data.toList ++ (bs.map (·.data.toList)).flatten := by
  induction bs generalizing acc with
  | nil => simp [joinFrom]
  | cons b bs ih => simp [joinFrom, ih, List.append_assoc]

/-- The deployed assembler: load only the selected blocks, then clip their two boundary pieces. -/
def assemble (blocks : List ByteArray) (skip count : Nat) : ByteArray :=
  (joinFrom .empty blocks).extract skip (skip + count)

theorem assemble_eq (blocks : List ByteArray) (skip count : Nat) :
    (assemble blocks skip count).data.toList =
      ((blocks.map (·.data.toList)).flatten.drop skip).take count := by
  simp [assemble, List.extract, joinFrom_eq]

/-- Assembling a window of physical segments gives exactly the corresponding logical byte slice,
including short final blocks. This is the pure function used by `readRangeOf`. -/
theorem assemble_split (n : Nat) (positive : 0 < n) (bs : Bytes)
    (first blocks skip count : Nat) (covers : skip + count ≤ blocks * n) :
    (assemble (((split n positive bs).drop first).take blocks |>.map
      (fun b => (⟨b.toArray⟩ : ByteArray))) skip count).data.toList =
        (bs.drop (first * n + skip)).take count := by
  rw [assemble_eq]
  simp only [List.map_map, Function.comp_def]
  change (((((split n positive bs).drop first).take blocks).map (fun x => x)).flatten.drop skip).take count = _
  have identity : (((split n positive bs).drop first).take blocks).map (fun x : Bytes => x) =
      ((split n positive bs).drop first).take blocks := by
    induction ((split n positive bs).drop first).take blocks with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, ih]
  rw [identity]
  rw [split_drop, split_take_join, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega

/-- The exact segment bounds used by `readRangeOf` cover and reconstruct every nonempty range. -/
theorem assemble_range (bs : Bytes) (start stop : Nat) (nonempty : start < stop) :
    (assemble (((split capacity (by decide) bs).drop (start / capacity)).take
      ((stop - 1) / capacity + 1 - start / capacity) |>.map
        (fun b => (⟨b.toArray⟩ : ByteArray))) (start % capacity) (stop - start)).data.toList =
      (bs.drop start).take (stop - start) := by
  have a := Nat.div_add_mod start capacity
  have b := Nat.div_add_mod (stop - 1) capacity
  have am := Nat.mod_lt start (show 0 < capacity by decide)
  have bm := Nat.mod_lt (stop - 1) (show 0 < capacity by decide)
  have cover : start % capacity + (stop - start) ≤
      ((stop - 1) / capacity + 1 - start / capacity) * capacity := by
    unfold capacity at *
    omega
  rw [assemble_split _ _ _ _ _ _ _ cover]
  congr 2
  simpa [Nat.mul_comm] using a

/-- Rebasing the checkpoint into a loaded suffix preserves its check against the whole log. -/
def localCheckpoint (ck : Checkpoint) (offset : Nat) : Checkpoint :=
  { ck with start := ck.start - offset, stop := ck.stop - offset }

theorem holds_window {W : Type} (Hb : Bytes → Bytes) (dec : Bytes → Option W)
    (ck : Checkpoint) (bs : Bytes) (offset : Nat) (ha : offset ≤ ck.start)
    (hb : ck.start ≤ ck.stop) :
    (localCheckpoint ck offset).holds Hb dec (bs.drop offset) = ck.holds Hb dec bs := by
  unfold Checkpoint.holds localCheckpoint
  simp only [List.drop_drop]
  have h1 : offset + (ck.start - offset) = ck.start := by omega
  have h2 : ck.stop - offset - (ck.start - offset) = ck.stop - ck.start := by omega
  rw [h1, h2]

/-- The deployed parser on the loaded suffix is exactly the old parser at its logical address. -/
theorem parse_window (Hb : Bytes → Bytes) (prev : Nat) (bs : Bytes) (offset : Nat)
    (window : ByteArray) (h : window.data.toList = bs.drop offset) :
    parseFrom Hb prev (bs.drop offset) =
      ((parseFromAt Hb prev window 0).1,
        bs.drop (offset + (parseFromAt Hb prev window 0).2.1),
        (parseFromAt Hb prev window 0).2.2) := by
  have e := parseFromAt_eq Hb prev window 0
  simp only [h, List.drop_drop] at e
  exact e

def root (dir : System.FilePath) : System.FilePath := dir / ".obend" / "log-segments"
def selector (dir : System.FilePath) : System.FilePath := dir / ".obend" / "log"
def block (dir : System.FilePath) (generation index : Nat) : System.FilePath :=
  root dir / toString generation / toString index

structure Index where
  generation : Nat
  active : Nat

def indexText (Hb : Bytes → Bytes) (idx : Index) : String :=
  let body := "obend-segments 1 " ++ toString idx.generation ++ " " ++ toString idx.active
  body ++ " " ++ toString (dig Hb body.toUTF8.toList) ++ "\n"

/-- A selector is checksummed; malformed selectors fail rather than silently selecting another log.
A legacy log starts with OBL1 (or a torn prefix of it); only it may use the migration path. -/
def index (Hb : Bytes → Bytes) (dir : System.FilePath) : IO (Option Index) := do
  if !(← (selector dir).pathExists) then return none
  let h ← IO.FS.Handle.mk (selector dir) .read
  let b ← h.read 256
  Obend.Vault.Cost.addRead b.size
  if (b.extract 0 (min b.size 4)).data.toList == magic.take (min b.size 4) then return none
  let some txt := String.fromUTF8? b | throw (IO.userError "invalid segmented log selector")
  match txt.trimAscii.toString.splitOn " " with
  | ["obend-segments", "1", g, a, _] =>
    let some n := g.toNat? | throw (IO.userError "invalid log generation")
    let some k := a.toNat? | throw (IO.userError "invalid active log segment")
    let idx : Index := ⟨n, k⟩
    if indexText Hb idx != txt then throw (IO.userError "segmented log selector checksum does not hold")
    return some idx
  | _ => throw (IO.userError "invalid log selector (neither OBL1 nor obend-segments 1)")

def sizeOf (dir : System.FilePath) (idx : Index) : IO Nat := do
  let f := block dir idx.generation idx.active
  if ← f.pathExists then
    let last := (← f.metadata).byteSize.toNat
    if last > capacity then throw (IO.userError "log segment exceeds its block width")
    return idx.active * capacity + last
  -- A rollover published its new index but had not yet created the new block. Only a complete
  -- predecessor can justify that boundary; a missing/short predecessor is corruption.
  if idx.active == 0 then return 0
  let prior := block dir idx.generation (idx.active - 1)
  if !(← prior.pathExists) || (← prior.metadata).byteSize.toNat != capacity then
    throw (IO.userError "active log segment and its complete predecessor are missing")
  return idx.active * capacity

def size (Hb : Bytes → Bytes) (dir : System.FilePath) : IO Nat := do
  match ← index Hb dir with
  | some idx => sizeOf dir idx
  | none =>
    if !(← (selector dir).pathExists) then return 0
    return (← (selector dir).metadata).byteSize.toNat

/-- Load exactly the blocks meeting [start, stop); at most two partial blocks are read in excess.
Every interior block must be full, otherwise recovery stops rather than joining over missing bytes. -/
def readRangeOf (dir : System.FilePath) (g start stop : Nat) : IO ByteArray := do
  if stop ≤ start then return .empty
  let mut selected : Array ByteArray := #[]
  for i in [start / capacity : (stop - 1) / capacity + 1] do
    let b ← Obend.Vault.Cost.readBinFile (block dir g i)
    if b.size > capacity || (i < (stop - 1) / capacity && b.size != capacity) then
      throw (IO.userError "log segment is truncated before the end of the log")
    selected := selected.push b
  return assemble selected.toList (start % capacity) (stop - start)

def readRange (Hb : Bytes → Bytes) (dir : System.FilePath) (start stop : Nat) : IO ByteArray := do
  match ← index Hb dir with
  | some idx => readRangeOf dir idx.generation start stop
  | none =>
    if !(← (selector dir).pathExists) then return .empty
    return (← Obend.Vault.Cost.readBinFile (selector dir)).extract start stop

def readAll (Hb : Bytes → Bytes) (dir : System.FilePath) : IO ByteArray := do
  readRange Hb dir 0 (← size Hb dir)

/-- Publish a checksummed index with an atomic rename. -/
def publish (Hb : Bytes → Bytes) (dir : System.FilePath) (idx : Index) : IO Unit := do
  let tmp := dir / ".obend" / "log.index-new"
  Obend.Vault.Cost.writeFile tmp (indexText Hb idx)
  IO.FS.rename tmp (selector dir)

/-- Prepare a boundary block before making it reachable. A prior interrupted truncation may have
left an orphan here: empty and flush it while it is still unselected, then publish the index.
A crash before publication sees the old prefix; after publication sees an empty next block. -/
def prepareBoundary (Hb : Bytes → Bytes) (dir : System.FilePath) (idx : Index)
    (bi : Nat) (publishing : Bool) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk (block dir idx.generation bi) .write
  h.flush
  if publishing && bi > idx.active then publish Hb dir ⟨idx.generation, bi⟩
  return h

/-- Append at a known logical end. Boundary blocks are cleared before publication, then written;
a crash at publication is the full predecessor. Blocks are flushed before proceeding. `publishing = false`
builds an unselected generation for migration or compaction. -/
def appendAt (Hb : Bytes → Bytes) (dir : System.FilePath) (idx : Index) (start : Nat)
    (b : ByteArray) (publishing : Bool) : IO Unit := do
  let mut off := 0
  while off < b.size do
    let pos := start + off
    let bi := pos / capacity
    let len := min (capacity - pos % capacity) (b.size - off)
    let h ← if pos % capacity == 0 then prepareBoundary Hb dir idx bi publishing
      else IO.FS.Handle.mk (block dir idx.generation bi) .append
    Obend.Vault.Cost.write h (b.extract off (off + len))
    h.flush
    off := off + len

def fresh (dir : System.FilePath) : IO Nat := do
  let mut g ← IO.monoNanosNow
  while ← (root dir / toString g).pathExists do g := g + 1
  IO.FS.createDirAll (root dir / toString g)
  return g

def lastBlock (size : Nat) : Nat := (size - 1) / capacity

/-- A legacy byte file is migrated once, before the next append. Publication is last. -/
def ensure (Hb : Bytes → Bytes) (dir : System.FilePath) : IO Index := do
  if let some idx ← index Hb dir then return idx
  let b ← if ← (selector dir).pathExists then Obend.Vault.Cost.readBinFile (selector dir) else pure .empty
  let g ← fresh dir
  let idx : Index := ⟨g, lastBlock b.size⟩
  appendAt Hb dir idx 0 b false
  publish Hb dir idx
  return idx

def append (Hb : Bytes → Bytes) (dir : System.FilePath) (b : ByteArray) : IO Unit := do
  let idx ← ensure Hb dir
  appendAt Hb dir idx (← sizeOf dir idx) b true

/-- Atomic replacement, used by compaction. The previously selected generation is removed only
after publication; an interrupted publication therefore preserves a complete log. -/
def replace (Hb : Bytes → Bytes) (dir : System.FilePath) (b : ByteArray) : IO Unit := do
  let old ← index Hb dir
  let g ← fresh dir
  let idx : Index := ⟨g, lastBlock b.size⟩
  appendAt Hb dir idx 0 b false
  publish Hb dir idx
  if let some previous := old then
    IO.FS.removeDirAll (root dir / toString previous.generation)

/-- Remove a rejected tail. Publish the retained last block before deleting later files; an
interrupted truncation can leave only rejected bytes or orphan files, never lose prefix bytes. -/
def truncate (Hb : Bytes → Bytes) (dir : System.FilePath) (stop : Nat) : IO Unit := do
  let idx ← ensure Hb dir
  let keep := (stop + capacity - 1) / capacity
  publish Hb dir ⟨idx.generation, lastBlock stop⟩
  if keep > 0 && stop % capacity != 0 then
    let f := block dir idx.generation (keep - 1)
    let b ← Obend.Vault.Cost.readBinFile f
    let tmp := f.withExtension "tmp"
    Obend.Vault.Cost.writeBinFile tmp (b.extract 0 (stop % capacity))
    IO.FS.rename tmp f
  for j in [keep : idx.active + 1] do
    let f := block dir idx.generation j
    if ← f.pathExists then IO.FS.removeFile f

end Obend.Vault.SegmentLog

namespace Obend.Vault.Log
open Obend.Digest.Cshake256.Fast (pushList pushList_data)

/-- Byte-array record encoder, with the same receipt framing as `encodeRecord`. -/
def encodeRecordExec (Hb : Bytes → Bytes) (r : Record) : ByteArray :=
  LogBytes.encodeRecordBytes Hb r

theorem encodeRecordExec_toList_eq_encodeRecord (Hb : Bytes → Bytes) (r : Record) :
    (encodeRecordExec Hb r).data.toList = encodeRecord Hb r := by
  rw [encodeRecordExec]
  exact LogBytes.encode_bytes_eq Hb r

/-- Append each record directly into one byte-array accumulator. -/
def encodeAllExecFrom (Hb : Bytes → Bytes) (acc : ByteArray) : List Record → ByteArray
  | [] => acc
  | r :: rs => encodeAllExecFrom Hb
      (pushList (pushList (pushList acc (headerOf r)) r.payload) (be 32 (Hr Hb r.receipt))) rs

theorem encodeAllExecFrom_eq (Hb : Bytes → Bytes) (rs : List Record) (acc : ByteArray) :
    (encodeAllExecFrom Hb acc rs).data.toList = acc.data.toList ++ encodeAll Hb rs := by
  induction rs generalizing acc with
  | nil => simp [encodeAllExecFrom, encodeAll]
  | cons r rs ih => simp [encodeAllExecFrom, ih, encodeAll, encodeRecord,
      pushList_data, List.append_assoc]

def encodeAllExec (Hb : Bytes → Bytes) (rs : List Record) : ByteArray :=
  encodeAllExecFrom Hb .empty rs

theorem encodeAllExec_toList_eq_encodeAll (Hb : Bytes → Bytes) (rs : List Record) :
    (encodeAllExec Hb rs).data.toList = encodeAll Hb rs := by
  simpa [encodeAllExec] using encodeAllExecFrom_eq Hb rs .empty

/-- Parse a loaded segment window at its byte offset, without traversing its prefix. -/
def parseSegmentExec (Hb : Bytes → Bytes) (prev : Nat) (bytes : ByteArray) (offset : Nat) :
    List Record × Nat × Option Drop := LogBytes.parseFromAt Hb prev bytes offset

theorem parseExec_eq_parseSpec (Hb : Bytes → Bytes) (prev : Nat) (bytes : ByteArray) (offset : Nat) :
    parseFrom Hb prev (bytes.data.toList.drop offset) =
      ((parseSegmentExec Hb prev bytes offset).1,
        bytes.data.toList.drop (parseSegmentExec Hb prev bytes offset).2.1,
        (parseSegmentExec Hb prev bytes offset).2.2) :=
  LogBytes.parseFromAt_eq Hb prev bytes offset
end Obend.Vault.Log

end
