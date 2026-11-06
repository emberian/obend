module
/-
# Obend.Vault.Retention — the right to forget a prefix of the log, as a declared judgment

A vault's log (`Obend.Vault.Log`, `Obend.Vault.Replay`) is its truth, and it grows with every
command; every command reads all of it. This module is the right to forget a prefix of it, as a
declared and scoped judgment, after Feldera's LATENESS (a declared bound on how late a correction may
arrive, after which state may be reclaimed and a later correction is refused by name) and the
epistemic reading of `collected-writings/prompts/RESEARCH-GPT-transport.md` §6 (a prefix may be
forgotten only when no still-admissible future needs it).

**The compacted log (§1).** A log may start with a CHECKPOINT RECORD: a record admitted at genesis
whose turn steps genesis to the world after a forgotten prefix and names, as its ANCHOR, the receipt
digest the prefix ended at (`anchorOf`). `parseLog` reads such a log: the records after the checkpoint
record follow its anchor, so the receipt chain is checked across it; a log without one is read from
genesis as before (`recoverLog_plain`). For a session whose log is compacted after `n` records
(`Compacts`):
* `state_eq_replay_compacted`: the compacted log replays to the world the session serves, the replay
  of its whole log (`state_eq_replay_log`, restated over the compacted log);
* `recover_eq_replay_prefix_compacted`: a crash at any byte of the compacted log recovers the replay
  of its longest prefix of whole records, a world the session served after the same records of its
  whole log (genesis when the checkpoint record itself is torn), and drops the rest as a torn tail
  (`recover_eq_replay_prefix`, restated).

**The contract (§2).** A `forget` turn (`Obend.Vault.Replay.Turn.forget`) declares a `Contract`: its
name, the forms it retires and the branches it abandons. At the deployed machine
(`Obend.Vault.Replay`): `forget_refused_when_needed` (a forget is refused, by name, while a proposal
sent from the vault awaits its receipt, a form issued there stands unretired, a retired form has a
continuity contract, or a declared branch has not merged and is not abandoned; `needs_none_iff`),
`forget_sound` (the theorems of §1 at the deployed machine) and `late_correction_refused` (after the
contract, a proposal for a retired form, a merge from an abandoned branch and a merge from a replica
whose log does not reach the horizon are each refused, naming the contract). The entry
(`Obend.Vault.Cli`) appends the forget, then writes the compacted log beside the log and renames it
over it; recovery drops an interrupted new log and compacts again a log whose last record is a forget.

**What is not here.** A forget forgets the whole log before it (the contract bounds lateness at that
point; a horizon inside the log, with obligations dated by record, is not done). The world itself is
not compacted: the store keeps every page's history, which a merge's base is read from, so a
checkpoint record is about the size of a checkpoint file. Whether another replica's log reaches the
horizon is read by the command and recorded in the merge's turn (as an open records the files it
read); the step trusts the record. A branch merged before a forget that writes on afterwards does not
reach the horizon and is refused like any other. Bytes are `List UInt8`; a `ByteArray` codec is a
separate quest.
-/
public import Obend.Vault.Log
@[expose] public section

namespace Obend.Vault.Retention

open Obend.Vault.Rehydration (WitnessReceipt genesisSentinel)
open Obend.Vault.Log

set_option autoImplicit false

/-! ## 1. A compacted log, and how it is read -/

section Compact
variable {W O : Type} (Hb : Bytes → Bytes) (M : Machine W O) (anchorOf : Bytes → Option Nat)

/-- **Read a log that may be compacted**: when its first record follows genesis and its turn names an
ANCHOR (`anchorOf`: a checkpoint record, standing for a forgotten prefix that ended at that receipt
digest), the records after it follow the anchor; otherwise the log is read from genesis as ever
(`parseFrom`). -/
def parseLog (bs : Bytes) : List Record × Bytes × Option Drop :=
  match parseOne Hb (some genesisSentinel) bs with
  | .ok (r, rest) =>
    match anchorOf r.payload with
    | some a =>
      let (qs, tail, why) := parseFrom Hb a rest
      (r :: qs, tail, why)
    | none => parseFrom Hb genesisSentinel bs
  | .error _ => parseFrom Hb genesisSentinel bs

/-- **Recover from a log that may be compacted**: replay what `parseLog` reads, from genesis. -/
def recoverLog (w0 : W) (bs : Bytes) : Recovered W :=
  let (qs, tail, why) := parseLog Hb anchorOf bs
  ⟨replay M w0 qs, qs.length, tail, why⟩

/-- **The compaction of a session's log after `n` records**: the checkpoint record `cp` admitted at
genesis by a turn that steps genesis to the world after those records and names, as its anchor, the
receipt digest they end at; then the records after them, unchanged. -/
structure Compacts (w0 : W) (S : Session W) (n : Nat) (cp : Record) : Prop where
  pos : 0 < n
  le : n ≤ S.log.length
  admit : ∃ o, Log.admit Hb M w0 genesisSentinel cp.payload = .ok (replay M w0 (S.log.take n), o, cp)
  anchor : anchorOf cp.payload = some (lastHash Hb genesisSentinel (S.log.take n))

variable {Hb M anchorOf}

theorem compacts_wf {w0 : W} {S : Session W} {n : Nat} {cp : Record} (hc : Compacts Hb M anchorOf w0 S n cp) :
    cp.WF Hb ∧ cp.receipt.prevHash = genesisSentinel ∧
      M.step w0 cp.payload = .ok (replay M w0 (S.log.take n), hc.admit.choose) := by
  obtain ⟨hs, hr, hl⟩ := Log.admit_ok Hb M hc.admit.choose_spec
  refine ⟨?_, ?_, hs⟩
  · rw [hr]
    exact ⟨(by decide : genesisSentinel < bound), dig_lt Hb _, dig_lt Hb _, rfl, hl⟩
  · rw [hr]

/-- The checkpoint record steps genesis to the world after the prefix it stands for. -/
theorem replay_compacted {w0 : W} {S : Session W} {n : Nat} {cp : Record}
    (hc : Compacts Hb M anchorOf w0 S n cp) (rs : List Record) :
    replay M w0 (cp :: rs) = replay M w0 (S.log.take n ++ rs) := by
  rw [replay_append]
  simp only [replay, List.foldl_cons, stepB, (compacts_wf hc).2.2]

/-- **`forget_sound`, the world**: the world after forgetting is the replay of the whole log. The
compacted log (the checkpoint record, then the records after the prefix) replays to the world the
session serves, which is the replay of its whole log (`state_eq_replay_log`). -/
theorem state_eq_replay_compacted {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) {n : Nat} {cp : Record}
    (hc : Compacts Hb M anchorOf w0 S n cp) :
    S.world = replay M w0 (cp :: S.log.drop n) := by
  rw [replay_compacted hc, List.take_append_drop, state_eq_replay_log h]

/-- **A crash at any byte of a compacted log**: what is read is the longest prefix of whole records of
the compacted log; its replay is the world the session served after the same records of its whole
log (genesis, when the checkpoint record itself is torn); and the rest is dropped, named `torn`. -/
theorem recover_eq_replay_prefix_compacted {w0 : W} {S : Session W} (h : Reachable Hb M w0 S) {n : Nat}
    {cp : Record} (hc : Compacts Hb M anchorOf w0 S n cp) (k : Nat) :
    let C := cp :: S.log.drop n
    let m := whole Hb C k
    let tail := ((encodeAll Hb C).take k).drop (encodeAll Hb (C.take m)).length
    recoverLog Hb M anchorOf w0 ((encodeAll Hb C).take k) = ⟨replay M w0 (C.take m), m, tail, tornWhy tail⟩ ∧
      replay M w0 (C.take m) = replay M w0 (S.log.take (if m = 0 then 0 else n + (m - 1))) ∧
      Reachable Hb M w0 ⟨replay M w0 (C.take m), S.log.take (if m = 0 then 0 else n + (m - 1))⟩ := by
  obtain ⟨hl, hwf⟩ := log_sound h
  obtain ⟨hcwf, hcprev, _⟩ := compacts_wf hc
  have hsplit : S.log = S.log.take n ++ S.log.drop n := (List.take_append_drop _ _).symm
  have hlpost : Linked Hb (lastHash Hb genesisSentinel (S.log.take n)) (S.log.drop n) :=
    ((Linked_append Hb _ _ _).1 (hsplit ▸ hl)).2
  have hwpost : ∀ r ∈ S.log.drop n, r.WF Hb := fun r hr => hwf r (List.mem_of_mem_drop hr)
  have hP := encodeRecord_length Hb cp
  -- the served-world clause follows from the replay clause
  suffices hmain : let C := cp :: S.log.drop n
      let m := whole Hb C k
      let tail := ((encodeAll Hb C).take k).drop (encodeAll Hb (C.take m)).length
      recoverLog Hb M anchorOf w0 ((encodeAll Hb C).take k) = ⟨replay M w0 (C.take m), m, tail, tornWhy tail⟩ ∧
        replay M w0 (C.take m) = replay M w0 (S.log.take (if m = 0 then 0 else n + (m - 1))) by
    refine ⟨hmain.1, hmain.2, ?_⟩
    rw [hmain.2]
    exact prefix_reachable h _
  simp only
  by_cases hk : (encodeRecord Hb cp).length ≤ k
  · -- the checkpoint record is whole
    have hw : whole Hb (cp :: S.log.drop n) k = whole Hb (S.log.drop n) (k - (encodeRecord Hb cp).length) + 1 := by
      simp [whole, hk]
    have htk : (encodeAll Hb (cp :: S.log.drop n)).take k =
        encodeRecord Hb cp ++ (encodeAll Hb (S.log.drop n)).take (k - (encodeRecord Hb cp).length) := by
      simp only [encodeAll]
      rw [List.take_append, List.take_of_length_le hk]
    have hone : parseOne Hb (some genesisSentinel) (encodeAll Hb (cp :: S.log.drop n) |>.take k) =
        .ok (cp, (encodeAll Hb (S.log.drop n)).take (k - (encodeRecord Hb cp).length)) := by
      rw [htk]; exact parseOne_encode Hb hcwf (fun p hp => by cases hp; exact hcprev) _
    rw [hw]
    simp only [recoverLog, parseLog, hone, hc.anchor]
    rw [parseFrom_take Hb (S.log.drop n) _ hlpost hwpost]
    simp only [List.take_succ_cons, List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    refine ⟨?_, ?_⟩
    · simp only [Recovered.mk.injEq, true_and]
      have hd : ((encodeAll Hb (cp :: S.log.drop n)).take k).drop
          (encodeAll Hb (cp :: (S.log.drop n).take (whole Hb (S.log.drop n) (k - (encodeRecord Hb cp).length)))).length =
          ((encodeAll Hb (S.log.drop n)).take (k - (encodeRecord Hb cp).length)).drop
            (encodeAll Hb ((S.log.drop n).take (whole Hb (S.log.drop n) (k - (encodeRecord Hb cp).length)))).length := by
        rw [htk]; simp only [encodeAll, List.length_append]; rw [drop_len_append]
      refine ⟨?_, hd ▸ rfl, hd ▸ rfl⟩
      have := whole_le (Hb := Hb) (S.log.drop n) (k - (encodeRecord Hb cp).length)
      simp only [List.length_drop] at this
      simp [List.length_take, Nat.min_eq_left this]
    · rw [replay_compacted hc, List.take_add]
  · -- the checkpoint record is torn: nothing is read, and the world is genesis
    have hw : whole Hb (cp :: S.log.drop n) k = 0 := by simp [whole, hk]
    have htk : (encodeAll Hb (cp :: S.log.drop n)).take k = (encodeRecord Hb cp).take k := by
      simp only [encodeAll]
      rw [List.take_append, show k - (encodeRecord Hb cp).length = 0 by omega]; simp
    rw [hw]
    simp only [List.take_zero, ↓reduceIte, show encodeAll Hb ([] : List Record) = [] from rfl, List.length_nil,
      List.drop_zero]
    refine ⟨?_, by simp⟩
    rw [htk]
    have htorn : parseOne Hb (some genesisSentinel) ((encodeRecord Hb cp).take k) = .error .torn :=
      parseOne_torn Hb hcwf (List.take_append_drop _ _) (by rw [Ne, List.drop_eq_nil_iff]; omega)
    simp only [recoverLog, parseLog, htorn]
    by_cases hk0 : (encodeRecord Hb cp).take k = []
    · rw [hk0, parseFrom_nil]; simp [replay, tornWhy]
    · rw [parseFrom_error Hb hk0 htorn]; simp [replay, tornWhy, hk0]

/-- **A log never compacted reads as before**: where no turn of a session's log names an anchor,
reading it as a log that may be compacted is reading it from genesis, at every truncation. -/
theorem recoverLog_plain {w0 : W} {S : Session W} (h : Reachable Hb M w0 S)
    (hplain : ∀ r ∈ S.log, anchorOf r.payload = none) (k : Nat) :
    recoverLog Hb M anchorOf w0 ((encodeAll Hb S.log).take k) = recover Hb M w0 ((encodeAll Hb S.log).take k) := by
  obtain ⟨hl, hwf⟩ := log_sound h
  simp only [recoverLog, recover, parseLog]
  cases hone : parseOne Hb (some genesisSentinel) ((encodeAll Hb S.log).take k) with
  | error d => rfl
  | ok v =>
    obtain ⟨r, rest⟩ := v
    have hpf := parseFrom_ok Hb hone
    rw [parseFrom_take Hb S.log genesisSentinel hl hwf k] at hpf
    have hr : r ∈ S.log := by
      have : r ∈ S.log.take (whole Hb S.log k) := by
        have := congrArg Prod.fst hpf; simp only at this; rw [this]; simp
      exact List.mem_of_mem_take this
    simp only [hplain r hr]

end Compact

/-! ## 2. The retention contract a vault declares -/

/-- **A retention contract**, declared by a `forget` turn: its name, the forms it retires (a proposal
for one of them is refused after it, naming the contract) and the branches it abandons (a merge from
one of them is refused after it, naming the contract). Everything before the turn is forgotten from
the log; a correction that rests on it arrives later than the contract allows. -/
structure Contract where
  name : String
  retire : List String := []
  abandon : List String := []
deriving DecidableEq, Repr

/-- A branch this vault declared (`obend fork`), and whether it has merged since. -/
structure Fork where
  name : String
  merged : Bool := false
deriving DecidableEq, Repr

open Lean (Json toJson)

def strsJson (xs : List String) : Json := Json.arr (xs.map Json.str).toArray
def strsOf (j : Json) : Except String (List String) := do (← j.getArr?).toList.mapM fun e => e.getStr?

def contractJson (c : Contract) : Json :=
  Json.mkObj [("name", Json.str c.name), ("retire", strsJson c.retire), ("abandon", strsJson c.abandon)]

def contractOf (j : Json) : Except String Contract := do
  return ⟨← j.getObjValAs? String "name", ← strsOf (← j.getObjVal? "retire"), ← strsOf (← j.getObjVal? "abandon")⟩

def forkJson (b : Fork) : Json := Json.mkObj [("name", Json.str b.name), ("merged", toJson b.merged)]

def forkOf (j : Json) : Except String Fork := do
  return ⟨← j.getObjValAs? String "name", ← j.getObjValAs? Bool "merged"⟩

end Obend.Vault.Retention

end
