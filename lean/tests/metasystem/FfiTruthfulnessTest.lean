module
/-
# FfiTruthfulnessTest — End-to-End Verification of `Obend.FFI.Bridge` Soundness & Refusals

Verifies that:
1. `turnCommitCore_unproposed_tid_refused`: committing an un-proposed 32-byte `tidBytes` in
   `SessionState.empty` returns `-5` and leaves `committedRoots = #[]`.
2. `verifyReceiptCore_empty_session_refused`: a 64-byte self-opening `[leaf(0, h) || h]` slice,
   like any receipt, is refused (`-8`) by a session that has committed nothing.
3. `evalCellCore` refuses non-`.obend` payloads fail-closed (`-4`) with empty output rather than echoing.
4. `projectHardwareCore` refuses non-witness payloads fail-closed (`-7`) with empty output.
5. `cellPopLeanCore` refuses non-empty payloads (`-4`) with empty output (no string-interpolated Lean codegen).
6. A pending proposal commits (`0`), advances `replaySession` preserving `Obend.Vault.Replay.Reachable`,
   records the root in `committedRoots`, and refuses the bare 32-byte root as a receipt.
-/

public import Obend.FFI.Bridge
public import Obend.Tactic.Tooth
import all Obend.FFI.Bridge

@[expose] public section

namespace Obend.Tests.FfiTruthfulnessTest

open Obend.FFI
open Obend.Digest.Cshake256.Native

set_option autoImplicit false

/-- Sample 32-byte turn ID for unproposed commit refusal tests. -/
def sampleTid32 : ByteArray :=
  ByteArray.mk (Array.replicate 32 0x42)

theorem sampleTid32_size : sampleTid32.size = 32 := by decide

/-- Sample non-empty payload for `cellPopLeanCore` refusal check. -/
def samplePopPayload : ByteArray :=
  ByteArray.mk #[0x63, 0x31, 0x3a, 0x32, 0x38]

/-- 1. Un-proposed 32-byte `tidBytes` is refused with `-5` and does not pollute `committedRoots`. -/
theorem test_unproposed_turn_commit_refused :
    (turnCommitCore SessionState.empty sampleTid32).2 = -5 ∧
    (turnCommitCore SessionState.empty sampleTid32).1.committedRoots = #[] :=
  turnCommitCore_unproposed_tid_refused sampleTid32 sampleTid32_size

/-- 2. Self-opening 64-byte `[leaf(0, h) || h]` receipt slice is refused (`-8`) when not admitted in session. -/
theorem test_unadmitted_self_opening_receipt_refused (h : Nat) :
    (verifyReceiptCore SessionState.empty (computeReceiptCommitment h ++ natTo32Bytes h)).2 = -8 :=
  verifyReceiptCore_empty_session_refused _

/-- 3. Concrete 64-byte `[leaf(0, 7) || 7]` self-opening slice is refused (`-8`) in `SessionState.empty`. -/
theorem test_concrete_self_opening_64_refused :
    (verifyReceiptCore SessionState.empty (computeReceiptCommitment 7 ++ natTo32Bytes 7)).2 = -8 :=
  verifyReceiptCore_empty_session_refused _

/-- 4. Non-`.obend` UTF-8 cell payloads fail closed (`-4`) with empty output and preserve `doc`. -/
theorem test_non_obend_cell_refused (cellBytes : ByteArray) (text : String)
    (hne : cellBytes.isEmpty = false)
    (hdec : Obend.Spec.Parse.decodeSource cellBytes = some text)
    (hnot : isObendPayload text = false) :
    (evalCellCore SessionState.empty cellBytes).2.2 = -4 ∧
    (evalCellCore SessionState.empty cellBytes).2.1 = ByteArray.empty ∧
    (evalCellCore SessionState.empty cellBytes).1.doc = SessionState.empty.doc :=
  evalCellCore_non_obend_refused SessionState.empty cellBytes text hne hdec hnot

/-- 5. Non-witness hardware projection payloads fail closed (`-7`) instead of echoing bytes. -/
theorem test_mock_hardware_projection_refused (hwBytes : ByteArray)
    (hne : hwBytes.isEmpty = false)
    (hdec : decodeTurnWitness? hwBytes = none) :
    (projectHardwareCore SessionState.empty hwBytes).2.2 = -7 ∧
    (projectHardwareCore SessionState.empty hwBytes).2.1 = ByteArray.empty :=
  projectHardwareCore_non_witness_refused SessionState.empty hwBytes hne hdec

/-- 6. Non-empty `cellPopLeanCore` payload fails closed (`-4`) with empty output. -/
theorem test_cell_pop_lean_refused :
    (cellPopLeanCore SessionState.empty samplePopPayload).2.2 = -4 ∧
    (cellPopLeanCore SessionState.empty samplePopPayload).2.1 = ByteArray.empty :=
  cellPopLeanCore_nonempty_refused SessionState.empty samplePopPayload rfl

/-- 7. A pending proposal commits (`0`), advances `replaySession` preserving `Obend.Vault.Replay.Reachable`,
records `sampleTid32` in `committedRoots`, and refuses the bare 32-byte root as a receipt. -/
theorem test_propose_commit_and_bare_root_refused (nextReplay : Obend.Vault.Replay.Session)
    (hadm : Obend.Vault.Log.Session.admit Obend.Vault.Replay.logHash Obend.Vault.Replay.deployed
      SessionState.empty.replaySession
      (Obend.Vault.Replay.encodeTurn
        (.base (applyWritesToWorld SessionState.empty.replaySession.world SessionState.empty.doc []))) =
      .ok nextReplay) :
    let prop : PendingTurnProposal := ⟨sampleTid32, [], [], none, none⟩
    let s1 : SessionState := { SessionState.empty with pendingProposals := [prop] }
    let res := turnCommitCore s1 sampleTid32
    res.2 = 0 ∧
      res.1.replaySession = nextReplay ∧
      sampleTid32 ∈ res.1.committedRoots ∧
      Obend.Vault.Replay.Reachable res.1.replaySession ∧
      (verifyReceiptCore res.1 sampleTid32).2 = -8 := by
  intro prop s1 res
  have hfind : s1.pendingProposals.find? (fun (p : PendingTurnProposal) => p.tidBytes == sampleTid32) = some prop := by
    simp [s1, prop]
    decide
  cases hturnEq : proposalTurn s1 prop with
  | none =>
    exfalso
    simp [proposalTurn, Obend.Vault.VaultTurn.ofWitnessLegs, prop] at hturnEq
  | some turn =>
    have hwitNil : turn.witnesses = [] :=
      (Obend.Vault.VaultTurn.ofWitnessLegs_fields hturnEq).2.2.2
    have hall : turn.witnesses.all (Obend.Vault.checkTurnWitness sessionJudgeFormats) = true := by
      rw [hwitNil]; rfl
    have hcomm := turnCommitCore_commits_turn s1 sampleTid32 prop turn nextReplay
      sampleTid32_size hfind rfl rfl hturnEq hall hadm
    have hreach : Obend.Vault.Replay.Reachable res.1.replaySession :=
      @turnCommitCore_preserves_reachable s1 sampleTid32 Obend.Vault.Log.Reachable.genesis
    have hshort : (verifyReceiptCore res.1 sampleTid32).2 = -8 := by
      apply verifyReceiptCore_short_refused
      rw [sampleTid32_size]
      omega
    exact ⟨hcomm.1, hcomm.2.1, hcomm.2.2.2.1, hreach, hshort⟩

#tooth turnCommitCore_unproposed_tid_refused by
  mutation turnCommitCore := fun s tidBytes =>
    ({ s with committedRoots := s.committedRoots.push tidBytes }, 0)

#tooth verifyReceiptCore_no_committed_refused by
  mutation verifyReceiptCore := fun s _ => (s, 0)

#tooth evalCellCore_non_obend_refused by
  mutation evalCellCore := fun s bs => (s, bs, 0)

#tooth projectHardwareCore_non_witness_refused by
  mutation projectHardwareCore := fun s bs => (s, bs, 0)

#print axioms test_unproposed_turn_commit_refused
#print axioms test_unadmitted_self_opening_receipt_refused
#print axioms test_concrete_self_opening_64_refused
#print axioms test_non_obend_cell_refused
#print axioms test_mock_hardware_projection_refused
#print axioms test_cell_pop_lean_refused
#print axioms test_propose_commit_and_bare_root_refused

end Obend.Tests.FfiTruthfulnessTest
end
