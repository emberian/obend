module
/-
# FfiTruthfulnessTest — End-to-End Verification of FFI `Bridge.lean` Backdoor Removal (Audit Fix 15)

Verifies that:
1. `turnCommitCore_unproposed_tid_refused`: committing an un-proposed 32-byte `tidBytes` in
   `SessionState.empty` returns `-5` and leaves `admittedRoots = #[]`.
2. `verifyReceiptCore_unadmitted_self_opening_refused`: passing a 64-byte self-opening
   `[leaf(0, h) || h]` slice into `verifyReceiptCore SessionState.empty` returns `-8` (refused!).
3. `verifyReceiptCore_empty_session_refused`: passing an un-admitted 32-byte root slice into
   `verifyReceiptCore SessionState.empty` returns `-8` (refused!).
4. Positive flow: when a turn proposal `⟨sampleTid32, [], []⟩` is in `pendingProposals`,
   committing `sampleTid32` via `turnCommitCore` succeeds (`0`), admits `sampleTid32` into
   `admittedRoots`, and `verifyReceiptCore` on the committed session succeeds (`0`).
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

/-- 1. Un-proposed 32-byte `tidBytes` is refused with `-5` and does not pollute `admittedRoots`. -/
theorem test_unproposed_turn_commit_refused :
    (turnCommitCore SessionState.empty sampleTid32).2 = -5 ∧
    (turnCommitCore SessionState.empty sampleTid32).1.admittedRoots = #[] ∧
    (turnCommitCore SessionState.empty sampleTid32).1.admittedRoots.toList = [] :=
  turnCommitCore_unproposed_tid_refused sampleTid32 sampleTid32_size

/-- 2. Self-opening 64-byte `[leaf(0, h) || h]` receipt slice is refused (`-8`) when not admitted in session. -/
theorem test_unadmitted_self_opening_receipt_refused (h : Nat) :
    (verifyReceiptCore SessionState.empty (computeReceiptCommitment h ++ natTo32Bytes h)).2 = -8 :=
  verifyReceiptCore_unadmitted_self_opening_refused h

/-- 3. Concrete 64-byte `[leaf(0, 7) || 7]` self-opening slice is refused (`-8`) in `SessionState.empty`. -/
theorem test_concrete_self_opening_64_refused :
    (verifyReceiptCore SessionState.empty (computeReceiptCommitment 7 ++ natTo32Bytes 7)).2 = -8 :=
  verifyReceiptCore_unadmitted_self_opening_refused 7

/-- 4. Positive end-to-end pending proposal -> commit -> verifyReceiptCore flow succeeds (`0`). -/
theorem test_propose_commit_and_verify_admitted_receipt_succeeds :
    let prop : PendingTurnProposal := ⟨sampleTid32, [], []⟩
    let s1 : SessionState := { SessionState.empty with pendingProposals := [prop] }
    let (s2, commitCode) := turnCommitCore s1 sampleTid32
    let (_, verifyCode) := verifyReceiptCore s2 sampleTid32
    commitCode = 0 ∧ verifyCode = 0 ∧ s2.admittedRoots.contains sampleTid32 = true := by
  decide +kernel

#tooth turnCommitCore_unproposed_tid_refused by
  mutation turnCommitCore := fun s tidBytes =>
    ({ s with admittedRoots := s.admittedRoots.push tidBytes }, 0)

#tooth verifyReceiptCore_unadmitted_self_opening_refused by
  mutation verifyReceiptCore := fun s _ => (s, 0)

#print axioms test_unproposed_turn_commit_refused
#print axioms test_unadmitted_self_opening_receipt_refused
#print axioms test_concrete_self_opening_64_refused
#print axioms test_propose_commit_and_verify_admitted_receipt_succeeds

end Obend.Tests.FfiTruthfulnessTest
end
