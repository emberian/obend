module
/-
# FfiTruthfulnessTest — End-to-End Verification of FFI `Bridge.lean` Backdoor Removal (Audit Fix 15)

Verifies that:
1. `turnCommitCore_unproposed_tid_refused`: committing an un-proposed 32-byte `tidBytes` in
   `SessionState.empty` returns `-5` and leaves `committedRoots = #[]`.
2. `verifyReceiptCore_empty_session_refused`: a 64-byte self-opening `[leaf(0, h) || h]` slice,
   like any receipt, is refused (`-8`) by a session that has committed nothing.
3. The same at the concrete slice `[leaf(0, 7) || 7]`.
4. A turn proposal `⟨sampleTid32, [], []⟩` in `pendingProposals` commits (`0`) and its id is a
   committed root; the bare 32-byte root is NOT a receipt (`verifyReceiptCore_short_refused`):
   since 2026-11-04 a receipt is a framed Merkle opening against a committed root, and accepting a
   bare root was the self-admission path this test was written against.
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

/-- 4. A pending proposal commits and its id becomes a committed root; the bare root is refused as a
receipt (it is shorter than a receipt frame's header). -/
theorem test_propose_commit_and_bare_root_refused :
    let prop : PendingTurnProposal := ⟨sampleTid32, [], [], none⟩
    let s1 : SessionState := { SessionState.empty with pendingProposals := [prop] }
    let (s2, commitCode) := turnCommitCore s1 sampleTid32
    commitCode = 0 ∧ s2.committedRoots.contains sampleTid32 = true ∧
      (verifyReceiptCore s2 sampleTid32).2 = -8 := by
  refine ⟨by decide +kernel, by decide +kernel, verifyReceiptCore_short_refused _ _ ?_⟩
  rw [sampleTid32_size]; omega

#tooth turnCommitCore_unproposed_tid_refused by
  mutation turnCommitCore := fun s tidBytes =>
    ({ s with committedRoots := s.committedRoots.push tidBytes }, 0)

#tooth verifyReceiptCore_no_committed_refused by
  mutation verifyReceiptCore := fun s _ => (s, 0)

#print axioms test_unproposed_turn_commit_refused
#print axioms test_unadmitted_self_opening_receipt_refused
#print axioms test_concrete_self_opening_64_refused
#print axioms test_propose_commit_and_bare_root_refused

end Obend.Tests.FfiTruthfulnessTest
end
