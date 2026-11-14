module
/-
# DurableNodeTest — End-to-End Verification of `UnifiedDeos`, `SimplexFinalityGate`, Epistemic Races & Durable WAL Recovery

Verifies:
1. Durable WAL Crash-Recovery (`DurableSimplexHost`, `durable_recovery_prevents_equivocation`,
   `durable_expose_once_across_crashes`, and the journaled outbox:
   `durable_outbox_dispatch_once_across_crashes`; its concrete run is in
   `DeosSimplexOutboxSeamTest`).
2. 4-Tier Finality Promotion (`SimplexFinalityGate`, `advanceSimplexGate`, `quorum_final_gates_unique_per_height`,
   `advanceSimplexGate_collapsed_binds_cshake`, `accountable`).
3. Bernstein-Disjoint Fast-Path Commutativity & Collapsed Root Convergence
   (`unifiedDeos_fastpath_and_simplex_finality_sound`).
4. `AgenticEDA` Epistemic Winner Selection (`goldenEdaSwarmRace_selects_valid_winner`,
   `order_insensitive_perm`).
5. FFI Boundary Refusal Guarantees (`turnCommitCore_unproposed_tid_refused`,
   `verifyReceiptCore_empty_session_refused`).
-/

public import Obend.Vault.UnifiedDeos
public import Obend.Hardware.AgenticEDA
public import Obend.FFI.Bridge
public import Obend.Tactic.Tooth
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Vault.UnifiedDeos
import all Obend.Hardware.AgenticEDA
import all Obend.FFI.Bridge

public section

namespace Obend.Tests.DurableNodeTest

open Obend.Vault.UnifiedDeos
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexTrace
open Obend.Consensus.Finality
open Obend.Consensus.Epistemic
open Obend.Hardware.AgenticEDA
open Obend.Run.Durable
open Obend.Fold.Collapse
open Obend.FFI

set_option autoImplicit false

/-- 1. Concrete verification of `DurableSimplexHost` crash + recovery preventing post-crash double-voting. -/
example :
    (let initialState : VolatileSimplexVoter := { self := 0, deadline := 10, votes := [] }
     let initialHost : DurableSimplexHost :=
       { self := 0, deadline := 10, journaledVotes := [], volatileState := some initialState,
         outbox := ⟨3, 0, 0, 0, [], 0, []⟩ }
     let chainA : Chain := [.block 1 101]
     let chainB : Chain := [.block 1 202]
     match durableCastVote initialHost 1 chainA with
     | none => false
     | some votedHost =>
       let crashed := crashSimplexHost votedHost
       let recovered := recoverSimplexHost crashed
       crashed.volatileState.isNone &&
       match recovered.volatileState with
       | none => false
       | some restoredSt =>
         hasVotedSimplexView restoredSt 1 &&
         (castSimplexVote restoredSt 1 chainB == restoredSt)) = true := by
  decide +kernel

/-- 2. Concrete verification of Tier 2 `SimplexFinalityGate` promotion + accountable slashing receipt extraction. -/
example :
    let proto4 : Protocol := ⟨[0, 1, 2, 3], 1, (· == 3), by decide +kernel, by decide +kernel, by decide +kernel⟩
    let vRoot : ByteArray := bytesOfList (List.replicate 32 0xCA)
    let cert99 : FinCert := ⟨1, [.block 1 99], [0, 1, 2]⟩
    let sentFin : Sent :=
      [ ⟨0, 1, .finalize, .block [.block 1 99]⟩
      , ⟨1, 1, .finalize, .block [.block 1 99]⟩
      , ⟨2, 1, .finalize, .block [.block 1 99]⟩ ]
    let gate0 : SimplexFinalityGate :=
      { turnId := bytesOfList (List.replicate 32 0x01)
        currentTier := .attested
        vaultRoot := some vRoot }
    let tA : Target := .block [.block 1 100]
    let tB : Target := .block [.block 1 200]
    let sentSlash : Sent :=
      [ ⟨0, 1, .vote, tA⟩, ⟨1, 1, .vote, tA⟩, ⟨2, 1, .vote, tA⟩
      , ⟨1, 1, .vote, tB⟩, ⟨2, 1, .vote, tB⟩, ⟨3, 1, .vote, tB⟩ ]
    let slash := extractReceipt [0, 1, 2, 3] sentSlash 1 tA tB
    (match advanceSimplexGate proto4 sentFin gate0 (.finalizeWithCert cert99 vRoot) with
     | some next => next.currentTier == .quorum_final && (next.finCert == some cert99)
     | none => false) = true ∧
    slash.checks sentSlash = true ∧
    slash.signers = [1, 2] ∧
    2 ≤ slash.signers.length := by
  decide +kernel

/-- `VerifiableRace` over `AgenticEDA` multi-agent board merge proposals (`Epistemic.selectWinner`). -/
def checkEdaSwarmCandidate (p : MultiAgentBoardMergeProposal) : Bool :=
  decide (mergeAndJudgeAgenticEdaBoard p = .admitted)

instance : VerifiableRace Nat MultiAgentBoardMergeProposal where
  isValid maxCost p := decide (p.rfLayoutAgentBoard.costCents ≤ maxCost) && checkEdaSwarmCandidate p
  cost baseCost p := baseCost + p.rfLayoutAgentBoard.costCents
  digest p := ByteArray.mk #[UInt8.ofNat (p.rfLayoutAgentBoard.costCents % 256)]

/-- 3. Concrete verification of `AgenticEDA` epistemic race winner selection and conflict refusal. -/
theorem test_eda_swarm_epistemic_winner :
    checkEdaSwarmCandidate goldenMultiAgentCoDesignProposal = true ∧
    checkEdaSwarmCandidate conflictingMultiAgentCoDesignProposal = false ∧
    selectWinner 500 [conflictingMultiAgentCoDesignProposal, goldenMultiAgentCoDesignProposal] =
      some goldenMultiAgentCoDesignProposal ∧
    selectWinner 500 [goldenMultiAgentCoDesignProposal, conflictingMultiAgentCoDesignProposal] =
      some goldenMultiAgentCoDesignProposal := by
  have hAdm := goldenMultiAgentCoDesign_admitted_and_conflict_refused.2.1
  have hConf := goldenMultiAgentCoDesign_admitted_and_conflict_refused.2.2
  have hc1 : checkEdaSwarmCandidate goldenMultiAgentCoDesignProposal = true := by
    unfold checkEdaSwarmCandidate; rw [hAdm]; decide
  have hc2 : checkEdaSwarmCandidate conflictingMultiAgentCoDesignProposal = false := by
    unfold checkEdaSwarmCandidate; rw [hConf]; decide
  have hv1 : certValid 500 goldenMultiAgentCoDesignProposal = true := by
    change (decide (goldenMultiAgentCoDesignProposal.rfLayoutAgentBoard.costCents ≤ 500) &&
      checkEdaSwarmCandidate goldenMultiAgentCoDesignProposal) = true
    rw [hc1]
    decide
  have hv2 : certValid 500 conflictingMultiAgentCoDesignProposal = false := by
    change (decide (conflictingMultiAgentCoDesignProposal.rfLayoutAgentBoard.costCents ≤ 500) &&
      checkEdaSwarmCandidate conflictingMultiAgentCoDesignProposal) = false
    rw [hc2]
    simp
  refine ⟨hc1, hc2, ?_, ?_⟩
  · unfold selectWinner
    simp only [List.filter_cons, hv1, hv2, Bool.false_eq_true, ↓reduceIte, List.filter_nil]
    rfl
  · unfold selectWinner
    simp only [List.filter_cons, hv1, hv2, Bool.false_eq_true, ↓reduceIte, List.filter_nil]
    rfl

/-- Any `AgenticEDA` board merge proposal refused by physical/merge DRC is strictly refused by `checkEdaSwarmCandidate`. -/
theorem edaSwarm_refusedByPhysics_candidate_refused
    (p : MultiAgentBoardMergeProposal) (msg : String)
    (h : mergeAndJudgeAgenticEdaBoard p = .refusedByPhysics msg) :
    checkEdaSwarmCandidate p = false := by
  simp [checkEdaSwarmCandidate, h]

#tooth edaSwarm_refusedByPhysics_candidate_refused by
  mutation checkEdaSwarmCandidate := fun _ => true

/-! ## 4. Verify UnifiedDeos, SimplexFinalityGate, Durable Recovery & FFI Refusal Theorems -/
#check @unifiedDeos_ledger_and_turn_sound
#check @unifiedDeos_zoe_and_escrow_safety
#check @unifiedDeos_markets_sound
#check @unifiedDeos_carry_and_mandate_sound
#check @unifiedDeos_fastpath_and_simplex_finality_sound
#check @quorum_final_gates_unique_per_height
#check @advanceSimplexGate_collapsed_binds_cshake
#check @durable_recovery_prevents_equivocation
#check @durable_expose_once_across_crashes
#check @durable_outbox_dispatch_once_across_crashes
#check @validHostRun_outboxTrace
#check @turnCommitCore_unproposed_tid_refused
#check @verifyReceiptCore_empty_session_refused

#print axioms unifiedDeos_ledger_and_turn_sound
#print axioms unifiedDeos_zoe_and_escrow_safety
#print axioms unifiedDeos_markets_sound
#print axioms unifiedDeos_carry_and_mandate_sound
#print axioms unifiedDeos_fastpath_and_simplex_finality_sound
#print axioms quorum_final_gates_unique_per_height
#print axioms advanceSimplexGate_collapsed_binds_cshake
#print axioms durable_recovery_prevents_equivocation
#print axioms durable_expose_once_across_crashes
#print axioms durable_outbox_dispatch_once_across_crashes

end Obend.Tests.DurableNodeTest
end
