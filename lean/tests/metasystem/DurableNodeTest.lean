module
/-
# DurableNodeTest — End-to-End Verification of 4-Tier `SovereignFinality.lean` & Durable Crash-Recovery

Verifies:
1. Tier 0 (`tier0_dial_free_confluent`): `.free` `.obend` laws commute under `joinData` semilattice join.
2. Tier 1 (`tier1_disjoint_fast_path_commutes`): Bernstein-disjoint `VaultTurn`s commute and preserve `collapseRoot`.
3. Tier 2 (`tier2_simplex_quorum_and_accountable_safety`): `advanceQuorumBoundGate` + `Simplex` accountable slashing.
4. Tier 3 (`edaSwarm_winner_admitted_and_sound`, `tier3_epistemic_drex_and_eda_race_sound`): Epistemic races over
   both `DrEXRace` (`drex-clearing@1`) and `AgenticEDA` (`mergeAndJudgeAgenticEdaBoard`).
5. Durable Crash-Recovery Metatheorems:
   - `durable_recovery_prevents_equivocation`,
   - `durable_expose_once_across_crashes`,
   - `durable_recovered_converges_on_collapse_root`,
   - `turnCommitCore_unproposed_tid_refused` & `verifyReceiptCore_unadmitted_self_opening_refused`.
-/

public import Obend.Consensus.SovereignFinality
public import Obend.FFI.Bridge
public import Obend.Tactic.Tooth
import all Obend.Consensus.Simplex
import all Obend.Consensus.SovereignFinality
import all Obend.FFI.Bridge

@[expose] public section

namespace Obend.Tests.DurableNodeTest

open Obend.Consensus.SovereignFinality
open Obend.Consensus.Simplex
open Obend.Consensus.Finality
open Obend.Consensus.Epistemic
open Obend.Hardware.AgenticEDA
open Obend.Run.Durable
open Obend.Fold.Collapse
open Obend.FFI

set_option autoImplicit false

/-- 1. Concrete verification of `DurableSimplexHost` crash + recovery preventing post-crash double-voting. -/
theorem test_durable_simplex_host_recovery_blocks_double_vote :
    (let initialState : State := { self := 0, deadline := 10 }
     let initialHost : DurableSimplexHost :=
       { self := 0, deadline := 10, journaledViews := [], volatileState := some initialState }
     let blockA : Block := [{ turnId := ByteArray.mk #[0x01], turn := none }]
     let blockB : Block := [{ turnId := ByteArray.mk #[0x02], turn := none }]
     match durableCastVote initialHost 1 blockA with
     | none => false
     | some votedHost =>
       let crashed := crashSimplexHost votedHost
       let recovered := recoverSimplexHost crashed
       crashed.volatileState.isNone &&
       match recovered.volatileState with
       | none => false
       | some restoredSt =>
         (viewAt restoredSt 1).voted &&
         (castVote restoredSt 1 blockB == restoredSt)) = true := by
  decide +kernel

/-- 2. Concrete verification of Tier 2 `QuorumBoundFinalityGate` promotion + accountable slashing receipt extraction. -/
theorem test_tier2_quorum_gate_and_slashing_extraction :
    let gate0 : QuorumBoundFinalityGate :=
      { turnId := 1
        currentTier := .attested
        faults := 1
        stateRoot := 0xCAFE
        attestSigners := [0]
        qcSigners := []
        qcDigest := none
        merkleRoot := none }
    let ev := QuorumBoundPromotionEvent.formQC 99 [0, 1, 2] 0xCAFE
    let slash := extractSlashingReceiptFromLists 1 100 200 [0, 1, 2, 3] [0, 1, 2] [1, 2, 3]
    (match advanceQuorumBoundGate gate0 ev with
     | some next => next.currentTier == .quorum_final && decide (next.qcSigners.length = 3)
     | none => false) = true ∧
    slash.equivocatingVoters = [1, 2] ∧
    2 ≤ slash.equivocatingVoters.length := by
  decide +kernel

/-- 3. Concrete verification of Tier 3 `AgenticEDA` epistemic race winner selection and conflict refusal. -/
theorem test_tier3_eda_swarm_epistemic_winner :
    checkEdaSwarmCandidate goldenEdaSwarmCandidate = true ∧
    checkEdaSwarmCandidate conflictingEdaSwarmCandidate = false ∧
    selectWinner () [conflictingEdaSwarmCandidate, goldenEdaSwarmCandidate] =
      some goldenEdaSwarmCandidate ∧
    selectWinner () [goldenEdaSwarmCandidate, conflictingEdaSwarmCandidate] =
      some goldenEdaSwarmCandidate :=
  goldenEdaSwarmRace_selects_valid_winner

/-! ## 4. Re-export and verify all 4-Tier & Durable Crash-Recovery metatheorems and FFI refusal theorems. -/
#check @tier0_dial_free_confluent
#check @tier1_disjoint_fast_path_commutes
#check @tier2_simplex_quorum_and_accountable_safety
#check @edaSwarm_winner_admitted_and_sound
#check @edaSwarm_conflicting_candidate_invalid
#check @tier3_epistemic_drex_and_eda_race_sound
#check @durable_recovery_prevents_equivocation
#check @durable_expose_once_across_crashes
#check @durable_recovered_converges_on_collapse_root
#check @turnCommitCore_unproposed_tid_refused
#check @verifyReceiptCore_unadmitted_self_opening_refused

#tooth edaSwarm_conflicting_candidate_invalid by
  mutation checkEdaSwarmCandidate := fun _ => true

#print axioms tier0_dial_free_confluent
#print axioms tier1_disjoint_fast_path_commutes
#print axioms tier2_simplex_quorum_and_accountable_safety
#print axioms edaSwarm_winner_admitted_and_sound
#print axioms tier3_epistemic_drex_and_eda_race_sound
#print axioms durable_recovery_prevents_equivocation
#print axioms durable_expose_once_across_crashes
#print axioms durable_recovered_converges_on_collapse_root

end Obend.Tests.DurableNodeTest
end
