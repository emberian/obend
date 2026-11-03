module
/-
# Obend.Consensus — Umbrella consensus interface for Obend

Re-exports symbolic Simplex BFT consensus, 4-tier finality ladder, and epistemic
consensus for parallel solver/prover race resolution.
-/

public import Obend.Consensus.Simplex
public import Obend.Consensus.Finality
public import Obend.Consensus.Epistemic
public import Obend.Consensus.SovereignFinality

@[expose] public section
namespace Obend.Consensus

export Obend.Consensus.Finality (
  FinalityTier
  Operation
  minTier
  admitsOp
  admitsOp_mono
  PromotionEvent
  promoteStep
  FinalityStep
  FinalitySteps
  promoteStep_sound
  reachable_no_downgrade
  downgrade_not_a_step
  collapsed_downgrade_not_a_step
  downgrade_unreachable
  collapsed_is_terminal
  joinTier
  joinTier_dominates
  turnCommitTier
  turnCommitTier_dominates_cells
  turnCommitTier_admits_stateWrite
  FinalityGate
  advanceGate
  advanceGate_advances
)

export Obend.Consensus.Epistemic (
  byteListLt
  byteArrayLt
  byteListLt_irreflexive
  byteArrayLt_irreflexive
  byteListLt_asymmetric
  byteArrayLt_asymmetric
  VerifiableRace
  certCost
  certDigest
  certValid
  betterCert
  betterCert_irreflexive
  betterCert_asymmetric
  pickBest
  selectWinner
  pickBest_mem
  mem_filter
  winner_mem
  winner_is_valid
  selectWinner_nil
  selectWinner_all_invalid
  selectWinner_singleton_valid
  frontrunning_resistant_pair
  order_insensitive_pair
  EpistemicFrame
)

end Obend.Consensus
