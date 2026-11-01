import Obend.Consensus.Simplex
import Obend.Consensus.Finality
import Obend.Consensus.Epistemic
import Obend.Fold.Collapse

open Obend.Consensus.Simplex
open Obend.Consensus.Finality
open Obend.Consensus.Epistemic
open Obend.Fold.Collapse

set_option autoImplicit false

/-! # Milestone 4 Axiom Hygiene Inspection -/

-- Feature 30: Simplex BFT Consensus
#print axioms honest_quorum_intersection
#print axioms qc_same_view_unique
#print axioms prefix_monotonic_of_ancestor
#print axioms prefix_length_le
#print axioms exponential_backoff_timing
#print axioms exponential_backoff_base

-- Feature 31: 4-Tier Finality Ladder
#print axioms FinalityTier.speculative_bot
#print axioms FinalityTier.collapsed_top
#print axioms admitsOp_mono
#print axioms promoteStep_sound
#print axioms reachable_no_downgrade
#print axioms downgrade_not_a_step
#print axioms collapsed_downgrade_not_a_step
#print axioms downgrade_unreachable
#print axioms collapsed_is_terminal
#print axioms joinTier_dominates
#print axioms turnCommitTier_dominates_cells
#print axioms turnCommitTier_admits_stateWrite
#print axioms FinalityGate.init_wf
#print axioms advanceGate_advances

-- Feature 32: Epistemic Consensus
#print axioms byteListLt_irreflexive
#print axioms byteArrayLt_irreflexive
#print axioms byteListLt_asymmetric
#print axioms byteArrayLt_asymmetric
#print axioms betterCert_irreflexive
#print axioms betterCert_asymmetric
#print axioms winner_mem
#print axioms winner_is_valid
#print axioms frontrunning_resistant_pair
#print axioms order_insensitive_pair
#print axioms EpistemicFrame.verified_world_independent
#print axioms EpistemicFrame.all_know_verified
#print axioms EpistemicFrame.honest_distKnows_verified
#print axioms EpistemicFrame.no_dist_knowledge_of_invalid

-- Feature 33: Merkle Fold & Collapse
#print axioms foldTrace_append
#print axioms foldTurns_append
#print axioms foldTrace_deterministic
#print axioms collapseRoot_congr
#print axioms collapseTrace_deterministic
#print axioms collapseTrace_semantic_determinism
#print axioms foldTrace_filter_empty
#print axioms collapseTrace_prune_empty
#print axioms collapseRoot_binds
