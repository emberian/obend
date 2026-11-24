/-
# `Obend.Teeth.ZkCapFoldTeeth` — Mutation-Sensitivity & Axiom-Hygiene Suite for `Obend.Polis.ZkCapFold`

Verifies via `#tooth` kernel replay and `#assert_axioms_tree` whole-cone audit that:
1. Weakening the sorted-gap lower bound `lo < x` to `lo ≤ x` (`checkStrictGap256`) is rejected
   by the stored proofs of `not_mem_revoked_iff_in_unique_gap`,
   `zkCapFold_epoch_decoupled_iff_foldChain_at_presentation`,
   `retroactive_ancestor_revocation_kills_pre_folded_cone`, and
   `retroactive_ancestor_revocation_forces_refresh_false`.
2. Skipping `subMask` capability attenuation in `foldHopsEpochFree` is rejected by
   `foldChainEpochFree_attenuation_monotone` and
   `zkCapFold_epoch_decoupled_iff_foldChain_at_presentation`.
3. Dropping `chanNul256 b.channel` from `collectHopNullifiers256` or omitting salted slot padding in
   `padNullifiersList` is rejected by `zkCapFold_epoch_decoupled_iff_foldChain_at_presentation`,
   `retroactive_channel_revocation_kills_pre_folded_chain`, and `padded_nullifier_arity_depth_invariant`.
4. Skipping live epoch-floor or `RevokedGapRoot256` epoch binding (`checkLiveEpochBound`) is rejected
   by `verifyEpochPresentation_enforces_epoch_binding` and
   `zkCapFold_epoch_decoupled_iff_foldChain_at_presentation`.
5. Dropping `epoch`, `secretSalt`, or `turnId` from `presNulPreimage` is rejected by
   `presNul_binds_or_collides`.
6. Whole-tree axiom hygiene (`#assert_axioms_tree`): `0 sorryAx`, `0` custom axioms, `0 native_decide`.
-/
import Obend.Polis.ZkCapFold
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Teeth.ZkCapFoldTeeth

open Obend.Polis
open Obend.Polis.ZkCapFold
open Obend.Crypto
open Obend.Digest.HashBytes

set_option autoImplicit false

-- 1. Mutating strict gap `lo < x && x < hi` to weak `lo ≤ x && x < hi` breaks gap disjointness
--    and retroactive cone revocation (allowing a revoked `x = r_j` to verify!).
#tooth not_mem_revoked_iff_in_unique_gap by mutation
  checkStrictGap256 := fun lo x hi => decide (lo ≤ x) && decide (x < hi)

#tooth zkCapFold_epoch_decoupled_iff_foldChain_at_presentation by mutation
  checkStrictGap256 := fun lo x hi => decide (lo ≤ x) && decide (x < hi)

#tooth retroactive_ancestor_revocation_kills_pre_folded_cone by mutation
  checkStrictGap256 := fun lo x hi => decide (lo ≤ x) && decide (x < hi)

#tooth retroactive_ancestor_revocation_forces_refresh_false by mutation
  checkStrictGap256 := fun lo x hi => decide (lo ≤ x) && decide (x < hi)

-- 2. Skipping `subMask` rights attenuation in `foldHopsEpochFree` breaks monotonic attenuation & soundness!
private def foldHopsSkipAttenuationPlant {S : HopSigScheme} (staticEnv : Nat → KleenePred3) :
    (UInt64 × Nat × ResidualCaveat × ByteArray × ByteArray) → List (SignedHop S) →
    Option (UInt64 × Nat × ResidualCaveat × ByteArray × ByteArray)
  | state, [] => some state
  | (_, curFloor, curRes, curHolder, curLin), sh :: rest =>
    if S.verify curHolder (hopSignPreimage curLin sh.epochFloor sh.block) sh.hopSig then
      let nextFloor := Nat.max curFloor sh.epochFloor
      let nextRes := conjoinResidual staticEnv curRes (pevalCaveat staticEnv sh.block.caveat)
      let nextLin := stepLineage curLin sh.block
      foldHopsSkipAttenuationPlant staticEnv
        (sh.block.rights, nextFloor, nextRes, sh.block.holder, nextLin) rest
    else none

#tooth foldChainEpochFree_attenuation_monotone by mutation
  foldHopsEpochFree := @foldHopsSkipAttenuationPlant

#tooth zkCapFold_epoch_decoupled_iff_foldChain_at_presentation by mutation
  foldHopsEpochFree := @foldHopsSkipAttenuationPlant

-- 3. Nullifier slot binding: dropping `chanNul256 b.channel` or omitting salted slot padding!
private def collectHopNullifiersDropChannelPlant : ByteArray → List Block → List (BitVec 256)
  | _, [] => []
  | prevLin, b :: rest =>
    let nextLin := stepLineage prevLin b
    credNul256 nextLin :: credNul256 nextLin :: collectHopNullifiersDropChannelPlant nextLin rest

#tooth zkCapFold_epoch_decoupled_iff_foldChain_at_presentation by mutation
  collectHopNullifiers256 := collectHopNullifiersDropChannelPlant

#tooth retroactive_channel_revocation_kills_pre_folded_chain by mutation
  collectHopNullifiers256 := collectHopNullifiersDropChannelPlant

#tooth padded_nullifier_arity_depth_invariant by mutation
  padNullifiersList := fun _ _ realNuls => realNuls

-- 4. Epoch binding: skipping `epochFloor ≤ liveEpoch` and `gapRootEpoch == liveEpoch`!
#tooth verifyEpochPresentation_enforces_epoch_binding by mutation
  checkLiveEpochBound := fun _ _ _ => true

#tooth zkCapFold_epoch_decoupled_iff_foldChain_at_presentation by mutation
  checkLiveEpochBound := fun _ _ _ => true

-- 5. Presentation-nullifier binding: dropping `epoch`, `secretSalt`, and `turnId` in `presNulPreimage`!
#tooth presNul_binds_or_collides by mutation
  presNulPreimage := fun _ _ _ lineage => encodeFrameList [] [] lineage.data.toList

-- 6. Whole-cone axiom hygiene (`0 sorryAx`, `0` custom axioms, `0 native_decide`).
#assert_axioms_tree

end Obend.Teeth.ZkCapFoldTeeth
