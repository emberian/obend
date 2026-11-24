module
/-
# `Obend.Teeth.SemidirectGspTeeth` — Mutation Sensitivity Witnesses for `Obend.Vault.SemidirectGsp` & `Obend.Run.Fork`

Verifies that mutating any load-bearing causal-ancestry, bounded-escrow, MixT IFC, GSP tombstone GC,
semidirect merge, or per-cone settlement guard turns the corresponding universal soundness theorem
RED in the Lean kernel (`#tooth`).
-/
public import Obend.Tactic.Tooth
import all Obend.Vault.SemidirectGsp
import all Obend.Vault.Branch
import all Obend.Run.Fork

public section
end

namespace Obend.Teeth.SemidirectGspTeeth

open Obend.Vault.SemidirectGsp
open Obend.Run.Fork

-- 1. Dropping the `¬(op.stamp ≺c rev.stamp)` causal-ancestry guard in `revokeHitsHeader`
--    (reverting to `Branch.lean:81`'s flat tip check!) breaks `causally_prior_write_survives_revocation`.
#tooth Obend.Vault.SemidirectGsp.causally_prior_write_survives_revocation by mutation
  Obend.Vault.SemidirectGsp.revokeHitsHeader :=
    fun rev hdr => hdr.nullifiers.contains rev.nul

-- 2. Inverting the `¬(op.stamp ≺c rev.stamp)` guard in `revokeHitsHeader` breaks
--    `concurrent_write_annihilated` and `actRevoke_noop_iff`.
#tooth Obend.Vault.SemidirectGsp.concurrent_write_annihilated by mutation
  Obend.Vault.SemidirectGsp.revokeHitsHeader :=
    fun rev hdr => hdr.nullifiers.contains rev.nul && causallyLt hdr.stamp rev.stamp

-- 3. Disabling revocation filtering (`revokeHitsHeader := false`) breaks `actRevoke_noop_iff`.
#tooth Obend.Vault.SemidirectGsp.actRevoke_noop_iff by mutation
  Obend.Vault.SemidirectGsp.revokeHitsHeader := fun _ _ => false

-- 4. Skipping the semidirect kill-bit action `mergeKillBit` inside `semidirectMerge` breaks
--    `semidirectMerge_concurrent_revoke_annihilates`.
#tooth Obend.Vault.SemidirectGsp.semidirectMerge_concurrent_revoke_annihilates by mutation
  Obend.Vault.SemidirectGsp.mergeKillBit := fun ann _ => ann

-- 5. Dropping the bounded local debit guard (`spend ≤ slice.remaining`) in `canLocalDebit`
--    breaks `multi_locus_escrow_nonneg_and_conserved` (signed `globalBalanceInt ≥ 0` goes `< 0`!).
#tooth Obend.Vault.SemidirectGsp.multi_locus_escrow_nonneg_and_conserved by mutation
  Obend.Vault.SemidirectGsp.canLocalDebit := fun _ _ => true

-- 6. Bypassing MixT consistency-as-integrity checking (`checkMethodIfc := .ok ()`) breaks
--    `ifc_unendorsed_strong_noninterference`.
#tooth Obend.Vault.SemidirectGsp.ifc_unendorsed_strong_noninterference by mutation
  Obend.Vault.SemidirectGsp.checkMethodIfc := fun _ _ _ => .ok ()

-- 7. Dropping finalized tombstones into thin air instead of compacting into `SortedNullifierSet`
--    breaks `compactFinalizedTombstones_exact`.
#tooth Obend.Vault.SemidirectGsp.compactFinalizedTombstones_exact by mutation
  Obend.Vault.SemidirectGsp.compactFinalizedTombstones :=
    fun _ compacted _ => (compacted, RevokeSet.empty)

-- 8. Reverting per-cone `settleConeOutcome` to abort clean cones (`(false, s)`) breaks
--    `settleByConeBuckets_clean_head_commits`; forcing conflicted cones to commit (`(true, tentative)`)
--    breaks `settleByConeBuckets_conflict_rolls_back_cone`.
#tooth Obend.Run.Fork.settleByConeBuckets_clean_head_commits by mutation
  Obend.Run.Fork.settleConeOutcome := fun {_ _ _} s _ _ => (false, s)

#tooth Obend.Run.Fork.settleByConeBuckets_conflict_rolls_back_cone by mutation
  Obend.Run.Fork.settleConeOutcome := fun {_ _ _} _ tentative _ => (true, tentative)

end Obend.Teeth.SemidirectGspTeeth
