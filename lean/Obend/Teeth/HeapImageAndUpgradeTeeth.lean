/-
# Obend.Teeth.HeapImageAndUpgradeTeeth — Mutation-Sensitivity & Choice-Free Axiom Audit

Tier-2 legacy leaf verifying that planted bugs in `Obend.Core.HeapImage` and
`Obend.Repair.UpgradeEnvelope` cause the Lean 4 kernel to reject the stored soundness proofs, and
confirming `0 Classical.choice`, `0 sorry`, `0 axiom`, and `0 native_decide` across both modules:

1. **Dropping a `Frame` field (`environment`) in `encodeHeapImage` (`encFrameSpec`)** rejects
   `decodeHeapImage_encodeHeapImage` and `rehydrate_resume_steps_eq`.
2. **Mutating `Consistent` preservation in `putr` (`deltaPutr` & `peerSplitPutr`)** rejects
   `deltaToSymmetric_putr_sound` and `peerSplitLens_putr_sound`.
3. **Skipping the lazy per-bucket epoch check (`needsBucketUpgrade := false`)** rejects
   `lazyUpgrade_obs_eq_eagerUpgrade`.
4. **Bypassing the `Genealogy.succeed` + epoch gate (`admitUpgradeEnvelope := true`)** rejects
   `relinkLogAcrossEpochs_sound`.
5. **Forgetting heap-address relocation in `liftContinuationControl`** rejects
   `liftYieldedContinuation_commutes`.
6. **`#assert_choice_free` + `#assert_axioms_tree`**: verifies zero `Classical.choice` in extractors
   and core theorems, and zero `sorryAx` or custom axioms in the transitive closure.
-/
import Obend.Core.HeapImage
import Obend.Repair.UpgradeEnvelope
import Obend.Tactic.Tooth
import Obend.AssertAxioms

open Lean Elab Command
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.HeapImage
open Obend.Repair

elab "#assert_choice_free " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let axs ← liftCoreM <| collectAxioms name
  if axs.contains ``Classical.choice then
    throwError "{name} depends on Classical.choice: {axs.toList}"
  if axs.contains ``sorryAx then
    throwError "{name} depends on sorryAx: {axs.toList}"

-- 1a. Dropping the `environment` field of `Frame.argument` in `encFrameSpec` turns round-trip red!
#tooth decodeHeapImage_encodeHeapImage by mutation encFrameSpec := fun fr =>
  match fr with
  | .argument t _ => (0 : UInt8) :: (encTermSpec t ++ encAddrsSpec [])
  | .update addr => (1 : UInt8) :: encVarNat addr
  | .field name => (2 : UInt8) :: encStrSpec name
  | .reflect => [3]
  | .metadata => [4]
  | .project => [5]
  | .extend fs env => (6 : UInt8) :: (encFieldsSpec fs ++ encAddrsSpec env)
  | .condition z s env => (7 : UInt8) :: (encTermSpec z ++ encTermSpec s ++ encAddrsSpec env)
  | .binaryLeft p r env => (8 : UInt8) :: primTag p :: (encTermSpec r ++ encAddrsSpec env)
  | .binaryRight p l => (9 : UInt8) :: primTag p :: encValueSpec l
  | .case arms env => (10 : UInt8) :: (encFieldsSpec arms ++ encAddrsSpec env)
  | .ifBool wt wf env => (11 : UInt8) :: (encTermSpec wt ++ encTermSpec wf ++ encAddrsSpec env)
  | .split names fn env => (12 : UInt8) :: (encNamesSpec names ++ encTermSpec fn ++ encAddrsSpec env)

-- 1b. Same dropped `Frame` field turns multi-yield persisted session equivalence red!
#tooth rehydrate_resume_steps_eq by mutation encFrameSpec := fun fr =>
  match fr with
  | .argument t _ => (0 : UInt8) :: (encTermSpec t ++ encAddrsSpec [])
  | .update addr => (1 : UInt8) :: encVarNat addr
  | .field name => (2 : UInt8) :: encStrSpec name
  | .reflect => [3]
  | .metadata => [4]
  | .project => [5]
  | .extend fs env => (6 : UInt8) :: (encFieldsSpec fs ++ encAddrsSpec env)
  | .condition z s env => (7 : UInt8) :: (encTermSpec z ++ encTermSpec s ++ encAddrsSpec env)
  | .binaryLeft p r env => (8 : UInt8) :: primTag p :: (encTermSpec r ++ encAddrsSpec env)
  | .binaryRight p l => (9 : UInt8) :: primTag p :: encValueSpec l
  | .case arms env => (10 : UInt8) :: (encFieldsSpec arms ++ encAddrsSpec env)
  | .ifBool wt wf env => (11 : UInt8) :: (encTermSpec wt ++ encTermSpec wf ++ encAddrsSpec env)
  | .split names fn env => (12 : UInt8) :: (encNamesSpec names ++ encTermSpec fn ++ encAddrsSpec env)

-- 2a. Failing to advance the complement `c` in `deltaPutr` violates `Consistent` and turns red!
#tooth deltaToSymmetric_putr_sound by mutation deltaPutr := fun L e₁ c =>
  match e₁ with
  | none => (none, c)
  | some s' => (some (L.get s'), c)

-- 2b. Failing to update the peer complement in `peerSplitPutr` violates `Consistent` and turns red!
#tooth peerSplitLens_putr_sound by mutation peerSplitPutr := fun e₁ c =>
  (⟨e₁.deltaBalance, none⟩, c)

-- 3. Skipping the lazy per-bucket epoch check (`needsBucketUpgrade := false`) turns Thor M1 red!
#tooth lazyUpgrade_obs_eq_eagerUpgrade by mutation needsBucketUpgrade := fun _ _ => false

-- 4. Bypassing `admitUpgradeEnvelope` (`Genealogy.succeed` + epoch monotonicity) turns log relinking red!
#tooth relinkLogAcrossEpochs_sound by mutation admitUpgradeEnvelope := fun _ _ _ => true

-- 5. Skipping address relocation on `Control.yielded` in `liftContinuationControl` turns lifting red!
#tooth liftYieldedContinuation_commutes by mutation liftContinuationControl := fun _ ctrl => ctrl

-- 5b. Dropping `Frame` emission in the `ByteArray` writer `pushFrame` turns round-trip red!
#tooth decodeHeapImage_encodeHeapImage by mutation pushFrame := fun out _ => out

-- 6a. End-to-end two-yield `Array`-allocating `perform 10 + perform 20` persisted session witness:
example :
    ∃ finalState,
      runPersistedSession ⟨16, 16⟩ (initial twoYieldSumTerm)
        [⟨8, .nat 19⟩, ⟨8, .nat 23⟩, ⟨8, .nat 0⟩] =
        some ([0, 1], .finished (.natural 42) finalState) := by
  rw [rehydrate_resume_steps_eq]
  exact ⟨_, rfl⟩

-- 6b. End-to-end multi-epoch `Array` `LazyBucketStore` execution witness (`[11, 37, 33]`):
example :
    let mig : EpochMigrator Nat := ⟨fun e v => v + (e + 1) * 10⟩
    let init : LazyBucketStore Nat := ⟨0, #[⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩]⟩
    let turns : List (BucketStoreTurn Nat Nat) := [
      .upgradeEpoch, .read 0 id, .write 1 (· + 5), .upgradeEpoch, .read 1 id, .read 2 id
    ]
    (runLazyStoreTrace mig init turns).2 = [11, 37, 33] ∧
    (runEagerStoreTrace mig init turns).2 = [11, 37, 33] := by
  have hLazy : (runLazyStoreTrace ⟨fun e v => v + (e + 1) * 10⟩
      ⟨0, #[⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩]⟩
      [.upgradeEpoch, .read 0 id, .write 1 (· + 5), .upgradeEpoch, .read 1 id, .read 2 id]).2 =
      [11, 37, 33] := rfl
  exact ⟨hLazy, lazyBucketStore_multiEpoch_inhabited.1.symm.trans hLazy⟩

-- 7. Zero `Classical.choice` & zero `sorryAx` verification across Extractors and Apex Theorems:
-- (Note: `Core.Machine.stepRaw` in `Core/Machine.lean` derives `DecidableEq Term` via Lean's
-- `String.decEq`, whereas every `HeapImage` and `UpgradeEnvelope` extractor, codec, CID, lens,
-- lazy bucket store, and epoch log relinking theorem below is 100% `Classical.choice`-free.)
#assert_choice_free encodeHeapImage
#assert_choice_free decodeHeapImage
#assert_choice_free decodeHeapImageExec
#assert_choice_free heapImageCid
#assert_choice_free checkpointYielded
#assert_choice_free rehydrateAndResume
#assert_choice_free decodeHeapImage_encodeHeapImage
#assert_choice_free encodeHeapImage_of_decodeHeapImage
#assert_choice_free encodeHeapImage_injective
#assert_choice_free heapImageCid_binds_or_collides
#assert_choice_free heapImageCid_binds_or_extract_collision
#assert_choice_free liftContinuationState
#assert_choice_free upgradePersistedHeapImage
#assert_choice_free stepLazyStore
#assert_choice_free flushLazyBuckets
#assert_choice_free admitUpgradeEnvelope
#assert_choice_free deltaToSymmetric_putr_sound
#assert_choice_free peerSplitLens_putr_sound
#assert_choice_free lazyUpgrade_obs_eq_eagerUpgrade
#assert_choice_free relinkLogAcrossEpochs_sound
#assert_choice_free runMultiEpochTrace_floors

#assert_axioms_tree
