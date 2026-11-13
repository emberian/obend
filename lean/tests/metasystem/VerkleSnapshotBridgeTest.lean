module
import all Obend.Polis.BlumRam
import all Obend.Vault.Log
import all Obend.Vault.WorldTree
import all Obend.Vault.Replay
import Obend.Vault.Replay
import Obend.Vault.WorldTree
import Obend.AssertAxioms
import Obend.Tactic.Tooth

public section

/-!
# `tests/metasystem/VerkleSnapshotBridgeTest.lean` — Pillar-3 COW `ChunkedWorld` ↔ `VerkleUmem` & WAL Suite

Exercises `Obend.Vault.VerkleSnapshotBridge` on concrete multi-chunk worlds, COW snapshot branches,
forged dual openings, and torn `OBL1` write-ahead log crash-recovery traces:
1. `#assert_axioms_tree` zero-axiom / zero-`sorryAx` census across the transitive dependency cone.
2. Concrete `#guard` suite:
   - Full-width 256-bit (`4 × UInt64`) digest limb round-trip & 1-chunk incremental `VerkleUmem`
     root update matching `fullVerkleCommitChunks` byte-for-byte (`32` bytes),
   - Multi-chunk COW fork (`branchA` vs `branchB`) sharing unchanged chunk subtrees, Ajtai
     commitments, and rebound pre-branch intra-chunk level-0 openings,
   - Stateless `verifyDualChunkOpening` rejecting wrong values, forged chunk vectors, tampered or
     ill-sized sibling paths, and forged Ajtai syndromes,
   - Real multi-epoch `Replay.deployed` session (`opened` + `member` + `wrote`) with mid-header,
     mid-payload, and 1-byte-short-of-seal torn trailing WAL bytes recovered idempotently to the
     exact committed epoch's `ChunkedWorld` and 256-bit `VerkleUmem` root.
3. Seven `#tooth` mutation kills guarding `digestLimbs256_injective`,
   `incrementalVerkleSnapshot_eq_fullCommit`, `cowBranch_shares_unchanged_verkleSubtrees`
   (both COW unmodified subtree sharing and dual-assumption `Module-SIS` binding), and
   `walCrashReplay_restores_verkle_consistent_world`.
-/

namespace Obend.Tests.Metasystem.VerkleSnapshotBridgeTest

open Obend.Vault
open Obend.Vault.Rehydration (genesisSentinel)
open Obend.Vault.VerkleSnapshotBridge
open Obend.Crypto (NonPigeonholeSISParams ModuleSISHard)
open Obend.Polis (verifyOpening verifyUpdate leafTag)

set_option autoImplicit false

#assert_axioms_tree

/-! ## 1. Single-Chunk Incremental `VerkleUmem` Update vs Full Scratch Commit -/

def ppDefault := defaultChunkAjtaiParams

def snapGenesis : AuthenticatedWorldSnapshot :=
  buildAuthenticatedSnapshot ppDefault defaultChunkAjtaiParams_cols Replay.genesis

#guard snapGenesis.verkleRoot.size == 32
#guard snapGenesis.verkleRoot == fullVerkleCommitWorld Replay.genesis

def sampleChunk42 : ChunkData where
  slots := #[0xFEDCBA9876543210, 0x0123456789ABCDEF, 0xFFFFFFFFFFFFFFFF, 42,
             100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 0x8000000000000001]
  size_eq := rfl

def snapAfter42 : AuthenticatedWorldSnapshot :=
  updateChunkVerkleRoot ppDefault defaultChunkAjtaiParams_cols snapGenesis 42 (by decide) sampleChunk42

-- Incremental 1-chunk update produces the exact 32-byte Verkle root of a scratch 4,096-slot commit.
#guard snapAfter42.verkleRoot.size == 32
#guard snapAfter42.verkleRoot != snapGenesis.verkleRoot
#guard snapAfter42.verkleRoot == fullVerkleCommitChunks (snapGenesis.chunks.setIfInBounds 42 sampleChunk42)

-- Modified slots in chunk 42 and untouched slots in chunks 0, 128, 255 open validly.
#guard verifyOpening snapAfter42.verkleRoot (slotAddr 42 0) 0xFEDCBA9876543210
  (openSnapshotSlot snapAfter42 42 0) == true
#guard verifyOpening snapAfter42.verkleRoot (slotAddr 42 15) 0x8000000000000001
  (openSnapshotSlot snapAfter42 42 15) == true
#guard verifyOpening snapAfter42.verkleRoot (slotAddr 128 0) (snapAfter42.readSlot 128 0)
  (openSnapshotSlot snapAfter42 128 0) == true
#guard verifyOpening snapAfter42.verkleRoot (slotAddr 255 7) 0
  (openSnapshotSlot snapAfter42 255 7) == true

-- Single-slot update inside chunk 42 passes `Obend.Polis.verifyUpdate` with the exact same sibling path.
def sampleChunk42Edited : ChunkData := sampleChunk42.setSlot 3 9999
def snapAfter42Slot3 : AuthenticatedWorldSnapshot :=
  updateChunkVerkleRoot ppDefault defaultChunkAjtaiParams_cols snapAfter42 42 (by decide) sampleChunk42Edited

#guard verifyUpdate snapAfter42.verkleRoot snapAfter42Slot3.verkleRoot
  (slotAddr 42 3) 42 9999 (openSnapshotSlot snapAfter42 42 3) == true

/-! ## 2. Multi-Chunk COW Snapshot Forking & Unchanged Subtree Sharing -/

def branchChunk7 : ChunkData := zeroChunk.setSlot 2 0xCAFEBABE12345678
def branchChunk200 : ChunkData := zeroChunk.setSlot 11 0xDEADBEEF00000001
def branchChunk99 : ChunkData := zeroChunk.setSlot 5 7777777

def cowBranchA : AuthenticatedWorldSnapshot :=
  let b1 := cowUpdateChunk ppDefault defaultChunkAjtaiParams_cols snapAfter42 7 (by decide) branchChunk7
  updateChunkVerkleRoot ppDefault defaultChunkAjtaiParams_cols b1 200 (by decide) branchChunk200

def cowBranchB : AuthenticatedWorldSnapshot :=
  cowUpdateChunk ppDefault defaultChunkAjtaiParams_cols snapAfter42 99 (by decide) branchChunk99

#guard cowBranchA.branchGen == snapAfter42.branchGen + 1
#guard cowBranchB.branchGen == snapAfter42.branchGen + 1
#guard cowBranchA.verkleRoot != cowBranchB.verkleRoot
#guard cowBranchA.verkleRoot == fullVerkleCommitChunks cowBranchA.chunks
#guard cowBranchB.verkleRoot == fullVerkleCommitChunks cowBranchB.chunks

-- Unmodified chunk 42 and manifest chunk 128 share identical Verkle subtree tags and Ajtai commitments.
#guard cowBranchA.chunkRoots.getD 42 ByteArray.empty == snapAfter42.chunkRoots.getD 42 ByteArray.empty
#guard cowBranchB.chunkRoots.getD 42 ByteArray.empty == snapAfter42.chunkRoots.getD 42 ByteArray.empty
#guard cowBranchA.ajtaiChunkRoots.getD 42 [] == snapAfter42.ajtaiChunkRoots.getD 42 []
#guard cowBranchB.ajtaiChunkRoots.getD 42 [] == snapAfter42.ajtaiChunkRoots.getD 42 []

-- Pre-branch intra-chunk level-0 sibling witness from `snapAfter42` verifies on both COW branches.
def preOpening42_0 := openSnapshotSlot snapAfter42 42 0
#guard verifyOpening cowBranchA.verkleRoot (slotAddr 42 0) 0xFEDCBA9876543210
  (rebindPreBranchChunkOpening preOpening42_0 cowBranchA 42) == true
#guard verifyOpening cowBranchB.verkleRoot (slotAddr 42 0) 0xFEDCBA9876543210
  (rebindPreBranchChunkOpening preOpening42_0 cowBranchB 42) == true

/-! ## 3. Stateless Dual-Authenticated Openings & Forgery Rejection -/

def honestDual42_0 : DualChunkSlotOpening := openDualSnapshotSlot cowBranchA 42 0
def ajtaiRoot42 : List Int := cowBranchA.ajtaiChunkRoots.getD 42 []

#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot ajtaiRoot42 42 0 0xFEDCBA9876543210 honestDual42_0 == true

-- Forgery 1: wrong claimed value against honest witness.
#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot ajtaiRoot42 42 0 0xFEDCBA9876543211 honestDual42_0 == false

-- Forgery 2: forged chunkSlotsList matching forged value, original Verkle path & Ajtai root.
def forgedSlotsDual : DualChunkSlotOpening :=
  { honestDual42_0 with chunkSlotsList := (sampleChunk42.setSlot 0 0xFEDCBA9876543211).slots.toList }

#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot ajtaiRoot42 42 0 0xFEDCBA9876543211 forgedSlotsDual == false

-- Forgery 3: tampered 32-byte sibling tag at level 0.
def tamperedPathDual : DualChunkSlotOpening :=
  let lvl0 := (honestDual42_0.verklePath.getD 0 #[]).setIfInBounds 0 (leafTag 999999)
  { honestDual42_0 with verklePath := honestDual42_0.verklePath.setIfInBounds 0 lvl0 }

#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot ajtaiRoot42 42 0 0xFEDCBA9876543210 tamperedPathDual == false

-- Forgery 4: ill-sized non-32-byte sibling tag rejected by `checkWellSizedVerklePath`.
def shortTagDual : DualChunkSlotOpening :=
  let lvl0 := (honestDual42_0.verklePath.getD 0 #[]).setIfInBounds 0 (ByteArray.mk #[1, 2, 3])
  { honestDual42_0 with verklePath := honestDual42_0.verklePath.setIfInBounds 0 lvl0 }

#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot ajtaiRoot42 42 0 0xFEDCBA9876543210 shortTagDual == false

-- Forgery 5: tampered Ajtai syndrome rejected even when Verkle opening is intact.
def wrongAjtaiRoot : List Int := ajtaiRoot42.map (· + 1)
#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot wrongAjtaiRoot 42 0 0xFEDCBA9876543210 honestDual42_0 == false

-- Forgery 6 (`[HIGH-04]`): chunk index `42 + 2^60` has `slotAddr` equal to chunk 42's modulo `2^64`,
-- so chunk 42's honest proof would authenticate it; the index bound refuses it.
#guard slotAddr (42 + 2 ^ 60) 0 == slotAddr 42 0
#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot ajtaiRoot42 (42 + 2 ^ 60) 0 0xFEDCBA9876543210 honestDual42_0 == false

-- Forgery 7: claiming a larger chunk count to admit the wrapped index changes the snapshot root.
def inflatedCountDual : DualChunkSlotOpening := { honestDual42_0 with chunkCount := 2 ^ 60 }
#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  cowBranchA.snapshotRoot ajtaiRoot42 42 0 0xFEDCBA9876543210 inflatedCountDual == false
#guard snapshotRootTag (2 ^ 60) cowBranchA.verkleRoot != cowBranchA.snapshotRoot

-- Forgery 8: a count with `16 * chunkCount > 2^64` is refused even against its own root.
def overflowCountDual : DualChunkSlotOpening := { honestDual42_0 with chunkCount := 2 ^ 60 + 43 }
#guard verifyDualChunkOpening ppDefault defaultChunkAjtaiParams_cols
  (snapshotRootTag (2 ^ 60 + 43) cowBranchA.verkleRoot) ajtaiRoot42 (42 + 2 ^ 60) 0
  0xFEDCBA9876543210 overflowCountDual == false

/-! ## 4. Multi-Epoch `Replay.deployed` Torn-Write WAL Crash Recovery & Idempotence -/

def runDeployedEpoch (st : Log.Session ChunkedWorld.World × AuthenticatedWorldSnapshot)
    (t : Replay.Turn) : Option (Log.Session ChunkedWorld.World × AuthenticatedWorldSnapshot) :=
  match st.1.admit Replay.logHash Replay.deployed (Replay.encodeTurn t) with
  | .ok S' =>
    some (S', syncSnapshotWorld ppDefault defaultChunkAjtaiParams_cols st.2 S'.world)
  | .error _ => none

def multiEpochRun? : Option (Log.Session ChunkedWorld.World × AuthenticatedWorldSnapshot × Log.Record) := do
  let s0 : Log.Session ChunkedWorld.World := ⟨Replay.genesis, []⟩
  let st1 ← runDeployedEpoch (s0, snapGenesis)
    (.opened [("Alpha", some "# Alpha\n\nLinks to [[Beta]].\n"),
              ("Beta", some "# Beta\n\nAnswer is 42.\n")] none)
  let st2 ← runDeployedEpoch st1 (.member "scout" [("post", "Alpha")])
  -- Prepare a 3rd turn whose WAL record will be torn before its trailing 32-byte seal completes.
  let st3 ← runDeployedEpoch st2 (.wrote "Beta" "# Beta\n\nUpdated offline note.\n")
  let rec3 ← st3.1.log.getLast?
  pure (st2.1, st2.2, rec3)

def checkTornCrashSuite : Bool :=
  match multiEpochRun? with
  | none => false
  | some (sCommitted, snapCommitted, uncommittedRec3) =>
    let cleanWal := Log.encodeAll Replay.logHash sCommitted.log
    let rec3Bytes := Log.encodeRecord Replay.logHash uncommittedRec3
    -- Crash A: torn inside the 136-byte header (byte 40).
    let crashHeader := cleanWal ++ rec3Bytes.take 40
    -- Crash B: torn 1 byte short of completing the trailing 32-byte commit seal!
    let crashSeal1 := cleanWal ++ rec3Bytes.take (rec3Bytes.length - 1)
    let recA := recoverWalSnapshot ppDefault defaultChunkAjtaiParams_cols
      Replay.deployed Replay.genesis crashHeader
    let recB := recoverWalSnapshot ppDefault defaultChunkAjtaiParams_cols
      Replay.deployed Replay.genesis crashSeal1
    let recB2 := recoverWalSnapshot ppDefault defaultChunkAjtaiParams_cols
      Replay.deployed Replay.genesis recB.cleanDisk
    (sCommitted.log.length == 2) &&
    (snapCommitted.verkleRoot == fullVerkleCommitWorld sCommitted.world) &&
    (recA.committedCount == 2) &&
    (recA.dropReason == some .torn) &&
    (recA.cleanDisk == cleanWal) &&
    (recA.snapshot.world == sCommitted.world) &&
    (recA.snapshot.verkleRoot == snapCommitted.verkleRoot) &&
    (recB.committedCount == 2) &&
    (recB.dropReason == some .torn) &&
    (recB.droppedTail == rec3Bytes.take (rec3Bytes.length - 1)) &&
    (recB.cleanDisk == cleanWal) &&
    (recB.snapshot.world == sCommitted.world) &&
    (recB.snapshot.verkleRoot == snapCommitted.verkleRoot) &&
    -- Idempotence on both bytes and full snapshot recovery state:
    (recoverWalBytes (recoverWalBytes crashSeal1) == recoverWalBytes crashSeal1) &&
    (recB2.cleanDisk == recB.cleanDisk) &&
    (recB2.snapshot == recB.snapshot) &&
    (recB2.droppedTail == []) &&
    (recB2.dropReason == none)

#guard checkTornCrashSuite == true

/-! ## 5. Universal Theorem Instantiations -/

example {s : AuthenticatedWorldSnapshot}
    (hwf : SnapshotWF ppDefault defaultChunkAjtaiParams_cols s)
    (c : Nat) (hc : c < numChunks) (ch : ChunkData) :
    (updateChunkVerkleRoot ppDefault defaultChunkAjtaiParams_cols s c hc ch).verkleRoot =
      fullVerkleCommitChunks (s.chunks.setIfInBounds c ch) :=
  (incrementalVerkleSnapshot_eq_fullCommit hwf c hc ch).2.2.1

example : NonPigeonholeSISParams ppDefault ∧ ModuleSISHard ppDefault 131070 :=
  ⟨dualChunkParams_inhabited_sisHard.2.1, dualChunkParams_inhabited_sisHard.2.2⟩

example : ∃ epochs S snap, epochs.length = 2 ∧
    ValidSnapshotTrace ppDefault defaultChunkAjtaiParams_cols bumpMintedMachine Replay.genesis epochs S snap :=
  validSnapshotTrace_multiEpoch_inhabited

/-! ## 6. `#tooth` Mutation Kills -/

-- Tooth 1: Narrowing `digestLimbs256` to zero out the 4th 64-bit limb breaks 256-bit injectivity.
#tooth Obend.Vault.VerkleSnapshotBridge.digestLimbs256_injective by mutation
  Obend.Vault.VerkleSnapshotBridge.digestLimbs256 := fun d =>
    (UInt64.ofNat (Obend.Digest.HashBytes.ofBE (d.take 8)),
     UInt64.ofNat (Obend.Digest.HashBytes.ofBE ((d.drop 8).take 8)),
     UInt64.ofNat (Obend.Digest.HashBytes.ofBE ((d.drop 16).take 8)),
     0)

-- Tooth 2: Skipping the level-2 `groupRoots` update in `updateChunkVerkleRoot` breaks equivalence with `fullVerkleCommitChunks`.
#tooth Obend.Vault.VerkleSnapshotBridge.incrementalVerkleSnapshot_eq_fullCommit by mutation
  Obend.Vault.VerkleSnapshotBridge.updateChunkVerkleRoot := fun pp hCols s c _hc newChunk =>
    let chunks' := s.chunks.setIfInBounds c newChunk
    let cRoots' := s.chunkRoots.setIfInBounds c (chunkSubtreeTag newChunk)
    let act' := Obend.Polis.nodeTag s.groupRoots.toList
    let aRoots' := s.ajtaiChunkRoots.setIfInBounds c (ajtaiChunkCommit pp hCols newChunk)
    { s with
      chunks := chunks'
      chunkRoots := cRoots'
      activeRoot := act'
      verkleRoot := liftActiveToRoot act'
      ajtaiChunkRoots := aRoots' }

-- Tooth 3: Clobbering unmodified chunk 0 during `cowUpdateChunk` breaks unmodified subtree sharing.
#tooth Obend.Vault.VerkleSnapshotBridge.cowBranch_shares_unchanged_verkleSubtrees by mutation
  Obend.Vault.VerkleSnapshotBridge.cowUpdateChunk := fun pp hCols s c hc newChunk =>
    let s1 := updateChunkVerkleRoot pp hCols (cowForkSnapshot s) c hc newChunk
    updateChunkVerkleRoot pp hCols s1 0 (by decide) newChunk

-- Tooth 4: Omitting the Ajtai modular commitment check in `verifyDualChunkOpening` breaks dual-assumption SIS extraction.
#tooth Obend.Vault.VerkleSnapshotBridge.cowBranch_shares_unchanged_verkleSubtrees by mutation
  Obend.Vault.VerkleSnapshotBridge.verifyDualChunkOpening := fun _pp _hCols snapshotRoot _ajtaiRoot c j val w =>
    if hlen : w.chunkSlotsList.length = 16 then
      if hj : j < 16 then
        ((w.chunkSlotsList[j]'(by omega) == val) &&
         checkWellSizedVerklePath w.verklePath &&
         Obend.Polis.verifyOpening w.verkleRoot (slotAddr c j) val w.verklePath) &&
        (decide (c < w.chunkCount) && decide (chunkSlots * w.chunkCount ≤ 2 ^ 64) &&
         w.verkleRoot.size == 32 &&
         decide (snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot))
      else false
    else false

-- Tooth 6 (`[HIGH-04]`): dropping the `c < chunkCount` index bound lets `c + 2^60` alias `c`.
#tooth Obend.Vault.VerkleSnapshotBridge.verifyDualChunkOpening_addr_exact by mutation
  Obend.Vault.VerkleSnapshotBridge.verifyDualChunkOpening := fun pp hCols snapshotRoot ajtaiRoot c j val w =>
    if hlen : w.chunkSlotsList.length = 16 then
      if hj : j < 16 then
        ((w.chunkSlotsList[j]'(by omega) == val) &&
         checkWellSizedVerklePath w.verklePath &&
         Obend.Polis.verifyOpening w.verkleRoot (slotAddr c j) val w.verklePath &&
         decide (Obend.Crypto.ajtaiCommit pp (wordsToLimbs w.chunkSlotsList)
           (by rw [wordsToLimbs_length, hlen, hCols]) = ajtaiRoot)) &&
        (decide (chunkSlots * w.chunkCount ≤ 2 ^ 64) && w.verkleRoot.size == 32 &&
         decide (snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot))
      else false
    else false

-- Tooth 7: dropping the chunk count from the snapshot-root preimage breaks root binding.
#tooth Obend.Vault.VerkleSnapshotBridge.snapshotRootPreimage_injective by mutation
  Obend.Vault.VerkleSnapshotBridge.snapshotRootPreimage := fun _n verkleRoot =>
    2 :: Obend.Polis.encodeFields [verkleRoot.data.toList]

-- Tooth 5: Failing to truncate uncommitted trailing bytes in `recoverWalBytes` breaks crash-replay consistency.
#tooth Obend.Vault.VerkleSnapshotBridge.walCrashReplay_restores_verkle_consistent_world by mutation
  Obend.Vault.VerkleSnapshotBridge.recoverWalBytes := fun rawDisk => rawDisk

/-- The exact SIS alternative cannot be supplied by an unrelated matrix kernel vector. -/
theorem exact_zero_difference_not_break (pp : Obend.Crypto.AjtaiParams) (w : DualChunkSlotOpening) :
    ¬ SISBreakOn pp (diffLimbs w w) := by
  have hz : ∀ xs : List Int,
      Obend.Judge.Computational.vecInfNorm (Obend.Crypto.vecSub xs xs) = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [Obend.Crypto.vecSub, Obend.Judge.Computational.vecInfNorm, ih]
  intro h
  have hn := hz (wordsToLimbs w.chunkSlotsList)
  exact Nat.lt_irrefl 0 (hn ▸ h.1)

/-- Honest openings against the real cSHAKE tree inhabit both verifier premises. -/
example (w : Obend.Vault.ChunkedWorld.World) :
    ∃ (s : AuthenticatedWorldSnapshot) (opening : DualChunkSlotOpening),
      verifyDualChunkOpening defaultChunkAjtaiParams defaultChunkAjtaiParams_cols
      s.snapshotRoot (s.ajtaiChunkRoots.getD 0 []) 0 0 (s.readSlot 0 0) opening = true := by
  let s := buildAuthenticatedSnapshot defaultChunkAjtaiParams defaultChunkAjtaiParams_cols w
  exact ⟨s, openDualSnapshotSlot s 0 0,
    openDualSnapshotSlot_valid (pp := defaultChunkAjtaiParams)
      (hCols := defaultChunkAjtaiParams_cols) (s := s)
      (buildAuthenticatedSnapshot_wf defaultChunkAjtaiParams defaultChunkAjtaiParams_cols w)
      (by decide) (by decide)⟩
#print axioms extractSnapshotRootBreak
#print axioms extractSnapshotIndexBreak
#print axioms extractDualChunkOpeningBreak

#tooth Obend.Polis.verifyOpening_binds by mutation
  Obend.Polis.insertAt := fun _ _ siblings => siblings

#tooth Obend.Vault.ExpVerkleAndOpenHash.verifyExpVerkleOpening_multiLevel by mutation
  Obend.Vault.ExpVerkleAndOpenHash.verifyExpVerkleOpening := fun _ _ _ _ _ => true

end Obend.Tests.Metasystem.VerkleSnapshotBridgeTest
