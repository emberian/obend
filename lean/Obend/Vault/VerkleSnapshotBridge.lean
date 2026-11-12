module
/-
# Obend.Vault.VerkleSnapshotBridge — COW `ChunkedWorld` ↔ `VerkleUmem` & Crash-Safe WAL Spine

Welds `Vault.ChunkedWorld` chunk tables to `Polis.VerkleUmem` (16-ary `cSHAKE256` tree, stateless
openings), `Crypto.DualSpine` (Ajtai `Module-SIS` chunk commitments) and the `OBL1` WAL:
1. `digestLimbs256_injective`: lossless `4 × UInt64` digests across 256 chunks of 16 slots.
2. `incrementalVerkleSnapshot_eq_fullCommit`: a one-chunk update rehashes $O(\log K)$ nodes and
   matches `fullVerkleCommitChunks` and the $2^{64}$-key `ExtRam` specification.
3. `cowBranch_shares_unchanged_verkleSubtrees`: COW forks share untouched subtrees; dual openings
   bind up to `BoundedCollision treeHash 529` and `ModuleSISHard pp 131070` (`PSum` extractor).
4. `verifyDualChunkOpening_addr_exact`, `extractSnapshotIndexBreak`: the snapshot root frames the
   chunk count and openings check `c < chunkCount`, so no index aliases another modulo `2^64`.
5. `walCrashReplay_restores_verkle_consistent_world`: truncating a torn WAL tail and replaying is
   idempotent and restores the world and its root across multi-epoch `ValidSnapshotTrace`s.
-/
public import Obend.Vault.ChunkedWorld
public import Obend.Vault.Replay
public import Obend.Vault.SegmentLog
public import Obend.Polis.VerkleUmem
public import Obend.Crypto.DualSpine

public section

namespace Obend.Vault.VerkleSnapshotBridge

open Obend.Digest.HashBytes (Hash be ofBE ofBE_lt)
open Obend.Judge.Computational (HashCollisionWitness SISShortVecWitness)
open Obend.Crypto (AjtaiParams NonPigeonholeSISParams ModuleSISHard BoundedCollision
  cshake32ByteArray cshake32ByteArray_size encodeListField leb128 Short ShortNormBound
  ajtaiCommit extractShortDiffSISWitness inhabitedAjtaiParams inhabitedAjtaiParams_sisHard)
open Obend.Polis (ExtRam treeCustomization treeHash tagOf leafPreimage nodePreimage
  leafTag nodeTag nibbleAt insertAt insertAt_inj climbStep climb verifyOpening
  encodeFields encodeFields_injective map_toList_injective)
open Obend.Vault
open Obend.Vault.Rehydration (genesisSentinel)

set_option autoImplicit false

/-! ## 1. Dimensions, Full-Width 256-Bit Digest Limbs & Chunk Carriers -/

/-- Number of persistent COW chunks ($K = 16^2 = 256$). -/
@[expose] def numChunks : Nat := 256
/-- Number of 64-bit `UInt64` slots per chunk ($B = 16$). -/
@[expose] def chunkSlots : Nat := 16
/-- Number of chunk groups at level 2 (`256 / 16 = 16`). -/
def numGroups : Nat := 16
/-- Total materialized leaf slots across all chunks ($N = K \cdot B = 4{,}096$). -/
@[expose] def totalSlots : Nat := 4096
/-- Maximum `VerkleUmem` preimage byte length hashed by any well-sized opening (`1 + 16 * 33 = 529`). -/
@[expose] def verkleMaxPreimageBytes : Nat := 529

/-- One fixed-width chunk of `B = 16` 64-bit `UInt64` slots. -/
structure ChunkData where
  slots : Array UInt64
  size_eq : slots.size = chunkSlots
  deriving DecidableEq

/-- All-zero 16-slot chunk. -/
def zeroChunk : ChunkData := ⟨Array.replicate chunkSlots 0, by simp [chunkSlots]⟩
/-- Read slot `j < 16` from `chunk` (`0` out of range). -/
def ChunkData.getSlot (chunk : ChunkData) (j : Nat) : UInt64 := chunk.slots.getD j 0
/-- Return an updated copy of `chunk` with slot `j` set to `v`. -/
def ChunkData.setSlot (chunk : ChunkData) (j : Nat) (v : UInt64) : ChunkData :=
  ⟨chunk.slots.setIfInBounds j v, by simp [chunk.size_eq]⟩
/-- Map `(chunkIdx, slotIdx)` (`c < 256`, `j < 16`) to its 64-bit `VerkleUmem` key `16 * c + j`. -/
@[expose] def slotAddr (c j : Nat) : UInt64 := UInt64.ofNat (c * chunkSlots + j)

/-- `slotAddr` is exact (no `2^64` wraparound) whenever `c < n` for a chunk count `16 * n ≤ 2^64`. -/
theorem slotAddr_toNat_of_bound {c j n : Nat} (hc : c < n) (hn : chunkSlots * n ≤ 2 ^ 64)
    (hj : j < chunkSlots) : (slotAddr c j).toNat = c * chunkSlots + j := by
  unfold slotAddr chunkSlots at *; rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
theorem slotAddr_toNat {c j : Nat} (hc : c < numChunks) (hj : j < chunkSlots) :
    (slotAddr c j).toNat = c * chunkSlots + j := slotAddr_toNat_of_bound hc (by decide) hj
private theorem foldl_be_inj : ∀ (xs ys : List UInt8) (a₁ a₂ : Nat), xs.length = ys.length →
    xs.foldl (fun a b => a * 256 + b.toNat) a₁ = ys.foldl (fun a b => a * 256 + b.toNat) a₂ →
    a₁ = a₂ ∧ xs = ys
  | [], [], a₁, a₂, _, h => ⟨h, rfl⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | x :: xs, y :: ys, a₁, a₂, hlen, h => by
    obtain ⟨ha, htail⟩ := foldl_be_inj xs ys (a₁ * 256 + x.toNat) (a₂ * 256 + y.toNat)
      (Nat.succ.inj hlen) h
    have hx : x.toNat < 256 := x.toNat_lt
    have hy : y.toNat < 256 := y.toNat_lt
    have hxy : x = y := UInt8.toNat_inj.1 (by omega)
    exact ⟨by omega, by rw [hxy, htail]⟩
private theorem uint64_ofBE_8_inj {xs ys : List UInt8} (hx : xs.length = 8) (hy : ys.length = 8)
    (heq : UInt64.ofNat (ofBE xs) = UInt64.ofNat (ofBE ys)) : xs = ys := by
  have hpow : 256 ^ 8 = 2 ^ 64 := by decide
  have hxlt : ofBE xs < 2 ^ 64 := by have := ofBE_lt xs; rw [hx, hpow] at this; exact this
  have hylt : ofBE ys < 2 ^ 64 := by have := ofBE_lt ys; rw [hy, hpow] at this; exact this
  have hnat : (UInt64.ofNat (ofBE xs)).toNat = (UInt64.ofNat (ofBE ys)).toNat :=
    congrArg UInt64.toNat heq
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hnat
  exact (foldl_be_inj xs ys 0 0 (hx.trans hy.symm) hnat).2

/-- Split a 32-byte (256-bit) digest into four big-endian 64-bit `UInt64` limbs without truncation. -/
def digestLimbs256 (d : List UInt8) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (UInt64.ofNat (ofBE (d.take 8)), UInt64.ofNat (ofBE ((d.drop 8).take 8)),
   UInt64.ofNat (ofBE ((d.drop 16).take 8)),
   UInt64.ofNat (ofBE ((d.drop 24).take 8)))

/-- **Full-Width 256-Bit Carrier Injectivity (`digestLimbs256_injective`)**:
    Two 32-byte digests with equal `4 × UInt64` limb tuples are byte-for-byte identical. -/
theorem digestLimbs256_injective {d₁ d₂ : List UInt8} (h₁ : d₁.length = 32) (h₂ : d₂.length = 32)
    (heq : digestLimbs256 d₁ = digestLimbs256 d₂) : d₁ = d₂ := by
  unfold digestLimbs256 at heq
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨e0, e1, e2, e3⟩
  have s0 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e0
  have s1 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e1
  have s2 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e2
  have s3 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e3
  have split32 : ∀ (xs : List UInt8), xs.length = 32 →
      xs = xs.take 8 ++ ((xs.drop 8).take 8 ++ ((xs.drop 16).take 8 ++ (xs.drop 24).take 8)) := by
    intro xs hlen
    have h24 : (xs.drop 24).take 8 = xs.drop 24 := List.take_of_length_le (by simp [hlen])
    have h16 : xs.drop 16 = (xs.drop 16).take 8 ++ xs.drop 24 := by
      simpa [List.drop_drop] using (List.take_append_drop 8 (xs.drop 16)).symm
    have h8 : xs.drop 8 = (xs.drop 8).take 8 ++ xs.drop 16 := by
      simpa [List.drop_drop] using (List.take_append_drop 8 (xs.drop 8)).symm
    rw [h24, ← h16, ← h8, List.take_append_drop]
  rw [split32 d₁ h₁, split32 d₂ h₂, s0, s1, s2, s3]

/-- Pack four 64-bit digest limbs plus two metadata words into a 16-slot `ChunkData`. -/
def packDigestChunk (limbs : UInt64 × UInt64 × UInt64 × UInt64) (meta0 meta1 : UInt64) : ChunkData where
  slots := #[limbs.1, limbs.2.1, limbs.2.2.1, limbs.2.2.2, meta0, meta1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  size_eq := rfl

/-- Chunk encoding of `ChunkedWorld` bucket `b < 128`. -/
def worldBucketChunk (w : ChunkedWorld.World) (b : Nat) : ChunkData :=
  match ChunkedWorld.shardForBucket w b with
  | none => zeroChunk
  | some (_, sb) =>
    packDigestChunk (digestLimbs256 (ChunkedWorld.logHash sb)) 1 (UInt64.ofNat sb.length)

/-- Chunk `128` encoding the full 256-bit `cSHAKE256` digest of `ChunkedWorld.manifestBytes w`. -/
def worldManifestChunk (w : ChunkedWorld.World) : ChunkData :=
  let mb := ChunkedWorld.manifestBytes w
  packDigestChunk (digestLimbs256 (ChunkedWorld.logHash mb))
    (UInt64.ofNat w.store.pages.length) (UInt64.ofNat w.store.tombs.length)

/-- Materialize all `256` chunks of `w` from scratch (`0..127`: buckets; `128`: manifest; `129..255`: COW). -/
def materializeWorldChunks (w : ChunkedWorld.World) : Array ChunkData :=
  ((List.range numChunks).map fun c =>
    if c < ChunkedWorld.numBuckets then worldBucketChunk w c
    else if c = ChunkedWorld.numBuckets then worldManifestChunk w
    else zeroChunk).toArray
theorem materializeWorldChunks_size (w : ChunkedWorld.World) :
    (materializeWorldChunks w).size = numChunks := by simp [materializeWorldChunks]

/-! ## 2. `VerkleUmem` Tree Specification, Scratch Commit & $O(\log K)$ Incremental Update -/

private theorem leafTag_size (v : UInt64) : (leafTag v).size = 32 := by
  unfold leafTag tagOf; exact cshake32ByteArray_size treeCustomization (leafPreimage v)
private theorem nodeTag_size (children : List ByteArray) : (nodeTag children).size = 32 := by
  unfold nodeTag tagOf; exact cshake32ByteArray_size treeCustomization (nodePreimage children)
private theorem getD_lt {α : Type} (xs : Array α) (i : Nat) (d : α) (hi : i < xs.size) :
    xs.getD i d = xs[i]'hi := by unfold Array.getD; simp [hi]
private theorem map_const_range (n : Nat) (x : ByteArray) :
    (List.range n).map (fun _ => x) = List.replicate n x := by
  apply List.ext_getElem (by simp); intro _ _ _; simp

/-- Canonical all-zero `VerkleUmem` subtree tag of height `lvl`. -/
def zeroTreeTag : Nat → ByteArray
  | 0 => leafTag 0
  | lvl + 1 => nodeTag (List.replicate 16 (zeroTreeTag lvl))
theorem zeroTreeTag_size : ∀ (lvl : Nat), (zeroTreeTag lvl).size = 32
  | 0 => leafTag_size 0
  | lvl + 1 => nodeTag_size (List.replicate 16 (zeroTreeTag lvl))

/-- Level-1 `VerkleUmem` subtree tag of a 16-slot `ChunkData`. -/
def chunkSubtreeTag (c : ChunkData) : ByteArray := nodeTag (c.slots.toList.map leafTag)
theorem chunkSubtreeTag_size (c : ChunkData) : (chunkSubtreeTag c).size = 32 :=
  nodeTag_size (c.slots.toList.map leafTag)
theorem chunkSubtreeTag_zero : chunkSubtreeTag zeroChunk = zeroTreeTag 1 := by
  unfold chunkSubtreeTag zeroChunk zeroTreeTag chunkSlots
  exact congrArg nodeTag (by simp [Array.toList_replicate, zeroTreeTag])

/-- Extract the 16 chunk roots belonging to group `g < 16`. -/
def groupChunkTags (chunkRoots : Array ByteArray) (g : Nat) : List ByteArray :=
  (List.range 16).map fun d => chunkRoots.getD (g * 16 + d) (zeroTreeTag 1)
private theorem groupChunkTags_getElem (cr : Array ByteArray) (g d : Nat) (hd : d < 16) :
    (groupChunkTags cr g)[d]'(by simp [groupChunkTags]; exact hd) =
      cr.getD (g * 16 + d) (zeroTreeTag 1) := by
  unfold groupChunkTags; simp

/-- Level-2 `VerkleUmem` subtree tag for group `g` from `chunkRoots`. -/
def groupSubtreeTag (chunkRoots : Array ByteArray) (g : Nat) : ByteArray :=
  nodeTag (groupChunkTags chunkRoots g)

/-- Lift the level-3 active-prefix root (`4,096` slots) up `steps` levels starting at `lvl`. -/
def liftSpineFrom : Nat → Nat → ByteArray → ByteArray
  | _, 0, cur => cur
  | lvl, steps + 1, cur =>
    liftSpineFrom (lvl + 1) steps (nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl)))
theorem liftSpineFrom_size : ∀ (lvl steps : Nat) (cur : ByteArray),
    cur.size = 32 → (liftSpineFrom lvl steps cur).size = 32
  | _, 0, _, hcur => hcur
  | lvl, steps + 1, cur, _ =>
    liftSpineFrom_size (lvl + 1) steps
      (nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl))) (nodeTag_size _)

/-- Lift a level-3 tag across levels `3..15` (`13` spine hashes) to the level-16 `VerkleUmem` root. -/
def liftActiveToRoot (activeTag : ByteArray) : ByteArray := liftSpineFrom 3 13 activeTag

/-- **Full Materialized Verkle Commit (`fullVerkleCommitChunks`)**:
    Hashes all $N = 4{,}096$ slots across all $K = 256$ chunks from scratch into the 32-byte root. -/
def fullVerkleCommitChunks (chunks : Array ChunkData) : ByteArray :=
  let cRoots := ((List.range numChunks).map fun c =>
    chunkSubtreeTag (chunks.getD c zeroChunk)).toArray
  liftActiveToRoot (nodeTag ((List.range numGroups).map fun g => groupSubtreeTag cRoots g))

/-- Full scratch Verkle root of a `ChunkedWorld.World`. -/
def fullVerkleCommitWorld (w : ChunkedWorld.World) : ByteArray :=
  fullVerkleCommitChunks (materializeWorldChunks w)
theorem fullVerkleCommitChunks_size (chunks : Array ChunkData) :
    (fullVerkleCommitChunks chunks).size = 32 := by
  unfold fullVerkleCommitChunks liftActiveToRoot; dsimp only
  exact liftSpineFrom_size 3 13 _ (nodeTag_size _)

/-- View `chunks` as an `Obend.Polis.ExtRam` over all $2^{64}$ addresses (`0` for `addr ≥ 4096`). -/
@[expose] def chunksToExtRam (chunks : Array ChunkData) : ExtRam := fun addr =>
  let a := addr.toNat
  if a < totalSlots then (chunks.getD (a / chunkSlots) zeroChunk).getSlot (a % chunkSlots) else 0

/-- Pure mathematical 16-ary tree tag over an arbitrary `ExtRam` at `(lvl, pfx)`. -/
def specExtRamTreeTag (ram : ExtRam) : Nat → Nat → ByteArray
  | 0, pfx => if pfx < 2 ^ 64 then leafTag (ram (UInt64.ofNat pfx)) else leafTag 0
  | lvl + 1, pfx => nodeTag ((List.range 16).map fun d => specExtRamTreeTag ram lvl (pfx * 16 + d))
private theorem specExtRamTreeTag_zero (ram : ExtRam) (pfx : Nat) : specExtRamTreeTag ram 0 pfx =
      if pfx < 2 ^ 64 then leafTag (ram (UInt64.ofNat pfx)) else leafTag 0 := rfl
private theorem specExtRamTreeTag_succ (ram : ExtRam) (lvl pfx : Nat) :
    specExtRamTreeTag ram (lvl + 1) pfx =
      nodeTag ((List.range 16).map fun d => specExtRamTreeTag ram lvl (pfx * 16 + d)) := rfl
private theorem specExtRamTreeTag_zero_above (chunks : Array ChunkData) :
    ∀ (lvl pfx : Nat), totalSlots ≤ pfx * 16 ^ lvl →
      specExtRamTreeTag (chunksToExtRam chunks) lvl pfx = zeroTreeTag lvl
  | 0, pfx, hge => by
    simp only [Nat.pow_zero, Nat.mul_one] at hge
    rw [specExtRamTreeTag_zero]; unfold zeroTreeTag
    split
    · rename_i hlt
      unfold chunksToExtRam; dsimp only
      have hu : (UInt64.ofNat pfx).toNat = pfx := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
      rw [hu]
      have hnot : ¬ pfx < totalSlots := by omega
      simp only [hnot, ↓reduceIte]
    · rfl
  | lvl + 1, pfx, hge => by
    rw [specExtRamTreeTag_succ]; unfold zeroTreeTag
    apply congrArg nodeTag
    rw [← map_const_range 16 (zeroTreeTag lvl)]
    apply List.map_congr_left
    intro d _
    apply specExtRamTreeTag_zero_above chunks lvl (pfx * 16 + d)
    rw [Nat.pow_succ, Nat.mul_comm (16 ^ lvl) 16, ← Nat.mul_assoc] at hge
    exact Nat.le_trans hge (Nat.mul_le_mul_right (16 ^ lvl) (by omega))
private theorem chunkSlots_toList_eq_range (c : ChunkData) :
    c.slots.toList.map leafTag = (List.range 16).map (fun j => leafTag (c.getSlot j)) := by
  have hlen : c.slots.toList.length = 16 := by rw [Array.length_toList, c.size_eq]; rfl
  apply List.ext_getElem (by simp [hlen])
  intro j _ hj2
  simp only [List.getElem_map, List.getElem_range]
  have hjb : j < c.slots.size := by rw [c.size_eq]; simp at hj2; exact hj2
  unfold ChunkData.getSlot; rw [getD_lt c.slots j 0 hjb]; simp
private theorem specExtRamTreeTag_lvl3 (chunks : Array ChunkData) :
    specExtRamTreeTag (chunksToExtRam chunks) 3 0 = nodeTag ((List.range numGroups).map fun g =>
        groupSubtreeTag (((List.range numChunks).map fun c =>
          chunkSubtreeTag (chunks.getD c zeroChunk)).toArray) g) := by
  have hlvl1 : ∀ c < numChunks, specExtRamTreeTag (chunksToExtRam chunks) 1 c =
        chunkSubtreeTag (chunks.getD c zeroChunk) := by
    intro c hc
    rw [specExtRamTreeTag_succ]; unfold chunkSubtreeTag; rw [chunkSlots_toList_eq_range]
    apply congrArg nodeTag; apply List.map_congr_left
    intro j hj
    have hjlt : j < 16 := List.mem_range.mp hj
    rw [specExtRamTreeTag_zero]
    have hlt64 : c * 16 + j < 2 ^ 64 := by unfold numChunks at hc; omega
    have hltTot : c * 16 + j < totalSlots := by unfold numChunks totalSlots at *; omega
    simp only [hlt64, ↓reduceIte]; unfold chunksToExtRam; dsimp only
    have hu : (UInt64.ofNat (c * 16 + j)).toNat = c * 16 + j := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt64
    have hdiv : (c * 16 + j) / chunkSlots = c := by unfold chunkSlots; omega
    have hmod : (c * 16 + j) % chunkSlots = j := by unfold chunkSlots; omega
    rw [hu]; simp only [hltTot, ↓reduceIte, hdiv, hmod]
  rw [specExtRamTreeTag_succ]; unfold numGroups
  apply congrArg nodeTag; apply List.map_congr_left
  intro g hg
  have hglt : g < 16 := List.mem_range.mp hg
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [specExtRamTreeTag_succ]; unfold groupSubtreeTag groupChunkTags
  apply congrArg nodeTag; apply List.map_congr_left
  intro d hd
  have hdlt : d < 16 := List.mem_range.mp hd
  have hclt : g * 16 + d < numChunks := by unfold numChunks; omega
  rw [hlvl1 (g * 16 + d) hclt]
  let arr := ((List.range numChunks).map fun c =>
    chunkSubtreeTag (chunks.getD c zeroChunk)).toArray
  have hsz : arr.size = numChunks := by simp [arr]
  rw [getD_lt arr (g * 16 + d) (zeroTreeTag 1) (by rw [hsz]; exact hclt)]; simp [arr]
private theorem liftSpineFrom_eq_specExtRam (chunks : Array ChunkData) :
    ∀ (steps lvl : Nat), 3 ≤ lvl →
      liftSpineFrom lvl steps (specExtRamTreeTag (chunksToExtRam chunks) lvl 0) =
        specExtRamTreeTag (chunksToExtRam chunks) (lvl + steps) 0 := by
  intro steps
  induction steps with
  | zero => intro lvl _; simp [liftSpineFrom]
  | succ steps ih =>
    intro lvl hlvl
    have hstep : specExtRamTreeTag (chunksToExtRam chunks) (lvl + 1) 0 =
        nodeTag (specExtRamTreeTag (chunksToExtRam chunks) lvl 0 ::
          List.replicate 15 (zeroTreeTag lvl)) := by
      rw [specExtRamTreeTag_succ]; apply congrArg nodeTag
      have hr : List.range 16 = 0 :: (List.range 15).map (· + 1) := by decide
      rw [hr, List.map_cons, List.map_map]
      simp only [Nat.zero_mul, Nat.zero_add, Function.comp_def]
      apply congrArg (specExtRamTreeTag (chunksToExtRam chunks) lvl 0 :: ·)
      rw [← map_const_range 15 (zeroTreeTag lvl)]
      apply List.map_congr_left; intro d _
      apply specExtRamTreeTag_zero_above
      have hpow : 16 ^ 3 ≤ 16 ^ lvl := Nat.pow_le_pow_right (by decide) hlvl
      have htot : totalSlots = 16 ^ 3 := by decide
      rw [htot]; exact Nat.le_trans hpow (Nat.le_mul_of_pos_left _ (by omega))
    unfold liftSpineFrom; rw [← hstep]
    have heq := ih (lvl + 1) (by omega)
    have hadd : lvl + 1 + steps = lvl + (steps + 1) := by omega
    rwa [hadd] at heq

/-- **`fullVerkleCommitChunks` Equals the 16-Level `ExtRam` Root**: materializing the 4,096 chunk
    slots gives the `VerkleUmem` root of `chunksToExtRam chunks` over the $2^{64}$ address space. -/
theorem fullVerkleCommitChunks_eq_specExtRamRoot (chunks : Array ChunkData) :
    fullVerkleCommitChunks chunks = specExtRamTreeTag (chunksToExtRam chunks) 16 0 := by
  unfold fullVerkleCommitChunks liftActiveToRoot; dsimp only
  rw [← specExtRamTreeTag_lvl3 chunks]
  exact liftSpineFrom_eq_specExtRam chunks 13 3 (by decide)

/-! ## 3. Base-$2^{16}$ `UInt64` Gadget Decomposition & Per-Chunk Ajtai Lattice Commitments -/

/-- Decompose a 64-bit `UInt64` word losslessly into four 16-bit integer limbs in `[0, 65535]`. -/
def decomposeUInt64Limbs (u : UInt64) : List Int :=
  let n := u.toNat
  [(((n % 65536) : Nat) : Int), ((((n / 65536) % 65536) : Nat) : Int),
   ((((n / 4294967296) % 65536) : Nat) : Int), (((n / 281474976710656) : Nat) : Int)]
theorem decomposeUInt64Limbs_injective {u₁ u₂ : UInt64}
    (h : decomposeUInt64Limbs u₁ = decomposeUInt64Limbs u₂) : u₁ = u₂ := by
  unfold decomposeUInt64Limbs at h
  simp only [List.cons.injEq, Int.ofNat_inj, and_true] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have hb1 : u₁.toNat < 2 ^ 64 := u₁.toNat_lt
  have hb2 : u₂.toNat < 2 ^ 64 := u₂.toNat_lt
  exact UInt64.toNat_inj.1 (by omega)
theorem decomposeUInt64Limbs_short (u : UInt64) :
    ∀ z ∈ decomposeUInt64Limbs u, z.natAbs ≤ 65535 := by
  intro z hz; have hb : u.toNat < 2 ^ 64 := u.toNat_lt
  simp only [decomposeUInt64Limbs, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> omega

/-- Flatten a list of `UInt64` words into `4 * words.length` short 16-bit integer limbs. -/
def wordsToLimbs (words : List UInt64) : List Int := words.flatMap decomposeUInt64Limbs
theorem wordsToLimbs_length (words : List UInt64) :
    (wordsToLimbs words).length = 4 * words.length := by
  unfold wordsToLimbs
  induction words with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, decomposeUInt64Limbs,
      List.cons_append, List.nil_append, List.length_cons, ih]; omega
theorem wordsToLimbs_short (words : List UInt64) : ShortNormBound 65535 (wordsToLimbs words) := by
  unfold ShortNormBound; apply Obend.Crypto.normInf_le_of_forall
  intro z hz; unfold wordsToLimbs at hz
  obtain ⟨u, _, hzu⟩ := List.mem_flatMap.1 hz
  exact decomposeUInt64Limbs_short u z hzu
theorem wordsToLimbs_injective : ∀ {l₁ l₂ : List UInt64},
    wordsToLimbs l₁ = wordsToLimbs l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [wordsToLimbs, decomposeUInt64Limbs] at h
  | _ :: _, [], h => by simp [wordsToLimbs, decomposeUInt64Limbs] at h
  | u :: us, v :: vs, h => by
    simp only [wordsToLimbs, List.flatMap_cons, decomposeUInt64Limbs,
      List.cons_append, List.nil_append, List.cons.injEq] at h
    rcases h with ⟨h0, h1, h2, h3, hrest⟩
    have huv : u = v := decomposeUInt64Limbs_injective (by
      simp [decomposeUInt64Limbs, h0, h1, h2, h3])
    rw [huv, wordsToLimbs_injective hrest]

/-- Convert a 16-slot `ChunkData` to its 64-coordinate short Ajtai witness (`‖w‖_∞ ≤ 65535`). -/
def chunkToLimbs (c : ChunkData) : List Int := wordsToLimbs c.slots.toList
theorem chunkToLimbs_length (c : ChunkData) : (chunkToLimbs c).length = 64 := by
  unfold chunkToLimbs; rw [wordsToLimbs_length, Array.length_toList, c.size_eq]; rfl
theorem chunkToLimbs_short (c : ChunkData) : Short 64 65535 (chunkToLimbs c) :=
  ⟨chunkToLimbs_length c, wordsToLimbs_short c.slots.toList⟩

/-- Compute the modular Ajtai commitment $\mathbf{A} \cdot \text{limbs}(c) \bmod q$ of chunk `c`. -/
def ajtaiChunkCommit (pp : AjtaiParams) (hCols : pp.cols = 64) (c : ChunkData) : List Int :=
  ajtaiCommit pp (chunkToLimbs c) ((chunkToLimbs_length c).trans hCols.symm)

/-- Default concrete `AjtaiParams` (`arity = 4`, `rows = 16`, `cols = 64`, `modulus = 262141^4`). -/
def defaultChunkAjtaiParams : AjtaiParams := inhabitedAjtaiParams 4
theorem defaultChunkAjtaiParams_cols : defaultChunkAjtaiParams.cols = 64 := (inhabitedAjtaiParams_sisHard 4).1

/-- **Inhabitedness / Non-Vacuity Theorem (`dualChunkParams_inhabited_sisHard`)**:
    `defaultChunkAjtaiParams` satisfies `cols = 64`, `NonPigeonholeSISParams`, and `ModuleSISHard` (`0` axioms). -/
theorem dualChunkParams_inhabited_sisHard :
    defaultChunkAjtaiParams.cols = 64 ∧ NonPigeonholeSISParams defaultChunkAjtaiParams ∧
    ModuleSISHard defaultChunkAjtaiParams 131070 := inhabitedAjtaiParams_sisHard 4

/-! ## 4. `AuthenticatedWorldSnapshot`, Incremental Root Update & Point Openings -/

/-- Persistent COW world snapshot pairing `ChunkedWorld.World` with its 256-chunk table,
    cached level-1/level-2 `VerkleUmem` tags, 256-bit `verkleRoot`, and per-chunk Ajtai roots. -/
structure AuthenticatedWorldSnapshot where
  world : ChunkedWorld.World
  branchGen : Nat
  chunks : Array ChunkData
  chunkRoots : Array ByteArray
  groupRoots : Array ByteArray
  activeRoot : ByteArray
  verkleRoot : ByteArray
  ajtaiChunkRoots : Array (List Int)
  deriving DecidableEq

/-- Structural invariant relating cached internal tags of `s` to `s.chunks`. -/
@[expose] def SnapshotWF (pp : AjtaiParams) (hCols : pp.cols = 64) (s : AuthenticatedWorldSnapshot) : Prop :=
  s.chunks.size = numChunks ∧ s.chunkRoots.size = numChunks ∧
  s.groupRoots.size = numGroups ∧ s.ajtaiChunkRoots.size = numChunks ∧
  (∀ c : Nat, c < numChunks → s.chunkRoots.getD c ByteArray.empty = chunkSubtreeTag (s.chunks.getD c zeroChunk)) ∧
  (∀ g : Nat, g < numGroups → s.groupRoots.getD g ByteArray.empty = groupSubtreeTag s.chunkRoots g) ∧
  s.activeRoot = nodeTag s.groupRoots.toList ∧ s.verkleRoot = liftActiveToRoot s.activeRoot ∧
  (∀ c : Nat, c < numChunks → s.ajtaiChunkRoots.getD c [] = ajtaiChunkCommit pp hCols (s.chunks.getD c zeroChunk))
private theorem snapshotWF_with_world {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) (w' : ChunkedWorld.World) :
    SnapshotWF pp hCols { s with world := w' } := hwf

/-- Build an `AuthenticatedWorldSnapshot` from `chunks` and `w`. -/
def buildSnapshotFromChunks (pp : AjtaiParams) (hCols : pp.cols = 64)
    (w : ChunkedWorld.World) (chunks : Array ChunkData) (gen : Nat := 0) : AuthenticatedWorldSnapshot :=
  let normChunks := ((List.range numChunks).map fun c => chunks.getD c zeroChunk).toArray
  let cRoots := ((List.range numChunks).map fun c => chunkSubtreeTag (normChunks.getD c zeroChunk)).toArray
  let gRoots := ((List.range numGroups).map fun g => groupSubtreeTag cRoots g).toArray
  let act := nodeTag gRoots.toList
  let aRoots := ((List.range numChunks).map fun c => ajtaiChunkCommit pp hCols (normChunks.getD c zeroChunk)).toArray
  { world := w, branchGen := gen, chunks := normChunks, chunkRoots := cRoots,
    groupRoots := gRoots, activeRoot := act, verkleRoot := liftActiveToRoot act, ajtaiChunkRoots := aRoots }
/-- Build the canonical `AuthenticatedWorldSnapshot` of `w : ChunkedWorld.World`. -/
def buildAuthenticatedSnapshot (pp : AjtaiParams) (hCols : pp.cols = 64) (w : ChunkedWorld.World) :
    AuthenticatedWorldSnapshot := buildSnapshotFromChunks pp hCols w (materializeWorldChunks w) 0
theorem buildSnapshotFromChunks_wf (pp : AjtaiParams) (hCols : pp.cols = 64)
    (w : ChunkedWorld.World) (chunks : Array ChunkData) (gen : Nat) :
    SnapshotWF pp hCols (buildSnapshotFromChunks pp hCols w chunks gen) := by
  unfold SnapshotWF buildSnapshotFromChunks; dsimp only
  refine ⟨by simp, by simp, by simp, by simp, ?_, ?_, rfl, rfl, ?_⟩
  · intro c hc; rw [getD_lt _ c ByteArray.empty (by simp; exact hc)]; simp
  · intro g hg; rw [getD_lt _ g ByteArray.empty (by simp; exact hg)]; simp
  · intro c hc; rw [getD_lt _ c [] (by simp; exact hc)]; simp
theorem buildAuthenticatedSnapshot_wf (pp : AjtaiParams) (hCols : pp.cols = 64) (w : ChunkedWorld.World) :
    SnapshotWF pp hCols (buildAuthenticatedSnapshot pp hCols w) :=
  buildSnapshotFromChunks_wf pp hCols w (materializeWorldChunks w) 0
theorem snapshotWF_verkleRoot_eq_fullCommit {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) :
    s.verkleRoot = fullVerkleCommitChunks s.chunks := by
  obtain ⟨_, hrsz, hgsz, _, hcEq, hgEq, hact, hroot, _⟩ := hwf
  unfold fullVerkleCommitChunks; dsimp only; rw [hroot, hact]
  apply congrArg liftActiveToRoot; apply congrArg nodeTag
  have hcArr : s.chunkRoots = ((List.range numChunks).map fun c =>
      chunkSubtreeTag (s.chunks.getD c zeroChunk)).toArray := by
    apply Array.ext (by simp [hrsz]); intro c hc1 _
    rw [← getD_lt s.chunkRoots c ByteArray.empty hc1, hcEq c (by rw [hrsz] at hc1; exact hc1)]; simp
  rw [← hcArr]
  apply List.ext_getElem (by simp [hgsz]); intro g _ hg2
  have hglt : g < numGroups := by simp at hg2; exact hg2
  rw [Array.getElem_toList, ← getD_lt s.groupRoots g ByteArray.empty (by rw [hgsz]; exact hglt), hgEq g hglt]; simp
theorem buildAuthenticatedSnapshot_verkleRoot (pp : AjtaiParams) (hCols : pp.cols = 64) (w : ChunkedWorld.World) :
    (buildAuthenticatedSnapshot pp hCols w).verkleRoot = fullVerkleCommitWorld w := by
  rw [snapshotWF_verkleRoot_eq_fullCommit (buildAuthenticatedSnapshot_wf pp hCols w)]
  unfold buildAuthenticatedSnapshot buildSnapshotFromChunks fullVerkleCommitWorld; dsimp only
  apply congrArg fullVerkleCommitChunks; apply Array.ext (by simp [materializeWorldChunks_size])
  intro c _ hc2
  rw [List.getElem_toArray, List.getElem_map, List.getElem_range, getD_lt (materializeWorldChunks w) c zeroChunk hc2]

/-- **Incremental Single-Chunk Update**: recomputes only dirty chunk `c`'s tag, its 16-chunk group
    tag, the $O(\log K)$ upper spine, and its Ajtai chunk commitment. -/
def updateChunkVerkleRoot (pp : AjtaiParams) (hCols : pp.cols = 64)
    (s : AuthenticatedWorldSnapshot) (c : Nat) (_hc : c < numChunks)
    (newChunk : ChunkData) : AuthenticatedWorldSnapshot :=
  let chunks' := s.chunks.setIfInBounds c newChunk
  let newChunkTag := chunkSubtreeTag newChunk
  let cRoots' := s.chunkRoots.setIfInBounds c newChunkTag
  let g := c / 16
  let gRoots' := s.groupRoots.setIfInBounds g (groupSubtreeTag cRoots' g)
  let act' := nodeTag gRoots'.toList
  let aRoots' := s.ajtaiChunkRoots.setIfInBounds c (ajtaiChunkCommit pp hCols newChunk)
  { s with chunks := chunks', chunkRoots := cRoots', groupRoots := gRoots',
           activeRoot := act', verkleRoot := liftActiveToRoot act', ajtaiChunkRoots := aRoots' }
private theorem getD_setIfInBounds_eq {α : Type} (xs : Array α) (i : Nat) (v d : α)
    (hi : i < xs.size) : (xs.setIfInBounds i v).getD i d = v := by unfold Array.getD; simp [hi]
private theorem getD_setIfInBounds_ne {α : Type} (xs : Array α) (i j : Nat) (v d : α)
    (hne : j ≠ i) : (xs.setIfInBounds i v).getD j d = xs.getD j d := by
  unfold Array.getD
  by_cases hj : j < xs.size
  · simp [hj, Ne.symm hne]
  · simp [hj]
theorem updateChunkVerkleRoot_wf {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    (c : Nat) (hc : c < numChunks) (newChunk : ChunkData) :
    SnapshotWF pp hCols (updateChunkVerkleRoot pp hCols s c hc newChunk) := by
  obtain ⟨hcsz, hrsz, hgsz, hasz, hcEq, hgEq, _, _, haEq⟩ := hwf
  unfold SnapshotWF updateChunkVerkleRoot; dsimp only
  refine ⟨by simp [hcsz], by simp [hrsz], by simp [hgsz], by simp [hasz], ?_, ?_, rfl, rfl, ?_⟩
  · intro c' hc'
    by_cases heq : c' = c
    · subst heq
      rw [getD_setIfInBounds_eq _ _ _ _ (by rw [hrsz]; exact hc),
          getD_setIfInBounds_eq _ _ _ _ (by rw [hcsz]; exact hc)]
    · rw [getD_setIfInBounds_ne _ _ _ _ _ heq, getD_setIfInBounds_ne _ _ _ _ _ heq, hcEq c' hc']
  · intro g' hg'
    have hglt : c / 16 < numGroups := by unfold numChunks numGroups at *; omega
    by_cases hgeq : g' = c / 16
    · subst hgeq; rw [getD_setIfInBounds_eq _ _ _ _ (by rw [hgsz]; exact hglt)]
    · rw [getD_setIfInBounds_ne _ _ _ _ _ hgeq, hgEq g' hg']
      unfold groupSubtreeTag groupChunkTags; apply congrArg nodeTag; apply List.map_congr_left
      intro d hd
      have hdlt : d < 16 := List.mem_range.mp hd
      have hne : g' * 16 + d ≠ c := by intro e; apply hgeq; omega
      exact (getD_setIfInBounds_ne _ _ _ _ _ hne).symm
  · intro c' hc'
    by_cases heq : c' = c
    · subst heq
      rw [getD_setIfInBounds_eq _ _ _ _ (by rw [hasz]; exact hc),
          getD_setIfInBounds_eq _ _ _ _ (by rw [hcsz]; exact hc)]
    · rw [getD_setIfInBounds_ne _ _ _ _ _ heq, getD_setIfInBounds_ne _ _ _ _ _ heq, haEq c' hc']

/-- **Headline Theorem 1**: `updateChunkVerkleRoot` on any chunk `c < 256` preserves `SnapshotWF`,
    yields a 32-byte root, and equals `fullVerkleCommitChunks` and `specExtRamTreeTag`. -/
theorem incrementalVerkleSnapshot_eq_fullCommit {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    (c : Nat) (hc : c < numChunks) (newChunk : ChunkData) :
    let s' := updateChunkVerkleRoot pp hCols s c hc newChunk
    SnapshotWF pp hCols s' ∧
    s'.verkleRoot.size = 32 ∧
    s'.verkleRoot = fullVerkleCommitChunks (s.chunks.setIfInBounds c newChunk) ∧
    s'.verkleRoot = specExtRamTreeTag (chunksToExtRam (s.chunks.setIfInBounds c newChunk)) 16 0 := by
  have hwf' := updateChunkVerkleRoot_wf hwf c hc newChunk
  have hfull := snapshotWF_verkleRoot_eq_fullCommit hwf'
  refine ⟨hwf', ?_, hfull, hfull.trans (fullVerkleCommitChunks_eq_specExtRamRoot _)⟩
  rw [hfull]; exact fullVerkleCommitChunks_size _
private def syncStep (pp : AjtaiParams) (hCols : pp.cols = 64)
    (target : Array ChunkData) (acc : AuthenticatedWorldSnapshot) (c : Nat) :
    AuthenticatedWorldSnapshot :=
  if hc : c < numChunks then
    let nextChunk := target.getD c zeroChunk
    if acc.chunks.getD c zeroChunk == nextChunk then acc
    else updateChunkVerkleRoot pp hCols acc c hc nextChunk
  else acc

/-- Sync a snapshot to a new `ChunkedWorld.World` `w'` by updating **only** modified chunks. -/
def syncSnapshotWorld (pp : AjtaiParams) (hCols : pp.cols = 64)
    (s : AuthenticatedWorldSnapshot) (w' : ChunkedWorld.World) : AuthenticatedWorldSnapshot :=
  let s1 := (List.range numChunks).foldl (syncStep pp hCols (materializeWorldChunks w')) s
  { s1 with world := w' }
private theorem syncStep_props {pp : AjtaiParams} {hCols : pp.cols = 64}
    (target : Array ChunkData) {acc : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols acc)
    (idx : Nat) :
    SnapshotWF pp hCols (syncStep pp hCols target acc idx) ∧
    (idx < numChunks →
      (syncStep pp hCols target acc idx).chunks.getD idx zeroChunk = target.getD idx zeroChunk) ∧
    (∀ c, c ≠ idx →
      (syncStep pp hCols target acc idx).chunks.getD c zeroChunk = acc.chunks.getD c zeroChunk) := by
  unfold syncStep
  split
  · rename_i hc
    dsimp only
    split
    · rename_i heq
      exact ⟨hwf, fun _ => beq_iff_eq.mp heq, fun _ _ => rfl⟩
    · refine ⟨updateChunkVerkleRoot_wf hwf idx hc _, fun _ => ?_, fun c hne => ?_⟩
      · unfold updateChunkVerkleRoot
        exact getD_setIfInBounds_eq acc.chunks idx _ zeroChunk (by rw [hwf.1]; exact hc)
      · unfold updateChunkVerkleRoot
        exact getD_setIfInBounds_ne acc.chunks idx c _ zeroChunk hne
  · rename_i hnc
    exact ⟨hwf, fun h => (hnc h).elim, fun _ _ => rfl⟩
private theorem syncFold_preserves {pp : AjtaiParams} {hCols : pp.cols = 64}
    (target : Array ChunkData) (idxs : List Nat) :
    ∀ (acc : AuthenticatedWorldSnapshot), SnapshotWF pp hCols acc →
      SnapshotWF pp hCols (idxs.foldl (syncStep pp hCols target) acc) ∧
      (∀ c ∈ idxs, c < numChunks →
        (idxs.foldl (syncStep pp hCols target) acc).chunks.getD c zeroChunk =
          target.getD c zeroChunk) ∧
      (∀ c, c ∉ idxs → (idxs.foldl (syncStep pp hCols target) acc).chunks.getD c zeroChunk =
          acc.chunks.getD c zeroChunk) := by
  induction idxs with
  | nil =>
    intro acc hwf
    refine ⟨hwf, ?_, ?_⟩
    · intro _ hm; cases hm
    · intro _ _; rfl
  | cons idx rest ih =>
    intro acc hwf
    obtain ⟨hwf1, hEq1, hNe1⟩ := syncStep_props target hwf idx
    obtain ⟨hwf2, hIn2, hOut2⟩ := ih (syncStep pp hCols target acc idx) hwf1
    simp only [List.foldl_cons]
    refine ⟨hwf2, ?_, ?_⟩
    · intro c hmem hclt
      by_cases hcr : c ∈ rest
      · exact hIn2 c hcr hclt
      · rcases List.mem_cons.1 hmem with rfl | hcr'
        · rw [hOut2 c hcr]; exact hEq1 hclt
        · exact (hcr hcr').elim
    · intro c hnot
      have hnotIdx : c ≠ idx := fun e => hnot (List.mem_cons.2 (.inl e))
      have hnotRest : c ∉ rest := fun hm => hnot (List.mem_cons.2 (.inr hm))
      rw [hOut2 c hnotRest, hNe1 c hnotIdx]
theorem syncSnapshotWorld_wf_and_eq_fullCommit {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) (w' : ChunkedWorld.World) :
    let s' := syncSnapshotWorld pp hCols s w'
    SnapshotWF pp hCols s' ∧ s'.world = w' ∧ s'.verkleRoot = fullVerkleCommitWorld w' := by
  unfold syncSnapshotWorld; dsimp only
  obtain ⟨hwf1, hIn, _⟩ := syncFold_preserves (materializeWorldChunks w') (List.range numChunks) s hwf
  generalize hs1 :
    (List.range numChunks).foldl (syncStep pp hCols (materializeWorldChunks w')) s = s1 at hwf1 hIn ⊢
  have hwf' : SnapshotWF pp hCols { s1 with world := w' } := snapshotWF_with_world hwf1 w'
  refine ⟨hwf', rfl, ?_⟩
  have hchunksEq : s1.chunks = materializeWorldChunks w' := by
    apply Array.ext
    · rw [hwf1.1, materializeWorldChunks_size]
    · intro c hc1 hc2
      have hclt : c < numChunks := by rw [hwf1.1] at hc1; exact hc1
      rw [← getD_lt s1.chunks c zeroChunk hc1, ← getD_lt (materializeWorldChunks w') c zeroChunk hc2]
      exact hIn c (List.mem_range.mpr hclt) hclt
  have hroot := snapshotWF_verkleRoot_eq_fullCommit hwf'
  dsimp only at hroot
  rw [hroot, hchunksEq]; rfl

/-! ### Stateless 16-Level `VerkleUmem` Point Openings From Cached Snapshot Subtrees -/

/-- Read slot `(c, j)` of `s` (`0` out of bounds). -/
def AuthenticatedWorldSnapshot.readSlot (s : AuthenticatedWorldSnapshot) (c j : Nat) : UInt64 :=
  (s.chunks.getD c zeroChunk).getSlot j
/-- Build the 16-level `Obend.Polis.verifyOpening` sibling path for slot `(c, j)`. -/
def openSnapshotSlot (s : AuthenticatedWorldSnapshot) (c j : Nat) : Array (Array ByteArray) :=
  let chunk := s.chunks.getD c zeroChunk
  let sib0 := ((chunk.slots.toList.map leafTag).eraseIdx j).toArray
  let sib1 := ((groupChunkTags s.chunkRoots (c / 16)).eraseIdx (c % 16)).toArray
  let sib2 := (s.groupRoots.toList.eraseIdx (c / 16)).toArray
  let upper := (List.range 13).map fun k => Array.replicate 15 (zeroTreeTag (3 + k))
  (sib0 :: sib1 :: sib2 :: upper).toArray
private theorem insertAt_eraseIdx : ∀ (xs : List ByteArray) (n : Nat) (hn : n < xs.length),
    insertAt n (xs[n]'hn) (xs.eraseIdx n) = xs
  | [], _, hn => by simp at hn
  | _ :: _, 0, _ => rfl
  | x :: xs, n + 1, hn => by
    simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, insertAt,
      List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact congrArg (x :: ·) (insertAt_eraseIdx xs n (Nat.lt_of_succ_lt_succ hn))
private theorem eraseIdx_length_of_lt : ∀ (xs : List ByteArray) (n : Nat),
    n < xs.length → (xs.eraseIdx n).length = xs.length - 1
  | [], _, hn => by simp at hn
  | _ :: _, 0, _ => by simp
  | _ :: xs, n + 1, hn => by
    have ih := eraseIdx_length_of_lt xs n (Nat.lt_of_succ_lt_succ hn)
    have hpos : 0 < xs.length := Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_of_succ_lt_succ hn)
    simp only [List.eraseIdx_cons_succ, List.length_cons, ih]; omega
private theorem climb_upper_zeroSpine (addr : UInt64) (haddr : addr.toNat < totalSlots) :
    ∀ (steps lvl : Nat) (cur : ByteArray), 3 ≤ lvl → List.foldlM (climbStep addr) (lvl, cur)
        ((List.range steps).map fun k => Array.replicate 15 (zeroTreeTag (lvl + k))) =
        some (lvl + steps, liftSpineFrom lvl steps cur)
  | 0, lvl, cur, _ => by simp [liftSpineFrom]
  | steps + 1, lvl, cur, hlvl => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, Function.comp_def]
    have hshift : (fun x => Array.replicate 15 (zeroTreeTag (lvl + (x + 1)))) =
        (fun k => Array.replicate 15 (zeroTreeTag ((lvl + 1) + k))) := by
      funext k; congr 2; omega
    rw [hshift, Obend.Polis.foldlM_cons_some]
    have hnib : nibbleAt addr lvl = 0 := by
      unfold nibbleAt
      have hpow : totalSlots ≤ 16 ^ lvl := by
        have h3 : totalSlots = 16 ^ 3 := by decide
        rw [h3]; exact Nat.pow_le_pow_right (by decide) hlvl
      have hdiv : addr.toNat / 16 ^ lvl = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le haddr hpow)
      simp [hdiv]
    refine ⟨(lvl + 1, nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl))), ?_, ?_⟩
    · unfold climbStep; simp [hnib, insertAt]
    · have ih := climb_upper_zeroSpine addr haddr steps (lvl + 1)
        (nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl))) (by omega)
      have hadd : lvl + 1 + steps = lvl + (steps + 1) := by omega
      rwa [hadd] at ih

/-- **Snapshot Opening Completeness**: every slot `(c, j)` (`c < 256`, `j < 16`) of a well-formed
    snapshot has a 16-level sibling path accepted by `Obend.Polis.verifyOpening`. -/
theorem openSnapshotSlot_valid {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    {c j : Nat} (hc : c < numChunks) (hj : j < chunkSlots) :
    verifyOpening s.verkleRoot (slotAddr c j) (s.readSlot c j) (openSnapshotSlot s c j) = true := by
  obtain ⟨_, hrsz, hgsz, _, hcEq, hgEq, hact, hroot, _⟩ := hwf
  rw [Obend.Polis.verifyOpening_iff]
  refine ⟨by simp [openSnapshotSlot], 16, ?_⟩
  unfold climb openSnapshotSlot
  rw [← Array.foldlM_toList]
  dsimp only
  have haddrNat := slotAddr_toNat hc hj
  have haddrTot : (slotAddr c j).toNat < totalSlots := by
    rw [haddrNat]; unfold numChunks chunkSlots totalSlots at *; omega
  have hnib0 : nibbleAt (slotAddr c j) 0 = j := by
    unfold nibbleAt; rw [haddrNat]; unfold chunkSlots at *; omega
  have hnib1 : nibbleAt (slotAddr c j) 1 = c % 16 := by
    unfold nibbleAt; rw [haddrNat]; unfold chunkSlots at *; omega
  have hnib2 : nibbleAt (slotAddr c j) 2 = c / 16 := by
    unfold nibbleAt; rw [haddrNat]; unfold numChunks chunkSlots at *; omega
  have hxs0Len : ((s.chunks.getD c zeroChunk).slots.toList.map leafTag).length = 16 := by
    rw [List.length_map, Array.length_toList, (s.chunks.getD c zeroChunk).size_eq]; rfl
  have hjxs0 : j < ((s.chunks.getD c zeroChunk).slots.toList.map leafTag).length := by
    rw [hxs0Len]; exact hj
  have hxs0Get : ((s.chunks.getD c zeroChunk).slots.toList.map leafTag)[j]'hjxs0 =
      leafTag (s.readSlot c j) := by
    rw [List.getElem_map]; apply congrArg leafTag
    unfold AuthenticatedWorldSnapshot.readSlot ChunkData.getSlot
    have hjsz : j < (s.chunks.getD c zeroChunk).slots.size := by
      rw [(s.chunks.getD c zeroChunk).size_eq]; exact hj
    rw [getD_lt _ j 0 hjsz]; simp
  rw [Obend.Polis.foldlM_cons_some]
  refine ⟨(1, s.chunkRoots.getD c ByteArray.empty), ?_, ?_⟩
  · unfold climbStep
    have hsz0 : (((s.chunks.getD c zeroChunk).slots.toList.map leafTag).eraseIdx j).toArray.size = 15 := by
      rw [List.size_toArray, eraseIdx_length_of_lt _ j hjxs0, hxs0Len]
    simp only [hsz0, ↓reduceIte, hnib0, ← hxs0Get]
    rw [insertAt_eraseIdx _ j hjxs0, hcEq c hc]; rfl
  · have hxs1Len : (groupChunkTags s.chunkRoots (c / 16)).length = 16 := by simp [groupChunkTags]
    have hm16 : c % 16 < (groupChunkTags s.chunkRoots (c / 16)).length := by rw [hxs1Len]; omega
    have hxs1Get : (groupChunkTags s.chunkRoots (c / 16))[c % 16]'hm16 =
        s.chunkRoots.getD c ByteArray.empty := by
      rw [groupChunkTags_getElem s.chunkRoots (c / 16) (c % 16) (by omega)]
      have hdivmod : c / 16 * 16 + c % 16 = c := by omega
      rw [hdivmod]
      have hcrLt : c < s.chunkRoots.size := by rw [hrsz]; exact hc
      rw [getD_lt s.chunkRoots c (zeroTreeTag 1) hcrLt, getD_lt s.chunkRoots c ByteArray.empty hcrLt]
    have hglt : c / 16 < numGroups := by unfold numChunks numGroups at *; omega
    rw [Obend.Polis.foldlM_cons_some]
    refine ⟨(2, s.groupRoots.getD (c / 16) ByteArray.empty), ?_, ?_⟩
    · unfold climbStep
      have hsz1 : ((groupChunkTags s.chunkRoots (c / 16)).eraseIdx (c % 16)).toArray.size = 15 := by
        rw [List.size_toArray, eraseIdx_length_of_lt _ (c % 16) hm16, hxs1Len]
      simp only [hsz1, ↓reduceIte, hnib1, ← hxs1Get]
      rw [insertAt_eraseIdx _ (c % 16) hm16, hgEq (c / 16) hglt]; rfl
    · have hxs2Len : s.groupRoots.toList.length = 16 := by rw [Array.length_toList, hgsz]; rfl
      have hgxs2 : c / 16 < s.groupRoots.toList.length := by rw [hxs2Len]; exact hglt
      have hxs2Get : s.groupRoots.toList[c / 16]'hgxs2 =
          s.groupRoots.getD (c / 16) ByteArray.empty := by
        rw [Array.getElem_toList, getD_lt s.groupRoots (c / 16) ByteArray.empty (by rw [hgsz]; exact hglt)]
      rw [Obend.Polis.foldlM_cons_some]
      refine ⟨(3, s.activeRoot), ?_, ?_⟩
      · unfold climbStep
        have hsz2 : (s.groupRoots.toList.eraseIdx (c / 16)).toArray.size = 15 := by
          rw [List.size_toArray, eraseIdx_length_of_lt _ (c / 16) hgxs2, hxs2Len]
        simp only [hsz2, ↓reduceIte, hnib2, ← hxs2Get]
        rw [insertAt_eraseIdx _ (c / 16) hgxs2, hact]
      · rw [hroot]
        exact climb_upper_zeroSpine (slotAddr c j) haddrTot 13 3 s.activeRoot (by decide)

/-! ## 5. $O(1)$ COW Snapshot Forking, Subtree Sharing & Dual-Track Binding -/
/-- Fork `s` in $O(1)$ by bumping `branchGen` while structurally sharing all persistent arrays. -/
def cowForkSnapshot (s : AuthenticatedWorldSnapshot) : AuthenticatedWorldSnapshot :=
  { s with branchGen := s.branchGen + 1 }
/-- Fork `s` and apply a COW update to a single dirty chunk `c < 256` (`O(\log K)` hashes). -/
def cowUpdateChunk (pp : AjtaiParams) (hCols : pp.cols = 64)
    (s : AuthenticatedWorldSnapshot) (c : Nat) (hc : c < numChunks)
    (newChunk : ChunkData) : AuthenticatedWorldSnapshot :=
  updateChunkVerkleRoot pp hCols (cowForkSnapshot s) c hc newChunk
/-- Rebind a pre-branch slot opening's level-0 intra-chunk sibling witness (`prePath[0]`) onto
    `postBranch`'s updated upper spine (`levels 1..15`) without reading `postBranch.chunks[c']`. -/
def rebindPreBranchChunkOpening (prePath : Array (Array ByteArray))
    (postBranch : AuthenticatedWorldSnapshot) (c' : Nat) : Array (Array ByteArray) :=
  let sib0 := prePath.getD 0 #[]
  let sib1 := ((groupChunkTags postBranch.chunkRoots (c' / 16)).eraseIdx (c' % 16)).toArray
  let sib2 := (postBranch.groupRoots.toList.eraseIdx (c' / 16)).toArray
  let upper := (List.range 13).map fun k => Array.replicate 15 (zeroTreeTag (3 + k))
  (sib0 :: sib1 :: sib2 :: upper).toArray
/-- Every sibling tag at every level of `path` has arity `15` and exact byte width `32`. -/
def checkWellSizedVerklePath (path : Array (Array ByteArray)) : Bool :=
  path.size == 16 &&
  path.toList.all fun sibs => sibs.size == 15 && sibs.toList.all fun b => b.size == 32

/-- Two distinct bounded preimages under one `tagOf` are a named `treeHash` collision. -/
private def mkTagCollision {p q : List UInt8} (hp : p.length ≤ verkleMaxPreimageBytes)
    (hq : q.length ≤ verkleMaxPreimageBytes) (hne : p ≠ q) (h : tagOf p = tagOf q) :
    HashCollisionWitness treeHash verkleMaxPreimageBytes where
  msgA := p
  msgB := q
  lenA := hp
  lenB := hq
  distinct := hne
  sameDigest := by
    have hl : (tagOf p).data.toList = (tagOf q).data.toList := congrArg (fun b => b.data.toList) h
    simp only [tagOf, cshake32ByteArray, Obend.Digest.Cshake256.Native.bytesOfList_toList] at hl
    exact congrArg ofBE hl

/-- Snapshot-root header preimage: tag byte `2` (leaves are `0`, nodes `1`), then the length-framed
    8-byte chunk count and the length-framed 32-byte `VerkleUmem` root. -/
def snapshotRootPreimage (n : Nat) (verkleRoot : ByteArray) : List UInt8 :=
  2 :: encodeFields [be 8 n, verkleRoot.data.toList]

/-- The snapshot root: the chunk count `n` and the Verkle root under one `treeHash` tag. -/
def snapshotRootTag (n : Nat) (verkleRoot : ByteArray) : ByteArray :=
  tagOf (snapshotRootPreimage n verkleRoot)

/-- The snapshot root of `s`, committing to its own chunk count. -/
def AuthenticatedWorldSnapshot.snapshotRoot (s : AuthenticatedWorldSnapshot) : ByteArray :=
  snapshotRootTag s.chunks.size s.verkleRoot
theorem snapshotRootPreimage_injective {n₁ n₂ : Nat} {r₁ r₂ : ByteArray}
    (hn₁ : n₁ < 2 ^ 64) (hn₂ : n₂ < 2 ^ 64)
    (h : snapshotRootPreimage n₁ r₁ = snapshotRootPreimage n₂ r₂) : n₁ = n₂ ∧ r₁ = r₂ := by
  simp only [snapshotRootPreimage, List.cons.injEq, true_and] at h
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  exact ⟨Obend.Digest.HashBytes.be_injective (h8 ▸ hn₁) (h8 ▸ hn₂) hf.1,
    (List.cons.inj (map_toList_injective [r₁] [r₂] (congrArg (fun x => [x]) hf.2))).1⟩

/-- **Snapshot-Root Binding (`0 Classical`)**: equal snapshot roots commit to the same chunk count
    and Verkle root, or their two header preimages are a named `treeHash` collision. -/
def extractSnapshotRootBreak {n₁ n₂ : Nat} {r₁ r₂ : ByteArray}
    (hn₁ : n₁ < 2 ^ 64) (hn₂ : n₂ < 2 ^ 64) (hr₁ : r₁.size = 32) (hr₂ : r₂.size = 32)
    (h : snapshotRootTag n₁ r₁ = snapshotRootTag n₂ r₂) :
    PSum (n₁ = n₂ ∧ r₁ = r₂) (HashCollisionWitness treeHash verkleMaxPreimageBytes) :=
  have hlen : ∀ (n : Nat) (r : ByteArray), r.size = 32 →
      (snapshotRootPreimage n r).length ≤ verkleMaxPreimageBytes := by
    intro n r hr
    have hr' : r.data.toList.length = 32 := by rw [Array.length_toList]; exact hr
    have h8 : (leb128 8).length = 1 := by decide
    have h32 : (leb128 32).length = 1 := by decide
    simp [snapshotRootPreimage, encodeFields, encodeListField, hr', h8, h32, verkleMaxPreimageBytes]
  if heq : n₁ = n₂ ∧ r₁ = r₂ then .inl heq
  else .inr (mkTagCollision (hlen n₁ r₁ hr₁) (hlen n₂ r₂ hr₂)
    (fun hp => heq (snapshotRootPreimage_injective hn₁ hn₂ hp)) h)

/-- Stateless dual-authenticated opening of slot `(c, j)` against `(snapshotRoot, ajtaiChunkRoot)`:
    the chunk's slots, the Verkle path, and the opened snapshot-root header `(chunkCount, verkleRoot)`. -/
structure DualChunkSlotOpening where
  chunkSlotsList : List UInt64
  verklePath : Array (Array ByteArray)
  chunkCount : Nat
  verkleRoot : ByteArray
  deriving DecidableEq

/-- Stateless dual verifier: chunk membership, well-sized Verkle path, Ajtai syndrome, the opened
    snapshot-root header, and the index bound `c < chunkCount` with `16 * chunkCount ≤ 2^64`, so
    `slotAddr c j` never wraps (an index `c + 2^60` is refused, not aliased to `c`). -/
def verifyDualChunkOpening (pp : AjtaiParams) (hCols : pp.cols = 64)
    (snapshotRoot : ByteArray) (ajtaiRoot : List Int)
    (c j : Nat) (val : UInt64) (w : DualChunkSlotOpening) : Bool :=
  if hlen : w.chunkSlotsList.length = 16 then
    if hj : j < 16 then
      let hw : (wordsToLimbs w.chunkSlotsList).length = pp.cols := by
        rw [wordsToLimbs_length, hlen, hCols]
      ((w.chunkSlotsList[j]'(by omega) == val) &&
       checkWellSizedVerklePath w.verklePath &&
       verifyOpening w.verkleRoot (slotAddr c j) val w.verklePath &&
       decide (ajtaiCommit pp (wordsToLimbs w.chunkSlotsList) hw = ajtaiRoot)) &&
      (decide (c < w.chunkCount) && decide (chunkSlots * w.chunkCount ≤ 2 ^ 64) &&
       w.verkleRoot.size == 32 &&
       decide (snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot))
    else false
  else false
/-- Produce the honest `DualChunkSlotOpening` for slot `(c, j)` of `s`. -/
def openDualSnapshotSlot (s : AuthenticatedWorldSnapshot) (c j : Nat) : DualChunkSlotOpening where
  chunkSlotsList := (s.chunks.getD c zeroChunk).slots.toList
  verklePath := openSnapshotSlot s c j
  chunkCount := s.chunks.size
  verkleRoot := s.verkleRoot
private theorem all_32_of_eraseIdx : ∀ (xs : List ByteArray) (n : Nat),
    (∀ b ∈ xs, b.size = 32) → ∀ b ∈ xs.eraseIdx n, b.size = 32
  | [], _, _, _, hm => by cases hm
  | _ :: xs, 0, h, b, hb => h b (.tail _ hb)
  | y :: xs, n + 1, h, b, hb => by
    rcases List.mem_cons.1 hb with heq | hb'
    · rw [heq]; exact h y (.head _)
    · exact all_32_of_eraseIdx xs n (fun z hz => h z (.tail _ hz)) b hb'
theorem openDualSnapshotSlot_valid {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    {c j : Nat} (hc : c < numChunks) (hj : j < chunkSlots) :
    verifyDualChunkOpening pp hCols s.snapshotRoot (s.ajtaiChunkRoots.getD c [])
      c j (s.readSlot c j) (openDualSnapshotSlot s c j) = true := by
  have hopen := openSnapshotSlot_valid hwf hc hj
  have hroot32 : s.verkleRoot.size = 32 := by
    rw [snapshotWF_verkleRoot_eq_fullCommit hwf]; exact fullVerkleCommitChunks_size _
  obtain ⟨hcsz, hrsz, hgsz, _, hcEq, hgEq, _, _, haEq⟩ := hwf
  unfold verifyDualChunkOpening openDualSnapshotSlot AuthenticatedWorldSnapshot.snapshotRoot
  have hlen16 : ((s.chunks.getD c zeroChunk).slots.toList).length = 16 := by
    rw [Array.length_toList, (s.chunks.getD c zeroChunk).size_eq]; rfl
  have hj16 : j < 16 := hj
  simp only [hlen16, hj16, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, hopen⟩, ?_⟩, ⟨⟨hcsz ▸ hc, by rw [hcsz]; decide⟩, hroot32⟩, trivial⟩
  · unfold AuthenticatedWorldSnapshot.readSlot ChunkData.getSlot
    have hjsz : j < (s.chunks.getD c zeroChunk).slots.size := by
      rw [(s.chunks.getD c zeroChunk).size_eq]; exact hj
    rw [getD_lt _ j 0 hjsz]; simp
  · unfold checkWellSizedVerklePath openSnapshotSlot
    simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray, List.length_cons,
      List.length_map, List.length_range, List.all_cons, List.all_eq_true]
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [eraseIdx_length_of_lt _ j (by rw [List.length_map, hlen16]; exact hj16),
            List.length_map, hlen16]
      · intro b hb
        apply all_32_of_eraseIdx ((s.chunks.getD c zeroChunk).slots.toList.map leafTag) j _ b hb
        intro y hy; obtain ⟨_, _, rfl⟩ := List.mem_map.1 hy; exact leafTag_size _
    · refine ⟨?_, ?_⟩
      · rw [eraseIdx_length_of_lt _ (c % 16) (by simp [groupChunkTags]; omega)]
        simp [groupChunkTags]
      · intro b hb
        apply all_32_of_eraseIdx (groupChunkTags s.chunkRoots (c / 16)) (c % 16) _ b hb
        intro y hy; unfold groupChunkTags at hy
        obtain ⟨d, _, rfl⟩ := List.mem_map.1 hy
        by_cases hlt : c / 16 * 16 + d < s.chunkRoots.size
        · have hclt : c / 16 * 16 + d < numChunks := by rw [← hrsz]; exact hlt
          rw [getD_lt s.chunkRoots _ (zeroTreeTag 1) hlt,
              ← getD_lt s.chunkRoots _ ByteArray.empty hlt, hcEq _ hclt]
          exact chunkSubtreeTag_size _
        · unfold Array.getD; simp [hlt, zeroTreeTag_size]
    · refine ⟨?_, ?_⟩
      · have hgLen : s.groupRoots.toList.length = 16 := by rw [Array.length_toList, hgsz]; rfl
        have hglt : c / 16 < 16 := by unfold numChunks at hc; omega
        rw [eraseIdx_length_of_lt _ (c / 16) (by rw [hgLen]; exact hglt), hgLen]
      · intro b hb
        apply all_32_of_eraseIdx s.groupRoots.toList (c / 16) _ b hb
        intro y hy
        obtain ⟨g, hg, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hy)
        have hglt : g < numGroups := by rw [← hgsz]; exact hg
        rw [← getD_lt s.groupRoots g ByteArray.empty hg, hgEq g hglt]
        exact nodeTag_size _
    · intro sibs hsibs
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hsibs
      refine ⟨by simp, ?_⟩
      intro b hb
      have hb' : b = zeroTreeTag (3 + k) := by simpa [Array.toList_replicate] using hb
      rw [hb']; exact zeroTreeTag_size _
  · rw [haEq c hc]; rfl
private theorem encodeFields_32_length : ∀ (children : List ByteArray),
    (∀ b ∈ children, b.size = 32) →
    (encodeFields (children.map fun b => b.data.toList)).length = 33 * children.length
  | [], _ => rfl
  | b :: bs, hall => by
    have hb32 : b.data.toList.length = 32 := by rw [Array.length_toList]; exact hall b (.head _)
    have hleb32 : (leb128 32).length = 1 := by decide
    have ih := encodeFields_32_length bs (fun y hy => hall y (.tail _ hy))
    simp only [encodeFields, List.map_cons, List.flatMap_cons, encodeListField,
      List.length_append, hb32, hleb32, List.length_cons]
    change 1 + 32 + (encodeFields (bs.map fun x => x.data.toList)).length = 33 * (bs.length + 1)
    omega
private theorem nodePreimage_16_32_length {children : List ByteArray}
    (hlen : children.length = 16) (hall : ∀ b ∈ children, b.size = 32) :
    (nodePreimage children).length = verkleMaxPreimageBytes := by
  unfold nodePreimage verkleMaxPreimageBytes
  simp only [List.length_cons, encodeFields_32_length children hall, hlen]
private theorem insertAt_15_length_and_32 (n : Nat) {cur : ByteArray} {sibs : List ByteArray}
    (hcur : cur.size = 32) (hsibsLen : sibs.length = 15) (hsibs32 : ∀ b ∈ sibs, b.size = 32) :
    (insertAt n cur sibs).length = 16 ∧ ∀ b ∈ insertAt n cur sibs, b.size = 32 := by
  unfold insertAt
  refine ⟨?_, ?_⟩
  · have htd : (sibs.take n).length + (sibs.drop n).length = sibs.length := by
      rw [← List.length_append, List.take_append_drop]
    simp only [List.length_append, List.length_cons]; omega
  · intro b hb
    rcases List.mem_append.1 hb with hb1 | hb2
    · exact hsibs32 b (List.mem_of_mem_take hb1)
    · rcases List.mem_cons.1 hb2 with rfl | hb3
      · exact hcur
      · exact hsibs32 b (List.mem_of_mem_drop hb3)
private def mkNodeCollisionWitness (n : Nat) {c₁ c₂ : ByteArray} {s₁ s₂ : Array ByteArray}
    (hc1 : c₁.size = 32) (hc2 : c₂.size = 32)
    (hw1 : s₁.size = 15 ∧ ∀ b ∈ s₁.toList, b.size = 32)
    (hw2 : s₂.size = 15 ∧ ∀ b ∈ s₂.toList, b.size = 32) (hne : c₁ ≠ c₂)
    (htag : nodeTag (insertAt n c₁ s₁.toList) = nodeTag (insertAt n c₂ s₂.toList)) :
    HashCollisionWitness treeHash verkleMaxPreimageBytes :=
  mkTagCollision
    (by obtain ⟨hl, ha⟩ := insertAt_15_length_and_32 n hc1 (by rw [Array.length_toList, hw1.1]) hw1.2
        exact Nat.le_of_eq (nodePreimage_16_32_length hl ha))
    (by obtain ⟨hl, ha⟩ := insertAt_15_length_and_32 n hc2 (by rw [Array.length_toList, hw2.1]) hw2.2
        exact Nat.le_of_eq (nodePreimage_16_32_length hl ha))
    (by intro hpre; simp only [nodePreimage, List.cons.injEq, true_and] at hpre
        have hch := map_toList_injective _ _ (encodeFields_injective _ _ hpre)
        have hszEq : s₁.toList.length = s₂.toList.length := by
          rw [Array.length_toList, Array.length_toList, hw1.1, hw2.1]
        exact hne (insertAt_inj hszEq hch).1)
    htag
private theorem climbStep_tail_some {addr : UInt64} {lvl : Nat} {c : ByteArray}
    {s : Array ByteArray} {t : List (Array ByteArray)} {out : Nat × ByteArray}
    (h : List.foldlM (climbStep addr) (lvl, c) (s :: t) = some out) :
    List.foldlM (climbStep addr)
      (lvl + 1, nodeTag (insertAt (nibbleAt addr lvl) c s.toList)) t = some out := by
  obtain ⟨_, hs, hr⟩ := (Obend.Polis.foldlM_cons_some _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := Obend.Polis.climbStep_eq_some hs
  exact hr

/-- Constructive (`0 Classical`) climb collision extractor over 32-byte well-sized sibling paths. -/
private def extractClimbCollision (addr : UInt64) : ∀ (p₁ p₂ : List (Array ByteArray)) (lvl : Nat)
      (c₁ c₂ : ByteArray) (out₁ out₂ : Nat × ByteArray),
      p₁.length = p₂.length → c₁.size = 32 → c₂.size = 32 →
      (∀ s ∈ p₁, s.size = 15 ∧ ∀ b ∈ s.toList, b.size = 32) →
      (∀ s ∈ p₂, s.size = 15 ∧ ∀ b ∈ s.toList, b.size = 32) →
      List.foldlM (climbStep addr) (lvl, c₁) p₁ = some out₁ →
      List.foldlM (climbStep addr) (lvl, c₂) p₂ = some out₂ →
      out₁.2 = out₂.2 → c₁ ≠ c₂ →
      HashCollisionWitness treeHash verkleMaxPreimageBytes
  | [], [], lvl, c₁, c₂, out₁, out₂, _, _, _, _, _, h₁, h₂, hout, hne =>
    False.elim (by
      have e₁ : some (lvl, c₁) = some out₁ := h₁
      have e₂ : some (lvl, c₂) = some out₂ := h₂
      cases e₁; cases e₂; exact hne hout)
  | [], _ :: _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => False.elim (by simp at hlen)
  | _ :: _, [], _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => False.elim (by simp at hlen)
  | s₁ :: t₁, s₂ :: t₂, lvl, c₁, c₂, out₁, out₂, hlen, hc1, hc2, hw1, hw2, h₁, h₂, hout, hne =>
    if htag : nodeTag (insertAt (nibbleAt addr lvl) c₁ s₁.toList) =
              nodeTag (insertAt (nibbleAt addr lvl) c₂ s₂.toList) then
      mkNodeCollisionWitness (nibbleAt addr lvl) hc1 hc2
        (hw1 s₁ (.head _)) (hw2 s₂ (.head _)) hne htag
    else
      extractClimbCollision addr t₁ t₂ (lvl + 1)
        (nodeTag (insertAt (nibbleAt addr lvl) c₁ s₁.toList))
        (nodeTag (insertAt (nibbleAt addr lvl) c₂ s₂.toList))
        out₁ out₂ (Nat.succ.inj hlen) (nodeTag_size _) (nodeTag_size _)
        (fun s hs => hw1 s (.tail _ hs)) (fun s hs => hw2 s (.tail _ hs))
        (climbStep_tail_some h₁) (climbStep_tail_some h₂) hout htag
private theorem foldlM_climbStep_fst (addr : UInt64) :
    ∀ (ps : List (Array ByteArray)) (lvl : Nat) (cur : ByteArray) (out : Nat × ByteArray),
      List.foldlM (climbStep addr) (lvl, cur) ps = some out → out.1 = lvl + ps.length
  | [], lvl, cur, out, h => by have e : some (lvl, cur) = some out := h; cases e; simp
  | _ :: t, lvl, _, out, h => by
    have ih := foldlM_climbStep_fst addr t (lvl + 1) _ out (climbStep_tail_some h)
    simp only [List.length_cons]; omega
private theorem verifyOpening_some16 {root : ByteArray} {addr val : UInt64}
    {path : Array (Array ByteArray)} (h : verifyOpening root addr val path = true) :
    path.size = 16 ∧
    List.foldlM (climbStep addr) (0, leafTag val) path.toList = some (16, root) := by
  obtain ⟨hsz, n, hc⟩ := (Obend.Polis.verifyOpening_iff root addr val path).1 h
  unfold climb at hc; rw [← Array.foldlM_toList] at hc
  have hn := foldlM_climbStep_fst addr path.toList 0 (leafTag val) (n, root) hc
  simp only [Nat.zero_add, Array.length_toList, hsz] at hn
  subst hn; exact ⟨hsz, hc⟩
private theorem verifyDualChunkOpening_props {pp : AjtaiParams} {hCols : pp.cols = 64}
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v : UInt64} {w : DualChunkSlotOpening}
    (hv : verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v w = true) :
    w.chunkSlotsList.length = 16 ∧
    j < 16 ∧
    w.chunkSlotsList.getD j 0 = v ∧
    checkWellSizedVerklePath w.verklePath = true ∧
    verifyOpening w.verkleRoot (slotAddr c j) v w.verklePath = true ∧
    (c < w.chunkCount ∧ chunkSlots * w.chunkCount ≤ 2 ^ 64 ∧ w.verkleRoot.size = 32 ∧
      snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot) ∧
    ∃ hw : (wordsToLimbs w.chunkSlotsList).length = pp.cols,
      ajtaiCommit pp (wordsToLimbs w.chunkSlotsList) hw = ajtaiRoot := by
  unfold verifyDualChunkOpening at hv
  by_cases hlen : w.chunkSlotsList.length = 16
  · by_cases hj : j < 16
    · simp only [hlen, hj, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      have hget : w.chunkSlotsList.getD j 0 = v := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact hv.1.1.1.1
      exact ⟨hlen, hj, hget, hv.1.1.1.2, hv.1.1.2,
        ⟨hv.2.1.1.1, hv.2.1.1.2, hv.2.1.2, hv.2.2⟩,
        ⟨by rw [wordsToLimbs_length, hlen, hCols], hv.1.2⟩⟩
    · simp [hlen, hj] at hv
  · simp [hlen] at hv

/-- What an accepted dual opening establishes about its opened snapshot-root header. -/
theorem verifyDualChunkOpening_header {pp : AjtaiParams} {hCols : pp.cols = 64}
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v : UInt64} {w : DualChunkSlotOpening} :
    verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v w = true →
    c < w.chunkCount ∧ chunkSlots * w.chunkCount ≤ 2 ^ 64 ∧ w.verkleRoot.size = 32 ∧
    snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot :=
  fun hv => (verifyDualChunkOpening_props hv).2.2.2.2.2.1

/-- **No `UInt64` Wraparound (`verifyDualChunkOpening_addr_exact`)**: the key an accepted opening
    authenticates is exactly `16 * c + j`; no other chunk index shares it modulo `2^64`. -/
theorem verifyDualChunkOpening_addr_exact {pp : AjtaiParams} {hCols : pp.cols = 64}
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v : UInt64} {w : DualChunkSlotOpening} :
    verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v w = true →
    (slotAddr c j).toNat = c * chunkSlots + j := fun hv =>
  have hh := verifyDualChunkOpening_header hv
  slotAddr_toNat_of_bound hh.1 hh.2.1 (verifyDualChunkOpening_props hv).2.1

/-- **Chunk Index Bound (`0 Classical`)**: an opening accepted against a well-formed `s.snapshotRoot`
    addresses a real chunk (`c < 256`) under `s.verkleRoot`, or the two headers collide. -/
def extractSnapshotIndexBreak {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    {ajtaiRoot : List Int} {c j : Nat} {v : UInt64} {w : DualChunkSlotOpening}
    (hv : verifyDualChunkOpening pp hCols s.snapshotRoot ajtaiRoot c j v w = true) :
    PSum (c < numChunks ∧ w.verkleRoot = s.verkleRoot)
      (HashCollisionWitness treeHash verkleMaxPreimageBytes) :=
  have hh := verifyDualChunkOpening_header hv
  have hroot32 : s.verkleRoot.size = 32 := by
    rw [snapshotWF_verkleRoot_eq_fullCommit hwf]; exact fullVerkleCommitChunks_size _
  match extractSnapshotRootBreak (by have := hh.2.1; unfold chunkSlots at this; omega)
      (by rw [hwf.1]; decide) hh.2.2.1 hroot32 hh.2.2.2 with
  | .inl heq => .inl ⟨by have := hh.1; rw [heq.1, hwf.1] at this; exact this, heq.2⟩
  | .inr col => .inr col

/-- **Constructive Dual-Opening Extractor (`0 Classical`)**: two accepted dual openings of slot
    `(c, j)` under one snapshot root agree on the value, or exhibit **both** a bounded `cSHAKE256`
    `HashCollisionWitness` (`≤ 529` bytes) **and** a short `SISShortVecWitness` (`‖z‖_∞ ≤ 131070`). -/
def extractDualChunkOpeningBreak (pp : AjtaiParams) (hCols : pp.cols = 64)
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v₁ v₂ : UInt64} {w₁ w₂ : DualChunkSlotOpening}
    (hv₁ : verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v₁ w₁ = true)
    (hv₂ : verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v₂ w₂ = true) :
    PSum (v₁ = v₂) (HashCollisionWitness treeHash verkleMaxPreimageBytes ×
       SISShortVecWitness pp.modulus 131070 pp.matrix) :=
  if heq : v₁ = v₂ then .inl heq
  else
    .inr (
      let p₁ := verifyDualChunkOpening_props hv₁
      let p₂ := verifyDualChunkOpening_props hv₂
      let q₁ := verifyDualChunkOpening_header hv₁
      let q₂ := verifyDualChunkOpening_header hv₂
      let hw1 : HashCollisionWitness treeHash verkleMaxPreimageBytes :=
        match extractSnapshotRootBreak (by have := q₁.2.1; unfold chunkSlots at this; omega)
            (by have := q₂.2.1; unfold chunkSlots at this; omega) q₁.2.2.1 q₂.2.2.1
            (q₁.2.2.2.trans q₂.2.2.2.symm) with
        | .inr col => col
        | .inl hhdr =>
        if hleaf : leafTag v₁ = leafTag v₂ then
          mkTagCollision (by simp [leafPreimage, verkleMaxPreimageBytes])
            (by simp [leafPreimage, verkleMaxPreimageBytes])
            (by intro hp; simp only [leafPreimage, List.cons.injEq, true_and] at hp
                have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
                exact heq (UInt64.toNat_inj.1
                  (Obend.Digest.HashBytes.be_injective (h8 ▸ v₁.toNat_lt) (h8 ▸ v₂.toNat_lt) hp)))
            hleaf
        else
          let op₁ := verifyOpening_some16 p₁.2.2.2.2.1
          let op₂ := verifyOpening_some16 (hhdr.2 ▸ p₂.2.2.2.2.1)
          have hwsProp : ∀ {p : Array (Array ByteArray)}, checkWellSizedVerklePath p = true →
              ∀ s ∈ p.toList, s.size = 15 ∧ ∀ b ∈ s.toList, b.size = 32 := by
            intro p hp s hs; unfold checkWellSizedVerklePath at hp
            simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp
            exact hp.2 s hs
          extractClimbCollision (slotAddr c j) w₁.verklePath.toList w₂.verklePath.toList 0
            (leafTag v₁) (leafTag v₂) (16, w₁.verkleRoot) (16, w₁.verkleRoot)
            (by rw [Array.length_toList, Array.length_toList, op₁.1, op₂.1])
            (leafTag_size v₁) (leafTag_size v₂)
            (hwsProp p₁.2.2.2.1) (hwsProp p₂.2.2.2.1) op₁.2 op₂.2 rfl hleaf
      let hw2 : SISShortVecWitness pp.modulus 131070 pp.matrix :=
        have huLen : (wordsToLimbs w₁.chunkSlotsList).length = pp.cols := by
          rw [wordsToLimbs_length, p₁.1, hCols]
        have hvLen : (wordsToLimbs w₂.chunkSlotsList).length = pp.cols := by
          rw [wordsToLimbs_length, p₂.1, hCols]
        have hneLimbs : wordsToLimbs w₁.chunkSlotsList ≠ wordsToLimbs w₂.chunkSlotsList := by
          intro hl; have hlEq := wordsToLimbs_injective hl
          apply heq; rw [← p₁.2.2.1, ← p₂.2.2.1, hlEq]
        extractShortDiffSISWitness pp
          (wordsToLimbs w₁.chunkSlotsList) (wordsToLimbs w₂.chunkSlotsList)
          huLen hvLen
          (wordsToLimbs_short w₁.chunkSlotsList) (wordsToLimbs_short w₂.chunkSlotsList)
          hneLimbs (by
            obtain ⟨_, h₁⟩ := p₁.2.2.2.2.2.2
            obtain ⟨_, h₂⟩ := p₂.2.2.2.2.2.2
            exact h₁.trans h₂.symm)
      (hw1, hw2))

/-- **Headline Theorem 2**: after a COW fork updating dirty chunk `c < 256`, (1) every chunk
    `c' ≠ c` shares its `ChunkData`, subtree tag, Ajtai commitment and rebound level-0 openings
    without rehashing; (2) two accepted dual openings of any slot against the branch's snapshot
    root agree, or break both `BoundedCollision treeHash 529` and `ModuleSISHard pp 131070`. -/
theorem cowBranch_shares_unchanged_verkleSubtrees {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    (c : Nat) (hc : c < numChunks) (newChunk : ChunkData) :
    let branched := cowUpdateChunk pp hCols s c hc newChunk
    SnapshotWF pp hCols branched ∧
    branched.branchGen = s.branchGen + 1 ∧
    (∀ c' : Nat, c' < numChunks → c' ≠ c →
      branched.chunks.getD c' zeroChunk = s.chunks.getD c' zeroChunk ∧
      branched.chunkRoots.getD c' ByteArray.empty = s.chunkRoots.getD c' ByteArray.empty ∧
      branched.ajtaiChunkRoots.getD c' [] = s.ajtaiChunkRoots.getD c' [] ∧
      ∀ j : Nat, j < chunkSlots →
        rebindPreBranchChunkOpening (openSnapshotSlot s c' j) branched c' =
          openSnapshotSlot branched c' j ∧
        verifyOpening branched.verkleRoot (slotAddr c' j) (s.readSlot c' j)
          (rebindPreBranchChunkOpening (openSnapshotSlot s c' j) branched c') = true) ∧
    (∀ (c'' j : Nat), c'' < numChunks → ∀ (v₁ v₂ : UInt64) (w₁ w₂ : DualChunkSlotOpening),
        verifyDualChunkOpening pp hCols branched.snapshotRoot
          (branched.ajtaiChunkRoots.getD c'' []) c'' j v₁ w₁ = true →
        verifyDualChunkOpening pp hCols branched.snapshotRoot
          (branched.ajtaiChunkRoots.getD c'' []) c'' j v₂ w₂ = true →
        v₁ = v₂ ∨
          (BoundedCollision treeHash verkleMaxPreimageBytes ∧ ¬ ModuleSISHard pp 131070)) := by
  have hwfFork : SnapshotWF pp hCols (cowForkSnapshot s) := hwf
  have hwfB : SnapshotWF pp hCols (cowUpdateChunk pp hCols s c hc newChunk) :=
    updateChunkVerkleRoot_wf hwfFork c hc newChunk
  refine ⟨hwfB, rfl, ?_, ?_⟩
  · intro c' hc' hne
    have hchEq : (cowUpdateChunk pp hCols s c hc newChunk).chunks.getD c' zeroChunk =
        s.chunks.getD c' zeroChunk :=
      getD_setIfInBounds_ne s.chunks c c' newChunk zeroChunk hne
    have hcrEq : (cowUpdateChunk pp hCols s c hc newChunk).chunkRoots.getD c' ByteArray.empty =
        s.chunkRoots.getD c' ByteArray.empty :=
      getD_setIfInBounds_ne s.chunkRoots c c' _ ByteArray.empty hne
    have harEq : (cowUpdateChunk pp hCols s c hc newChunk).ajtaiChunkRoots.getD c' [] =
        s.ajtaiChunkRoots.getD c' [] :=
      getD_setIfInBounds_ne s.ajtaiChunkRoots c c' _ [] hne
    refine ⟨hchEq, hcrEq, harEq, ?_⟩
    intro j hj
    have hrebind : rebindPreBranchChunkOpening (openSnapshotSlot s c' j)
        (cowUpdateChunk pp hCols s c hc newChunk) c' =
        openSnapshotSlot (cowUpdateChunk pp hCols s c hc newChunk) c' j := by
      unfold rebindPreBranchChunkOpening openSnapshotSlot; rw [hchEq]; rfl
    have hslotEq : (cowUpdateChunk pp hCols s c hc newChunk).readSlot c' j = s.readSlot c' j := by
      unfold AuthenticatedWorldSnapshot.readSlot; rw [hchEq]
    refine ⟨hrebind, ?_⟩
    rw [hrebind, ← hslotEq]; exact openSnapshotSlot_valid hwfB hc' hj
  · intro c'' j _ v₁ v₂ w₁ w₂ hv₁ hv₂
    cases extractDualChunkOpeningBreak pp hCols hv₁ hv₂ with
    | inl heq => exact .inl heq
    | inr hpair => exact .inr ⟨⟨hpair.1⟩, fun hHard => hHard ⟨hpair.2⟩⟩

/-! ## 6. Crash-Safe Torn-Write WAL Recovery Idempotence & Multi-Epoch `ValidSnapshotTrace` -/

private theorem unbe_take32_lt_bound (s : Log.Bytes) : Log.unbe (s.take 32) < Log.bound := by
  unfold Log.bound
  exact Nat.lt_of_lt_of_le (Log.unbe_lt (s.take 32))
    (Nat.pow_le_pow_right (by decide) (List.length_take_le 32 s))

/-- Every `OBL1` record accepted by `Log.parseOne` is automatically well-formed (`Record.WF Hb`). -/
theorem parseOne_ok_wf (Hb : Log.Bytes → Log.Bytes) {prev : Option Nat}
    {bs rest : Log.Bytes} {r : Log.Record}
    (h : Log.parseOne Hb prev bs = .ok (r, rest)) : r.WF Hb := by
  have heff := (Log.parseOne_ok_inv Hb h).2.1
  unfold Log.parseOne at h
  cases e1 : Log.takeN 136 bs with
  | none => rw [e1] at h; cases h
  | some x =>
    obtain ⟨hd, tl⟩ := x
    rw [e1] at h; dsimp only at h
    split at h
    · cases h
    · cases e2 : Log.takeN (Log.unbe ((hd.drop 4).take 4) + 32) tl with
      | none => rw [e2] at h; cases h
      | some y =>
        obtain ⟨bd, tl'⟩ := y
        rw [e2] at h; dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h
              refine ⟨unbe_take32_lt_bound _, unbe_take32_lt_bound _, unbe_take32_lt_bound _, heff, ?_⟩
              have hlen4 : Log.unbe ((hd.drop 4).take 4) < 256 ^ 4 :=
                Nat.lt_of_lt_of_le (Log.unbe_lt ((hd.drop 4).take 4))
                  (Nat.pow_le_pow_right (by decide) (List.length_take_le 4 _))
              exact Nat.lt_of_le_of_lt (List.length_take_le _ _) hlen4

/-- Every record parsed from any raw byte sequence by `Log.parseFrom` satisfies `Record.WF Hb`. -/
theorem parseFrom_wf (Hb : Log.Bytes → Log.Bytes) (prev : Nat) (bs : Log.Bytes) :
    ∀ r ∈ (Log.parseFrom Hb prev bs).1, r.WF Hb := by
  induction h : bs.length using Nat.strongRecOn generalizing prev bs with
  | ind n ih =>
    by_cases hne : bs = []
    · subst hne; simp [Log.parseFrom_nil]
    · cases hp : Log.parseOne Hb (some prev) bs with
      | error d => rw [Log.parseFrom_error Hb hne hp]; simp
      | ok x =>
        obtain ⟨r, rest⟩ := x; rw [Log.parseFrom_ok Hb hp]
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact parseOne_ok_wf Hb hp
        · exact ih rest.length (h ▸ Log.parseOne_rest Hb hp) (Log.Hr Hb r.receipt) rest rfl y hy'

/-- **Open-World WAL Frame Filter Completeness (`walDrop_complete_iff_invalid_frame`)**:
    `Log.parseFrom` drops a non-empty suffix iff `Log.parseOne` rejects it at the ending anchor. -/
theorem walDrop_complete_iff_invalid_frame (Hb : Log.Bytes → Log.Bytes) (prev : Nat) (bs : Log.Bytes) :
    let parsed := Log.parseFrom Hb prev bs
    parsed.2.1 ≠ [] ↔ ∃ d : Log.Drop, parsed.2.2 = some d ∧
      Log.parseOne Hb (some (Log.lastHash Hb prev parsed.1)) parsed.2.1 = .error d := by
  induction h : bs.length using Nat.strongRecOn generalizing prev bs with
  | ind n ih =>
    by_cases hne : bs = []
    · subst hne; simp [Log.parseFrom_nil]
    · cases hp : Log.parseOne Hb (some prev) bs with
      | error d => rw [Log.parseFrom_error Hb hne hp]; simp [Log.lastHash, hne, hp]
      | ok x =>
        obtain ⟨r, rest⟩ := x
        have ih' := ih rest.length (h ▸ Log.parseOne_rest Hb hp) (Log.Hr Hb r.receipt) rest rfl
        rw [Log.parseFrom_ok Hb hp]; simpa [Log.lastHash] using ih'

/-- Trailing WAL bytes lacking a valid linked commit frame at `anchor`. -/
@[expose] def UncommittedWalTail (Hb : Log.Bytes → Log.Bytes) (anchor : Nat)
    (tail : Log.Bytes) : Prop :=
  tail = [] ∨ ∃ d : Log.Drop, Log.parseOne Hb (some anchor) tail = .error d

/-- Any proper byte prefix `(encodeRecord Hb r).take k` satisfies `UncommittedWalTail`. -/
theorem tornRecordPrefix_is_uncommitted (Hb : Log.Bytes → Log.Bytes) (anchor : Nat)
    {r : Log.Record} (hwf : r.WF Hb) {k : Nat} (hk : k < (Log.encodeRecord Hb r).length) :
    UncommittedWalTail Hb anchor ((Log.encodeRecord Hb r).take k) := by
  by_cases hk0 : k = 0
  · subst hk0; exact .inl rfl
  · exact .inr ⟨.torn, Log.parseOne_torn Hb hwf (List.take_append_drop k _)
      (by rw [Ne, List.drop_eq_nil_iff]; omega)⟩
theorem parseFrom_uncommittedWalTail (Hb : Log.Bytes → Log.Bytes) (anchor : Nat)
    {tail : Log.Bytes} (hu : UncommittedWalTail Hb anchor tail) :
    (Log.parseFrom Hb anchor tail).1 = [] ∧ (Log.parseFrom Hb anchor tail).2.1 = tail := by
  rcases hu with rfl | ⟨d, hd⟩
  · simp [Log.parseFrom_nil]
  · by_cases hne : tail = []
    · subst hne; simp [Log.parseFrom_nil]
    · rw [Log.parseFrom_error Hb hne hd]; exact ⟨rfl, rfl⟩

/-- Outcome of crash-safe WAL recovery. -/
structure WalRecoveryResult where
  cleanDisk : Log.Bytes
  snapshot : AuthenticatedWorldSnapshot
  committedCount : Nat
  droppedTail : Log.Bytes
  dropReason : Option Log.Drop
  deriving DecidableEq
/-- Canonical WAL byte truncation: encodes committed `OBL1` frames and drops any uncommitted tail. -/
def recoverWalBytes (rawDisk : Log.Bytes) : Log.Bytes :=
  Log.encodeAll Replay.logHash (Log.parseFrom Replay.logHash genesisSentinel rawDisk).1
/-- Full WAL crash recovery over a world machine `M` (defaulting to `Replay.deployed`). -/
def recoverWalSnapshot {O : Type} (pp : AjtaiParams) (hCols : pp.cols = 64)
    (M : Log.Machine ChunkedWorld.World O) (w0 : ChunkedWorld.World)
    (rawDisk : Log.Bytes) : WalRecoveryResult :=
  let parsed := Log.parseFrom Replay.logHash genesisSentinel rawDisk
  { cleanDisk := Log.encodeAll Replay.logHash parsed.1
    snapshot := buildAuthenticatedSnapshot pp hCols (Log.replay M w0 parsed.1)
    committedCount := parsed.1.length, droppedTail := parsed.2.1, dropReason := parsed.2.2 }

/-- Re-parsing the encoded records recovered by `Log.parseFrom` yields `(qs, [], none)`. -/
theorem parseFrom_encodeAll_recovered (Hb : Log.Bytes → Log.Bytes) (prev : Nat) (rawDisk : Log.Bytes) :
    Log.parseFrom Hb prev (Log.encodeAll Hb (Log.parseFrom Hb prev rawDisk).1) =
      ((Log.parseFrom Hb prev rawDisk).1, [], none) := by
  let qs := (Log.parseFrom Hb prev rawDisk).1
  simpa [qs, List.append_nil, Log.parseFrom_nil] using
    Log.parseFrom_encodeAll Hb qs prev (Log.parseFrom_sound Hb prev rawDisk).1
      (parseFrom_wf Hb prev rawDisk) []

/-- **Unconditional Byte-Level WAL Truncation Idempotence (`recoverWalBytes_idempotent`)**. -/
theorem recoverWalBytes_idempotent (rawDisk : Log.Bytes) :
    recoverWalBytes (recoverWalBytes rawDisk) = recoverWalBytes rawDisk := by
  unfold recoverWalBytes; rw [parseFrom_encodeAll_recovered]

/-- **Unconditional Snapshot WAL Recovery Idempotence (`walCrashRecovery_idempotent`)**. -/
theorem walCrashRecovery_idempotent {O : Type} (pp : AjtaiParams) (hCols : pp.cols = 64)
    (M : Log.Machine ChunkedWorld.World O) (w0 : ChunkedWorld.World) (rawDisk : Log.Bytes) :
    recoverWalSnapshot pp hCols M w0 (recoverWalSnapshot pp hCols M w0 rawDisk).cleanDisk =
      { recoverWalSnapshot pp hCols M w0 rawDisk with droppedTail := [], dropReason := none } := by
  unfold recoverWalSnapshot; dsimp only; rw [parseFrom_encodeAll_recovered]

/-- One admitted epoch turn in a multi-epoch snapshot trace. -/
structure SnapshotEpoch where
  turnBytes : Log.Bytes
  record : Log.Record
  deriving DecidableEq

/-- **Multi-Epoch Snapshot & WAL Trace Invariant (`ValidSnapshotTrace`)**. -/
inductive ValidSnapshotTrace {O : Type} (pp : AjtaiParams) (hCols : pp.cols = 64)
    (M : Log.Machine ChunkedWorld.World O) (w0 : ChunkedWorld.World) :
    List SnapshotEpoch → Log.Session ChunkedWorld.World → AuthenticatedWorldSnapshot → Prop where
  | genesis : ValidSnapshotTrace pp hCols M w0 [] ⟨w0, []⟩ (buildAuthenticatedSnapshot pp hCols w0)
  | commitEpoch {epochs : List SnapshotEpoch} {S S' : Log.Session ChunkedWorld.World}
      {snap : AuthenticatedWorldSnapshot} {turnBytes : Log.Bytes} {rec : Log.Record} :
      ValidSnapshotTrace pp hCols M w0 epochs S snap →
      S.admit Replay.logHash M turnBytes = .ok S' → S'.log = S.log ++ [rec] →
      ValidSnapshotTrace pp hCols M w0 (epochs ++ [⟨turnBytes, rec⟩])
        S' (syncSnapshotWorld pp hCols snap S'.world)
/-- Specialization of `ValidSnapshotTrace` to `Replay.deployed`. -/
abbrev DeployedSnapshotTrace (pp : AjtaiParams) (hCols : pp.cols = 64) (w0 : ChunkedWorld.World) :=
  ValidSnapshotTrace pp hCols Replay.deployed w0
theorem validSnapshotTrace_invariants {O : Type} {pp : AjtaiParams} {hCols : pp.cols = 64}
    {M : Log.Machine ChunkedWorld.World O} {w0 : ChunkedWorld.World}
    {epochs : List SnapshotEpoch} {S : Log.Session ChunkedWorld.World}
    {snap : AuthenticatedWorldSnapshot}
    (htr : ValidSnapshotTrace pp hCols M w0 epochs S snap) :
    Log.Reachable Replay.logHash M w0 S ∧ S.log.length = epochs.length ∧
    SnapshotWF pp hCols snap ∧ snap.world = S.world ∧
    snap.verkleRoot = fullVerkleCommitWorld S.world := by
  induction htr with
  | genesis =>
    exact ⟨.genesis, rfl, buildAuthenticatedSnapshot_wf pp hCols w0, rfl,
      buildAuthenticatedSnapshot_verkleRoot pp hCols w0⟩
  | @commitEpoch epochs S S' snap turnBytes rec _ hadm hlog ih =>
    obtain ⟨hreach, hlen, hwf, _, _⟩ := ih
    obtain ⟨hwf', hw', hroot'⟩ := syncSnapshotWorld_wf_and_eq_fullCommit hwf S'.world
    refine ⟨.admit hreach hadm, ?_, hwf', hw', hroot'⟩
    rw [hlog, List.length_append, List.length_append, hlen]; rfl

/-- Pure multi-epoch deterministic machine witnessing non-vacuity of `ValidSnapshotTrace`. -/
def bumpMintedMachine : Log.Machine ChunkedWorld.World Unit where
  step w bs := .ok ({ w with minted := w.minted + bs.length + 1 }, ())
  encW := ChunkedWorld.manifestBytes

/-- **Multi-Epoch Trace Inhabitedness Witness (`validSnapshotTrace_multiEpoch_inhabited`)**. -/
theorem validSnapshotTrace_multiEpoch_inhabited :
    ∃ (epochs : List SnapshotEpoch) (S : Log.Session ChunkedWorld.World)
      (snap : AuthenticatedWorldSnapshot), epochs.length = 2 ∧
      ValidSnapshotTrace defaultChunkAjtaiParams defaultChunkAjtaiParams_cols
        bumpMintedMachine Replay.genesis epochs S snap := by
  let S0 : Log.Session ChunkedWorld.World := ⟨Replay.genesis, []⟩
  let b1 : Log.Bytes := [0x01]
  let b2 : Log.Bytes := [0x02, 0x03]
  let w1 : ChunkedWorld.World := { Replay.genesis with minted := 2 }
  let r1 : Log.Record := ⟨⟨Log.lastHash Replay.logHash genesisSentinel [],
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes Replay.genesis),
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes w1), Log.dig Replay.logHash b1⟩, b1⟩
  let S1 : Log.Session ChunkedWorld.World := ⟨w1, [r1]⟩
  let w2 : ChunkedWorld.World := { w1 with minted := 5 }
  let r2 : Log.Record := ⟨⟨Log.lastHash Replay.logHash genesisSentinel [r1],
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes w1),
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes w2), Log.dig Replay.logHash b2⟩, b2⟩
  let S2 : Log.Session ChunkedWorld.World := ⟨w2, [r1, r2]⟩
  have ha1 := Log.admit_of_step Replay.logHash bumpMintedMachine (w := Replay.genesis) (w' := w1)
    (o := ()) (prev := Log.lastHash Replay.logHash genesisSentinel []) (b := b1) (by decide) rfl rfl
  have hadm1 : S0.admit Replay.logHash bumpMintedMachine b1 = .ok S1 := by
    unfold Log.Session.admit S0; dsimp only; rw [ha1]; rfl
  have ha2 := Log.admit_of_step Replay.logHash bumpMintedMachine (w := w1) (w' := w2)
    (o := ()) (prev := Log.lastHash Replay.logHash genesisSentinel [r1]) (b := b2) (by decide) rfl rfl
  have hadm2 : S1.admit Replay.logHash bumpMintedMachine b2 = .ok S2 := by
    unfold Log.Session.admit S1; dsimp only; rw [ha2]; rfl
  have tr0 := ValidSnapshotTrace.genesis (pp := defaultChunkAjtaiParams)
    (hCols := defaultChunkAjtaiParams_cols) (M := bumpMintedMachine) (w0 := Replay.genesis)
  exact ⟨[⟨b1, r1⟩, ⟨b2, r2⟩], S2, _, rfl,
    ValidSnapshotTrace.commitEpoch (ValidSnapshotTrace.commitEpoch tr0 hadm1 rfl) hadm2 rfl⟩

/-- **Headline Theorem 3**: across any multi-epoch `ValidSnapshotTrace` and any uncommitted or
    torn WAL tail, `recoverWalSnapshot` truncates the tail, is idempotent, and restores the exact
    committed `ChunkedWorld` and 256-bit `VerkleUmem` root. -/
theorem walCrashReplay_restores_verkle_consistent_world {O : Type}
    {pp : AjtaiParams} {hCols : pp.cols = 64}
    {M : Log.Machine ChunkedWorld.World O} {w0 : ChunkedWorld.World}
    {epochs : List SnapshotEpoch} {S : Log.Session ChunkedWorld.World}
    {snap : AuthenticatedWorldSnapshot}
    (htr : ValidSnapshotTrace pp hCols M w0 epochs S snap) {tornTail : Log.Bytes}
    (htorn : UncommittedWalTail Replay.logHash
      (Log.lastHash Replay.logHash genesisSentinel S.log) tornTail) :
    let crashDisk := Log.encodeAll Replay.logHash S.log ++ tornTail
    let out := recoverWalSnapshot pp hCols M w0 crashDisk
    out.cleanDisk = Log.encodeAll Replay.logHash S.log ∧
    out.committedCount = epochs.length ∧ out.droppedTail = tornTail ∧
    recoverWalBytes (recoverWalBytes crashDisk) = out.cleanDisk ∧
    (recoverWalSnapshot pp hCols M w0 out.cleanDisk).cleanDisk = out.cleanDisk ∧
    (recoverWalSnapshot pp hCols M w0 out.cleanDisk).snapshot = out.snapshot ∧
    SnapshotWF pp hCols out.snapshot ∧ out.snapshot.world = S.world ∧
    out.snapshot.verkleRoot = snap.verkleRoot ∧
    out.snapshot.verkleRoot = fullVerkleCommitWorld S.world := by
  obtain ⟨hreach, hlen, _, _, hsnapRoot⟩ := validSnapshotTrace_invariants htr
  obtain ⟨hlinked, hwfLog⟩ := Log.log_sound hreach
  have hparseEnc := Log.parseFrom_encodeAll Replay.logHash S.log genesisSentinel hlinked hwfLog tornTail
  obtain ⟨htailRecs, htailRest⟩ := parseFrom_uncommittedWalTail Replay.logHash _ htorn
  have hparseFull : (Log.parseFrom Replay.logHash genesisSentinel
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).1 = S.log := by
    rw [hparseEnc, htailRecs, List.append_nil]
  have hparseDrop : (Log.parseFrom Replay.logHash genesisSentinel
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).2.1 = tornTail := by
    rw [hparseEnc]; exact htailRest
  have hreplayEq : Log.replay M w0 S.log = S.world := (Log.state_eq_replay_log hreach).symm
  have hidem := walCrashRecovery_idempotent pp hCols M w0 (Log.encodeAll Replay.logHash S.log ++ tornTail)
  have hbytesIdem := recoverWalBytes_idempotent (Log.encodeAll Replay.logHash S.log ++ tornTail)
  dsimp only
  have hclean : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).cleanDisk =
      Log.encodeAll Replay.logHash S.log := by unfold recoverWalSnapshot; dsimp only; rw [hparseFull]
  have hcnt : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).committedCount = epochs.length := by
    unfold recoverWalSnapshot; dsimp only; rw [hparseFull, hlen]
  have hdrop : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).droppedTail = tornTail := by
    unfold recoverWalSnapshot; dsimp only; exact hparseDrop
  have hsnapEq : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).snapshot =
      buildAuthenticatedSnapshot pp hCols S.world := by
    unfold recoverWalSnapshot; dsimp only; rw [hparseFull, hreplayEq]
  refine ⟨hclean, hcnt, hdrop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbytesIdem]; unfold recoverWalBytes; rw [hparseFull, hclean]
  · rw [hidem]
  · rw [hidem]
  · rw [hsnapEq]; exact buildAuthenticatedSnapshot_wf pp hCols S.world
  · rw [hsnapEq]; rfl
  · rw [hsnapEq, buildAuthenticatedSnapshot_verkleRoot, hsnapRoot]
  · rw [hsnapEq, buildAuthenticatedSnapshot_verkleRoot]

end Obend.Vault.VerkleSnapshotBridge
end
