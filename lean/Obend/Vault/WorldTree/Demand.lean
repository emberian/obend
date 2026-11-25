module
public import Obend.Vault.WorldTree.ShardedWorld
import all Obend.Vault.WorldTree.ShardedWorld
public section

namespace Obend.Vault.ChunkedWorld
open Obend.Codec.Hex (bytesToHex)
set_option autoImplicit false

/-- The manifest's directory of checkpoint shards. An open handle owns no decoded pages. -/
structure DemandWorld where
  metadata : NonStoreMeta
  pages : Nat
  tombs : Nat
  digests : Array (Option String)

def openDemandWorld (manifest : ByteArray) : Option DemandWorld := do
  let (metadata, pages, tombs, ds) ← unframeManifestArray manifest
  guard (ds.length == numBuckets)
  return ⟨metadata, pages, tombs, ds.toArray⟩

def DemandWorld.manifest (w : DemandWorld) : ByteArray :=
  frameManifestArray (w.metadata, w.pages, w.tombs, w.digests.toList)

def DemandWorld.load {m : Type → Type} [Monad m] (w : DemandWorld) (read : String → m (Option ByteArray))
    (b : Nat) : m (Option ShardPayload) := do
  match w.digests[b]? with
  | none => return none
  | some none => return some ([], [])
  | some (some d) =>
    let some bytes ← read (shardKey b d) | return none
    if bytesToHex (logHashArray bytes) != d then return none
    return decodeShardPayloadArray bytes

/-- Outer none denotes failed authentication, inner none an absent title. -/
def DemandWorld.getPage {m : Type → Type} [Monad m] (w : DemandWorld) (read : String → m (Option ByteArray))
    (name : String) : m (Option (Option Page)) := do
  let pay ← w.load read (bucketOf name)
  return pay.map fun (ps, _) => (ps.find? (fun (_, p) => p.name == name)).map Prod.snd

def fullDirectory (w : World) : DemandWorld :=
  ⟨metaOf w, w.store.pages.length, w.store.tombs.length,
    (Array.range numBuckets).map fun b => (shardForBucket w b).map Prod.fst⟩

def fullPayload (w : World) (b : Nat) : ShardPayload :=
  (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs))

private theorem load_full (w : World) (read : String → Option ByteArray)
    (hs : ∀ b d bytes, b < numBuckets → shardForBucket w b = some (d, bytes) →
      read (shardKey b d) = some ⟨bytes.toArray⟩) (b : Nat) (hb : b < numBuckets) :
    (fullDirectory w).load (m := Id) read b = some (fullPayload w b) := by
  have hg : (fullDirectory w).digests[b]? = some ((shardForBucket w b).map Prod.fst) := by
    simp [fullDirectory, hb]
  unfold DemandWorld.load
  rw [hg]
  let pay := fullPayload w b
  by_cases he : isEmptyShard pay = true
  · have hf : shardForBucket w b = none := by change shardSpecOf pay = none; simp [shardSpecOf, he]
    rw [hf]
    exact congrArg some ((isEmptyShard_iff pay).mp he).symm
  · let bytes := encodeShardPayload pay
    have hf : shardForBucket w b = some (bytesToHex (logHash bytes), bytes) := by
      change shardSpecOf pay = _
      simp [shardSpecOf, he, bytes]
    rw [hf]
    simp [hs _ _ _ hb hf, logHashArray_eq, decodeShardPayloadArray_eq, bytes,
      decodeShardPayload_encodeShardPayload, pay, Bind.bind]
    rfl

private theorem directory_manifest (w : World) :
    (fullDirectory w).manifest.data.toList = manifestBytes w := by
  simp [DemandWorld.manifest, fullDirectory, frameManifestArray_eq, manifestBytes, List.map_map,
    Function.comp_def, Array.toList_range]

private theorem unframe_array_frame (c : ManifestCore) :
    unframeManifestArray (frameManifestArray c) = some c := by
  let bs := frameManifestArray c
  let p := manifestPrefixArray
  have hdata : bs.data.toList = p.data.toList ++ cManifestCore.enc c := frameManifestArray_eq _
  have hsize : p.size ≤ bs.size := by
    have h := congrArg List.length hdata
    simp only [List.length_append, Array.length_toList, ByteArray.size_data] at h
    omega
  have hs : sliceEq bs 0 p = true := by
    unfold sliceEq
    have bound : 0 + p.size ≤ bs.size := by simpa using hsize
    rw [sliceEqGo_eq bs 0 p bound 0, decide_eq_true bound]
    simp only [Nat.add_zero, List.drop_zero, Nat.sub_zero, Bool.true_and]
    change (bs.data.toList.take p.data.toList.length == p.data.toList) = true
    rw [hdata, take_append_exact, beq_self_eq_true]
  have hd : (bs.extract p.size bs.size).data.toList = cManifestCore.enc c := by
    rw [ByteArray.data_extract]
    change (bs.data.extract p.data.toList.length bs.data.toList.length).toList = _
    rw [Array.toList_extract, hdata]
    simp [List.extract]
  change (if decide (p.size ≤ bs.size) && sliceEq bs 0 p then _ else _) = _
  simp only [hs, decide_eq_true hsize, Bool.and_self, ↓reduceIte]
  change cManifestCore.decodeExactArray (bs.extract p.size bs.size) = _
  rw [FastCodec.decodeExactArray_eq, hd, FastCodec.decodeExact_enc]

private theorem open_fullDirectory (w : World) :
    openDemandWorld (fullDirectory w).manifest = some (fullDirectory w) := by
  simp [openDemandWorld, DemandWorld.manifest, unframe_array_frame, fullDirectory, guard]
  apply Array.toList_inj.mp; simp

theorem openDemandWorld_getPage_eq_openFullWorld (w : World) (read : String → Option ByteArray)
    (hs : ∀ b d bytes, b < numBuckets → shardForBucket w b = some (d, bytes) →
      read (shardKey b d) = some ⟨bytes.toArray⟩) (name : String) :
    ((openDemandWorld (encodeWorldIncremental w none).1).bind
      (fun d => d.getPage (m := Id) read name)) = some (w.store.page? name) := by
  have he : (encodeWorldIncremental w none).1 = (fullDirectory w).manifest := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [encodeWorldIncremental_manifest_eq, directory_manifest]
  rw [he, open_fullDirectory]
  simp only [Option.bind_some, DemandWorld.getPage, load_full w read hs _ (bucketOf_lt name)]
  exact congrArg some (find_bucketItems_enumGo name 0 w.store.pages)

/-- One admitted Store.setPage replacement, using its pre-edit bucket payload. The caller persists
the returned content-addressed shard before publishing the returned manifest. -/
def applyEditDemand (d : DemandWorld) (p : Page) (old : ShardPayload) : DemandWorld × CachedBucket :=
  let pages := old.1.map fun (i, q) => (i, if q.name == p.name then p else q)
  let cb := buildCachedBucket (pages, old.2) none
  let dir := { d with
    metadata := { d.metadata with turn := d.metadata.turn + 1 }
    digests := d.digests.setIfInBounds (bucketOf p.name) (cb.entry?.map Prod.fst) }
  (dir, cb)

/-- Authenticated point replacement. Corrupt or absent shard data cannot enter the update. -/
def DemandWorld.edit {m : Type → Type} [Monad m] (d : DemandWorld) (read : String → m (Option ByteArray))
    (p : Page) : m (Option (DemandWorld × CachedBucket)) := do
  let old ← d.load read (bucketOf p.name)
  return old.map (applyEditDemand d p)

private theorem edit_partition (p : Page) (b k : Nat) (ps : List Page) :
    bucketItems b (enumGo k (ps.map (fun q => if q.name == p.name then p else q))) =
    if b = bucketOf p.name then
      (bucketItems b (enumGo k ps)).map (fun (i,q) => (i, if q.name == p.name then p else q))
    else bucketItems b (enumGo k ps) := by
  induction ps generalizing k with
  | nil => simp [enumGo, bucketItems]
  | cons q qs ih =>
    simp only [List.map_cons, enumGo, bucketItems, List.filter_cons] at ih ⊢
    specialize ih (k + 1)
    by_cases hn : q.name = p.name <;> by_cases hb : b = bucketOf p.name <;>
      by_cases hq : bucketOf q.name = b <;> simp_all

theorem applyEditDemand_root_eq_full (w : World) (p : Page) :
    let d := fullDirectory w
    ((applyEditDemand d p (fullPayload w (bucketOf p.name))).1.manifest).data.toList =
      manifestBytes { w with store := w.store.setPage p } := by
  intro d
  rw [← directory_manifest]
  apply congrArg (fun dir : DemandWorld => dir.manifest.data.toList)
  let after := { w with store := w.store.setPage p }
  let old := fullPayload w (bucketOf p.name)
  let pay : ShardPayload := (old.1.map (fun (i,q) => (i, if q.name == p.name then p else q)), old.2)
  have hdigest : (buildCachedBucket pay none).entry?.map Prod.fst = (shardSpecOf pay).map Prod.fst := by
    have h := congrArg (Option.map Prod.fst) (buildCachedBucket pay none).entry_eq
    simpa [Option.map_map, Function.comp_def, buildCachedBucket_payload] using h
  have hdirs : (applyEditDemand d p old).1.digests = (fullDirectory after).digests := by
    apply Array.ext (by simp [applyEditDemand, d, fullDirectory, after])
    intro b hb1 hb2
    have hb : b < numBuckets := by simpa [fullDirectory] using hb2
    have hsize : b < d.digests.size := by simpa [d, fullDirectory] using hb
    change (d.digests.setIfInBounds (bucketOf p.name) _)[b] = _
    refine (Array.getElem_setIfInBounds (xs := d.digests) (i := bucketOf p.name)
      (a := (buildCachedBucket pay none).entry?.map Prod.fst) hsize).trans ?_
    simp only [d, fullDirectory, Array.getElem_map, Array.getElem_range, after, Store.setPage,
      shardForBucket, enumList, edit_partition]
    by_cases h : b = bucketOf p.name
    · subst b; simpa [pay, old, fullPayload, enumList] using hdigest
    · simp [h, Ne.symm h]
  have extDir {a b : DemandWorld} (hm : a.metadata = b.metadata) (hp : a.pages = b.pages)
      (ht : a.tombs = b.tombs) (hd : a.digests = b.digests) : a = b := by
    cases a; cases b; simp_all
  apply extDir (a := (applyEditDemand d p old).1) (b := fullDirectory after)
  · rfl
  · simp [applyEditDemand, d, fullDirectory, after, Store.setPage]
  · rfl
  · exact hdirs

/-- The authenticated read-modify-write endpoint realizes the full store's next manifest. -/
theorem edit_manifest_eq_full (w : World) (read : String → Option ByteArray)
    (hs : ∀ b d bytes, b < numBuckets → shardForBucket w b = some (d, bytes) →
      read (shardKey b d) = some ⟨bytes.toArray⟩) (p : Page) :
    ((fullDirectory w).edit (m := Id) read p).map (fun r => r.1.manifest.data.toList) =
      some (manifestBytes { w with store := w.store.setPage p }) := by
  simp only [DemandWorld.edit, load_full w read hs _ (bucketOf_lt p.name)]
  exact congrArg some (applyEditDemand_root_eq_full w p)

end Obend.Vault.ChunkedWorld
