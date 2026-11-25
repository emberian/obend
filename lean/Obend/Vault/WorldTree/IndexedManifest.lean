module
public import Obend.Vault.WorldTree.Demand
import all Obend.Vault.WorldTree.ShardedWorld
import Obend.Codec.HexString
public import Std.Data.HashMap
public section

namespace Obend.Vault.ChunkedWorld
set_option autoImplicit false

/-- A working-tree observation. Filesystem timestamps are local to the replica. -/
structure FileStamp where
  seconds : Int
  nanoseconds : Nat
  size : Nat
  digest : ByteArray

/-- Position preserves the order in which the full store proposes backlink candidates. -/
structure TitleRecord where
  title : String
  ordinal : Nat
  pageDigest : ByteArray
  targets : Array Nat
  stamp : Option FileStamp

private abbrev Incoming := Nat × Nat × String
private def cStamp : FastCodec FileStamp :=
  cMap (fun s => (s.seconds, s.nanoseconds, s.size, s.digest))
    (fun (sec, ns, size, digest) => some ⟨sec, ns, size, digest⟩) (fun _ => rfl)
    (cPair cInt (cPair cNat (cPair cNat cByteArray)))

private def cTitle : FastCodec TitleRecord :=
  cMap (fun t => (t.title, t.ordinal, t.pageDigest, t.targets, t.stamp))
    (fun (title, i, d, ts, stat) => some ⟨title, i, d, ts, stat⟩) (fun _ => rfl)
    (cPair cString (cPair cNat (cPair cByteArray (cPair (cArray cNat) (cOption cStamp)))))

private def cIncoming := cArray (cPair cNat (cPair cNat cString))
private def hashBlock (domain : String) (bytes : ByteArray) : ByteArray :=
  Obend.Digest.Cshake256.Fast.cshake256ByteArrayFast domain.toUTF8 bytes

private def storeBlock (dir : System.FilePath) (domain : String) (bytes : ByteArray) : IO ByteArray := do
  let digest := hashBlock domain bytes
  let path := worldDir dir / "index" / (Obend.Codec.Hex.hexString digest)
  if ← path.pathExists then
    if (← Obend.Vault.Cost.readBinFile path) == bytes then return digest
  writeFileAtomicArray path bytes
  return digest

private def readBlock (dir : System.FilePath) (domain : String) (digest : ByteArray) : IO (Option ByteArray) := do
  if digest.size != 32 then return none
  let path := worldDir dir / "index" / (Obend.Codec.Hex.hexString digest)
  if !(← path.pathExists) then return none
  let bytes ← Obend.Vault.Cost.readBinFile path
  if hashBlock domain bytes != digest then return none
  return some bytes

private def putRows {α : Type} (dir : System.FilePath) (domain : String) (c : FastCodec (Array α))
    (rows : Array α) : IO (Option ByteArray) := do
  if rows.isEmpty then return none
  return some (← storeBlock dir domain (c.encodeArray rows))

private def getRows {α : Type} (dir : System.FilePath) (domain : String) (c : FastCodec (Array α))
    (ref : Option ByteArray) : IO (Option (Array α)) := do
  let some digest := ref | return some #[]
  return (← readBlock dir domain digest).bind c.decodeExactArray

structure IndexDirectory where
  logical : ByteArray
  source : Array (Option String)
  titles : Array (Option ByteArray)
  incoming : Array (Option ByteArray)

private def cDirectory : FastCodec IndexDirectory :=
  cMap (fun d => (d.logical, d.source, d.titles, d.incoming))
    (fun (w, s, t, i) => some ⟨w, s, t, i⟩) (fun _ => rfl)
    (cPair cByteArray (cPair (cArray (cOption cString))
      (cPair (cArray (cOption cByteArray)) (cArray (cOption cByteArray)))))

private def marker := "OBIXEND!".toUTF8

/-- The durable checkpoint carries the index address after its canonical log-committed world.
Both parts have independent validation so replicas with different mtimes replay the same log. -/
def attachIndex (logical address : ByteArray) : ByteArray := logical ++ address ++ marker

def splitIndex (physical : ByteArray) : ByteArray × Option ByteArray :=
  if physical.size ≥ 40 && decide (physical.extract 0 8 = manifestPrefixArray) &&
      decide (physical.extract (physical.size - 8) physical.size = marker) then
    let i := physical.size - 40
    (physical.extract 0 i, some (physical.extract i (i+32)))
  else (physical, none)

/-- Unframing returns the exact replay bytes and all 256 address bits, for arbitrary payloads. -/
theorem splitIndex_attach (payload address : ByteArray) (ha : address.size = 32) :
    let logical := manifestPrefixArray ++ payload
    splitIndex (attachIndex logical address) = (logical, some address) := by
  intro logical
  let physical := attachIndex logical address
  have hm : marker.size = 8 := by simp only [marker, String.toUTF8_eq_toByteArray]; decide
  have hp : manifestPrefixArray.size = 8 := by simp only [manifestPrefixArray, String.toUTF8_eq_toByteArray]; decide
  have size : physical.size = logical.size + 40 := by
    simp [physical, attachIndex, ByteArray.size_append, ha, hm, Nat.add_assoc]
  have header : physical.extract 0 8 = manifestPrefixArray := by
    change (((manifestPrefixArray ++ payload) ++ address) ++ marker).extract 0 8 = _
    rw [ByteArray.append_assoc, ByteArray.append_assoc]
    apply ByteArray.extract_append_eq_left hp.symm
  have trailer : physical.extract (physical.size-8) physical.size = marker :=
    ByteArray.extract_append_eq_right (by simp [size, ha]) (by simp [physical, attachIndex])
  have body : physical.extract 0 (physical.size-40) = logical := by
    change ((logical ++ address) ++ marker).extract 0 (physical.size-40) = logical
    rw [ByteArray.append_assoc]
    apply ByteArray.extract_append_eq_left (by omega)
  have digest : physical.extract (physical.size-40) (physical.size-40+32) = address := by
    change ((logical ++ address) ++ marker).extract (physical.size-40) (physical.size-40+32) = address
    rw [ByteArray.append_assoc]
    have hi : physical.size-40 = logical.size := by omega
    rw [hi, ← Nat.add_zero logical.size, Nat.add_zero]
    have h := @ByteArray.extract_append_size_add logical (address ++ marker) 0 32
    rw [Nat.add_zero] at h
    exact h.trans (ByteArray.extract_append_eq_left ha.symm)
  change splitIndex physical = _
  simp [splitIndex, show 40 ≤ physical.size by omega, header, trailer, body, digest]

def openDemandCheckpoint (physical : ByteArray) := openDemandWorld (splitIndex physical).1

theorem indexed_getPage_eq_openFullWorld (w : World) (read : String → Option ByteArray)
    (hs : ∀ b d bytes, b < numBuckets → shardForBucket w b = some (d, bytes) →
      read (shardKey b d) = some ⟨bytes.toArray⟩) (name : String)
    (address : ByteArray) (ha : address.size = 32) :
    ((openDemandCheckpoint (attachIndex (encodeWorldIncremental w none).1 address)).bind
      (fun d => d.getPage (m := Id) read name)) = some (w.store.page? name) := by
  have frame : ∃ payload, (encodeWorldIncremental w none).1 = manifestPrefixArray ++ payload := by
    unfold encodeWorldIncremental frameManifestArray
    exact ⟨_, rfl⟩
  obtain ⟨payload, he⟩ := frame
  unfold openDemandCheckpoint
  rw [he, splitIndex_attach _ _ ha, ← he]
  exact openDemandWorld_getPage_eq_openFullWorld w read hs name

def openIndex (dir : System.FilePath) (physical : ByteArray) : IO (Option IndexDirectory) := do
  let (logical, some address) := splitIndex physical | return none
  let some header ← readBlock dir "obend.vault.index.root.1" address | return none
  let some d := cDirectory.decodeExactArray header | return none
  let some w := openDemandWorld logical | return none
  if d.logical != hashBlock "obend.vault.index.world.1" logical || d.source != w.digests ||
      d.titles.size != numBuckets || d.incoming.size != numBuckets then return none
  return some d

def IndexDirectory.title? (idx : IndexDirectory) (dir : System.FilePath) (title : String) :
    IO (Option (Option TitleRecord)) := do
  let some key := idx.titles[bucketOf title]? | return none
  return (← getRows dir "obend.vault.index.titles.1" (cArray cTitle) key).map
    (fun rows => rows.find? (fun t => t.title == title))

def IndexDirectory.backlinks (idx : IndexDirectory) (dir : System.FilePath) (target : Nat) :
    IO (Option (Array String)) := do
  let some key := idx.incoming[target % numBuckets]? | return none
  return (← getRows dir "obend.vault.index.incoming.1" cIncoming key).map fun rows =>
    rows.filterMap fun (t, _, name) => if t == target then some name else none

/-- Gather a stamp only for a stable observation. A caller can compare the recorded digest to a
new content observation after a change notification, including a same-size mtime-preserving edit. -/
def observeFile (path : System.FilePath) : IO (Option FileStamp) := do
  try
    let before ← path.metadata
    if before.type != .file then return none
    let bytes ← Obend.Vault.Cost.readBinFile path
    let after ← path.metadata
    if before.modified != after.modified || before.byteSize != after.byteSize ||
        after.byteSize.toNat != bytes.size then return none
    return some ⟨after.modified.sec, after.modified.nsec.toNat, bytes.size,
      hashBlock "obend.vault.index.file.1" bytes⟩
  catch e =>
    if e matches .noFileOrDirectory .. then return none else throw e

private def record (observe : String → IO (Option FileStamp)) (old : Std.HashMap String TitleRecord)
    (item : Nat × Page) : IO TitleRecord := do
  let (ordinal, p) := item
  let digest := hashBlock "obend.vault.index.page.1" (cPage.encodeArray p)
  if let some row := old[p.name]? then
    if row.pageDigest == digest then return { row with ordinal }
  let targets := (p.current.map citeTargets).getD []
  return ⟨p.name, ordinal, digest,
    targets.toArray, ← observe p.name⟩

def TitleRecord.matchesPage (row : TitleRecord) (p : Page) : Bool :=
  row.title == p.name && row.pageDigest == hashBlock "obend.vault.index.page.1" (cPage.encodeArray p)

/-- Only validated bytes can justify reusing the working-tree digest when file events are absent. -/
def FileStamp.matchesBytes (s : FileStamp) (bytes : ByteArray) : Bool :=
  s.size == bytes.size && s.digest == hashBlock "obend.vault.index.file.1" bytes

private def emptyDirectory : IndexDirectory :=
  ⟨ByteArray.empty, Array.replicate numBuckets none, Array.replicate numBuckets none,
    Array.replicate numBuckets none⟩

/-- Incremental construction reads old title shards only for changed source buckets. A reverse
shard is rewritten exactly when a changed source bucket previously or currently cites its key. -/
private def updateIndex (dir : System.FilePath) (logical : ByteArray) (w : DemandWorld)
    (payload : Nat → IO (Option ShardPayload)) (observe : String → IO (Option FileStamp))
    (prev : IndexDirectory) : IO (Option ByteArray) := do
  let mut titles := prev.titles
  let mut incoming := prev.incoming
  let dirty := (Array.range numBuckets).map fun b => prev.source[b]? != w.digests[b]?
  let mut affected := Array.replicate numBuckets false
  let mut removed : Std.HashSet (Nat × String) := {}
  let mut additions : Array (Array Incoming) := Array.replicate numBuckets #[]
  for b in [:numBuckets] do
    unless dirty[b]?.getD false do continue
    let some old ← getRows dir "obend.vault.index.titles.1" (cArray cTitle) (titles[b]?.join) | return none
    let some (pages, _) ← payload b | return none
    let byName := old.foldl (fun (m : Std.HashMap String TitleRecord) r => m.insert r.title r) {}
    let rows ← pages.toArray.mapM (record observe byName)
    titles := titles.setIfInBounds b (← putRows dir "obend.vault.index.titles.1" (cArray cTitle) rows)
    let key := fun (row : TitleRecord) => (row.ordinal, row.title)
    let edges := fun (rs : Array TitleRecord) => rs.foldl
      (fun (m : Std.HashMap (Nat × String) (Array Nat)) row => m.insert (key row) row.targets) {}
    let newEdges := edges rows
    let oldEdges := edges old
    for row in old do
      if newEdges[key row]? != some row.targets then
        removed := removed.insert (key row)
        for t in row.targets do affected := affected.setIfInBounds (t % numBuckets) true
    for row in rows do
      if oldEdges[key row]? != some row.targets then
        for t in row.targets do
          let k := t % numBuckets
          affected := affected.setIfInBounds k true
          additions := additions.modify k (·.push (t, row.ordinal, row.title))
  for k in [:numBuckets] do
    unless affected[k]?.getD false do continue
    let some old ← getRows dir "obend.vault.index.incoming.1" cIncoming (incoming[k]?.join) | return none
    let kept := old.filter fun (_, ordinal, title) => !removed.contains (ordinal, title)
    let rows := (kept ++ additions[k]?.getD #[]).qsort fun a b => a.2.1 < b.2.1
    incoming := incoming.setIfInBounds k (← putRows dir "obend.vault.index.incoming.1" cIncoming rows)
  let idx : IndexDirectory := ⟨hashBlock "obend.vault.index.world.1" logical, w.digests, titles, incoming⟩
  return some (attachIndex logical (← storeBlock dir "obend.vault.index.root.1" (cDirectory.encodeArray idx)))

def writeIndexedManifest (dir : System.FilePath) (logical : ByteArray)
    (payload : Nat → IO (Option ShardPayload)) (observe : String → IO (Option FileStamp))
    (previous : Option IndexDirectory) : IO (Option ByteArray) := do
  let some w := openDemandWorld logical | return none
  if let some prev := previous then
    if let some bytes ← updateIndex dir logical w payload observe prev then return some bytes
  updateIndex dir logical w payload observe emptyDirectory

/-- Update both the canonical world and its secondary indexes for an already admitted page. The
caller writes the returned page shard before publishing the physical checkpoint under the vault lock. -/
def editIndexedManifest (dir : System.FilePath) (physical : ByteArray) (p : Page)
    (read : String → IO (Option ByteArray)) (observe : String → IO (Option FileStamp)) :
    IO (Option (ByteArray × CachedBucket)) := do
  let some w := openDemandWorld (splitIndex physical).1 | return none
  let some (next, changed) ← w.edit read p | return none
  let load := fun b => if b == bucketOf p.name then pure (some changed.payload) else w.load read b
  let some manifest ← writeIndexedManifest dir next.manifest load observe (← openIndex dir physical)
    | return none
  return some (manifest, changed)

end Obend.Vault.ChunkedWorld
