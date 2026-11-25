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

/-- Compact per-page stat and cleanliness metadata packed into a single scan summary block so
repeat `obend open` walks the working tree with one `stat` per file and zero shard reads. -/
structure ScanEntry where
  title : String
  ordinal : Nat
  pageId : Nat
  seconds : Int
  nanoseconds : Nat
  size : Nat
  flags : UInt8
deriving Inhabited

def flagHasStamp : UInt8 := 1
def flagHasSeen : UInt8 := 2
def flagHasNote : UInt8 := 4
def flagHasHistory : UInt8 := 8
def flagIsEnvPage : UInt8 := 16
def flagHasDangling : UInt8 := 32
def flagLocallyClean : UInt8 := 64
def flagIsKind : UInt8 := 128

def ScanEntry.hasStamp (e : ScanEntry) : Bool := (e.flags &&& flagHasStamp) != 0
def ScanEntry.hasSeen (e : ScanEntry) : Bool := (e.flags &&& flagHasSeen) != 0
def ScanEntry.hasNote (e : ScanEntry) : Bool := (e.flags &&& flagHasNote) != 0
def ScanEntry.hasHistory (e : ScanEntry) : Bool := (e.flags &&& flagHasHistory) != 0
def ScanEntry.isEnvPage (e : ScanEntry) : Bool := (e.flags &&& flagIsEnvPage) != 0
def ScanEntry.hasDangling (e : ScanEntry) : Bool := (e.flags &&& flagHasDangling) != 0
def ScanEntry.locallyClean (e : ScanEntry) : Bool := (e.flags &&& flagLocallyClean) != 0
def ScanEntry.isKindPage (e : ScanEntry) : Bool := (e.flags &&& flagIsKind) != 0

structure ScanSummary where
  entries : Array ScanEntry
  /-- Sorted `(sourceOrdinal, targetPageId)` pairs for cite targets not currently present. -/
  nonPresentEdges : Array (Nat × Nat)

private def pageScanFlags (p : Page) (hasStamp : Bool) : UInt8 :=
  (if hasStamp then flagHasStamp else 0) |||
  (if p.seen.isSome then flagHasSeen else 0) |||
  (if p.note.isSome then flagHasNote else 0) |||
  (if !p.history.isEmpty then flagHasHistory else 0) |||
  (if ((p.seen.getD "").splitOn "environment").length > 1 then flagIsEnvPage else 0) |||
  (if (p.current.map fun G => G.atoms.any fun a => danglingCandidate a.2).getD false then flagHasDangling else 0) |||
  (if pageLocallyClean p then flagLocallyClean else 0) |||
  (if isKind p.name then flagIsKind else 0)

private def mkScanEntry (ordinal : Nat) (p : Page) (stamp : Option FileStamp) : ScanEntry :=
  match stamp with
  | some s => ⟨p.name, ordinal, p.id, s.seconds, s.nanoseconds, s.size, pageScanFlags p true⟩
  | none => ⟨p.name, ordinal, p.id, 0, 0, 0, pageScanFlags p false⟩

private def rawEnc {α : Type} (c : RawCodec α) (a : α) : ByteArray :=
  c.push ByteArray.empty a

private def rawDec {α : Type} (c : RawCodec α) (b : ByteArray) : Option α :=
  match c.readAt b 0 with
  | some (a, off) => if b.size ≤ off then some a else none
  | none => none

private def rawArray {α : Type} (c : RawCodec α) : RawCodec (Array α) :=
  rawMap Array.toList (fun xs => some xs.toArray) (rawList c)

private def rawUtf8String : RawCodec String :=
  rawMap String.toUTF8 String.fromUTF8? cByteArray.toRawCodec

private def encodeScanSummary (s : ScanSummary) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (s.entries.size * 32 + s.nonPresentEdges.size * 8 + 16)
  out := pushNat out s.entries.size
  for e in s.entries do
    let tb := e.title.toUTF8
    out := appendByteArray (pushNat out tb.size) tb
    out := pushNat out e.pageId
    out := cInt.push out e.seconds
    out := pushNat out e.nanoseconds
    out := pushNat out e.size
    out := out.push e.flags
  out := pushNat out s.nonPresentEdges.size
  for (ord, tid) in s.nonPresentEdges do
    out := pushNat out ord
    out := pushNat out tid
  return out

private def decodeScanSummary (b : ByteArray) : Option ScanSummary := Id.run do
  let some (n, pos0) := readNatAt b 0 | return none
  let mut pos := pos0
  let mut entries : Array ScanEntry := Array.mkEmpty n
  for ord in [:n] do
    let some (tlen, p1) := readNatAt b pos | return none
    if p1 + tlen > b.size then return none
    let some title := String.fromUTF8? (b.extract p1 (p1 + tlen)) | return none
    let some (pid, p2) := readNatAt b (p1 + tlen) | return none
    let some (sec, p3) := cInt.readAt b p2 | return none
    let some (ns, p4) := readNatAt b p3 | return none
    let some (sz, p5) := readNatAt b p4 | return none
    if h : p5 < b.size then
      let fl := b[p5]'h
      entries := entries.push ⟨title, ord, pid, sec, ns, sz, fl⟩
      pos := p5 + 1
    else return none
  let some (m, pos1) := readNatAt b pos | return none
  pos := pos1
  let mut edges : Array (Nat × Nat) := Array.mkEmpty m
  for _ in [:m] do
    let some (ord, p1) := readNatAt b pos | return none
    let some (tid, p2) := readNatAt b p1 | return none
    edges := edges.push (ord, tid)
    pos := p2
  if pos < b.size then return none
  return some ⟨entries, edges⟩

private abbrev Incoming := Nat × Nat × String
private def rStamp : RawCodec FileStamp :=
  rawMap (fun s => (s.seconds, s.nanoseconds, s.size, s.digest))
    (fun (sec, ns, size, digest) => some ⟨sec, ns, size, digest⟩)
    (rawPair cInt.toRawCodec (rawPair cNat.toRawCodec (rawPair cNat.toRawCodec cByteArray.toRawCodec)))

private def rTitle : RawCodec TitleRecord :=
  rawMap (fun t => (t.title, t.ordinal, t.pageDigest, t.targets, t.stamp))
    (fun (title, i, d, ts, stat) => some ⟨title, i, d, ts, stat⟩)
    (rawPair rawUtf8String (rawPair cNat.toRawCodec (rawPair cByteArray.toRawCodec
      (rawPair (rawArray cNat.toRawCodec) (rawOption rStamp)))))

private def rIncoming : RawCodec (Array Incoming) :=
  rawArray (rawPair cNat.toRawCodec (rawPair cNat.toRawCodec rawUtf8String))
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

private def putRows {α : Type} (dir : System.FilePath) (domain : String) (c : RawCodec (Array α))
    (rows : Array α) : IO (Option ByteArray) := do
  if rows.isEmpty then return none
  return some (← storeBlock dir domain (rawEnc c rows))

private def getRows {α : Type} (dir : System.FilePath) (domain : String) (c : RawCodec (Array α))
    (ref : Option ByteArray) : IO (Option (Array α)) := do
  let some digest := ref | return some #[]
  return (← readBlock dir domain digest).bind (rawDec c)

structure IndexDirectory where
  logical : ByteArray
  source : Array (Option String)
  titles : Array (Option ByteArray)
  incoming : Array (Option ByteArray)
  scan : Option ByteArray := none

private def rDirectory : RawCodec IndexDirectory :=
  rawMap (fun d => (d.logical, d.source, d.titles, d.incoming, d.scan))
    (fun (w, s, t, i, sc) => some ⟨w, s, t, i, sc⟩)
    (rawPair cByteArray.toRawCodec (rawPair (rawArray (rawOption rawUtf8String))
      (rawPair (rawArray (rawOption cByteArray.toRawCodec))
        (rawPair (rawArray (rawOption cByteArray.toRawCodec)) (rawOption cByteArray.toRawCodec)))))

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
  let some d := rawDec rDirectory header | return none
  let some w := openDemandWorld logical | return none
  if d.logical != hashBlock "obend.vault.index.world.1" logical || d.source != w.digests ||
      d.titles.size != numBuckets || d.incoming.size != numBuckets then return none
  return some d

def IndexDirectory.scanSummary (idx : IndexDirectory) (dir : System.FilePath) : IO (Option ScanSummary) := do
  let some digest := idx.scan | return none
  return (← readBlock dir "obend.vault.index.scan.1" digest).bind decodeScanSummary

def IndexDirectory.title? (idx : IndexDirectory) (dir : System.FilePath) (title : String) :
    IO (Option (Option TitleRecord)) := do
  let some key := idx.titles[bucketOf title]? | return none
  return (← getRows dir "obend.vault.index.titles.1" (rawArray rTitle) key).map
    (fun rows => rows.find? (fun t => t.title == title))

def IndexDirectory.backlinks (idx : IndexDirectory) (dir : System.FilePath) (target : Nat) :
    IO (Option (Array String)) := do
  let some key := idx.incoming[target % numBuckets]? | return none
  return (← getRows dir "obend.vault.index.incoming.1" rIncoming key).map fun rows =>
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
    Array.replicate numBuckets none, none⟩

private def sortEdgePairs (edges : Array (Nat × Nat)) : Array (Nat × Nat) :=
  edges.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- Incremental construction reads old title shards only for changed source buckets. A reverse
shard is rewritten exactly when a changed source bucket previously or currently cites its key,
and `ScanSummary` is updated incrementally whenever the set of present page IDs is unchanged. -/
private def updateIndex (dir : System.FilePath) (logical : ByteArray) (w : DemandWorld)
    (payload : Nat → IO (Option ShardPayload)) (observe : String → IO (Option FileStamp))
    (prev : IndexDirectory) (isFull : Bool) (prevScan? : Option ScanSummary := none) : IO (Option ByteArray) := do
  let mut titles := prev.titles
  let mut incoming := prev.incoming
  let dirty := (Array.range numBuckets).map fun b => isFull || prev.source[b]? != w.digests[b]?
  let mut affected := Array.replicate numBuckets false
  let mut removed : Std.HashSet (Nat × String) := {}
  let mut additions : Array (Array Incoming) := Array.replicate numBuckets #[]
  let mut scanEntries : Array ScanEntry := #[]
  let mut prevNonPresent : Array (Nat × Nat) := #[]
  let mut dirtyScanTargets : Array (Nat × Array Nat) := #[]
  let mut dirtyOrdinals : Std.HashSet Nat := {}
  let mut presentChanged := false
  if isFull then
    scanEntries := Array.replicate w.pages ⟨"", 0, 0, 0, 0, 0, 0⟩
  else
    let some prevScan ← (match prevScan? with | some s => pure (some s) | none => prev.scanSummary dir)
      | return none
    if prevScan.entries.size != w.pages then return none
    scanEntries := prevScan.entries
    prevNonPresent := prevScan.nonPresentEdges
  for b in [:numBuckets] do
    unless dirty[b]?.getD false do continue
    let some old ← getRows dir "obend.vault.index.titles.1" (rawArray rTitle) (titles[b]?.join) | return none
    let some (pages, _) ← payload b | return none
    let byName := old.foldl (fun (m : Std.HashMap String TitleRecord) r => m.insert r.title r) {}
    let pagesArr := pages.toArray
    let rows ← pagesArr.mapM (record observe byName)
    titles := titles.setIfInBounds b (← putRows dir "obend.vault.index.titles.1" (rawArray rTitle) rows)
    for idx in [:pagesArr.size] do
      let some (ordinal, p) := pagesArr[idx]? | return none
      let some row := rows[idx]? | return none
      if ordinal ≥ w.pages then return none
      let entry ← do
        if !isFull then
          let oldEntry := scanEntries[ordinal]!
          let reused := match byName[p.name]? with
            | some prevRow => prevRow.pageDigest == row.pageDigest && oldEntry.title == p.name
            | none => false
          if reused then
            pure { oldEntry with ordinal }
          else
            let fresh := mkScanEntry ordinal p row.stamp
            if oldEntry.pageId != fresh.pageId || oldEntry.hasHistory != fresh.hasHistory then
              presentChanged := true
            pure fresh
        else
          pure (mkScanEntry ordinal p row.stamp)
      scanEntries := scanEntries.setIfInBounds ordinal entry
      dirtyOrdinals := dirtyOrdinals.insert ordinal
      dirtyScanTargets := dirtyScanTargets.push (ordinal, row.targets)
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
  if !isFull && presentChanged then return none
  for k in [:numBuckets] do
    unless affected[k]?.getD false do continue
    let some old ← getRows dir "obend.vault.index.incoming.1" rIncoming (incoming[k]?.join) | return none
    let kept := old.filter fun (_, ordinal, title) => !removed.contains (ordinal, title)
    let rows := (kept ++ additions[k]?.getD #[]).qsort fun a b => a.2.1 < b.2.1
    incoming := incoming.setIfInBounds k (← putRows dir "obend.vault.index.incoming.1" rIncoming rows)
  let nonPresent ← do
    if isFull then
      let mut pids : Std.HashSet Nat := Std.HashSet.emptyWithCapacity scanEntries.size
      for e in scanEntries do
        if e.hasHistory then pids := pids.insert e.pageId
      let mut np : Array (Nat × Nat) := #[]
      for (ord, ts) in dirtyScanTargets do
        for t in ts do
          unless pids.contains t do np := np.push (ord, t)
      pure (sortEdgePairs np)
    else
      let mut wantTargets : Std.HashSet Nat := {}
      for (_, ts) in dirtyScanTargets do
        for t in ts do wantTargets := wantTargets.insert t
      let mut foundPresent : Std.HashSet Nat := {}
      unless wantTargets.isEmpty do
        for e in scanEntries do
          if e.hasHistory && wantTargets.contains e.pageId then
            foundPresent := foundPresent.insert e.pageId
      let mut np := prevNonPresent.filter fun (ord, _) => !dirtyOrdinals.contains ord
      for (ord, ts) in dirtyScanTargets do
        for t in ts do
          unless foundPresent.contains t do np := np.push (ord, t)
      pure (sortEdgePairs np)
  let scanDigest ← storeBlock dir "obend.vault.index.scan.1" (encodeScanSummary ⟨scanEntries, nonPresent⟩)
  let idx : IndexDirectory := ⟨hashBlock "obend.vault.index.world.1" logical, w.digests, titles, incoming, some scanDigest⟩
  return some (attachIndex logical (← storeBlock dir "obend.vault.index.root.1" (rawEnc rDirectory idx)))

def writeIndexedManifest (dir : System.FilePath) (logical : ByteArray)
    (payload : Nat → IO (Option ShardPayload)) (observe : String → IO (Option FileStamp))
    (previous : Option IndexDirectory) (prevScan? : Option ScanSummary := none) : IO (Option ByteArray) := do
  let some w := openDemandWorld logical | return none
  if let some prev := previous then
    if let some bytes ← updateIndex dir logical w payload observe prev false prevScan? then return some bytes
  updateIndex dir logical w payload observe emptyDirectory true none

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

/-- Walk all non-hidden `.md` files under `dir` with one `stat` per entry, matching against
`scan.entries` in linear time (in-place `visited` array, no `IO.Ref` copy). Returns `none` if any
file was added, removed, or duplicated; otherwise returns `(byTitle, candidates)` where
`candidates` lists every `(entryIdx, path)` whose `(mtime, size)` differs from the recorded stamp
or falls on the same filesystem tick as the checkpoint (`ckMod`). -/
def scanWorkingTree (dir : System.FilePath) (scan : ScanSummary)
    (ckMod : IO.FS.SystemTime) : IO (Option (Std.HashMap String Nat × Array (Nat × System.FilePath))) := do
  let n := scan.entries.size
  let mut byTitle : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity n
  for i in [:n] do
    byTitle := byTitle.insert scan.entries[i]!.title i
  if byTitle.size != n then return none
  let mut visited : Array Bool := Array.replicate n false
  let mut seenCount : Nat := 0
  let mut cands : Array (Nat × System.FilePath) := #[]
  let mut stack : Array (System.FilePath × String) := #[(dir, "")]
  while !stack.isEmpty do
    let (curDir, relPrefix) := stack.back!
    stack := stack.pop
    for e in ← curDir.readDir do
      let fn := e.fileName
      if fn.startsWith "." then continue
      let st ← e.path.metadata
      if st.type == .dir then
        stack := stack.push (e.path, relPrefix ++ fn ++ "/")
      else if st.type == .file && fn.endsWith ".md" then
        let some stem := (System.FilePath.mk fn).fileStem | return none
        let title := relPrefix ++ stem
        match byTitle[title]? with
        | none => return none
        | some idx =>
          if visited[idx]! then return none
          visited := visited.set! idx true
          seenCount := seenCount + 1
          let entry := scan.entries[idx]!
          let sameStamp := entry.hasStamp &&
            st.modified.sec == entry.seconds &&
            st.modified.nsec.toNat == entry.nanoseconds &&
            st.byteSize.toNat == entry.size &&
            st.modified != ckMod
          unless sameStamp do
            cands := cands.push (idx, e.path)
  if seenCount != n then return none
  return some (byTitle, cands)

end Obend.Vault.ChunkedWorld
