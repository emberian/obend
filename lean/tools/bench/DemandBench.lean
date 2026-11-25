import Obend.SemanticKG.ColtJoin
import Obend.Vault.WorldTree.IndexedManifest

open Obend.SemanticKG Obend.Vault Obend.Vault.ChunkedWorld

private def timed {α : Type} (label : String) (action : IO α) : IO α := do
  let start ← IO.monoNanosNow
  let result ← action
  let stop ← IO.monoNanosNow
  IO.println s!"{label} {(stop-start).toFloat / 1000000.0} ms"
  return result

private def page (i : Nat) (version : Nat := 0) : Page :=
  let name := s!"acct/P{i}"
  let body := s!"# Account {i}\n\nbalance: {i%61+version}\n"
  let graph : Obend.Doc.Graph := { atoms := [(i, .text body)] }
  ⟨name, i, [graph], some body, [], none, none⟩

private def fixture (dir : System.FilePath) (n : Nat) : IO Unit := do
  let w : World := { store := { pages := (List.range n).map (fun i => page i) } }
  let (mb, _) ← commitWorldManifest dir w
  let some _ ← writeShardedWorld dir 0 w (some ⟨mb.toArray⟩) | throw (IO.userError "fixture write failed")
  IO.FS.writeBinFile (dir / "manifest") ⟨mb.toArray⟩

private def readShard (dir : System.FilePath) (count : IO.Ref Nat) (key : String) : IO (Option ByteArray) := do
  count.modify (·+1)
  return some (← IO.FS.readBinFile (shardPath dir key))

private def vault (dir : System.FilePath) (n : Nat) (full edit : Bool) : IO Unit := do
  let newPage := page (n/2) 1
  let count ← IO.mkRef 0
  let root ← timed (if edit then "replace" else "lookup") do
    let bytes ← IO.FS.readBinFile (dir / "manifest")
    if full then
      let some w ← loadShardedWorld dir bytes | throw (IO.userError "bad full checkpoint")
      let some _ := w.store.page? newPage.name | throw (IO.userError "missing full title")
      if edit then
        let w' := { w with store := w.store.setPage newPage }
        let (mb, buckets) := encodeWorldIncremental w' (← getCachedBuckets dir)
        if let some (digest, raw) := buckets[bucketOf newPage.name]?.bind (·.entry?) then
          writeFileAtomicArray (shardPath dir (shardKey (bucketOf newPage.name) digest)) raw
        writeFileAtomicArray (dir / "next-manifest") mb
        return mb
      return bytes
    let some d := openDemandWorld bytes | throw (IO.userError "bad directory")
    if edit then
      let b := bucketOf newPage.name
      let some (next, cb) ← d.edit (readShard dir count) newPage | throw (IO.userError "bad shard")
      if let some (digest, raw) := cb.entry? then writeFileAtomicArray (shardPath dir (shardKey b digest)) raw
      let mb := next.manifest
      writeFileAtomicArray (dir / "next-manifest") mb
      return mb
    let some (some _) ← d.getPage (readShard dir count) newPage.name | throw (IO.userError "missing demand title")
    return bytes
  IO.println s!"root={Obend.Codec.Hex.bytesToHex (logHashArray root)}"
  unless full do IO.println s!"shards_read={← count.get}"

private def joins (n : Nat) (reference : Bool) : IO Unit := do
  let rows := Array.range n
  let cols := [rows.map (·%256), rows.map (·/256)]
  let keys := (Array.range 1200).map fun i => [i%3, i%41]
  let output ← timed (if reference then "scan" else "COLT") do
    Obend.Vault.Cost.compute fun _ => (if reference then Colt.relationalJoin else Colt.coltJoin) keys cols n
  IO.println s!"groups={output.size} matches={output.foldl (fun s rs => s+rs.size) 0} checksum={hash output}"

private def triangles (n : Nat) (reference : Bool) : IO Unit := do
  let x := Array.range n
  let y := x.map (·+1)
  let z := y.map (·+1)
  let db : Array Colt.Relation := #[⟨[x, y], n⟩, ⟨[y, z], n⟩, ⟨[x, z], n⟩]
  let steps : Array Colt.JoinStep := #[⟨⟨0, []⟩, 0, #[⟨2, [0]⟩]⟩,
    ⟨⟨0, [0]⟩, 1, #[⟨1, [1]⟩]⟩, ⟨⟨1, [1]⟩, 1, #[⟨2, [0, 2]⟩]⟩]
  let rows ← timed "triangle" (Obend.Vault.Cost.compute fun _ =>
    (if reference then Colt.relationalPlan else Colt.freeJoin) db steps)
  unless rows.size == n do throw (IO.userError "missing triangle")
  IO.println s!"triangles={rows.size} checksum={hash rows}"

/-- Validate the published directory against an independent full checkpoint load and the
actual working file. This exercises the same directory used by the CLI's next checkpoint. -/
private def checkIndex (dir : System.FilePath) (name : String) : IO Unit := do
  let file ← IO.FS.readBinFile (dir / ".obend" / "checkpoint")
  let some nl := (Array.range (min file.size 200)).find? (fun i => file[i]! == 10)
    | throw (IO.userError "invalid checkpoint header")
  let physical := file.extract (nl+1) file.size
  let (logical, some _) := splitIndex physical | throw (IO.userError "checkpoint has no index")
  let some idx ← openIndex dir physical | throw (IO.userError "invalid directory")
  let some world ← loadShardedWorld dir logical | throw (IO.userError "invalid logical checkpoint")
  let some p := world.store.page? name | throw (IO.userError "page absent")
  let some (some row) ← idx.title? dir name | throw (IO.userError "title missing in index")
  unless row.matchesPage p && (world.store.pages[row.ordinal]?.map (·.name)) == some name do
    throw (IO.userError "title or digest disagrees with full world")
  let some stamp := row.stamp | throw (IO.userError "no working file observed")
  let path := dir / (name ++ ".md")
  let fileInfo ← path.metadata
  unless stamp.seconds == fileInfo.modified.sec && stamp.nanoseconds == fileInfo.modified.nsec.toNat &&
      stamp.matchesBytes (← IO.FS.readBinFile path) do throw (IO.userError "working file changed")
  let expected := world.store.pages.filterMap fun q => do
    let g ← q.current
    guard (citesPage g p.id)
    return q.name
  let some links ← idx.backlinks dir p.id | throw (IO.userError "invalid backlink directory")
  unless expected == links.toList do throw (IO.userError "backlink order or membership differs")
  IO.println s!"title={name} ordinal={row.ordinal} incoming={links.size} checked_bytes={stamp.size}"

private def indexedReplacement (dir : System.FilePath) (name : String) : IO Unit := do
  let file ← IO.FS.readBinFile (dir / ".obend" / "checkpoint")
  let some nl := (Array.range (min file.size 200)).find? (fun i => file[i]! == 10)
    | throw (IO.userError "invalid checkpoint header")
  let physical := file.extract (nl+1) file.size
  let (logical, some _) := splitIndex physical | throw (IO.userError "checkpoint has no index")
  let some world ← loadShardedWorld dir logical | throw (IO.userError "invalid logical checkpoint")
  let some old := world.store.page? name | throw (IO.userError "page absent")
  -- Change an authenticated page field. The working file is unchanged in this storage workload.
  let p := { old with note := some "replacement benchmark" }
  let observations := fun title => observeFile (dir / (title ++ ".md"))
  let count ← IO.mkRef 0
  let some (incremental, cb) ← timed "indexed-replace" (editIndexedManifest dir physical p
      (readShard dir count) observations) | throw (IO.userError "point edit failed")
  let (full, buckets) := encodeWorldIncremental {world with store := world.store.setPage p} none
  let some rebuilt ← timed "rebuild-all-indexes" (writeIndexedManifest dir full
    (fun b => pure (buckets[b]?.map (·.payload))) observations none)
    | throw (IO.userError "full index rebuild failed")
  unless incremental == rebuilt do throw (IO.userError "physical roots differ")
  unless cb.entry?.isSome do throw (IO.userError "missing edited shard")
  IO.println s!"identical_physical_bytes={rebuilt.size} data_shards_read={← count.get}"

private def parseCount (s : String) : IO Nat := do
  let some n := s.toNat? | throw (IO.userError "expected a nonnegative row count")
  return n

def main (args : List String) : IO Unit := do
  match args with
  | ["index-edit", path, name] => indexedReplacement path name
  | ["check-index", path, name] => checkIndex path name
  | ["seed", path, n] => fixture path (← parseCount n)
  | ["vault", path, n, mode, op] =>
    unless ["full", "demand"].contains mode && ["open", "edit"].contains op do
      throw (IO.userError "vault DIR N (full|demand) (open|edit)")
    vault path (← parseCount n) (mode == "full") (op == "edit")
  | [op, n, mode] =>
    unless ["scan", "colt"].contains mode do throw (IO.userError "expected scan or colt")
    let count ← parseCount n
    match op with
    | "triangle" => triangles count (mode == "scan")
    | "join" => joins count (mode == "scan")
    | _ => throw (IO.userError "expected triangle or join")
  | _ => throw (IO.userError "expected seed, vault, check-index, index-edit, triangle, or join")
