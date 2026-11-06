module
/-
# Obend.Vault.Cli — `obend open` and the vault commands

    obend open [DIR]
        read every `.md` under DIR (default `.`; directories starting with `.` are skipped) as a page,
        keep the world beside it in DIR/.obend/ (its log), resolve links whose pages now exist, render
        each page at the current view back to its file (a cite that does not hold is marked,
        `![[Beta]]{behind}`; the reader strips the marks, so a mark is never read as an edit), and
        report what changed, what was refused, which cites are behind and which sections wait for a
        selection. A file removed is a page deleted (its cites go `missing`; its history is kept and
        a file of its name revives it), unless a kind's laws govern the page, which is then written
        back; a new file carrying a deleted page's text is that page renamed (`Store.forgetMissing`).
        Twice in a row, the second changes nothing.
    obend status [PAGE]
        open, then every page (or PAGE) with its version, each cite and whether it holds, its sections,
        and, where a kind page names an `environment:`, the backticked names it cites that the
        environment lacks.
    obend merge OTHER_DIR
        open both, then merge every page of OTHER_DIR's world into this one (the pushout of the two
        current versions); a page OTHER_DIR has alone is imported.
    obend member add NAME --grant VERB:PATTERN [--grant …]
        a member; VERB is post, select, write (re-cite) or relaw; PATTERN is a page, `folder/*` or `*`.
    obend member list
    obend post PAGE FILE [--as NAME] [--append | --into HEADING]
        a text for PAGE (FILE, or `-` for stdin): the whole page; with `--append`, PAGE's text with
        FILE's lines after it; with `--into HEADING`, with FILE's lines at the end of the row the
        heading HEADING begins. By a member (`--as NAME`), NAME's proposal, as candidates in sections;
        by the owner, the owner's write of PAGE, judged by its laws: admitted, the file is rendered;
        refused, the file is untouched and the refusal names the law and what would pass.
    obend select PAGE SECTION CANDIDATE [--as NAME]
        keep one candidate of a section; the owner, or a member granted select on PAGE.
    obend recite PAGE [--as NAME]
        re-justify PAGE's cites that are behind against their sources' current versions.
    obend create --from KIND PAGE
        a new page born under KIND (a kind page `folder/_kind`, or the folder): it names KIND in its
        frontmatter, starts with KIND's fields, and its birth is judged by KIND's laws.

    obend log [records]
        the log, read only: its records, a torn tail it drops, the checkpoint, and the world replayed
        from genesis, from the checkpoint, and as the last record commits to it, which must be one.

Every command but `member` opens the vault first (an edit on disk is the owner's write, judged by
the page's laws), so no command overwrites a file the person changed. Every change of the world is a
turn appended to `DIR/.obend/log` before any file is written (`commitTurn`); the world a command
starts from is the replay of the log, through `DIR/.obend/checkpoint` where it holds (`recoverLog`); a
torn tail is dropped by name and a turn whose files did not land is redone (`recoverForWrite`). The
log is appended with a flush and no fsync (Lean's `IO` has none): a stopped process loses nothing it
appended, a power loss can lose the records the kernel had not written, never more than a tail.
`-C DIR` before or after a command runs it in DIR. A kind page's line `environment: PATH` (PATH
relative to the vault) names the census's list of the library's names,
`.lake/build/census/environment.txt` (`lake build Obend.Census`, or `lake env lean
tests/decisions/Environment.lean`): the open reads it and the page's backticked names resolve against
it (`new.unresolved`, `new.unresolvedInserted`); a named file that is not there stops the command.
-/
public import Obend.Vault.Replay
public section

namespace Obend.Vault.Cli

open Obend.Doc Obend.Vault Obend.Vault.Json Obend.Vault.Log Obend.Vault.Replay

/-- The deployed byte hash (cSHAKE256, as `lean/tests/doc/RoundTrip.lean`); the log replays with it. -/
def H : Obend.Digest.HashBytes.Hash := Obend.Vault.Replay.H

/-- Every `.md` under `dir`, by name (its path from `dir` without `.md`), sorted. -/
def readVault (dir : System.FilePath) : IO (List (String × String)) := do
  let files ← System.FilePath.walkDir dir fun p => pure !((p.fileName.getD "").startsWith ".")
  let mut out : Array (String × String) := #[]
  let pre := dir.toString ++ "/"
  for f in files do
    if f.extension == some "md" && !(← f.isDir) then
      let rel := if f.toString.startsWith pre then String.ofList (f.toString.toList.drop pre.length) else f.toString
      let name := String.ofList (rel.toList.take (rel.length - 3))
      out := out.push (name, ← IO.FS.readFile f)
  return (out.toList.mergeSort fun a b => decide (a.1 ≤ b.1))

/-- The world from before the log (an earlier `obend`'s whole-world file); adopted as the log's first
record, then renamed `world.json.adopted`. -/
def worldPath (dir : System.FilePath) : System.FilePath := dir / ".obend" / "world.json"
/-- The register's journal from before the log; adopted with `world.json`. -/
def legacyLedgerPath (dir : System.FilePath) : System.FilePath := dir / ".obend" / "ledger.json"
/-- **The log**: the vault's only truth. -/
def logPath (dir : System.FilePath) : System.FilePath := dir / ".obend" / "log"
/-- The checkpoint: a cache of the world after the log's first records. -/
def checkpointPath (dir : System.FilePath) : System.FilePath := dir / ".obend" / "checkpoint"
/-- The lock a command holds while it reads, appends to and checkpoints the log. -/
def lockPath (dir : System.FilePath) : System.FilePath := dir / ".obend" / "lock"

/-- A vault: a directory with a log, a checkpoint or a world from before the log. -/
def isVault (dir : System.FilePath) : IO Bool := do
  return (← (logPath dir).pathExists) || (← (checkpointPath dir).pathExists) || (← (worldPath dir).pathExists)

/-- The environment the vault's pages name (`environment: PATH` in a frontmatter; a kind page's, as
a rule), read from PATH relative to the vault: the census's file, its `#` lines dropped
(`Obend.Vault.Page`, "Names cited in backticks"). A named file that is not there stops the command. -/
def loadEnvironment (dir : System.FilePath) (V : List (String × String)) : IO Environment := do
  let mut names : List String := []
  for (n, md) in V do
    for (k, path) in frontFields md do
      if k == "environment" then
        let f := dir / path
        unless ← f.pathExists do
          throw (IO.userError (n ++ ": its environment " ++ path ++ " is not there; write it with " ++
            "`lake build Obend.Census` (tier 2) or `cd lean && lake env lean tests/decisions/Environment.lean`"))
        let txt ← IO.FS.readFile f
        names := names ++ (txt.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"
  return environmentOf names

/-- The world from before the log, if the vault has one. -/
def legacyWorld (dir : System.FilePath) : IO (Option Replay.World) := do
  let hasW ← (worldPath dir).pathExists
  let hasL ← (legacyLedgerPath dir).pathExists
  if !hasW && !hasL then return none
  let s ← if hasW then
      match Lean.Json.parse (← IO.FS.readFile (worldPath dir)) >>= storeOf with
      | .ok s => pure s
      | .error e => throw (IO.userError ("cannot read " ++ (worldPath dir).toString ++ ": " ++ e))
    else pure {}
  let J ← if hasL then
      match Lean.Json.parse (← IO.FS.readFile (legacyLedgerPath dir)) >>= Obend.Ledger.Json.journalOf with
      | .ok j => pure j
      | .error e => throw (IO.userError ("cannot read " ++ (legacyLedgerPath dir).toString ++ ": " ++ e))
    else pure Obend.Ledger.Json.Journal.empty
  return some ⟨s, J⟩

/-! ## The log on disk -/

def readBytes (f : System.FilePath) : IO Bytes := do
  if !(← f.pathExists) then return []
  return (← IO.FS.readBinFile f).toList

/-- A checkpoint's file: `obend-checkpoint 1 COUNT START STOP ANCHOR`, a newline, the world's bytes. -/
def checkpointBytes (ck : Checkpoint) : Bytes :=
  textBytes ("obend-checkpoint 1 " ++ toString ck.count ++ " " ++ toString ck.start ++ " " ++
    toString ck.stop ++ " " ++ toString ck.anchor ++ "\n") ++ ck.world

def readCheckpoint (dir : System.FilePath) : IO (Option Checkpoint) := do
  let bs ← readBytes (checkpointPath dir)
  if bs.isEmpty then return none
  let line := bs.takeWhile (· != 10)
  let some txt := bytesText line | return none
  match txt.splitOn " " with
  | ["obend-checkpoint", "1", c, a, b, h] =>
    match c.toNat?, a.toNat?, b.toNat?, h.toNat? with
    | some c, some a, some b, some h => return some ⟨c, a, b, h, bs.drop (line.length + 1)⟩
    | _, _, _, _ => return none
  | _ => return none

/-- Write a file whole or not at all: beside it, then renamed over it. -/
def writeAtomically (f : System.FilePath) (bs : Bytes) : IO Unit := do
  let tmp := f.withExtension "tmp"
  IO.FS.writeBinFile tmp ⟨bs.toArray⟩
  IO.FS.rename tmp f

/-- What a process holds of a vault's log: the world (the replay of the log), the receipt digest of
the last record, how many records there are, the log's length and where its last record starts. -/
structure Head where
  world : Replay.World
  prev : Nat := Rehydration.genesisSentinel
  count : Nat := 0
  size : Nat := 0
  lastStart : Nat := 0

/-- The digest of a world, as `obend log` says it: the first 16 hex digits of its commitment. -/
def worldDigest (w : Replay.World) : String :=
  String.ofList ((hex (be 32 (dig logHash (encodeWorld w)))).toList.take 16)

/-- **Write a checkpoint** of the head's world, anchored to the log's last record, after checking that
the world's bytes decode to the world (`checkpoint_is_cache`'s premise). -/
def saveCheckpoint (dir : System.FilePath) (h : Head) : IO Unit := do
  if h.count == 0 then return
  let wb := encodeWorld h.world
  if decodeWorld wb != some h.world then
    IO.eprintln "checkpoint not written: the world's bytes do not decode to the world (the log stays the truth)"
    return
  writeAtomically (checkpointPath dir) (checkpointBytes ⟨h.count, h.lastStart, h.size, h.prev, wb⟩)

/-- The test-only write barrier (`OBEND_TEST_TEAR=N:K:PATH`): appending record `N`, write its first `K`
bytes (`all`: the whole record, and stop before its files are written), create `PATH` and wait to be
stopped. `lean/tests/vault/CRASH.md` stops the process there by its PID. -/
def tearAt (n : Nat) : IO (Option (Option Nat × String)) := do
  let some v ← IO.getEnv "OBEND_TEST_TEAR" | return none
  match v.splitOn ":" with
  | nStr :: kStr :: rest =>
    if nStr.toNat? != some n then return none
    let k := if kStr == "all" then none else kStr.toNat?
    return some (k, ":".intercalate rest)
  | _ => return none

def waitToBeStopped (barrier : String) : IO Unit := do
  IO.FS.writeFile barrier "stopped here\n"
  repeat IO.sleep 1000

/-- Append a record's bytes to the log (the barrier aside). -/
def appendRecord (dir : System.FilePath) (n : Nat) (bs : Bytes) : IO Unit := do
  let tear ← tearAt n
  let h ← IO.FS.Handle.mk (logPath dir) .append
  match tear with
  | some (some k, barrier) =>
    h.write ⟨(bs.take k).toArray⟩
    h.flush
    waitToBeStopped barrier
  | _ =>
    h.write ⟨bs.toArray⟩
    h.flush
  if let some (none, barrier) := tear then waitToBeStopped barrier

/-- **Commit a turn**: admit its bytes at the head (`Obend.Vault.Log.admit` at the deployed machine)
and append the record; the head after it and what the turn said, or the refusal (nothing appended). -/
def commitTurn (dir : System.FilePath) (h : Head) (t : Turn) : IO (Except String (Head × Outcome)) := do
  match Log.admit logHash deployed h.world h.prev (encodeTurn t) with
  | .error e => return .error e
  | .ok (w', o, r) =>
    let bs := encodeRecord logHash r
    appendRecord dir (h.count + 1) bs
    let h' : Head :=
      { world := w'
        prev := Hr logHash r.receipt
        count := h.count + 1
        size := h.size + bs.length
        lastStart := h.size }
    return .ok (h', o)

/-- What recovery read: the head, the records after the checkpoint (all of them without one) and the
world before them, the dropped tail and why, and what became of the checkpoint. -/
structure Recovery where
  head : Head
  base : Replay.World
  suffix : List Record
  tail : Bytes
  why : Option Drop
  checkpoint : String

def dropText : Drop → String
  | .torn => "torn: the bytes end inside a record"
  | .magic => "magic: it does not start a record"
  | .digest => "digest: its turn is not the one its receipt names"
  | .seal => "seal: its receipt is not the one its seal names"
  | .link => "link: it does not follow the record before it"

/-- **Recover a vault's world from its log**, through the checkpoint where it holds
(`Obend.Vault.Log.recoverWith`; `checkpoint_is_cache`), reading nothing past the longest prefix of
whole, linked records (`recover_eq_replay_prefix`). The replayed world must commit to what the last
record's receipt names; otherwise the command stops. -/
def recoverLog (dir : System.FilePath) : IO Recovery := do
  let bs ← readBytes (logPath dir)
  let ck? ← readCheckpoint dir
  let held := ck?.bind fun ck => (ck.holds logHash decodeWorld bs).map (ck, ·)
  let (base, anchor, from_, count0, note) := match ck?, held with
    | _, some (ck, w) => (w, ck.anchor, ck.stop, ck.count, "the world after record " ++ toString ck.count)
    | some _, none => (genesis, Rehydration.genesisSentinel, 0, 0,
        "dropped (it does not hold against the log); the world is replayed from genesis")
    | none, none => (genesis, Rehydration.genesisSentinel, 0, 0, "none; the world is replayed from genesis")
  let (qs, tail, why) := parseFrom logHash anchor (bs.drop from_)
  let world := replay deployed base qs
  let size := from_ + (encodeAll logHash qs).length
  let count := count0 + qs.length
  let lastStart := match qs.getLast? with
    | some r => size - (encodeRecord logHash r).length
    | none => match held with
      | some (ck, _) => ck.start
      | none => 0
  -- the replayed world commits to what the last record's receipt names
  let last? : Option Record := match qs.getLast? with
    | some r => some r
    | none => match held with
      | some (ck, _) => match parseOne logHash none ((bs.drop ck.start).take (ck.stop - ck.start)) with
        | .ok (r, _) => some r
        | .error _ => none
      | none => none
  if let some r := last? then
    if r.receipt.newCommit != dig logHash (encodeWorld world) then
      throw (IO.userError ("the log's replay does not reach the world record " ++ toString count ++
        " commits to: the log was written by another step (relinking is not done here)"))
  return ⟨⟨world, lastHash logHash anchor qs, count, size, lastStart⟩, base, qs, tail, why, note⟩

/-- The world from the log, read only (nothing is truncated, rewritten or redone). -/
def readWorld (dir : System.FilePath) : IO Replay.World := do
  if !(← (logPath dir).pathExists) then
    if let some w ← legacyWorld dir then return w
  return (← recoverLog dir).head.world

def loadStore (dir : System.FilePath) : IO Store := return (← readWorld dir).store

/-- A file's text, if it is there. -/
def readText? (f : System.FilePath) : IO (Option String) := do
  if ← f.pathExists then return some (← IO.FS.readFile f) else return none

/-- **Redo a turn's files** after a crash between its record and its files: each page whose file is
not the text the turn left, and is still the text the turn found (the file it read for an open, the
text the world before it had seen otherwise), is written; a posting's receipt and page are written
when they are not there. A file changed since is left alone (the next open judges it). -/
def redoFiles (dir : System.FilePath) (before : Replay.World) (t : Turn) (after : Replay.World) (o : Outcome) :
    IO (List String) := do
  let found (n : String) : Option String := match t with
    | .opened files _ => (reconstruct before.store files).lookup n
    | _ => seenOf before.store n
  let mut done : List String := []
  for p in after.store.pages do
    if let some txt := p.seen then
      let f := dir / (p.name ++ ".md")
      let cur ← readText? f
      if cur != some txt && cur == found p.name then
        if let some parent := f.parent then IO.FS.createDirAll parent
        IO.FS.writeFile f txt
        done := done ++ [p.name ++ ".md"]
  if let .rows fs := o then
    for rf in fs do
      IO.FS.createDirAll (dir / ".obend" / "receipts")
      IO.FS.writeFile (dir / ".obend" / "receipts" / (rf.id ++ ".json")) rf.receipt
      done := done ++ [".obend/receipts/" ++ rf.id ++ ".json"]
      let pf := dir / "register" / (rf.id ++ ".md")
      unless ← pf.pathExists do
        IO.FS.createDirAll (dir / "register")
        IO.FS.writeFile pf rf.page
        done := done ++ ["register/" ++ rf.id ++ ".md"]
  return done

/-- **Open a vault's log for a command**: adopt a world from before the log as its first record; drop a
torn tail by name; redo the files of a turn whose record is whole but whose files may not be; write
the checkpoint. Says what it did only when it did something. -/
def recoverForWrite (dir : System.FilePath) : IO Head := do
  IO.FS.createDirAll (dir / ".obend")
  if !(← (logPath dir).pathExists) then
    if let some w ← legacyWorld dir then
      match ← commitTurn dir { world := genesis } (.base w) with
      | .ok (h, _) =>
        saveCheckpoint dir h
        if ← (worldPath dir).pathExists then IO.FS.rename (worldPath dir) (dir / ".obend" / "world.json.adopted")
        if ← (legacyLedgerPath dir).pathExists then
          IO.FS.rename (legacyLedgerPath dir) (dir / ".obend" / "ledger.json.adopted")
        IO.println "adopted the world from before the log as its first record"
      | .error e => throw (IO.userError ("cannot adopt the world from before the log: " ++ e))
  let r ← recoverLog dir
  if !r.tail.isEmpty then
    IO.println ("recovered: dropped a tail of " ++ toString r.tail.length ++ " bytes after record " ++
      toString r.head.count ++ " (" ++ ((r.why.map dropText).getD "") ++ ")")
    writeAtomically (logPath dir) ((← readBytes (logPath dir)).take r.head.size)
  match r.suffix.getLast? with
  | none => pure ()
  | some last =>
    let before := replay deployed r.base r.suffix.dropLast
    match decodeTurn last.payload, deployed.step before last.payload with
    | .ok t, .ok (after, o) =>
      let done ← redoFiles dir before t after o
      unless done.isEmpty do
        IO.println ("recovered: record " ++ toString r.head.count ++ " (" ++ t.kind ++
          ") was whole and its files were not: wrote " ++ ", ".intercalate done)
    | _, _ => pure ()
    saveCheckpoint dir r.head
  return r.head

/-- Run `k` holding the vault's lock, from the log as recovered. -/
def withLog {α : Type} (dir : System.FilePath) (k : Head → IO α) : IO α := do
  IO.FS.createDirAll (dir / ".obend")
  let lk ← IO.FS.Handle.mk (lockPath dir) .append
  lk.lock
  try
    k (← recoverForWrite dir)
  finally
    lk.unlock

/-- Commit one turn under the lock and write the checkpoint after `files` has written its files. -/
def commitWith {α : Type} (dir : System.FilePath) (t : Turn) (files : Head → Outcome → IO α) :
    IO (Except String α) :=
  withLog dir fun h => do
    match ← commitTurn dir h t with
    | .error e => return .error e
    | .ok (h', o) =>
      let a ← files h' o
      saveCheckpoint dir h'
      return .ok a

def writeFiles (dir : System.FilePath) (w : List (String × String)) : IO Unit :=
  for (n, t) in w do
    let f := dir / (n ++ ".md")
    if let some parent := f.parent then IO.FS.createDirAll parent
    IO.FS.writeFile f t

/-- What changed between two stores, page by page. -/
def changes (s s' : Store) : List String :=
  s'.pages.filterMap fun p' =>
    match s.page? p'.name with
    | none =>
      if p'.history.isEmpty then some (p'.name ++ ": not born: " ++ p'.note.getD "")
      else some (p'.name ++ ": new page (v1)")
    | some p =>
      if p'.history.length > p.history.length then
        some (p'.name ++ ": v" ++ toString p'.history.length ++ " written")
      -- a refused write is said when it is a new write: a different text (as the reader reads it,
      -- the view's marks stripped) or a different refusal
      else if p'.note.isSome && (p'.note != p.note || typed p' != typed p) then some (p'.name ++ ": " ++ p'.note.getD "")
      else none
where
  typed (q : Page) : Option (List Tok) := q.seen.map fun t => stripToks (tokens t)

/-- Cites that do not hold and sections waiting, over every page. -/
def problems (s : Store) : List String :=
  s.pages.flatMap fun p =>
    ((citeReport H s p).filterMap fun (c, ok, why) => if ok then none else some (p.name ++ ": " ++ c ++ " is " ++ why)) ++
      (sectionReport p).map (p.name ++ ": " ++ ·)

/-- What `forgetMissing` did, as lines: a page renamed is not also reported deleted. -/
def forgottenLines (f : Forgotten) : List String :=
  ((f.deleted.filter fun n => !f.renamed.any (·.1 == n)).map fun n => n ++ ": deleted (its file is gone; v" ++
      toString (((f.store.tombs.find? (·.name == n)).map (·.history.length)).getD 0) ++
      " kept; a file " ++ n ++ ".md revives it)") ++
    (f.renamed.map fun (o, n) => o ++ ": renamed to " ++ n ++ " (same page, v" ++
      toString (((f.store.page? n).map (·.history.length)).getD 0) ++ "; links to " ++ o ++ " still hold)") ++
    (f.revived.map fun n => n ++ ": revived (v" ++
      toString (((f.store.page? n).map (·.history.length)).getD 0) ++ ")") ++
    (f.kept.map fun (n, by_) => n ++ ": its file is gone, but it is under " ++ by_ ++ ": not deleted, written back")

/-- Pages whose birth stays refused: said again at every open, so a refusal is not seen once. -/
def unbornLines (s : Store) (already : List String) : List String :=
  s.pages.filterMap fun p =>
    if p.history.isEmpty then
      match p.note with
      | some n => if already.any (·.startsWith (p.name ++ ": not born")) then none
          else some (p.name ++ ": still not born: " ++ n)
      | none => none
    else none

/-- **Open the vault**: read the files and the environment, commit the open as a turn (its record
carries the files whose text the world has not seen, `readingOf`), then render and write the files it
changed and checkpoint. Returns the world and the files as they now are. -/
def openWorld (dir : System.FilePath) (verbose : Bool) : IO (Replay.World × List (String × String)) := do
  withLog dir fun h => do
    let V ← readVault dir
    let env ← loadEnvironment dir V
    match ← commitTurn dir h (.opened (readingOf h.world.store V) (envOf h.world.store env)) with
    | .error e => throw (IO.userError ("the open was refused: " ++ e))
    | .ok (h', .opened f o) =>
      -- a page a kind's laws keep is written back from the text the store holds for it
      let back := f.kept.filterMap fun (n, _) => (o.store.page? n).bind fun p => p.seen.map (n, ·)
      writeFiles dir (o.writes ++ back)
      saveCheckpoint dir h'
      if verbose then
        -- changes are read against the store after deletions and renames: a renamed page is not new
        let cs := changes f.store o.store
        let fl := forgottenLines f
        let ul := unbornLines o.store cs
        if cs.isEmpty && fl.isEmpty then IO.println "nothing changed"
        for c in fl do IO.println c
        for c in cs do IO.println c
        for c in ul do IO.println c
        for (n, _) in o.writes ++ back do IO.println ("rendered " ++ n ++ ".md")
      return (h'.world, overwrite (V ++ back) o.writes)
    | .ok (_, _) => throw (IO.userError "the open said what an open does not")

def openDir (dir : System.FilePath) (verbose : Bool) : IO (Store × List (String × String)) := do
  let (w, V) ← openWorld dir verbose
  return (w.store, V)

/-- **Commit a command's turn** and write the files its store renders: each page whose file
differs from the text the store holds for it, and each page that has no file. Returns the store, what
the turn said and the files written, or the refusal (nothing logged, nothing written). -/
def finishTurn (dir : System.FilePath) (t : Turn) (V : List (String × String)) :
    IO (Except String (Replay.World × Outcome × List String)) :=
  withLog dir fun h => do
    match ← commitTurn dir h t with
    | .error e => return .error e
    | .ok (h', o) =>
      let s := h'.world.store
      let w := writesFor s V
      let missing := s.pages.filterMap fun p => if V.any (·.1 == p.name) then none else
        match p.seen, p.history with
        | some t, _ :: _ => some (p.name, t)
        | _, _ => none
      writeFiles dir (w ++ missing)
      saveCheckpoint dir h'
      return .ok (h'.world, o, (w ++ missing).map fun (n, _) => "rendered " ++ n ++ ".md")

def statusOf (s : Store) (only : Option String) : List String :=
  ((s.pages.filter fun p => only.all (· == p.name)).flatMap fun p =>
    [p.name ++ " v" ++ toString p.history.length ++ (match p.note with | some n => "; its last write was " ++ n | none => "")] ++
      (if s.environment.isEmpty then [] else match p.current with
        | some G =>
          let ns := unresolvedNames s.environment (settled G)
          if ns.isEmpty then [] else ["  names the environment lacks: " ++ ", ".intercalate ns]
        | none => []) ++
      (citeReport H s p).map (fun (c, ok, why) => "  " ++ c ++ (if ok then " ✓ " else " ✗ ") ++ why) ++
      (sectionReport p).map ("  " ++ ·)) ++
  ((s.tombs.filter fun p => only.all (· == p.name)).map tombLine) ++
  (match only with
    | some n => if s.pages.any (·.name == n) || s.tombs.any (·.name == n) then [] else [n ++ ": no such page"]
    | none => [])

def fail (msg : String) : IO UInt32 := do IO.eprintln msg; return 2

/-- `--as NAME` and `--grant G` flags, and the rest. -/
def flag (name : String) : List String → Option String × List String
  | [] => (none, [])
  | f :: v :: rest => if f == name then (some v, rest) else
    let (r, rest') := flag name (v :: rest)
    (r, f :: rest')
  | [x] => (none, [x])

/-- A bare flag (`--append`), and the rest. -/
def bare (name : String) : List String → Bool × List String
  | [] => (false, [])
  | x :: rest => let (b, r) := bare name rest; if x == name then (true, r) else (b, x :: r)

/-- `addition` after `cur`, on its own line. -/
def appendText (cur addition : String) : String :=
  cur ++ (if cur.isEmpty || cur.endsWith "\n" then "" else "\n") ++ addition

/-- `addition`'s lines at the end of the row the heading `heading` begins in `cur` (before the blank
lines that close the row), or why not. -/
def insertInto (cur heading addition : String) : Except String String :=
  let ls := cur.splitOn "\n"
  let titled (l : String) : Option Nat :=
    (headingLevel l).bind fun lvl => if trim (String.ofList (l.toList.drop (lvl + 1))) == heading then some lvl else none
  match ls.zipIdx.findSome? (fun (l, i) => (titled l).map (i, ·)) with
  | none => .error ("no heading `" ++ heading ++ "` in the page")
  | some (i, lvl) =>
    let after := ls.drop (i + 1)
    let n := (after.zipIdx.findSome? fun (l, j) =>
      (headingLevel l).bind fun k => if k ≤ lvl then some j else none).getD after.length
    let row := after.take n
    let blank (l : String) : Bool := l.toList.all isSpace
    let t := (row.reverse.takeWhile blank).length
    let newLines := ((addition.splitOn "\n").reverse.dropWhile (· == "")).reverse
    .ok ("\n".intercalate (ls.take (i + 1) ++ row.take (row.length - t) ++ newLines ++
      row.drop (row.length - t) ++ after.drop n))

def grants : List String → List String
  | "--grant" :: g :: rest => g :: grants rest
  | _ :: rest => grants rest
  | [] => []

def parseGrant (g : String) : Option (String × String) :=
  match g.splitOn ":" with
  | [v, p] => if ["post", "select", "write", "relaw"].contains v then some (v, p) else none
  | _ => none

/-- `obend log`: the log, read only: its records, a dropped tail, the checkpoint, and the world three
ways (replayed from genesis, from the checkpoint and the records after it, and as the last record's
receipt commits to it), which must be one world. -/
def logReport (dir : System.FilePath) (records : Bool) : IO UInt32 := do
  if !(← (logPath dir).pathExists) then
    IO.println "no log"; return 2
  let bs ← readBytes (logPath dir)
  let (qs, tail, why) := parseFrom logHash Rehydration.genesisSentinel bs
  IO.println ("log: " ++ toString qs.length ++ " records, " ++ toString (encodeAll logHash qs).length ++
    " bytes, each following the one before it from the genesis sentinel")
  if records then
    let mut pos := 0
    let mut i := 0
    for r in qs do
      i := i + 1
      let len := (encodeRecord logHash r).length
      let kind := match decodeTurn r.payload with
        | .ok t => t.kind
        | .error _ => "?"
      IO.println ("  record " ++ toString i ++ " (" ++ kind ++ "): bytes " ++ toString pos ++ " to " ++ toString (pos + len))
      pos := pos + len
  if let some last := qs.getLast? then
    let stop := (encodeAll logHash qs).length
    let start := stop - (encodeRecord logHash last).length
    let kind := match decodeTurn last.payload with
      | .ok t => t.kind
      | .error _ => "?"
    IO.println ("last record: " ++ toString qs.length ++ " (" ++ kind ++ "), bytes " ++ toString start ++
      " to " ++ toString stop)
  unless tail.isEmpty do
    IO.println ("torn tail: " ++ toString tail.length ++ " bytes after record " ++ toString qs.length ++
      ", dropped (" ++ ((why.map dropText).getD "") ++ ")")
  let fromGenesis := (recover logHash deployed genesis bs).world
  let r ← recoverLog dir
  IO.println ("checkpoint: " ++ r.checkpoint)
  let committed := match qs.getLast? with
    | some last => String.ofList ((hex (be 32 last.receipt.newCommit)).toList.take 16)
    | none => worldDigest genesis
  IO.println ("world " ++ worldDigest fromGenesis ++ ": replayed from genesis")
  IO.println ("world " ++ worldDigest r.head.world ++ ": the checkpoint and the records after it")
  IO.println ("world " ++ committed ++ ": as record " ++ toString qs.length ++ " commits to it")
  if worldDigest fromGenesis == worldDigest r.head.world && worldDigest r.head.world == committed then
    IO.println "one world"; return 0
  else
    IO.println "NOT ONE WORLD"; return 3

/-- Run a vault command in `dir`. `none` when the arguments are not a vault command. -/
def run (dir : System.FilePath) (args : List String) : Option (IO UInt32) :=
  let (asName, args) := flag "--as" args
  let (into, args) := flag "--into" args
  let (append, args) := bare "--append" args
  match args with
  | ["open"] => some do
    let (s, _) ← openDir dir true
    for l in problems s do IO.println l
    return 0
  | ["status"] | ["status", _] => some do
    let (s, _) ← openDir dir false
    let ls := statusOf s (args[1]?)
    for l in ls do IO.println l
    return (if ls.any (·.endsWith ": no such page") then 2 else 0)
  | ["merge", other] => some do
    let (_, V) ← openDir dir false
    let (o, _) ← openDir other false
    let label := (System.FilePath.mk other).fileName.getD other
    match ← finishTurn dir (.merged label o) V with
    | .ok (_, .merged s' notes, rendered) =>
      for n in notes do IO.println n
      for l in rendered do IO.println l
      for l in problems s' do IO.println l
      return 0
    | .ok _ => fail "the merge said what a merge does not"
    | .error e => fail e
  | "member" :: "add" :: name :: rest => some do
    let gs := grants rest
    let parsed := gs.filterMap parseGrant
    if parsed.length != gs.length || gs.isEmpty then
      return ← fail "member add NAME --grant VERB:PATTERN …  (VERB: post, select, write, relaw)"
    match ← commitWith dir (.member name parsed) fun _ _ => pure () with
    | .ok () => IO.println ("member " ++ name ++ " may " ++
        ", ".intercalate (parsed.map fun (v, p) => v ++ " " ++ p)); return 0
    | .error e => fail e
  | ["member", "list"] => some do
    let s ← loadStore dir
    for m in s.members do
      IO.println (m.name ++ ": " ++ ", ".intercalate (m.grants.map fun (v, p) => v ++ " " ++ p))
    return 0
  | ["post", page, file] => some do
    let (s, V) ← openDir dir false
    let addition ← if file == "-" then (do let stdin ← IO.getStdin; stdin.readToEnd) else IO.FS.readFile file
    let some cur := V.lookup page | fail ("refused: no page named " ++ page)
    let text? : Except String String :=
      if append then .ok (appendText cur addition)
      else match into with
        | some h => insertInto cur h addition
        | none => .ok addition
    match text? with
    | .error e => fail ("refused: " ++ e)
    | .ok text =>
      match asName with
      | none =>
        -- the owner's post is the owner's write of the page as `text`, judged like an edit of its
        -- file; refused, nothing is logged and the file stands
        let some _ := s.page? page | fail ("refused: no page named " ++ page)
        match ← finishTurn dir (.wrote page text) V with
        | .ok (_, .wrote s' v, rendered) =>
          IO.println ("owner posted to " ++ page ++ " (v" ++ toString v ++ ")")
          for l in rendered do IO.println l
          for l in problems s' do IO.println l
          return 0
        | .ok _ => fail "the post said what a post does not"
        | .error e => fail e
      | some who =>
        match ← finishTurn dir (.posted who page text) V with
        | .ok (_, .changed s', rendered) =>
          IO.println (who ++ " posted to " ++ page)
          for l in rendered do IO.println l
          for l in problems s' do IO.println l
          return 0
        | .ok _ => fail "the post said what a post does not"
        | .error e => fail ("refused: " ++ e)
  | ["select", page, k, i] => some do
    let (_, V) ← openDir dir false
    match k.toNat?, i.toNat? with
    | some k, some i =>
      match ← finishTurn dir (.selected asName page k i) V with
      | .ok (_, _, rendered) =>
        IO.println ("kept candidate " ++ toString i ++ " of section " ++ toString k ++ " of " ++ page)
        for l in rendered do IO.println l
        return 0
      | .error e => fail ("refused: " ++ e)
    | _, _ => fail "select PAGE SECTION CANDIDATE"
  | ["recite", page] => some do
    let (_, V) ← openDir dir false
    match ← finishTurn dir (.recited asName page) V with
    | .ok (_, .recited _ n, rendered) =>
      IO.println ("re-cited " ++ toString n ++ " cite(s) of " ++ page)
      for l in rendered do IO.println l
      return 0
    | .ok _ => fail "the recital said what a recital does not"
    | .error e => fail ("refused: " ++ e)
  | ["log"] => some (logReport dir false)
  | ["log", "records"] => some (logReport dir true)
  | ["create", "--from", k, page] => some do
    let (s, _) ← openDir dir false
    match createFrom s k page with
    | .error e => fail e
    | .ok text =>
      writeFiles dir [(page, text)]
      let (s', _) ← openDir dir false
      match s'.page? page with
      | some p =>
        if p.history.isEmpty then
          fail (page ++ ": not born: " ++ p.note.getD "")
        else
          IO.println ("created " ++ page ++ " (kind " ++ kindName k ++ ")")
          return 0
      | none => fail (page ++ ": not born")
  | _ => none

/-- `obend` vault commands: `-C DIR` anywhere, `open DIR`. -/
def main? (args : List String) : Option (IO UInt32) :=
  let (dirFlag, args) := flag "-C" args
  match args with
  | ["open", d] => run (System.FilePath.mk d) ["open"]
  | _ => run (System.FilePath.mk (dirFlag.getD ".")) args

end Obend.Vault.Cli

end
