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
        open both, then merge OTHER_DIR's world into this one (`Obend.Vault.Merge`): the two read as
        branches of the base they share, merged at the tip (`Obend.Vault.Branch.merge`); a page both
        wrote merges by the pushout of the two versions; here's writes the tip does not land wait as
        refused writes.
    obend branch resolve K left|right
        resolve the merge conflict K the store keeps (`obend status` lists them) by landing one
        candidate through the store's own write; the receipt names the one dropped.
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

Forms (`Obend.Vault.Form`; the walkthrough is `lean/tests/vault/FORMS.md`):

    obend capture SITUATION FORM --for WHO --grant PATTERN [--grant …] [--held CAPS]
                  --move FROM TO AMOUNT [--field FIELD] [--ref PAGE …]
        capture the situation of the page SITUATION (it and the pages it links to) as the form FORM
        for WHO: the pages WHO's grant (CAPS, default read,write, on the PATTERNs) shows, as they are
        now; the live move of AMOUNT of FIELD (default balance) from FROM to TO. Kept in the
        world (exported as .obend/forms/FORM.json).
    obend abstract FORM VALUE HOLE
        VALUE (a number, or a page) in FORM's moves becomes the hole HOLE.
    obend form FORM [--out FILE]
        FORM as its holder sees it: the pages, the holes, the residual; with --out, the form to send.
    obend fill FILE HOLE=VALUE … --out FILE   (where the form was received)
        fill the holes of the form in FILE and write the proposal; what the fill makes of the
        residual is shown, the pages the form did not capture left as reads.
    obend reshare FILE --for WHO --grant PATTERN … [--held CAPS] --out FILE   (where it was received)
        hand the form on to WHO, attenuated; a reshare that would amplify is refused.
    obend judge FILE
        judge a proposal for one of this vault's forms: the membrane, the form's resources, the pins,
        then the one turn over every page it writes, each by its laws and the laws over links on the
        turn's tip; all of it lands or none, with one receipt in the world's chain (exported as .obend/forms/receipts.json).

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

/-- The `.json` files directly in a directory, by name without `.json`, sorted. -/
def jsonFiles (d : System.FilePath) : IO (List (String × String)) := do
  if !(← d.isDir) then return []
  let mut out : Array (String × String) := #[]
  for e in ← d.readDir do
    if e.path.extension == some "json" && !(← e.path.isDir) then
      out := out.push ((e.path.fileStem.getD ""), ← IO.FS.readFile e.path)
  return out.toList.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- The world from before the log, if the vault has one: `world.json`, `ledger.json`, and the forms
an earlier `obend` kept in `.obend/forms/` (its forms, `receipts.json`, `received/`, `sent/`). -/
def legacyWorld (dir : System.FilePath) : IO (Option Replay.World) := do
  let hasW ← (worldPath dir).pathExists
  let hasL ← (legacyLedgerPath dir).pathExists
  let fd := dir / ".obend" / "forms"
  let hasF ← fd.isDir
  if !hasW && !hasL && !hasF then return none
  let bad (f : System.FilePath) (e : String) : IO.Error := IO.userError ("cannot read " ++ f.toString ++ ": " ++ e)
  let s ← if hasW then
      match Lean.Json.parse (← IO.FS.readFile (worldPath dir)) >>= storeOf with
      | .ok s => pure s
      | .error e => throw (bad (worldPath dir) e)
    else pure {}
  let J ← if hasL then
      match Lean.Json.parse (← IO.FS.readFile (legacyLedgerPath dir)) >>= Obend.Ledger.Json.journalOf with
      | .ok j => pure j
      | .error e => throw (bad (legacyLedgerPath dir) e)
    else pure Obend.Ledger.Json.Journal.empty
  let mut forms : List Obend.Vault.Form.Form := []
  let mut receipts : List Rehydration.WitnessReceipt := []
  for (n, t) in ← jsonFiles fd do
    if n == "receipts" then
      match Lean.Json.parse t >>= (·.getArr?) >>= fun a => a.toList.mapM Obend.Vault.Form.receiptOf with
      | .ok rs => receipts := rs
      | .error e => throw (bad (fd / "receipts.json") e)
    else
      match Lean.Json.parse t >>= Obend.Vault.Form.formOf with
      | .ok f => forms := forms ++ [f]
      | .error e => throw (bad (fd / (n ++ ".json")) e)
  let received ← jsonFiles (fd / "received")
  let sent ← jsonFiles (fd / "sent")
  let w : Replay.World :=
    { store := s
      journal := J
      forms := forms
      receipts := receipts
      received := received
      sent := sent }
  return some w

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
stopped. Only the log of the vault the command runs in is torn. `lean/tests/vault/CRASH.md` stops the process there by its PID. -/
def tearAt (dir : System.FilePath) (n : Nat) : IO (Option (Option Nat × String)) := do
  let some v ← IO.getEnv "OBEND_TEST_TEAR" | return none
  -- only the vault the command runs in (`obend merge OTHER` also appends to OTHER's log)
  if (← IO.FS.realPath dir) != (← IO.FS.realPath ".") then return none
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
  let tear ← tearAt dir n
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

/-- Write a file when its text is not already that. -/
def writeIfChanged (f : System.FilePath) (t : String) : IO Unit := do
  if (← readText? f) != some t then
    if let some parent := f.parent then IO.FS.createDirAll parent
    IO.FS.writeFile f t

/-- **The forms' exports**: each form the world holds as `.obend/forms/NAME.json` (the wire format a
form is sent in), the receipt chain as `.obend/forms/receipts.json`, the forms received and the
proposals sent under `.obend/forms/received/` and `sent/`. Derived from the world after every turn
and at recovery; the truth is the log's records. -/
def writeExports (dir : System.FilePath) (w : Replay.World) : IO Unit := do
  let fd := dir / ".obend" / "forms"
  for f in w.forms do
    writeIfChanged (fd / (f.name ++ ".json")) ((Obend.Vault.Form.formJson f).pretty ++ "\n")
  unless w.receipts.isEmpty do
    writeIfChanged (fd / "receipts.json")
      ((Lean.Json.arr (w.receipts.map Obend.Vault.Form.receiptJson).toArray).pretty ++ "\n")
  for (n, t) in w.received do writeIfChanged (fd / "received" / (n ++ ".json")) t
  for (n, t) in w.sent do writeIfChanged (fd / "sent" / (n ++ ".json")) t

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
      writeExports dir after
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
      writeExports dir h'.world
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
      writeExports dir h'.world
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
  ((s.conflicts.zipIdx.filter fun (c, _) => only.all (· == c.page)).map fun (c, k) =>
    "conflict " ++ toString k ++ " at " ++ c.page ++ ": " ++ c.left.1 ++ "'s " ++ c.left.2.1 ++ " and " ++
      c.right.1 ++ "'s " ++ c.right.2.1 ++ " (both kept as candidates; neither landed); keep one with: " ++
      "obend branch resolve " ++ toString k ++ " left|right") ++
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


/-! ## Forms -/

section Forms
open Obend.Vault.Form (Form Grant formOf formJson grantOf grantJson receiptOf authOf)
open Obend.Vault.Affordance (Auth)

def formsDir (dir : System.FilePath) : System.FilePath := dir / ".obend" / "forms"

def readJson (f : System.FilePath) : IO Lean.Json := do
  unless ← f.pathExists do throw (IO.userError ("no file " ++ f.toString))
  match Lean.Json.parse (← IO.FS.readFile f) with
  | .ok j => return j
  | .error e => throw (IO.userError ("cannot read " ++ f.toString ++ ": " ++ e))

def writeJson (f : System.FilePath) (j : Lean.Json) : IO Unit := do
  if let some parent := f.parent then IO.FS.createDirAll parent
  IO.FS.writeFile f (j.pretty ++ "\n")

def ofExcept {α : Type} (what : String) : Except String α → IO α
  | .ok a => return a
  | .error e => throw (IO.userError (what ++ ": " ++ e))

/-- A form this vault issued: the world's (`Obend.Vault.Replay.World.forms`). -/
def loadForm? (dir : System.FilePath) (name : String) : IO (Option Form) := do
  return (← readWorld dir).forms.find? (·.name == name)

/-- Every value of a repeated flag, and the rest. -/
def allFlags (name : String) : List String → List String × List String
  | f :: v :: rest =>
    if f == name then let (vs, r) := allFlags name rest; (v :: vs, r)
    else let (vs, r) := allFlags name (v :: rest); (vs, f :: r)
  | rest => ([], rest)

/-- `--move FROM TO AMOUNT`, and the rest. -/
def moveFlag : List String → Option (String × String × String) × List String
  | "--move" :: a :: b :: n :: rest => (some (a, b, n), rest)
  | x :: rest => let (m, r) := moveFlag rest; (m, x :: r)
  | [] => (none, [])

def parseCaps (s : String) : Option (List Auth) := (s.splitOn ",").mapM authOf

/-- `HOLE=VALUE` pairs against a form's holes. -/
def parseFill (f : Form) : List String → Except String Obend.Vault.Form.Assignment
  | [] => .ok ({} : Obend.Vault.Form.Assignment)
  | x :: rest => do
    let a ← parseFill f rest
    match x.splitOn "=" with
    | [h, v] =>
      match f.holes.lookup h with
      | some .nat => match v.toNat? with
        | some n => return { a with nats := (h, n) :: a.nats }
        | none => throw ("the hole " ++ h ++ " is a natural; " ++ v ++ " is not")
      | some .page => return { a with pages := (h, v) :: a.pages }
      | none => throw ("the form " ++ f.name ++ " has no hole " ++ h)
    | _ => throw ("a fill is HOLE=VALUE, not " ++ x)

def fillText (a : Obend.Vault.Form.Assignment) : String :=
  ", ".intercalate (a.nats.map (fun (h, n) => h ++ " = " ++ toString n) ++ a.pages.map fun (h, n) => h ++ " = " ++ n)

/-- A received form: the form, its digest, the vault that issued it, the hops it was handed on by. -/
def readReceived (file : String) : IO (Form × String × String × List Grant) := do
  let j ← readJson file
  let f ← ofExcept file (formOf (← ofExcept file (j.getObjVal? "form")))
  let d ← ofExcept file (j.getObjValAs? String "digest")
  let v ← ofExcept file (j.getObjValAs? String "vault")
  let hops ← ofExcept file ((← ofExcept file (j.getObjValAs? (Array Lean.Json) "hops")).toList.mapM grantOf)
  return (f, d, v, hops)

def receivedJson (f : Form) (digest vault : String) (hops : List Grant) : Lean.Json :=
  Lean.Json.mkObj [("form", formJson f), ("digest", digest), ("vault", vault),
    ("hops", Lean.Json.arr (hops.map grantJson).toArray)]

def vaultName (dir : System.FilePath) : IO String := do
  return ((← IO.FS.realPath dir).fileName).getD "vault"

end Forms

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
    match ← finishTurn dir (.merged label o false) V with
    | .ok (_, .merged s' notes, rendered) =>
      for n in notes do IO.println n
      for l in rendered do IO.println l
      for l in problems s' do IO.println l
      return 0
    | .ok _ => fail "the merge said what a merge does not"
    | .error e => fail e
  | ["branch", "resolve", k, side] => some do
    let (_, V) ← openDir dir false
    let some k := k.toNat? | fail "branch resolve K left|right: K is a number"
    match ← finishTurn dir (.resolved k (side == "right")) V with
    | .ok (_, .resolved s' receipt, rendered) =>
      IO.println ("resolved conflict " ++ toString k ++ ": landed " ++ receipt)
      for l in rendered do IO.println l
      for l in problems s' do IO.println l
      return 0
    | .ok _ => fail "the resolution said what a resolution does not"
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
  | "capture" :: situation :: name :: rest => some do
    let (who, rest) := flag "--for" rest
    let (held, rest) := flag "--held" rest
    let (field, rest) := flag "--field" rest
    let (pats, rest) := allFlags "--grant" rest
    let (refs, rest) := allFlags "--ref" rest
    let (mv, rest) := moveFlag rest
    match who, mv, rest, parseCaps (held.getD "read,write") with
    | some who, some (src, dst, n), [], some caps =>
      match n.toNat? with
      | none => fail ("capture: the amount " ++ n ++ " is not a number")
      | some amount =>
        let _ ← openDir dir false
        match ← commitWith dir (.captured situation name ⟨who, caps, pats⟩ src dst amount (field.getD "balance") refs)
            (fun _ o => pure o) with
        | .error e => fail e
        | .ok (.form f culled) =>
          IO.println ("captured " ++ name ++ " from " ++ situation ++ " for " ++ who ++ ": " ++
            toString f.cells.length ++ " page(s) shown, " ++ toString culled ++ " not shown to " ++ who)
          for l in f.describe do IO.println l
          return 0
        | .ok _ => fail "the capture said what a capture does not"
    | _, _, _, _ => fail "capture SITUATION FORM --for WHO --grant PATTERN … [--held CAPS] --move FROM TO AMOUNT [--field FIELD] [--ref PAGE …]"
  | ["abstract", name, value, hole] => some do
    match ← commitWith dir (.abstracted name value hole) (fun _ o => pure o) with
    | .error e => fail e
    | .ok (.form g _) =>
      IO.println (name ++ ": " ++ value ++ " is now the hole " ++ hole)
      for l in g.describe do IO.println l
      return 0
    | .ok _ => fail "the abstraction said what an abstraction does not"
  | "form" :: name :: rest => some do
    let (out, rest) := flag "--out" rest
    unless rest.isEmpty do return ← fail "form FORM [--out FILE]"
    let some f ← loadForm? dir name | fail ("refused: no form named " ++ name)
    for l in f.describe do IO.println l
    if let some o := out then
      writeJson o (receivedJson f (Obend.Vault.Form.formDigest H f) (← vaultName dir) [])
      IO.println ("wrote " ++ o)
    return 0
  | "fill" :: file :: rest => some do
    let (out, rest) := flag "--out" rest
    let some o := out | fail "fill FILE HOLE=VALUE … --out FILE"
    let (f, digest, vault, hops) ← readReceived file
    match parseFill f rest with
    | .error e => fail ("refused: " ++ e)
    | .ok a =>
      let holder := (((f.grants ++ hops).getLast?).map (·.holder)).getD "owner"
      let prop := Lean.Json.mkObj [("proposal", f.name), ("digest", digest), ("vault", vault),
        ("hops", Lean.Json.arr (hops.map Obend.Vault.Form.grantJson).toArray),
        ("fill", Obend.Vault.Form.assignmentJson a), ("by", holder)]
      -- the form as received and the proposal as sent are a turn of this directory's log
      if let .error e ← commitWith dir (.filled f.name ((receivedJson f digest vault hops).pretty ++ "\n")
          (prop.pretty ++ "\n")) (fun _ _ => pure ()) then return ← fail e
      writeJson o prop
      IO.println (f.name ++ ": filled by " ++ holder ++ ": " ++ fillText a)
      for l in f.preview a do IO.println ("  " ++ l)
      IO.println ("wrote " ++ o)
      return 0
  | "reshare" :: file :: rest => some do
    let (who, rest) := flag "--for" rest
    let (held, rest) := flag "--held" rest
    let (out, rest) := flag "--out" rest
    let (pats, rest) := allFlags "--grant" rest
    match who, out, rest, parseCaps (held.getD "read,write") with
    | some who, some o, [], some caps =>
      let (f, digest, vault, hops) ← readReceived file
      let cur := ((f.grants ++ hops).getLast?).getD Obend.Vault.Form.ownerGrant
      let g : Obend.Vault.Form.Grant := ⟨who, caps, pats⟩
      match Obend.Vault.Rehydration.Membrane.reshare (cur.viewer f.scope) (g.viewer f.scope) with
      | none => fail (f.name ++ ": " ++ Obend.Vault.Form.refusalText f (.amplifies cur.holder who cur.held caps))
      | some _ =>
        writeJson o (receivedJson f digest vault (hops ++ [g]))
        IO.println (f.name ++ ": reshared by " ++ cur.holder ++ " to " ++ who ++ " (" ++
          Obend.Vault.Form.showAuths caps ++ " on " ++ ", ".intercalate pats ++ ")")
        IO.println ("wrote " ++ o)
        return 0
    | _, _, _, _ => fail "reshare FILE --for WHO --grant PATTERN … [--held CAPS] --out FILE"
  | ["judge", file] => some do
    let (_, V) ← openDir dir false
    let j ← readJson file
    let name ← ofExcept file (j.getObjValAs? String "proposal")
    let digest ← ofExcept file (j.getObjValAs? String "digest")
    let hops ← ofExcept file ((← ofExcept file (j.getObjValAs? (Array Lean.Json) "hops")).toList.mapM Obend.Vault.Form.grantOf)
    let a ← ofExcept file (Obend.Vault.Form.assignmentOf (← ofExcept file (j.getObjVal? "fill")))
    match ← finishTurn dir (.judged name digest hops a) V with
    | .error e => fail e
    | .ok (w', .judged s' ad t r count, rendered) =>
      let some f := w'.forms.find? (·.name == name) | fail ("refused: no form named " ++ name ++ " here")
      IO.println (name ++ ": landed as one turn over " ++ toString t.writeCells.length ++ " pages by " ++ ad.holder ++
        ", receipt " ++ Obend.Vault.Form.hex16 (Obend.Vault.Form.receiptDigest H r) ++ " (" ++
        toString count ++ " in the chain)")
      for d in t.writeCells do
        for A in f.assets do
          IO.println ("  " ++ d.cell ++ ": " ++ A ++ " " ++ toString (natAt d.preState A) ++ " → " ++
            toString (natAt d.postState A))
      for l in rendered do IO.println l
      for l in problems s' do IO.println l
      return 0
    | .ok _ => fail "the judgment said what a judgment does not"
  | _ => none

/-- `obend` vault commands: `-C DIR` anywhere, `open DIR`. -/
def main? (args : List String) : Option (IO UInt32) :=
  let (dirFlag, args) := flag "-C" args
  match args with
  | ["open", d] => run (System.FilePath.mk d) ["open"]
  | _ => run (System.FilePath.mk (dirFlag.getD ".")) args

end Obend.Vault.Cli

end
