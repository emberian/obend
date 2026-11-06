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
    obend fill FILE HOLE=VALUE … [--because CONCLUSION] --out FILE   (where the form was received)
        fill the holes of the form in FILE and write the proposal; what the fill makes of the
        residual is shown, the pages the form did not capture left as reads. With `--because`, the
        proposal carries its justification, and the vault judges it only while that is supported in
        its own reasons (`obend reasons`).
    obend reshare FILE --for WHO --grant PATTERN … [--held CAPS] --out FILE   (where it was received)
        hand the form on to WHO, attenuated; a reshare that would amplify is refused.
    obend judge FILE [--receipt FILE]
        judge a proposal for one of this vault's forms: transported first when the laws over its
        pages moved; a duplicate of an intent landed here is refused (and its receipt written
        again); then its values, the membrane, the authority of a standing grant, its contract's
        offer, the form's resources, then the one turn over every page it writes, each by its laws
        and the laws over links on the turn's tip; all of it lands or none, with one receipt in the
        world's chain (exported as .obend/forms/receipts.json), written to --receipt for the filler.

Retention (`Obend.Vault.Retention`; the walkthrough is `lean/tests/vault/RETAIN.md`):

    obend forget NAME [--retire FORM …] [--abandon BRANCH …]
        forget the log before this turn under the retention contract NAME: refused, by name, while a
        proposal sent from here awaits its receipt, a form issued here stands (unless retired), a
        retired form has a continuity contract, or a declared branch has not merged (unless
        abandoned); admitted, the log becomes one checkpoint record. A proposal for a retired form, a
        merge from an abandoned branch or from a copy whose log does not reach the forgotten prefix's
        end, is refused afterwards, naming the contract.
    obend fork DIR
        copy this vault to DIR as a declared branch: it holds a forget back until it merges.

Transport (`Obend.Vault.Transport`; the walkthrough is `lean/tests/vault/TRANSPORT.md`):

    obend offer FORM HOLE LO..HI [--promise LO..HI]
        FORM's continuity contract: the values of its one natural hole it offers (each judged now
        by the laws as they stand) and those it promises whatever becomes of the laws.
    obend grant ID --for WHO --grant PATTERN … [--held CAPS]
    obend revoke ID
    obend grants
        the grants this vault issued to holders of its forms, standing until revoked; a capture's
        own grant is issued under the form's name.
    obend transport FORM
        what FORM is now for a display and for an effect (what moved: values, support, laws,
        authority), and, when the laws over its pages moved, FORM carried across the change by its
        contract: continued, repaired (the offer narrowed), or refused.
    obend obligations   (where forms were filled)
        the proposals sent from here that no receipt has confirmed.
    obend confirm FILE   (where forms were filled)
        confirm a receipt written by `obend judge --receipt`: it must name a proposal sent from here.
    obend reasons observe NAME (--line FILE:N | TEXT) | assume NAME | withdraw NAME
          | explain NAME CONCLUSION --if PREMISE… [--unless DEFEATER…] | defeat EXPLANATION --by ATOM
          | propose ACTION --because CONCLUSION | admit ACTION | status | why ATOM
        the directory's reasons (`Obend.Reasons`; no vault needed, each event a turn of its log):
        observations (a line of a file, verbatim, with where it was read), assumptions, explanations
        and their defeaters, proposed actions. Each event says what changed status (supported,
        undefined, unsupported: the well-founded model) and how many atoms it judged anew; `admit`
        refuses an action whose justification is not supported now, by name and with the reasons
        (exit 1).


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
public import Obend.Vault.FormCheck
public import Obend.Vault.Cost
public import Obend.Vault.LogBytes
public section

namespace Obend.Vault.Cli

open Obend.Doc Obend.Vault Obend.Vault.Json Obend.Vault.Log Obend.Vault.Replay

/-- The deployed byte hash (cSHAKE256, as `lean/tests/doc/RoundTrip.lean`); the log replays with it. -/
def H : Obend.Digest.HashBytes.Hash := Obend.Vault.Replay.H

/-- Every `.md` under `dir`, by name (its path from `dir` without `.md`), sorted. -/
def readVault (dir : System.FilePath) : IO (List (String × String)) := Obend.Vault.Cost.phase "read" do
  let files ← System.FilePath.walkDir dir fun p => pure !((p.fileName.getD "").startsWith ".")
  let mut out : Array (String × String) := #[]
  let pre := dir.toString ++ "/"
  for f in files do
    if f.extension == some "md" && !(← f.isDir) then
      let rel := if f.toString.startsWith pre then String.ofList (f.toString.toList.drop pre.length) else f.toString
      let name := String.ofList (rel.toList.take (rel.length - 3))
      out := out.push (name, ← Obend.Vault.Cost.readFile f)
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
        let txt ← Obend.Vault.Cost.readFile f
        names := names ++ (txt.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"
  return environmentOf names

/-- The `.json` files directly in a directory, by name without `.json`, sorted. -/
def jsonFiles (d : System.FilePath) : IO (List (String × String)) := do
  if !(← d.isDir) then return []
  let mut out : Array (String × String) := #[]
  for e in ← d.readDir do
    if e.path.extension == some "json" && !(← e.path.isDir) then
      out := out.push ((e.path.fileStem.getD ""), ← Obend.Vault.Cost.readFile e.path)
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
      match Lean.Json.parse (← Obend.Vault.Cost.readFile (worldPath dir)) >>= storeOf with
      | .ok s => pure s
      | .error e => throw (bad (worldPath dir) e)
    else pure {}
  let J ← if hasL then
      match Lean.Json.parse (← Obend.Vault.Cost.readFile (legacyLedgerPath dir)) >>= Obend.Ledger.Json.journalOf with
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
  return (← Obend.Vault.Cost.readBinFile f).toList

/-- A file's bytes as they are (`Obend.Vault.LogBytes` reads records at offsets into them). -/
def readArray (f : System.FilePath) : IO ByteArray := do
  if !(← f.pathExists) then return .empty
  Obend.Vault.Cost.readBinFile f

open Obend.Vault.LogBytes (parseOneAt parseFromAt parseLogAt holdsAt encodeRecordBytes)

/-- A checkpoint's file: `obend-checkpoint 1 COUNT START STOP ANCHOR BASE`, a newline, the world's bytes.
`BASE` is the length of the log's checkpoint record when it starts with one, else 0 (a checkpoint
without it, from before, is read as not saying). -/
def checkpointBytes (ck : Checkpoint) (base : Nat) : Bytes :=
  textBytes ("obend-checkpoint 1 " ++ toString ck.count ++ " " ++ toString ck.start ++ " " ++
    toString ck.stop ++ " " ++ toString ck.anchor ++ " " ++ toString base ++ "\n") ++ ck.world

def readCheckpoint (dir : System.FilePath) : IO (Option (Checkpoint × Option Nat)) := do
  let bs ← readArray (checkpointPath dir)
  if bs.isEmpty then return none
  Obend.Vault.Cost.addCheckpoint bs.size
  let some nl := (List.range (min bs.size 200)).find? (fun i => bs.get! i == 10) | return none
  let some txt := bytesText (bs.extract 0 nl).data.toList | return none
  let (fields, base) := match txt.splitOn " " with
    | ["obend-checkpoint", "1", c, a, b, h] => (some (c, a, b, h), none)
    | ["obend-checkpoint", "1", c, a, b, h, k] => (some (c, a, b, h), k.toNat?)
    | _ => (none, none)
  let some (c, a, b, h) := fields | return none
  match c.toNat?, a.toNat?, b.toNat?, h.toNat? with
  | some c, some a, some b, some h => return some (⟨c, a, b, h, (bs.extract (nl + 1) bs.size).data.toList⟩, base)
  | _, _, _, _ => return none

/-- Write a file whole or not at all: beside it, then renamed over it. -/
def writeAtomically (f : System.FilePath) (bs : Bytes) : IO Unit := do
  let tmp := f.withExtension "tmp"
  Obend.Vault.Cost.writeBinFile tmp ⟨bs.toArray⟩
  IO.FS.rename tmp f

def writeAtomicallyArray (f : System.FilePath) (bs : ByteArray) : IO Unit := do
  let tmp := f.withExtension "tmp"
  Obend.Vault.Cost.writeBinFile tmp bs
  IO.FS.rename tmp f

/-- What a process holds of a vault's log: the world (the replay of the log), the receipt digest of
the last record, how many records there are, the log's length and where its last record starts. -/
structure Head where
  world : Replay.World
  prev : Nat := Rehydration.genesisSentinel
  count : Nat := 0
  size : Nat := 0
  lastStart : Nat := 0
  /-- the log's first record is a checkpoint record (`Obend.Vault.Retention`): a forgotten prefix -/
  base : Bool := false
  /-- the checkpoint record's length, when the log starts with one -/
  baseSize : Nat := 0
  /-- the world's bytes and their commitment, when known (the last record's `newCommit`): a turn
  needs the commitment of the world it steps from, and a checkpoint the bytes -/
  known : Option (Bytes × Nat) := none

/-- The digest of a world, as `obend log` says it: the first 16 hex digits of its commitment. -/
def worldDigest (w : Replay.World) : String :=
  String.ofList ((hex (be 32 (dig logHash (encodeWorld w)))).toList.take 16)

/-- **Write a checkpoint** of the head's world, anchored to the log's last record, after checking that
the world's bytes decode to the world (`checkpoint_is_cache`'s premise). -/
def saveCheckpoint (dir : System.FilePath) (h : Head) : IO Unit := Obend.Vault.Cost.phase "write" do
  if h.count == 0 then return
  -- a log that is its checkpoint record alone needs no checkpoint (and the record's anchor is the
  -- forgotten prefix's, not its own digest)
  if h.base && h.count == 1 then return
  -- after a forget the checkpoint record holds the world: a checkpoint is written again only once the
  -- records after it outweigh it
  if h.base && h.size < 2 * h.baseSize then return
  let wb := match h.known with
    | some (wb, _) => wb
    | none => encodeWorld h.world
  if decodeWorld wb != some h.world then
    IO.eprintln "checkpoint not written: the world's bytes do not decode to the world (the log stays the truth)"
    return
  writeAtomically (checkpointPath dir) (checkpointBytes ⟨h.count, h.lastStart, h.size, h.prev, wb⟩ (if h.base then h.baseSize else 0))

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
  Obend.Vault.Cost.writeFile barrier "stopped here\n"
  repeat IO.sleep 1000

/-- Append a record's bytes to the log (the barrier aside). -/
def appendRecord (dir : System.FilePath) (n : Nat) (bs : Bytes) : IO Unit := do
  let tear ← tearAt dir n
  let h ← IO.FS.Handle.mk (logPath dir) .append
  match tear with
  | some (some k, barrier) =>
    Obend.Vault.Cost.write h ⟨(bs.take k).toArray⟩
    h.flush
    waitToBeStopped barrier
  | _ =>
    Obend.Vault.Cost.write h ⟨bs.toArray⟩
    h.flush
  if let some (none, barrier) := tear then waitToBeStopped barrier

/-- **Commit a turn**: admit its bytes at the head (`Obend.Vault.Log.admit` at the deployed machine)
and append the record; the head after it and what the turn said, or the refusal (nothing appended). -/
def commitTurnRaw (dir : System.FilePath) (h : Head) (t : Turn) : IO (Except String (Head × Outcome × Bytes)) := do
  let b := encodeTurn t
  if b.length ≥ 256 ^ 4 then return .error "a turn is under 4 GiB"
  -- the step (`judge`), then the record (`land`): `admit_of_step` says this is `Log.admit`'s record,
  -- the commitment of the world stepped from being the one the head knows
  let step ← Obend.Vault.Cost.phase "judge" (Obend.Vault.Cost.compute fun _ => deployed.step h.world b)
  match step with
  | .error e => return .error e
  | .ok (w', o) =>
    let h' ← Obend.Vault.Cost.phase "land" do
      let oldC ← match h.known with
        | some (_, c) => pure c
        | none => pure (dig logHash (encodeWorld h.world))
      let (wb, newC) ← Obend.Vault.Cost.compute fun _ => let wb := encodeWorld w'; (wb, dig logHash wb)
      let r : Record := ⟨⟨h.prev, oldC, newC, dig logHash b⟩, b⟩
      let bs := encodeRecord logHash r
      appendRecord dir (h.count + 1) bs
      return (({ h with
        world := w'
        prev := Hr logHash r.receipt
        count := h.count + 1
        size := h.size + bs.length
        lastStart := h.size
        known := some (wb, newC) } : Head), bs)
    return .ok (h'.1, o, h'.2)

/-- The receipt digest a chain of records read from `prev` ends at: a checkpoint record first in a
log stands for a prefix that ended at its anchor, and the records after it follow the anchor. -/
def chainEnd (prev : Nat) (qs : List Record) : Nat :=
  match qs with
  | r :: rest =>
    match prev == Rehydration.genesisSentinel, anchorOfTurn r.payload with
    | true, some a => lastHash logHash a rest
    | _, _ => lastHash logHash prev qs
  | [] => prev

/-- What recovery read: the head, the records after the checkpoint (all of them without one) and the
world before them, the dropped tail and why, and what became of the checkpoint. -/
structure Recovery where
  head : Head
  base : Replay.World
  suffix : List Record
  tail : Bytes
  why : Option Drop
  checkpoint : String
  /-- the log's bytes as read (empty when the recovery is the head a turn of this process left) -/
  bytes : ByteArray := .empty
  /-- the bytes of the log's last record -/
  last : ByteArray := .empty

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
def recoverLogRead (dir : System.FilePath) : IO Recovery := Obend.Vault.Cost.phase "read" do
  let bs ← readArray (logPath dir)
  let ckb? ← readCheckpoint dir
  let ck? := ckb?.map (·.1)
  -- `holdsAt_eq`, `parseLogAt_eq`, `parseFromAt_eq`: these read what `Checkpoint.holds`,
  -- `Retention.parseLog` and `parseFrom` read of the log's list, at offsets into its bytes
  let held := ck?.bind fun ck => (holdsAt logHash decodeWorld ck bs).map (ck, ·)
  let (base, anchor, from_, count0, note) := match ck?, held with
    | _, some (ck, w) => (w, ck.anchor, ck.stop, ck.count, "the world after record " ++ toString ck.count)
    | some _, none => (genesis, Rehydration.genesisSentinel, 0, 0,
        "dropped (it does not hold against the log); the world is replayed from genesis")
    | none, none => (genesis, Rehydration.genesisSentinel, 0, 0, "none; the world is replayed from genesis")
  let (qs, stop, why) := if from_ == 0 then parseLogAt logHash anchorOfTurn bs
    else parseFromAt logHash anchor bs from_
  let tail := (bs.extract stop bs.size).data.toList
  let (isBase, baseSize) ← if from_ == 0 then
      pure (match qs.head? with
        | some r => if (anchorOfTurn r.payload).isSome then (true, (encodeRecord logHash r).length) else (false, 0)
        | none => (false, 0))
    else match ckb?.bind (·.2) with
      | some k => pure (k != 0, k)
      | none => pure (match parseOneAt logHash (some Rehydration.genesisSentinel) bs 0 with
        | .ok (r, o) => if (anchorOfTurn r.payload).isSome then (true, o) else (false, 0)
        | .error _ => (false, 0))
  Obend.Vault.Cost.addReplayed qs.length
  let world := replay deployed base qs
  let size := stop
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
      | some (ck, _) => match parseOneAt logHash none bs ck.start with
        | .ok (r, _) => some r
        | .error _ => none
      | none => none
  -- the replayed world commits to what the last record's receipt names (with no record after the
  -- checkpoint, `holdsAt` checked that the record commits to the checkpoint's bytes, which the writer
  -- checked decode to the world)
  let known ← match last?, held with
    | some r, some (ck, _) =>
      if qs.isEmpty then pure (some (ck.world, r.receipt.newCommit))
      else do
        let wb := encodeWorld world
        pure (if r.receipt.newCommit == dig logHash wb then some (wb, r.receipt.newCommit) else none)
    | some r, none => do
      let wb := encodeWorld world
      pure (if r.receipt.newCommit == dig logHash wb then some (wb, r.receipt.newCommit) else none)
    | none, _ => pure (some (encodeWorld world, dig logHash (encodeWorld world)))
  if last?.isSome && known.isNone then
    throw (IO.userError ("the log's replay does not reach the world record " ++ toString count ++
      " commits to: the log was written by another step (relinking is not done here)"))
  return ⟨⟨world, chainEnd anchor qs, count, size, lastStart, isBase, baseSize, known⟩, base, qs, tail, why, note, bs, bs.extract lastStart size⟩

/-- What this process last knew of each vault's log: the log's length then, and the recovery. A
command recovers a vault's world once: a later recovery of the same vault, the log the same length,
is the one known, and a turn this process appended leaves the head it made (`commitTurn`). A log
another process appended to is longer, and is recovered again. -/
initialize recoveries : IO.Ref (List (String × Nat × Recovery)) ← IO.mkRef []

def logSize (dir : System.FilePath) : IO Nat := do
  if !(← (logPath dir).pathExists) then return 0
  return (← (logPath dir).metadata).byteSize.toNat

def vaultKey (dir : System.FilePath) : IO String := do
  if ← dir.pathExists then return (← IO.FS.realPath dir).toString else return dir.toString

/-- **Recover a vault's world from its log** (`recoverLogRead`), once per process and log length. -/
def recoverLog (dir : System.FilePath) : IO Recovery := do
  let key ← vaultKey dir
  let size ← logSize dir
  match (← recoveries.get).find? (fun (k, n, _) => k == key && n == size) with
  | some (_, _, r) => return r
  | none =>
    let r ← recoverLogRead dir
    -- only a recovery that read the whole log as records is kept (a dropped tail is truncated next)
    if r.tail.isEmpty then recoveries.modify fun c => (key, size, r) :: c.filter (·.1 != key)
    return r

/-- The log was rewritten (compacted, or a torn tail truncated): recover it again. -/
def forgetRecovery (dir : System.FilePath) : IO Unit := do
  let key ← vaultKey dir
  recoveries.modify fun c => c.filter (·.1 != key)

/-- The head a turn of this process left, as the recovery of the log it appended to. -/
def rememberHead (dir : System.FilePath) (h : Head) (last : ByteArray) : IO Unit := do
  let key ← vaultKey dir
  let size ← logSize dir
  if size != h.size then return
  let r : Recovery := ⟨h, h.world, [], [], none, "the world after record " ++ toString h.count, .empty, last⟩
  recoveries.modify fun c => (key, size, r) :: c.filter (·.1 != key)

/-- **Commit a turn** (`commitTurnRaw`), and remember the head it leaves as the vault's recovery. -/
def commitTurn (dir : System.FilePath) (h : Head) (t : Turn) : IO (Except String (Head × Outcome)) := do
  match ← commitTurnRaw dir h t with
  | .error e => return .error e
  | .ok (h', o, bs) =>
    rememberHead dir h' ⟨bs.toArray⟩
    return .ok (h', o)

/-- The world from the log, read only (nothing is truncated, rewritten or redone). -/
def readWorld (dir : System.FilePath) : IO Replay.World := do
  if !(← (logPath dir).pathExists) then
    if let some w ← legacyWorld dir then return w
  return (← recoverLog dir).head.world

def loadStore (dir : System.FilePath) : IO Store := return (← readWorld dir).store

/-- A file's text, if it is there. -/
def readText? (f : System.FilePath) : IO (Option String) := do
  if ← f.pathExists then return some (← Obend.Vault.Cost.readFile f) else return none

/-- Write a file when its text is not already that. -/
def writeIfChanged (f : System.FilePath) (t : String) : IO Unit := do
  if (← readText? f) != some t then
    if let some parent := f.parent then IO.FS.createDirAll parent
    Obend.Vault.Cost.writeFile f t

/-- **The forms' exports**: each form the world holds as `.obend/forms/NAME.json` (the wire format a
form is sent in), the receipt chain as `.obend/forms/receipts.json`, the forms received and the
proposals sent under `.obend/forms/received/` and `sent/`. Derived from the world after every turn
and at recovery; the truth is the log's records. -/
def writeExports (dir : System.FilePath) (w : Replay.World) : IO Unit := Obend.Vault.Cost.phase "write" do
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
    | .reopened changed _ => (reconstructSeen before.store changed).lookup n
    | _ => seenOf before.store n
  let mut done : List String := []
  for p in after.store.pages do
    if let some txt := p.seen then
      let f := dir / (p.name ++ ".md")
      let cur ← readText? f
      if cur != some txt && cur == found p.name then
        if let some parent := f.parent then IO.FS.createDirAll parent
        Obend.Vault.Cost.writeFile f txt
        done := done ++ [p.name ++ ".md"]
  if let .rows fs := o then
    for rf in fs do
      IO.FS.createDirAll (dir / ".obend" / "receipts")
      Obend.Vault.Cost.writeFile (dir / ".obend" / "receipts" / (rf.id ++ ".json")) rf.receipt
      done := done ++ [".obend/receipts/" ++ rf.id ++ ".json"]
      let pf := dir / "register" / (rf.id ++ ".md")
      unless ← pf.pathExists do
        IO.FS.createDirAll (dir / "register")
        Obend.Vault.Cost.writeFile pf rf.page
        done := done ++ ["register/" ++ rf.id ++ ".md"]
  return done

/-- The test-only barrier of a compaction (`OBEND_TEST_COMPACT=K:PATH`): write the first `K` bytes of
the new log, create `PATH` and wait to be stopped. -/
def compactTear (dir : System.FilePath) : IO (Option (Nat × String)) := do
  let some v ← IO.getEnv "OBEND_TEST_COMPACT" | return none
  if (← IO.FS.realPath dir) != (← IO.FS.realPath ".") then return none
  match v.splitOn ":" with
  | kStr :: rest => return kStr.toNat?.map (·, ":".intercalate rest)
  | _ => return none

def newLogPath (dir : System.FilePath) : System.FilePath := dir / ".obend" / "log.new"

/-- **Compact the log** (`Obend.Vault.Retention`): its records, all of them, are replaced by one
checkpoint record, admitted at genesis, whose turn carries the world they leave, how many records of
the vault's whole history they stand for, the digest of their bytes, and the receipt digest they end
at (the anchor the records after it follow). Written beside the log and renamed over it, so a crash
leaves the log as it was or compacted; the checkpoint file, whose offsets were the old log's, goes. -/
def compactLog (dir : System.FilePath) (h : Head) : IO Head := do
  let bs := (← readBytes (logPath dir)).take h.size
  let before := match parseOne logHash (some Rehydration.genesisSentinel) bs with
    | .ok (r, _) => match decodeTurn r.payload with
      | .ok (.compacted n _ _ _) => n - 1
      | _ => 0
    | .error _ => 0
  let t := Turn.compacted (before + h.count) (dig logHash bs) h.prev h.world
  match Log.admit logHash deployed genesis Rehydration.genesisSentinel (encodeTurn t) with
  | .error e => throw (IO.userError ("not compacted: " ++ e))
  | .ok (w', _, r) =>
    if w' != h.world then
      throw (IO.userError "not compacted: the world's bytes do not decode to the world (the log stays as it is)")
    let rb := encodeRecord logHash r
    match ← compactTear dir with
    | some (k, barrier) =>
      Obend.Vault.Cost.writeBinFile (newLogPath dir) ⟨(rb.take k).toArray⟩
      waitToBeStopped barrier
    | none => Obend.Vault.Cost.writeBinFile (newLogPath dir) ⟨rb.toArray⟩
    IO.FS.rename (newLogPath dir) (logPath dir)
    forgetRecovery dir
    if ← (checkpointPath dir).pathExists then IO.FS.removeFile (checkpointPath dir)
    return { world := h.world, prev := h.prev, count := 1, size := rb.length, lastStart := 0, base := true,
             baseSize := rb.length }

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
    writeAtomicallyArray (logPath dir) (r.bytes.extract 0 r.head.size)
    forgetRecovery dir
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
  -- a forget interrupted: its new log is dropped, and the log, whose last record is the forget, is
  -- compacted again
  if ← (newLogPath dir).pathExists then
    let n := (← readBytes (newLogPath dir)).length
    IO.FS.removeFile (newLogPath dir)
    IO.println ("recovered: an interrupted forget's new log (" ++ toString n ++ " bytes) dropped; the log stands")
  -- the bytes recovery read: up to the head's size they are the log's (a dropped tail is past it)
  match parseOneAt logHash none r.last 0 with
  | .ok (last, _) =>
    if let .ok (.forget _) := decodeTurn last.payload then
      let h ← compactLog dir r.head
      IO.println ("recovered: the forget at record " ++ toString r.head.count ++
        " was whole and the log was not compacted: compacted to one checkpoint record")
      return h
    return r.head
  | .error _ => return r.head

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

def writeFiles (dir : System.FilePath) (w : List (String × String)) : IO Unit := Obend.Vault.Cost.phase "write" do
  for (n, t) in w do
    let f := dir / (n ++ ".md")
    if let some parent := f.parent then IO.FS.createDirAll parent
    Obend.Vault.Cost.writeFile f t

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

/-- The refusals among what changed between two stores: a birth refused, or a write refused anew
(as `changes` says them). -/
def refusalsOf (s s' : Store) : List String :=
  s'.pages.filterMap fun p' =>
    match s.page? p'.name with
    | none => if p'.history.isEmpty && p'.note.isSome then some (p'.name ++ ": not born: " ++ p'.note.getD "") else none
    | some p =>
      if p'.history.length > p.history.length then none
      else if p'.note.isSome && (p'.note != p.note || typed p' != typed p) then some (p'.name ++ ": " ++ p'.note.getD "")
      else none
where
  typed (q : Page) : Option (List Tok) := q.seen.map fun t => stripToks (tokens t)

/-- The refusals a command has said, this run: each makes its exit status 1 (`main?`). -/
initialize refusedRef : IO.Ref (List String) ← IO.mkRef []

/-- Say refusals on stderr and remember them for the exit status. -/
def sayRefused (ls : List String) : IO Unit := do
  for l in ls do IO.eprintln l
  refusedRef.modify (· ++ ls)

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
    -- the files the world has seen, by the same names: the record names only those that moved
    -- (`reopen_replays`); otherwise every file (`open_replays`)
    let names := V.map (·.1)
    -- `seenNames` is sorted, so its names are distinct when no two neighbours are equal
    let distinct := (names.zip (names.drop 1)).all fun (a, b) => a != b
    let t := if names == seenNames h.world.store && distinct then
        Turn.reopened (changedOf h.world.store V) (envOf h.world.store env)
      else .opened (readingOf h.world.store V) (envOf h.world.store env)
    match ← commitTurn dir h t with
    | .error e => throw (IO.userError ("the open was refused: " ++ e))
    | .ok (h', .opened f o) =>
      -- a page a kind's laws keep is written back from the text the store holds for it
      let back := f.kept.filterMap fun (n, _) => (o.store.page? n).bind fun p => p.seen.map (n, ·)
      writeFiles dir (o.writes ++ back)
      saveCheckpoint dir h'
      -- changes are read against the store after deletions and renames: a renamed page is not new;
      -- a refusal is said on stderr, by every command that opens, and makes its exit status 1
      let cs := changes f.store o.store
      let rs := refusalsOf f.store o.store
      if verbose then
        let fl := forgottenLines f
        if cs.isEmpty && fl.isEmpty then IO.println "nothing changed"
        for c in fl do IO.println c
        for c in cs do unless rs.contains c do IO.println c
      -- a refusal this command made; a page an earlier open left unborn is said again, as before,
      -- and is not this command's refusal
      sayRefused rs
      if verbose then
        for c in unbornLines o.store cs do IO.println c
      if verbose then
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
      sayRefused (refusalsOf h.world.store s)
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
  let bs ← readArray (logPath dir)
  let (qs, stop, why) := parseLogAt logHash anchorOfTurn bs
  let tail := (bs.extract stop bs.size).data.toList
  IO.println ("log: " ++ toString qs.length ++ " records, " ++ toString stop ++
    " bytes, each following the one before it from the genesis sentinel" ++
    (match qs.head? with
      | some r => match decodeTurn r.payload with
        | .ok (.compacted n d a _) => " through a checkpoint record: " ++ toString n ++
            " forgotten records (prefix digest " ++ String.ofList ((hex (be 32 d)).toList.take 16) ++
            "), ending at receipt " ++ String.ofList ((hex (be 32 a)).toList.take 16)
        | _ => ""
      | none => ""))
  IO.println ("a command reads: the log, " ++ toString bs.size ++ " bytes, and the checkpoint, " ++
    toString (← readArray (checkpointPath dir)).size ++ " bytes")
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
    let start := stop - (encodeRecord logHash last).length
    let kind := match decodeTurn last.payload with
      | .ok t => t.kind
      | .error _ => "?"
    IO.println ("last record: " ++ toString qs.length ++ " (" ++ kind ++ "), bytes " ++ toString start ++
      " to " ++ toString stop)
  unless tail.isEmpty do
    IO.println ("torn tail: " ++ toString tail.length ++ " bytes after record " ++ toString qs.length ++
      ", dropped (" ++ ((why.map dropText).getD "") ++ ")")
  Obend.Vault.Cost.addReplayed qs.length
  -- `Retention.recoverLog` of the log's list, through `parseLogAt_eq`
  let fromGenesis := replay deployed genesis qs
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
  match Lean.Json.parse (← Obend.Vault.Cost.readFile f) with
  | .ok j => return j
  | .error e => throw (IO.userError ("cannot read " ++ f.toString ++ ": " ++ e))

def writeJson (f : System.FilePath) (j : Lean.Json) : IO Unit := do
  if let some parent := f.parent then IO.FS.createDirAll parent
  Obend.Vault.Cost.writeFile f (j.pretty ++ "\n")

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
    match (x.splitOn "=") with
    | h :: v :: more =>
      let v := "=".intercalate (v :: more)
      match f.holes.lookup h with
      | some .nat => match v.toNat? with
        | some n => return { a with nats := (h, n) :: a.nats }
        | none => throw ("the hole " ++ h ++ " is a natural; " ++ v ++ " is not")
      | some .page => return { a with pages := (h, v) :: a.pages }
      | some .label =>
        if v.isEmpty || v.any Char.isWhitespace then throw ("the hole " ++ h ++ " is a label (one word); " ++ v ++ " is not")
        else return { a with labels := (h, v) :: a.labels }
      | some .text => return { a with labels := (h, v) :: a.labels }
      | none => throw ("the form " ++ f.name ++ " has no hole " ++ h)
    | _ => throw ("a fill is HOLE=VALUE, not " ++ x)

def fillText (a : Obend.Vault.Form.Assignment) : String :=
  ", ".intercalate (a.nats.map (fun (h, n) => h ++ " = " ++ toString n) ++ a.pages.map (fun (h, n) => h ++ " = " ++ n) ++
    a.labels.map fun (h, v) => h ++ " = \"" ++ v ++ "\"")

/-- A received form: the form, its digest, the vault that issued it, the hops it was handed on by, and
the continuity contract it was issued with, if any. -/
def readReceived (file : String) : IO (Form × String × String × List Grant × Option Transport.Contract) := do
  let j ← readJson file
  let f ← ofExcept file (formOf (← ofExcept file (j.getObjVal? "form")))
  let d ← ofExcept file (j.getObjValAs? String "digest")
  let v ← ofExcept file (j.getObjValAs? String "vault")
  let hops ← ofExcept file ((← ofExcept file (j.getObjValAs? (Array Lean.Json) "hops")).toList.mapM grantOf)
  let K ← match j.getObjVal? "contract" with
    | .ok c => some <$> ofExcept file (Transport.contractOf c)
    | .error _ => pure none
  return (f, d, v, hops, K)

def receivedJson (f : Form) (digest vault : String) (hops : List Grant) (K : Option Transport.Contract := none) :
    Lean.Json :=
  Lean.Json.mkObj ([("form", formJson f), ("digest", digest), ("vault", vault),
    ("hops", Lean.Json.arr (hops.map grantJson).toArray)] ++
    (match K with | some K => [("contract", Transport.contractJson K)] | none => []))

/-- A contract, said. -/
def contractLine (K : Transport.Contract) : String :=
  "  offer " ++ K.hole ++ ": " ++ Transport.runsText K.offer ++ " (promised " ++ Transport.runsText K.promise ++ ")"

/-- Where a vault keeps the laws over a form's holed states it checked once
(`Obend.Vault.Form.checkedOnce`): what it checked of its own form, so a judgment reuses it. -/
def checkedPath (dir : System.FilePath) (name : String) : System.FilePath :=
  dir / ".obend" / "checked" / (name ++ ".json")

/-- Check, once, every law over every leg the form `name` may write (`Form.checkedOnce`), and keep
the ones the checker accepted. -/
def recordChecks (dir : System.FilePath) (name : String) : IO Unit := do
  let w ← readWorld dir
  if let some f := w.forms.find? (·.name == name) then
    writeJson (checkedPath dir name) (Lean.toJson (f.checkedOnce w.store.entries))

/-- The laws over a form's holed states it checked once. -/
def readChecks (dir : System.FilePath) (name : String) : IO (List String) := do
  if !(← (checkedPath dir name).pathExists) then return []
  match (← readJson (checkedPath dir name)).getArr? with
  | .ok xs => return xs.toList.filterMap fun x => x.getStr?.toOption
  | .error _ => return []

/-- `work: laws over the holed states: K kept from the capture, N checked now, re-checked 0`: of the
laws the judgment applies to the pages a fill writes, how many the capture checked once (their fill
typed by `Obend.Vault.Form.checked_once`, not checked again) and how many it did not (a law added
since, or a page the capture could not read), checked here. -/
def checkWorkLine (dir : System.FilePath) (f : Obend.Vault.Form.Form) (es : List Entry)
    (a : Obend.Vault.Form.Assignment) : IO String := do
  let kept ← readChecks dir f.name
  let apps := f.lawAppsOf es a
  let reused := apps.filter fun x => kept.contains x.key
  let fresh := apps.filter fun x => !kept.contains x.key
  let refused := fresh.filter fun x => !(f.checkOver x.S x.term).toBool
  if apps.isEmpty then return ""
  return "work: laws over the holed states: " ++ toString reused.length ++ " kept from the capture, " ++
    toString fresh.length ++ " checked now" ++
    (if refused.isEmpty then "" else " (" ++ toString refused.length ++ " refused by the checker)") ++
    ", re-checked 0"

/-- `work: performed P, retained R of T`: of what a form carries (each move of its residual, each
value its contract offers), how much the step judged anew, and how much is still good without being
redone. -/
def workLine (p r t : Nat) : String :=
  "work: performed " ++ toString p ++ ", retained " ++ toString r ++ " of " ++ toString t

def carried (f : Form) (K : Option Transport.Contract) : Nat :=
  f.moves.length + ((K.map (·.offer.length)).getD 0)

def verdictLine (name : String) (ls : List Transport.Moved) : Transport.Verdict → Option Transport.Contract → String
  | .continues, none => name ++ ": transported over the laws of " ++ ", ".intercalate (ls.map Transport.Moved.text) ++
      ": nothing was promised; it continues"
  | .continues, some K => name ++ ": transported over the laws of " ++ ", ".intercalate (ls.map Transport.Moved.text) ++
      ": they admit every value it offers (" ++ Transport.runsText K.offer ++ "); it continues"
  | .repaired b a, some K => name ++ ": transported over the laws of " ++ ", ".intercalate (ls.map Transport.Moved.text) ++
      ": they admit " ++ K.hole ++ " = " ++ Transport.runsText a ++ " of " ++ Transport.runsText b ++
      "; the offer narrows to them, the residual kept"
  | .repaired b a, none => name ++ ": transported: " ++ Transport.runsText b ++ " → " ++ Transport.runsText a
  | .refused x, _ => name ++ ": refused at " ++ toString x

def vaultName (dir : System.FilePath) : IO String := do
  return ((← IO.FS.realPath dir).fileName).getD "vault"

end Forms

/-- Copy a directory, the vault's lock aside. -/
partial def copyTree (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for e in ← src.readDir do
    if e.fileName == "lock" then continue
    if ← e.path.isDir then copyTree e.path (dst / e.fileName)
    else Obend.Vault.Cost.writeBinFile (dst / e.fileName) (← Obend.Vault.Cost.readBinFile e.path)

/-- The line `N` (from 1) of a file, as read. -/
def lineOf (spec : String) : IO (Except String (String × String)) := do
  match spec.splitOn ":" with
  | [file, n] =>
    match n.toNat? with
    | some k =>
      if !(← (System.FilePath.mk file).pathExists) then return .error ("refused: no file " ++ file)
      let ls := (← Obend.Vault.Cost.readFile file).splitOn "\n"
      match ls[k - 1]? with
      | some l => if k == 0 then return .error "refused: lines count from 1" else return .ok (l, spec)
      | none => return .error ("refused: " ++ file ++ " has no line " ++ n)
    | none => return .error "--line FILE:N"
  | _ => return .error "--line FILE:N"

/-- One event of the vault's reasons, committed as a turn of its log: what changed status, said, and
how much was judged anew. -/
def reasonTurn (dir : System.FilePath) (said : String) (e : Obend.Reasons.Event) : IO UInt32 := do
  let w0 ← readWorld dir
  match ← commitWith dir (.reasoned e) (fun h _ => pure h.world) with
  | .error err => fail err
  | .ok w =>
    IO.println said
    let cs := Obend.Reasons.changes w0.reasons w.reasons
    if cs.isEmpty then IO.println "  no status changed" else for c in cs do IO.println ("  " ++ c)
    let (n, t) := Obend.Reasons.workOf w.reasons.base e
    IO.println ("  judged anew: " ++ toString n ++ " of " ++ toString t ++ " atoms")
    return 0

/-- `obend reasons …`: the vault's reasons (`Obend.Reasons`), each event a turn of its log. -/
def reasonsRun (dir : System.FilePath) : List String → Option (IO UInt32)
  | "observe" :: name :: rest => some do
    let (line, rest) := flag "--line" rest
    match line, rest with
    | some spec, [] =>
      match ← lineOf spec with
      | .error e => fail e
      | .ok (text, src) =>
        reasonTurn dir ("observed " ++ name ++ ": " ++ text) (.observe ⟨name, text, src⟩)
    | none, [text] => reasonTurn dir ("observed " ++ name ++ ": " ++ text) (.observe ⟨name, text, "said"⟩)
    | _, _ => fail "reasons observe NAME (--line FILE:N | TEXT)"
  | ["assume", a] => some (reasonTurn dir ("assumed " ++ a) (.assume a))
  | ["withdraw", a] => some (reasonTurn dir ("withdrew " ++ a) (.withdraw a))
  | "explain" :: name :: concl :: rest => some do
    let (pos, rest) := allFlags "--if" rest
    let (neg, rest) := allFlags "--unless" rest
    unless rest.isEmpty do return ← fail "reasons explain NAME CONCLUSION --if PREMISE… [--unless DEFEATER…]"
    let r : Obend.Reasons.Rule := ⟨name, concl, pos, neg⟩
    reasonTurn dir ("explained " ++ name ++ ": " ++ Obend.Reasons.ruleText r) (.explain r)
  | ["defeat", target, "--by", by'] => some
      (reasonTurn dir (target ++ " is defeated while " ++ by' ++ " is supported") (.defeat ⟨target, by'⟩))
  | ["propose", name, "--because", c] => some do
    let r ← reasonTurn dir ("proposed " ++ name ++ " because " ++ c) (.propose ⟨name, c⟩)
    if r != 0 then return r
    let w ← readWorld dir
    match w.reasons.admit name with
    | .ok _ => IO.println ("  " ++ name ++ ": admissible now"); return 0
    | .error e => IO.println ("  " ++ e); return 0
  | ["admit", name] => some do
    let w ← readWorld dir
    match w.reasons.admit name with
    | .ok a => IO.println (name ++ ": admitted (" ++ a.because ++ " is supported by " ++
        ((w.reasons.standing a.because).getD "observation or assumption") ++ ")"); return 0
    | .error e => IO.eprintln e; return 1
  | ["status"] => some do
    let w ← readWorld dir
    for x in w.reasons.atoms do IO.println (w.reasons.line x)
    for a in w.reasons.base.actions do
      IO.println (match w.reasons.admit a.name with
        | .ok _ => "action " ++ a.name ++ ": admissible (because " ++ a.because ++ ")"
        | .error _ => "action " ++ a.name ++ ": inadmissible (because " ++ a.because ++ ", " ++
            (w.reasons.status a.because).text ++ ")")
    return 0
  | ["why", x] => some do
    let w ← readWorld dir
    IO.println (w.reasons.line x)
    return 0
  | _ => none

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
    let (_, V) ← Obend.Vault.Cost.phase "read" (openDir dir false)
    let (ow, _) ← Obend.Vault.Cost.phase "read" (openWorld other false)
    let label := (System.FilePath.mk other).fileName.getD other
    let w0 ← Obend.Vault.Cost.phase "read" (readWorld dir)
    let (admitted, refused, dups) := sortLandings w0 (w0.grants.merge ow.grants) ow.landed
    -- after a forget, whether the other log reaches the horizon: holds, among its receipt digests (and
    -- the anchors of its own checkpoint record), the receipt the forgotten prefix here ended at
    let mine ← readArray (logPath dir)
    let reaches ← match parseOneAt logHash (some Rehydration.genesisSentinel) mine 0 with
      | .ok (r, _) => match anchorOfTurn r.payload with
        | some a => do
          let (qs, _, _) := parseLogAt logHash anchorOfTurn (← readArray (logPath other))
          let ds := qs.map (fun q => Hr logHash q.receipt) ++ qs.filterMap (fun q => anchorOfTurn q.payload)
          pure (some (ds.contains a))
        | none => pure none
      | .error _ => pure none
    match ← finishTurn dir (.merged label ow.store false (some ow.grants) ow.landed reaches) V with
    | .ok (_, .merged s' notes, rendered) =>
      -- a write of the other side the tip did not land is a refused write of this merge
      -- (here's own writes the merge left unsettled are refusals of their pages, said by `finishTurn`)
      let refused := notes.filter fun n => (n.splitOn ": not merged").length > 1
      let unsettled := notes.filter fun n => (n.splitOn "here's write was not settled").length > 1
      for n in notes do unless refused.contains n || unsettled.contains n do IO.println n
      sayRefused refused
      for l in rendered do IO.println l
      for l in problems s' do IO.println l
      -- of the other replica's landings, how many stand here (none is judged again)
      let n := admitted.length + refused.length + dups.length
      if n > 0 then IO.println (workLine 0 admitted.length n)
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
    let addition ← if file == "-" then (do let stdin ← IO.getStdin; stdin.readToEnd) else Obend.Vault.Cost.readFile file
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
          if let .error e ← commitWith dir (.issued name) (fun _ _ => pure ()) then return ← fail e
          recordChecks dir name
          IO.println ("captured " ++ name ++ " from " ++ situation ++ " for " ++ who ++ ": " ++
            toString f.cells.length ++ " page(s) shown, " ++ toString culled ++ " not shown to " ++ who)
          for l in f.describe do IO.println l
          return 0
        | .ok _ => fail "the capture said what a capture does not"
    | _, _, _, _ => fail "capture SITUATION FORM --for WHO --grant PATTERN … [--held CAPS] --move FROM TO AMOUNT [--field FIELD] [--ref PAGE …]"
  | "brief" :: page :: name :: rest => some do
    let (who, rest) := flag "--for" rest
    let (held, rest) := flag "--held" rest
    let (pats, rest) := allFlags "--grant" rest
    let (sets, rest) := allFlags "--set" rest
    let (holes, rest) := allFlags "--hole" rest
    let lits := sets.filterMap fun x => match x.splitOn "=" with
      | f :: v :: more => some (f, "=".intercalate (v :: more))
      | _ => none
    let hs := holes.filterMap fun x => match x.splitOn ":" with
      | [h, t] => if ["label", "text", "natural", "page"].contains t then some (h, t) else none
      | _ => none
    match who, rest, parseCaps (held.getD "read,write") with
    | some who, [], some caps =>
      if lits.length != sets.length || hs.length != holes.length then
        return ← fail "brief: a set is FIELD=VALUE, a hole FIELD:label or FIELD:text"
      let _ ← openDir dir false
      match ← commitWith dir (.briefed page name ⟨who, caps, pats⟩ lits hs) (fun _ o => pure o) with
      | .error e => fail e
      | .ok (.form f culled) =>
        if let .error e ← commitWith dir (.issued name) (fun _ _ => pure ()) then return ← fail e
        IO.println ("briefed " ++ name ++ " on " ++ page ++ " for " ++ who ++ ": " ++
          toString f.cells.length ++ " page(s) shown, " ++ toString culled ++ " not shown to " ++ who)
        for l in f.describe do IO.println l
        return 0
      | .ok _ => fail "the brief said what a brief does not"
    | _, _, _ => fail "brief PAGE FORM --for WHO --grant PATTERN … [--held CAPS] [--set FIELD=VALUE …] [--hole FIELD:label|text …]"
  | "offer" :: name :: hole :: range :: rest => some do
    let (promise, rest) := flag "--promise" rest
    unless rest.isEmpty do return ← fail "offer FORM HOLE LO..HI [--promise LO..HI]"
    let some offer := Transport.parseRange range | fail ("offer: " ++ range ++ " is not LO..HI")
    let some prom := (promise.map Transport.parseRange).getD (some []) | fail "offer: --promise LO..HI"
    let _ ← openDir dir false
    let K : Transport.Contract := ⟨hole, offer, prom⟩
    match ← commitWith dir (.offered name K) (fun _ o => pure o) with
    | .error e => fail (name ++ ": " ++ e)
    | .ok (.offered n) =>
      IO.println (name ++ ": offers " ++ hole ++ " = " ++ Transport.runsText offer ++ ", promises " ++
        Transport.runsText prom ++ " (each value judged by the laws as they stand: " ++ toString n ++ " admitted)")
      return 0
    | .ok _ => fail "the offer said what an offer does not"
  | "grant" :: id :: rest => some do
    let (who, rest) := flag "--for" rest
    let (held, rest) := flag "--held" rest
    let (pats, rest) := allFlags "--grant" rest
    match who, rest, parseCaps (held.getD "read,write") with
    | some who, [], some caps =>
      match ← commitWith dir (.granted id ⟨who, caps, pats⟩) (fun _ _ => pure ()) with
      | .error e => fail e
      | .ok () =>
        IO.println ("granted " ++ id ++ " to " ++ who ++ " (" ++ Obend.Vault.Form.showAuths caps ++ " on " ++
          ", ".intercalate pats ++ ")")
        return 0
    | _, _, _ => fail "grant ID --for WHO --grant PATTERN … [--held CAPS]"
  | ["revoke", id] => some do
    match ← commitWith dir (.revoked id) (fun _ _ => pure ()) with
    | .error e => fail e
    | .ok () => IO.println ("revoked " ++ id); return 0
  | ["grants"] => some do
    let w ← readWorld dir
    for g in w.grants.standing do
      IO.println (g.id ++ ": " ++ g.grant.holder ++ " (" ++ Obend.Vault.Form.showAuths g.grant.held ++ " on " ++
        ", ".intercalate g.grant.patterns ++ ")" ++ (if w.grants.revoked.contains g.id then ", revoked" else ""))
    return 0
  | "reasons" :: rest => reasonsRun dir rest
  | ["obligations"] => some do
    let w ← readWorld dir
    if w.outstanding.isEmpty then IO.println "nothing outstanding"
    for o in w.outstanding do
      IO.println (o.form ++ ": intent " ++ o.intent ++ " (" ++ fillText o.fill ++ ") sent to " ++ o.vault ++
        ", awaiting its receipt")
    return 0
  | ["confirm", file] => some do
    let j ← readJson file
    let i ← ofExcept file (j.getObjValAs? String "intent")
    let r ← ofExcept file (Obend.Vault.Form.receiptOf (← ofExcept file (j.getObjVal? "receipt")))
    match ← commitWith dir (.confirmed i r.effectsHash) (fun h _ => pure h.world) with
    | .error e => fail e
    | .ok w =>
      IO.println ("confirmed intent " ++ i ++ ": its receipt names the proposal sent from here; " ++
        (if w.outstanding.isEmpty then "nothing outstanding" else toString w.outstanding.length ++ " outstanding"))
      return 0
  | "forget" :: name :: rest => some do
    let (retire, rest) := allFlags "--retire" rest
    let (abandon, rest) := allFlags "--abandon" rest
    unless rest.isEmpty do return ← fail "forget NAME [--retire FORM …] [--abandon BRANCH …]"
    let _ ← openDir dir false
    let c : Retention.Contract := ⟨name, retire, abandon⟩
    let r ← withLog dir fun h => do
      match ← commitTurn dir h (.forget c) with
      | .error e => return Except.error e
      | .ok (h', _) =>
        let bytes := h'.size
        let records := h'.count
        let h'' ← compactLog dir h'
        return .ok (records, bytes, h''.size)
    match r with
    | .error e => fail e
    | .ok (n, b, b') =>
      IO.println ("forgot " ++ toString n ++ " records (" ++ toString b ++ " bytes) under the retention contract " ++
        name ++ (if retire.isEmpty then "" else ", retiring " ++ ", ".intercalate retire) ++
        (if abandon.isEmpty then "" else ", abandoning " ++ ", ".intercalate abandon) ++
        ": the log is one checkpoint record of " ++ toString b' ++ " bytes")
      return 0
  | ["fork", other] => some do
    let _ ← openDir dir false
    let name := (System.FilePath.mk other).fileName.getD other
    if ← (System.FilePath.mk other).pathExists then return ← fail ("refused: " ++ other ++ " exists")
    match ← commitWith dir (.forked name) (fun _ _ => pure ()) with
    | .error e => fail e
    | .ok () =>
      copyTree dir other
      IO.println ("forked " ++ name ++ ": a copy of this vault, declared here until it merges")
      return 0
  | ["transport", name] => some do
    let _ ← openDir dir false
    let w ← readWorld dir
    let some f := w.forms.find? (·.name == name) | fail ("refused: no form named " ++ name)
    let ms := Transport.cellMoves w.store f
    let iss := issueOf w f
    let ls := Transport.lawMoves w.store f iss.basis
    let am := Transport.authorityMoves w.grants f (Transport.formPages f)
    let vs := valueMoves ms
    let ws := waiting ms
    let T := carried f iss.contract
    IO.println (name ++ ": display: " ++
      (if !vs.isEmpty then "stale (value: " ++ ", ".intercalate (vs.map Transport.Moved.text) ++ ")"
       else if !ws.isEmpty then "waits (" ++ ", ".intercalate (ws.map Transport.Moved.text) ++ ")"
       else "as it was"))
    for m in ms do
      if let .support p d := m then
        IO.println (name ++ ": support moved under " ++ p ++ " (" ++ d ++ "); the values it read are as captured")
    IO.println (name ++ ": authority: " ++ supportsText w f)
    if !vs.isEmpty then
      IO.println (name ++ ": effect: stale (value)"); IO.println (workLine 0 0 T); return 0
    if !ws.isEmpty then
      IO.println (name ++ ": effect: waits"); IO.println (workLine 0 T T); return 0
    let mut performed := 0
    let mut K := iss.contract
    if !ls.isEmpty then
      match ← commitWith dir (.transported name) (fun _ o => pure o) with
      | .error e =>
        IO.eprintln (name ++ ": effect: stale (the laws over " ++ ", ".intercalate (ls.map Transport.Moved.text) ++
          " moved); " ++ e)
        IO.println (workLine (((iss.contract.map (·.offer.length)).getD 0)) 0 T)
        return 1
      | .ok (.transported v p _) =>
        performed := p
        K := match v, iss.contract with
          | .repaired _ a, some K0 => some { K0 with offer := a }
          | _, k => k
        IO.println (verdictLine name ls v iss.contract)
      | .ok _ => return ← fail "the transport said what a transport does not"
    IO.println (name ++ ": effect: " ++
      (if !am.isEmpty then "stale (authority: no grant that stands lets " ++ Transport.holderOf f ++ " write " ++
          ", ".intercalate (am.map Transport.Moved.text) ++ ")"
       else if ls.isEmpty then "as it was" else "as transported"))
    IO.println (workLine performed (carried f K) T)
    return 0
  | ["abstract", name, value, hole] => some do
    match ← commitWith dir (.abstracted name value hole) (fun _ o => pure o) with
    | .error e => fail e
    | .ok (.form g _) =>
      recordChecks dir name
      IO.println (name ++ ": " ++ value ++ " is now the hole " ++ hole)
      for l in g.describe do IO.println l
      return 0
    | .ok _ => fail "the abstraction said what an abstraction does not"
  | ["checked", name] => some do
    let w ← readWorld dir
    let some f := w.forms.find? (·.name == name) | fail ("refused: no form named " ++ name)
    let kept ← readChecks dir name
    let apps := (f.lawApps w.store.entries).filter fun x => kept.contains x.key
    IO.println (name ++ ": " ++ toString apps.length ++ " law(s) over its holed states, checked once with " ++
      ", ".intercalate (f.holes.filterMap fun (h, t) => if t == .nat then some h else none) ++ " open:")
    for x in apps do
      IO.println ("  " ++ x.pkg ++ ": " ++ x.law.drop (x.pkg.length + 2) ++ " at " ++ x.page ++
        (if x.src then " (debited)" else " (credited)"))
    return 0
  | "form" :: name :: rest => some do
    let (out, rest) := flag "--out" rest
    unless rest.isEmpty do return ← fail "form FORM [--out FILE]"
    let w ← readWorld dir
    let some f := w.forms.find? (·.name == name) | fail ("refused: no form named " ++ name)
    let K := (issueOf w f).contract
    for l in f.describe do IO.println l
    if let some K := K then IO.println (contractLine K)
    if let some o := out then
      writeJson o (receivedJson f (Obend.Vault.Form.formDigest H f) (← vaultName dir) [] K)
      IO.println ("wrote " ++ o)
    return 0
  | "fill" :: file :: rest => some do
    let (out, rest) := flag "--out" rest
    let (because, rest) := flag "--because" rest
    let some o := out | fail "fill FILE HOLE=VALUE … --out FILE"
    let (f, digest, vault, hops, K) ← readReceived file
    match parseFill f rest with
    | .error e => fail ("refused: " ++ e)
    | .ok a =>
      if let some K := K then
        if let some x := a.nats.lookup K.hole then
          unless K.offer.contains x do
            return ← fail (f.name ++ ": refused: " ++ K.hole ++ " = " ++ toString x ++ " is outside its offer (" ++
              Transport.runsText K.offer ++ ")")
      let holder := (((f.grants ++ hops).getLast?).map (·.holder)).getD "owner"
      -- the form as received and the proposal as sent, with the identity of its intent, are a turn of
      -- this directory's log; the proposal is outstanding until a receipt for it is confirmed
      match ← commitWith dir (.proposed f.name ((receivedJson f digest vault hops K).pretty ++ "\n") digest vault hops a
          holder because) (fun _ o => pure o) with
      | .error e => fail e
      | .ok (.proposed i text) =>
        Obend.Vault.Cost.writeFile o text
        IO.println (f.name ++ ": filled by " ++ holder ++ ": " ++ fillText a)
        for l in f.preview a do IO.println ("  " ++ l)
        if let some c := because then IO.println ("  because " ++ c)
        IO.println ("wrote " ++ o ++ " (intent " ++ i ++ ")")
        return 0
      | .ok _ => fail "the fill said what a fill does not"
  | "reshare" :: file :: rest => some do
    let (who, rest) := flag "--for" rest
    let (held, rest) := flag "--held" rest
    let (out, rest) := flag "--out" rest
    let (pats, rest) := allFlags "--grant" rest
    match who, out, rest, parseCaps (held.getD "read,write") with
    | some who, some o, [], some caps =>
      let (f, digest, vault, hops, K) ← readReceived file
      let cur := ((f.grants ++ hops).getLast?).getD Obend.Vault.Form.ownerGrant
      let g : Obend.Vault.Form.Grant := ⟨who, caps, pats⟩
      match Obend.Vault.Rehydration.Membrane.reshare (cur.viewer f.scope) (g.viewer f.scope) with
      | none => fail (f.name ++ ": " ++ Obend.Vault.Form.refusalText f (.amplifies cur.holder who cur.held caps))
      | some _ =>
        writeJson o (receivedJson f digest vault (hops ++ [g]) K)
        IO.println (f.name ++ ": reshared by " ++ cur.holder ++ " to " ++ who ++ " (" ++
          Obend.Vault.Form.showAuths caps ++ " on " ++ ", ".intercalate pats ++ ")")
        IO.println ("wrote " ++ o)
        return 0
    | _, _, _, _ => fail "reshare FILE --for WHO --grant PATTERN … [--held CAPS] --out FILE"
  | "judge" :: file :: rest => some do
    let (receiptOut, rest) := flag "--receipt" rest
    unless rest.isEmpty do return ← fail "judge FILE [--receipt FILE]"
    let (_, V) ← openDir dir false
    let j ← readJson file
    let name ← ofExcept file (j.getObjValAs? String "proposal")
    let digest ← ofExcept file (j.getObjValAs? String "digest")
    let hops ← ofExcept file ((← ofExcept file (j.getObjValAs? (Array Lean.Json) "hops")).toList.mapM Obend.Vault.Form.grantOf)
    let a ← ofExcept file (Obend.Vault.Form.assignmentOf (← ofExcept file (j.getObjVal? "fill")))
    let intent := (j.getObjValAs? String "intent").toOption
    let because := (j.getObjValAs? String "because").toOption
    let w0 ← readWorld dir
    let writeReceipt (w : Replay.World) (l : Transport.Landing) : IO Unit := do
      if let some ro := receiptOut then
        if let some r := w.receipts[l.receipt - 1]? then
          writeJson ro (Lean.Json.mkObj [("proposal", name), ("intent", l.intent), ("digest", digest),
            ("fill", Obend.Vault.Form.assignmentJson a), ("by", l.holder),
            ("receipt", Obend.Vault.Form.receiptJson r), ("chain", Lean.toJson l.receipt)])
          IO.println ("wrote " ++ ro)
    -- a proposal whose intent landed here: refused, and its receipt written again
    if let some i := intent then
      if let some l := Transport.duplicateOf w0.landed i then
        IO.eprintln (dupText w0 name l)
        writeReceipt w0 l
        if let some f := w0.forms.find? (·.name == name) then
          IO.println (workLine 0 (carried f (issueOf w0 f).contract) (carried f (issueOf w0 f).contract))
        return 1
    -- the laws over its pages moved since it was issued: transport it first
    let mut performed := 0
    if intent.isSome then
      if let some f := w0.forms.find? (·.name == name) then
        let ms := Transport.cellMoves w0.store f
        let ls := Transport.lawMoves w0.store f (issueOf w0 f).basis
        if (valueMoves ms).isEmpty && (waiting ms).isEmpty && !ls.isEmpty then
          match ← commitWith dir (.transported name) (fun _ o => pure o) with
          | .error e => IO.eprintln (name ++ ": " ++ e); return 1
          | .ok (.transported v p _) =>
            performed := p
            IO.println (verdictLine name ls v (issueOf w0 f).contract)
          | .ok _ => return ← fail "the transport said what a transport does not"
    let checkWork ← match w0.forms.find? (·.name == name) with
      | some f => checkWorkLine dir f w0.store.entries a
      | none => pure ""
    let turn : Turn := match because with
      | some c => .justified name digest hops a intent c
      | none => .judged name digest hops a intent
    match ← finishTurn dir turn V with
    | .error e =>
      IO.eprintln e
      let w ← readWorld dir
      if let some f := w.forms.find? (·.name == name) then
        let T := carried f (issueOf w f).contract
        IO.println (workLine performed (if (e.splitOn "stale (value)").length > 1 then 0 else T) T)
      return 2
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
      if let some l := w'.landed.getLast? then
        if intent == some l.intent then writeReceipt w' l
      if intent.isSome then
        let T := carried f (issueOf w' f).contract
        IO.println (workLine (performed + 1) T T)
      unless checkWork.isEmpty do IO.println checkWork
      return 0
    | .ok _ => fail "the judgment said what a judgment does not"
  | _ => none

/-- `obend` vault commands: `-C DIR` anywhere, `open DIR`. -/
def main? (args : List String) : Option (IO UInt32) :=
  let (dirFlag, args) := flag "-C" args
  let act := match args with
    | ["open", d] => run (System.FilePath.mk d) ["open"]
    | _ => run (System.FilePath.mk (dirFlag.getD ".")) args
  -- a command that ran but whose writes were refused (said on stderr) exits 1
  act.map fun a => do
    refusedRef.set []
    let rc ← a
    let rs ← refusedRef.get
    return (if rc == 0 && !rs.isEmpty then 1 else rc)

end Obend.Vault.Cli

end
