module
/-
# Obend.Vault.Cli — `obend open` and the vault commands

    obend open [DIR]
        read every `.md` under DIR (default `.`; directories starting with `.` are skipped) as a page,
        keep the world beside it in DIR/.obend/world.json, resolve links whose pages now exist, render
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

Forms (`Obend.Vault.Form`; the walkthrough is `lean/tests/vault/FORMS.md`):

    obend capture SITUATION FORM --for WHO --grant PATTERN [--grant …] [--held CAPS]
                  --move FROM TO AMOUNT [--field FIELD] [--ref PAGE …]
        capture the situation of the page SITUATION (it and the pages it links to) as the form FORM
        for WHO: the pages WHO's grant (CAPS, default read,write, on the PATTERNs) shows, as they are
        now; the live move of AMOUNT of FIELD (default balance) from FROM to TO. Kept in
        .obend/forms/FORM.json.
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
        turn's tip; all of it lands or none, with one receipt in .obend/forms/receipts.json.

Every command but `member` opens the vault first (an edit on disk is the owner's write, judged by
the page's laws), so no command overwrites a file the person changed. `-C DIR` before or after a
command runs it in DIR. A kind page's line `environment: PATH` (PATH relative to the vault) names
the census's list of the library's names, `.lake/build/census/environment.txt` (`lake build
Obend.Census`, or `lake env lean tests/decisions/Environment.lean`): the open reads it and the
page's backticked names resolve against it (`new.unresolved`, `new.unresolvedInserted`); a named
file that is not there stops the command.
-/
public import Obend.Vault.Json
public import Obend.Vault.Form
public import Obend.Digest.Cshake256
public section

namespace Obend.Vault.Cli

open Obend.Doc Obend.Vault Obend.Vault.Json

/-- The deployed byte hash (cSHAKE256, as `lean/tests/doc/RoundTrip.lean`). -/
def H : Obend.Digest.HashBytes.Hash := Obend.Digest.Cshake256.cshake256Bytes []

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

def worldPath (dir : System.FilePath) : System.FilePath := dir / ".obend" / "world.json"

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

def loadStore (dir : System.FilePath) : IO Store := do
  if !(← (worldPath dir).pathExists) then return {}
  let txt ← IO.FS.readFile (worldPath dir)
  match Lean.Json.parse txt >>= storeOf with
  | .ok s => return s
  | .error e => throw (IO.userError ("cannot read " ++ (worldPath dir).toString ++ ": " ++ e))

def saveStore (dir : System.FilePath) (s : Store) : IO Unit := do
  IO.FS.createDirAll (dir / ".obend")
  IO.FS.writeFile (worldPath dir) ((storeJson s).compress ++ "\n")

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

/-- Open the vault: read, forget the files that are gone, judge, render, write, save. Returns the
store and the files as they now are. -/
def openDir (dir : System.FilePath) (verbose : Bool) : IO (Store × List (String × String)) := do
  let s ← loadStore dir
  let V ← readVault dir
  let s := { s with environment := ← loadEnvironment dir V }
  let f := forgetMissing s V
  let o := openVault H f.store V
  -- a page a kind's laws keep is written back from the text the store holds for it
  let back := f.kept.filterMap fun (n, _) => (o.store.page? n).bind fun p => p.seen.map (n, ·)
  writeFiles dir (o.writes ++ back)
  saveStore dir o.store
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
  return (o.store, overwrite (V ++ back) o.writes)

/-- Save a store a command made, and write the files it renders. -/
def finish (dir : System.FilePath) (s : Store) (V : List (String × String)) : IO Unit := do
  let s := settle H s
  let w := writesFor s V
  let missing := s.pages.filterMap fun p => if V.any (·.1 == p.name) then none else
    match p.seen, p.history with
    | some t, _ :: _ => some (p.name, t)
    | _, _ => none
  writeFiles dir (w ++ missing)
  saveStore dir s
  for (n, _) in w ++ missing do IO.println ("rendered " ++ n ++ ".md")

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

def loadForm? (dir : System.FilePath) (name : String) : IO (Option Form) := do
  let f := formsDir dir / (name ++ ".json")
  if !(← f.pathExists) then return none
  return some (← ofExcept f.toString (formOf (← readJson f)))

def saveForm (dir : System.FilePath) (f : Form) : IO Unit :=
  writeJson (formsDir dir / (f.name ++ ".json")) (formJson f)

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

def loadReceipts (dir : System.FilePath) : IO (List Obend.Vault.Rehydration.WitnessReceipt) := do
  let f := formsDir dir / "receipts.json"
  if !(← f.pathExists) then return []
  ofExcept f.toString ((← ofExcept f.toString ((← readJson f).getArr?)).toList.mapM receiptOf)

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
    let (s, V) ← openDir dir false
    let (o, _) ← openDir other false
    let label := (System.FilePath.mk other).fileName.getD other
    let (s', notes) := mergeFrom s o label
    for n in notes do IO.println n
    finish dir s' V
    for l in problems s' do IO.println l
    return 0
  | "member" :: "add" :: name :: rest => some do
    let gs := grants rest
    let parsed := gs.filterMap parseGrant
    if parsed.length != gs.length || gs.isEmpty then
      return ← fail "member add NAME --grant VERB:PATTERN …  (VERB: post, select, write, relaw)"
    let s ← loadStore dir
    match addMember s name parsed with
    | .ok s' => saveStore dir s'; IO.println ("member " ++ name ++ " may " ++
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
        -- file; refused, nothing is saved and the file stands
        let some p := s.page? page | fail ("refused: no page named " ++ page)
        let ch := judgeAt H s.entries s p text
        match ch.note with
        | some why => fail (page ++ ": " ++ why)
        | none =>
          let s' := s.setPage (p.withChange ch)
          IO.println ("owner posted to " ++ page ++ " (v" ++ toString ch.history.length ++ ")")
          finish dir s' V
          for l in problems s' do IO.println l
          return 0
      | some _ =>
        match s.actor asName >>= fun who => postAs H s who page text with
        | .ok s' => IO.println ((asName.getD "owner") ++ " posted to " ++ page); finish dir s' V
                    for l in problems s' do IO.println l
                    return 0
        | .error e => fail ("refused: " ++ e)
  | ["select", page, k, i] => some do
    let (s, V) ← openDir dir false
    match k.toNat?, i.toNat? with
    | some k, some i =>
      match s.actor asName >>= fun who => selectIn s who page k i with
      | .ok s' => IO.println ("kept candidate " ++ toString i ++ " of section " ++ toString k ++ " of " ++ page)
                  finish dir s' V
                  return 0
      | .error e => fail ("refused: " ++ e)
    | _, _ => fail "select PAGE SECTION CANDIDATE"
  | ["recite", page] => some do
    let (s, V) ← openDir dir false
    match s.actor asName >>= fun who => reciteIn H s who page with
    | .ok (s', n) => IO.println ("re-cited " ++ toString n ++ " cite(s) of " ++ page); finish dir s' V
                     return 0
    | .error e => fail ("refused: " ++ e)
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
        let (s, _) ← openDir dir false
        if (← loadForm? dir name).isSome then return ← fail ("refused: a form named " ++ name ++ " exists")
        match Obend.Vault.Form.captureFrom s situation name ⟨who, caps, pats⟩ src dst amount (field.getD "balance") refs with
        | .error e => fail ("refused: " ++ e)
        | .ok (f, culled) =>
          saveForm dir f
          IO.println ("captured " ++ name ++ " from " ++ situation ++ " for " ++ who ++ ": " ++
            toString f.cells.length ++ " page(s) shown, " ++ toString culled ++ " not shown to " ++ who)
          for l in f.describe do IO.println l
          return 0
    | _, _, _, _ => fail "capture SITUATION FORM --for WHO --grant PATTERN … [--held CAPS] --move FROM TO AMOUNT [--field FIELD] [--ref PAGE …]"
  | ["abstract", name, value, hole] => some do
    let some f ← loadForm? dir name | fail ("refused: no form named " ++ name)
    match f.abstract value hole with
    | .error e => fail ("refused: " ++ e)
    | .ok g =>
      saveForm dir g
      IO.println (name ++ ": " ++ value ++ " is now the hole " ++ hole)
      for l in g.describe do IO.println l
      return 0
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
      writeJson (formsDir dir / "received" / (f.name ++ ".json")) (receivedJson f digest vault hops)
      let prop := Lean.Json.mkObj [("proposal", f.name), ("digest", digest), ("vault", vault),
        ("hops", Lean.Json.arr (hops.map Obend.Vault.Form.grantJson).toArray),
        ("fill", Obend.Vault.Form.assignmentJson a), ("by", holder)]
      writeJson (formsDir dir / "sent" / (f.name ++ ".json")) prop
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
    let (s, V) ← openDir dir false
    let j ← readJson file
    let name ← ofExcept file (j.getObjValAs? String "proposal")
    let some f ← loadForm? dir name | fail ("refused: no form named " ++ name ++ " here")
    let digest ← ofExcept file (j.getObjValAs? String "digest")
    if digest != Obend.Vault.Form.formDigest H f then
      return ← fail (name ++ ": refused: the form has changed since this proposal's copy was sent; send the form again")
    let hops ← ofExcept file ((← ofExcept file (j.getObjValAs? (Array Lean.Json) "hops")).toList.mapM Obend.Vault.Form.grantOf)
    let a ← ofExcept file (Obend.Vault.Form.assignmentOf (← ofExcept file (j.getObjVal? "fill")))
    match Obend.Vault.Form.judgeProposal H s f hops a with
    | .error e => fail (name ++ ": " ++ e)
    | .ok (s', ad, t) =>
      let rs ← loadReceipts dir
      let r := Obend.Vault.Form.receiptFor H rs.getLast? f a ad t
      writeJson (formsDir dir / "receipts.json") (Lean.Json.arr ((rs ++ [r]).map Obend.Vault.Form.receiptJson).toArray)
      IO.println (name ++ ": landed as one turn over " ++ toString t.writeCells.length ++ " pages by " ++ ad.holder ++
        ", receipt " ++ Obend.Vault.Form.hex16 (Obend.Vault.Form.receiptDigest H r) ++ " (" ++
        toString (rs.length + 1) ++ " in the chain)")
      for d in t.writeCells do
        for A in f.assets do
          IO.println ("  " ++ d.cell ++ ": " ++ A ++ " " ++ toString (natAt d.preState A) ++ " → " ++
            toString (natAt d.postState A))
      finish dir s' V
      for l in problems s' do IO.println l
      return 0
  | _ => none

/-- `obend` vault commands: `-C DIR` anywhere, `open DIR`. -/
def main? (args : List String) : Option (IO UInt32) :=
  let (dirFlag, args) := flag "-C" args
  match args with
  | ["open", d] => run (System.FilePath.mk d) ["open"]
  | _ => run (System.FilePath.mk (dirFlag.getD ".")) args

end Obend.Vault.Cli

end
