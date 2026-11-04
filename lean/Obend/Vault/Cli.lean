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
        open, then every page (or PAGE) with its version, each cite and whether it holds, its sections.
    obend merge OTHER_DIR
        open both, then merge every page of OTHER_DIR's world into this one (the pushout of the two
        current versions); a page OTHER_DIR has alone is imported.
    obend member add NAME --grant VERB:PATTERN [--grant …]
        a member; VERB is post, select, write (re-cite) or relaw; PATTERN is a page, `folder/*` or `*`.
    obend member list
    obend post PAGE FILE --as NAME
        NAME's proposed text of PAGE (FILE, or `-` for stdin), as candidates in sections.
    obend select PAGE SECTION CANDIDATE [--as NAME]
        keep one candidate of a section; the owner, or a member granted select on PAGE.
    obend recite PAGE [--as NAME]
        re-justify PAGE's cites that are behind against their sources' current versions.
    obend create --from KIND PAGE
        a new page born under KIND (a kind page `folder/_kind`, or the folder): it names KIND in its
        frontmatter, starts with KIND's fields, and its birth is judged by KIND's laws.

Every command but `member` opens the vault first (an edit on disk is the owner's write, judged by
the page's laws), so no command overwrites a file the person changed. `-C DIR` before or after a
command runs it in DIR.
-/
public import Obend.Vault.Json
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

def grants : List String → List String
  | "--grant" :: g :: rest => g :: grants rest
  | _ :: rest => grants rest
  | [] => []

def parseGrant (g : String) : Option (String × String) :=
  match g.splitOn ":" with
  | [v, p] => if ["post", "select", "write", "relaw"].contains v then some (v, p) else none
  | _ => none

/-- Run a vault command in `dir`. `none` when the arguments are not a vault command. -/
def run (dir : System.FilePath) (args : List String) : Option (IO UInt32) :=
  let (asName, args) := flag "--as" args
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
    let text ← if file == "-" then (do let stdin ← IO.getStdin; stdin.readToEnd) else IO.FS.readFile file
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
  | _ => none

/-- `obend` vault commands: `-C DIR` anywhere, `open DIR`. -/
def main? (args : List String) : Option (IO UInt32) :=
  let (dirFlag, args) := flag "-C" args
  match args with
  | ["open", d] => run (System.FilePath.mk d) ["open"]
  | _ => run (System.FilePath.mk (dirFlag.getD ".")) args

end Obend.Vault.Cli

end
