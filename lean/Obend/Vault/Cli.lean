module
/-
# Obend.Vault.Cli — `obend open` and the vault commands

    obend open [DIR]
        read every `.md` under DIR (default `.`; directories starting with `.` are skipped) as a page,
        keep the world beside it in DIR/.obend/world.json, resolve links whose pages now exist, render
        each page at the current view back to its file (a cite that does not hold is marked,
        `![[Beta]]{behind}`; the reader strips the marks, so a mark is never read as an edit), and
        report what changed, what was refused, which cites are behind and which sections wait for a
        selection. Twice in a row, the second changes nothing.
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

Every command but `member` opens the vault first (an edit on disk is the owner's write, judged by
the page's laws), so no command overwrites a file the person changed. `-C DIR` before or after a
command runs it in DIR.
-/
public import Obend.Vault.Json
public import Obend.Digest.Class
public section

namespace Obend.Vault.Cli

open Obend.Doc Obend.Vault Obend.Vault.Json

/-- The deployed byte hash (cSHAKE256, as `lean/tests/doc/RoundTrip.lean`). -/
def H : Obend.Digest.HashBytes.Hash := Obend.Digest.Digest.hash []

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
      else if p'.note != p.note && p'.note.isSome then some (p'.name ++ ": " ++ p'.note.getD "")
      else none

/-- Cites that do not hold and sections waiting, over every page. -/
def problems (s : Store) : List String :=
  s.pages.flatMap fun p =>
    ((citeReport H s p).filterMap fun (c, ok, why) => if ok then none else some (p.name ++ ": " ++ c ++ " is " ++ why)) ++
      (sectionReport p).map (p.name ++ ": " ++ ·)

/-- Open the vault: read, judge, render, write, save. Returns the store and the files as they now are. -/
def openDir (dir : System.FilePath) (verbose : Bool) : IO (Store × List (String × String)) := do
  let s ← loadStore dir
  let V ← readVault dir
  let o := openVault H s V
  writeFiles dir o.writes
  saveStore dir o.store
  if verbose then
    let cs := changes s o.store
    if cs.isEmpty then IO.println "nothing changed"
    for c in cs do IO.println c
    for (n, _) in o.writes do IO.println ("rendered " ++ n ++ ".md")
  return (o.store, overwrite V o.writes)

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
  (s.pages.filter fun p => only.all (· == p.name)).flatMap fun p =>
    [p.name ++ " v" ++ toString p.history.length ++ (match p.note with | some n => "; its last write was " ++ n | none => "")] ++
      (citeReport H s p).map (fun (c, ok, why) => "  " ++ c ++ (if ok then " ✓ " else " ✗ ") ++ why) ++
      (sectionReport p).map ("  " ++ ·)

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
    for l in statusOf s (args[1]?) do IO.println l
    return 0
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
  | _ => none

/-- `obend` vault commands: `-C DIR` anywhere, `open DIR`. -/
def main? (args : List String) : Option (IO UInt32) :=
  let (dirFlag, args) := flag "-C" args
  match args with
  | ["open", d] => run (System.FilePath.mk d) ["open"]
  | _ => run (System.FilePath.mk (dirFlag.getD ".")) args

end Obend.Vault.Cli

end
