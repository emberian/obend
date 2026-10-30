module
/-
# `journal` — export the tree's declarations; read two exports as a redesign

    lake exe journal export [--root DIR] [--out FILE] [--only PREFIX]
        DIR is the `lean/` directory (default `.`); the tree's modules are every `Obend/**.lean` and
        `Obend.lean` under it, imported from the built `.olean`s. `--only PREFIX` imports only the
        modules whose name starts with PREFIX (and what they import): a subtree export, usable while
        an unrelated module is red. Writes `DIR/tools/journal/env-<commit>[-dirty].jsonl` unless
        `--out` names the file.

    lake exe journal diff OLD.jsonl NEW.jsonl [--names]
        The report of `Journal.report`: withdrawn supports, revised theorems, STATEMENT-CITED and
        PROOF-CITED with their dead supports by name, reproved, added, removed, and the unaffected
        count (`--names` lists them).

The exporter reads `.olean`s: `lake build` (or the subtree's modules) first; `lake build journal`
builds only the tool and `Obend.Slot`, which `Journal.Journal` imports.
-/
public import Lean
public import Journal.Export

open Lean Journal Journal.Export

/-- `Obend/**.lean` and `Obend.lean` under `dir`, as module names, sorted. -/
def treeModules (dir : System.FilePath) (root : String) : IO (Array Name) := do
  let mut mods : Array Name := #[]
  if ← (dir / s!"{root}.lean").pathExists then
    mods := mods.push (Name.mkSimple root)
  let base := (dir / root).components.length
  let files ← (dir / root).walkDir
  for f in files do
    if f.extension == some "lean" then
      -- the components after `dir`, so `dir/Obend/Core/Term.lean` is `Obend.Core.Term`
      let parts := (f.withExtension "").components.drop (base - 1)
      mods := mods.push (parts.foldl (fun n p => Name.str n p) .anonymous)
  return mods.qsort Name.lt

def git (dir : System.FilePath) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args, cwd := dir }
  return out.stdout.trimAscii.toString

def exportTree (dir : System.FilePath) (out? : Option String) (only? : Option String) : IO Unit := do
  let root := "Obend"
  initSearchPath (← findSysroot)
  let mods ← treeModules dir root
  let mods := match only? with
    | some pre => mods.filter fun m => (String.toName pre).isPrefixOf m
    | none => mods
  if mods.isEmpty then throw <| IO.userError s!"no {root} modules under {dir}{only?.map (s!" starting with {·}") |>.getD ""}"
  let imports := mods.map fun m => { module := m : Import }
  let all ← importModules imports {} (level := .private)
  -- the `module` files, by the olean's own flag, for the exported view
  let moduleOnly := imports.filter fun i =>
    match all.header.moduleNames.idxOf? i.module with
    | some idx => all.header.moduleData[idx]!.isModule
    | none => false
  let exported ← importModules moduleOnly {} (level := .exported)
  let views : Views := { all, exported := some exported }
  let rs := rows views (Name.mkSimple root)
  let commit ← git dir #["rev-parse", "--short", "HEAD"]
  let status ← git dir #["status", "--porcelain", "--", root, s!"{root}.lean"]
  let dirty := !status.isEmpty
  let toolchain := (← IO.FS.readFile (dir / "lean-toolchain")).trimAscii.toString
  let header : Header := { commit, dirty, toolchain, root, only := only?.getD "", modules := mods.size, rows := rs.size }
  let out := match out? with
    | some f => System.FilePath.mk f
    | none => dir / "tools" / "journal" / s!"env-{commit}{if dirty then "-dirty" else ""}.jsonl"
  IO.FS.writeFile out (render header rs)
  IO.println s!"{out}: {rs.size} rows from {mods.size} modules ({moduleOnly.size} module files{only?.map (s!", only {·}") |>.getD ""}) at {commit}{if dirty then " (dirty)" else ""}"

def readExport (path : String) : IO Export := do
  match parse (← IO.FS.readFile path) with
  | .ok e => pure e
  | .error err => throw <| IO.userError s!"{path}: {err}"

def showSupport : Support → String
  | .stmt n _ => s!"{n} [statement]"
  | .proof n _ => s!"{n} [proof]"

def showVerdict : Verdict → String
  | .unaffected => "unaffected"
  | .statementCited d => s!"STATEMENT-CITED {d.map Support.name}"
  | .proofCited d => s!"PROOF-CITED {d.map Support.name}"

/-- A section: its entries, one per line; `count` is the number of entries when the lines also carry
each entry's dead supports. -/
def printSection (title : String) (items : List String) (count : Nat := items.length) : IO Unit := do
  IO.println s!"{title} ({count})"
  for i in items do IO.println s!"  {i}"

def diff (oldPath newPath : String) (names : Bool) : IO Unit := do
  let old ← readExport oldPath
  let new ← readExport newPath
  let rep := report old new
  IO.println s!"journal: {oldPath} -> {newPath}"
  printSection "withdrawn supports" <| rep.withdrawn.map fun
    | .removed n => s!"{n}  removed"
    | .changed n _ _ => s!"{n}  meaning changed"
  printSection "revised theorems (own statement meaning changed)" <|
    rep.revised.map fun (n, v) => s!"{n}  then {showVerdict v}"
  printSection "STATEMENT-CITED" (count := rep.statementCited.length) <|
    rep.statementCited.flatMap fun (n, d) => n :: d.map fun s => s!"    dead: {showSupport s}"
  printSection "PROOF-CITED" (count := rep.proofCited.length) <|
    rep.proofCited.flatMap fun (n, d) => n :: d.map fun s => s!"    dead: {showSupport s}"
  printSection "reproved (supports hold, proof hash differs)" rep.reproved
  printSection "added theorems" rep.added
  printSection "removed theorems" rep.removed
  if names then printSection "unaffected" rep.unaffected
  else IO.println s!"unaffected ({rep.unaffected.length})"

def usage : String :=
  "usage: journal export [--root DIR] [--out FILE] [--only PREFIX]\n       journal diff OLD.jsonl NEW.jsonl [--names]"

public def main (args : List String) : IO UInt32 := do
  match args with
  | "export" :: rest =>
    let rec opts : List String → Option (String × Option String × Option String)
      | [] => some (".", none, none)
      | "--root" :: d :: more => (opts more).map fun (_, o, p) => (d, o, p)
      | "--out" :: f :: more => (opts more).map fun (d, _, p) => (d, some f, p)
      | "--only" :: p :: more => (opts more).map fun (d, o, _) => (d, o, some p)
      | _ => none
    match opts rest with
    | some (dir, out?, only?) => exportTree dir out? only?; return 0
    | none => IO.eprintln usage; return 2
  | ["diff", o, n] => diff o n false; return 0
  | ["diff", o, n, "--names"] => diff o n true; return 0
  | _ => IO.eprintln usage; return 2

