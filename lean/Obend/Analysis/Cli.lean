module
/-
# Obend.Analysis.Cli — `obend analyze`

    obend analyze impact CELL@PIN --world PATH [--turn TURN.json] [--out RECEIPT.json]
        if CELL moved to PIN, what goes blocked, stale or behind, what is restored, and which law
        rows must be re-judged; each line with the opening it rests on (the support naming CELL and
        its value at PIN). PATH is a vault (a directory with `.obend/log`: CELL a page, PIN
        `N`/`vN` a version of its history, `retired`, or a file the owner would write) or a workspace
        (a `workspace.json`, or a directory holding one: CELL a record line `NAME^MAJOR`, PIN
        `P:VERSION`, `P:retired`, or another workspace file whose line it takes; the dependents are
        those of TURN, or of the entry's closure at the base). `PIN = ?` forgets CELL instead and
        lists what could change (`read3` under the forgetting setup). The list is checked by the
        registered `impact@1` judge before it is printed; `--out` writes it as a receipt, which
        `obend verify` re-checks with no producer state. Exit 0 when the list is accepted.
        (`--tooth drop-read`: the producer's index drops each dependent's last read; the checker
        then refuses the list as `missing` wherever that read was the one that moved.)
    obend analyze replay PAGE@FILE --world DIR
        the vault's history replayed with PAGE amended to FILE (the owner's write of it): every write
        of every page PAGE's laws judge, re-judged under the laws in force and under the amended ones;
        the first write they judge differently, per page (after it the history would differ).
-/
public import Obend.Analysis.Replay
public section

namespace Obend.Analysis.Cli

open Lean Obend.Analysis Obend.Slot

def pad (s : String) (n : Nat) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')

def pinText : Option String → String
  | some p => p
  | none => "retired"

/-- The word for a line: the dependent's kind's word when blocked. -/
def word (q : Question TView) (l : Line TFact) : String :=
  match l.goes with
  | .blocked => ((q.deps.find? (·.name == l.dep)).map (·.kind.word)).getD "blocked"
  | .restored => "restored"
  | .rejudge => "rejudge"

def kindOfLine (q : Question TView) (l : Line TFact) : String :=
  ((q.deps.find? (·.name == l.dep)).map (·.kind.name)).getD "?"

def lineText (q : Question TView) (l : Line TFact) : String :=
  pad (word q l) 12 ++ pad (kindOfLine q l) 10 ++ l.dep ++ "\n" ++
    "            rests on: " ++ l.support.name ++ " = " ++ toString l.value ++ " at " ++
      (show String from q.cell) ++ "@" ++ pinText q.pin

def clauseText : Clause → String
  | .notIndexed d => "not-indexed: " ++ d ++ " is no dependent of the question"
  | .doesNotRead d => "does-not-read: " ++ d ++ "'s line rests on a support it does not read, or not of the moved cell"
  | .wrongOpening d => "wrong-opening: " ++ d ++ "'s opening is not what the new pin says, or it does not go that way"
  | .missing d => "missing: " ++ d ++ " changes and is not listed"

def verdictText : Judge.Verdict Clause → String
  | .ok => "checked (impact@1, decidable, compiled)"
  | .refused k p => "refused: " ++ clauseText k ++ (if p.isEmpty then "" else " (line " ++ toString p ++ ")")
  | .uncovered => "uncovered"

/-- The receipt of an impact analysis: the question and the list. -/
def receiptJson (q : Question TView) (ls : List (Line TFact)) : Json :=
  Json.mkObj [("kind", toJson "impact"), ("format", toJson "impact@1"), ("object", questionJson q),
    ("certificate", linesJson ls)]

/-- Print the analysis of a concrete move, check it, and write the receipt. -/
def report (what : String) (q : Question TView) (tooth : Bool) (out : Option String) (note : Option String) :
    IO UInt32 := do
  let readers := q.deps.filter fun d => d.reads.any fun f => decide (f.cell = q.cell)
  let ls := if tooth then affectedWith (fun d => d.reads.dropLast) q else affected q
  let before := (q.base.pins.lookup q.cell)
  IO.println ("impact of " ++ (show String from q.cell) ++ ": " ++ pinText before ++ " -> " ++ pinText q.pin ++
    " (" ++ what ++ ")")
  if let some n := note then IO.println ("note: " ++ n)
  for l in ls do IO.println (lineText q l)
  IO.println (toString ls.length ++ " affected of " ++ toString readers.length ++ " dependents reading " ++
    (show String from q.cell) ++ " (" ++ toString q.deps.length ++ " indexed)")
  let v := check 0 q ls
  IO.println (verdictText v)
  if let some path := out then
    IO.FS.writeFile path ((receiptJson q ls).pretty ++ "\n")
    IO.println ("wrote " ++ path)
  return (if v == .ok then 0 else 3)

/-- Print what could change once a cell is forgotten: `read3` under the forgetting setup. -/
def reportForget (what : String) (q : Question TView) : IO UInt32 := do
  let σ := (Setup.ofView q.base).forget q.cell
  IO.println ("if " ++ (show String from q.cell) ++ " were unknown (" ++ what ++ ")")
  let mut n := 0
  for d in q.deps do
    let named := d.reads.filter fun f => decide (f.cell = q.cell)
    if named.isEmpty then continue
    if d.kind.isRow then
      IO.println (pad "rejudge" 12 ++ pad d.kind.name 10 ++ d.name)
      n := n + 1
    else
      match σ.read3 depSlot (some d) with
      | .undecided _ u =>
        IO.println (pad "open" 12 ++ pad d.kind.name 10 ++ d.name ++ "\n            undecided: " ++
          ", ".intercalate (u.map (·.name)))
        n := n + 1
      | .blocked _ dd =>
        IO.println (pad "known-dead" 12 ++ pad d.kind.name 10 ++ d.name ++ "\n            blocked whatever "
          ++ (show String from q.cell) ++ " holds: " ++ ", ".intercalate (dd.map (·.name)))
      | _ => pure ()
  IO.println (toString n ++ " could change")
  return 0

def flagVal (name : String) : List String → Option String × List String
  | [] => (none, [])
  | f :: v :: rest => if f == name then (some v, rest) else
      let (r, rest') := flagVal name (v :: rest); (r, f :: rest')
  | [x] => (none, [x])

/-- Split `CELL@PIN` at its last `@`. -/
def splitAt (s : String) : Option (String × String) :=
  match (s.splitOn "@").reverse with
  | pin :: cell@(_ :: _) => some ("@".intercalate cell.reverse, pin)
  | _ => none

/-- Split `NAME^MAJOR` at its last `^`. -/
def splitLine (s : String) : Option (String × Nat) :=
  match (s.splitOn "^").reverse with
  | m :: name@(_ :: _) => m.toNat?.map ("^".intercalate name.reverse, ·)
  | _ => none

def runFE {α : Type} (x : Obend.Spec.Capture.FE α) : IO (Except String α) := do
  match ← x.run with
  | .ok a => return .ok a
  | .error d => return .error d.message

/-- A workspace world: the file, or `workspace.json` in the directory. -/
def workspacePath? (path : String) : IO (Option String) := do
  let p := System.FilePath.mk path
  if (← p.isDir) then
    let w := p / "workspace.json"
    if (← w.pathExists) then return some w.toString else return none
  else if path.endsWith ".json" then return some path
  else return none

def impactVault (dir : String) (cell spec : String) (tooth : Bool) (out : Option String) : IO UInt32 := do
  let s ← Obend.Vault.Cli.loadStore dir
  if spec == "?" then
    let some p := s.page? cell | IO.eprintln ("no page named " ++ cell); return 2
    return ← reportForget ("vault " ++ dir) (VaultWorld.question s ⟨p.id, p.name, p.history, none⟩)
  match ← VaultWorld.move s cell spec with
  | .error e => IO.eprintln e; return 2
  | .ok m => report ("vault " ++ dir) (VaultWorld.question s m) tooth out m.note

def impactWorkspace (path : String) (cell spec : String) (turn : Option String) (tooth : Bool)
    (out : Option String) : IO UInt32 := do
  let some (name, major) := splitLine cell | IO.eprintln "a workspace cell is NAME^MAJOR"; return 2
  let w ← match ← runFE (Obend.Spec.Workspace.readWorkspace path) with
    | .ok w => pure w
    | .error e => IO.eprintln e; return 2
  let t ← match turn with
    | some tp => match ← runFE (do
        let (_, j) ← Obend.Spec.Capture.readJson tp
        Obend.Spec.Workspace.turnOfJson w ((j.getObjVal? "turn").toOption.getD j)) with
      | .ok t => pure t
      | .error e => IO.eprintln e; return 2
    | none => match Obend.Spec.Ecosystem.close w.view w.entry.release with
      | .ok cl => pure cl.turn
      | .error r => IO.eprintln ("the entry does not close at the base: " ++ r.message); return 2
  let c := WorkspaceWorld.cellName name major
  if spec == "?" then
    return ← reportForget ("workspace " ++ path) (WorkspaceWorld.question w.view t c none)
  let moved ← match spec.splitOn ":" with
    | [p, "retired"] => match p.toNat? with
      | some p => pure (some ⟨name, major, p, none, ""⟩)
      | none => IO.eprintln "PIN is P:VERSION, P:retired, `?`, or a workspace file"; return 2
    | [p, v] => match p.toNat? with
      | some p => pure (some ⟨name, major, p, some v, ""⟩)
      | none => IO.eprintln "PIN is P:VERSION, P:retired, `?`, or a workspace file"; return 2
    | _ =>
      let some other ← workspacePath? spec | IO.eprintln "PIN is P:VERSION, P:retired, `?`, or a workspace file"; return 2
      match ← runFE (Obend.Spec.Workspace.readWorkspace other) with
      | .ok w' => pure (w'.view.line name major)
      | .error e => IO.eprintln e; return 2
  report ("workspace " ++ path) (WorkspaceWorld.question w.view t c moved) tooth out none

def impact (args : List String) : IO UInt32 := do
  let (world, args) := flagVal "--world" args
  let (turn, args) := flagVal "--turn" args
  let (out, args) := flagVal "--out" args
  let (tooth, args) := flagVal "--tooth" args
  let some world := world | IO.eprintln "obend analyze impact CELL@PIN --world PATH [--turn TURN.json] [--out RECEIPT.json]"; return 64
  let [target] := args | IO.eprintln "obend analyze impact CELL@PIN --world PATH"; return 64
  let some (cell, spec) := splitAt target | IO.eprintln "name the move as CELL@PIN"; return 64
  let drop := tooth == some "drop-read"
  match ← workspacePath? world with
  | some ws => impactWorkspace ws cell spec turn drop out
  | none =>
    if !(← Obend.Vault.Cli.isVault world) then
      IO.eprintln (world ++ " is neither a vault (no .obend/log) nor a workspace"); return 2
    impactVault world cell spec drop out

def verdictWords : Except String Unit → String
  | .ok _ => "admitted"
  | .error e => e

/-- `obend analyze replay PAGE@FILE --world DIR`. -/
def replay (args : List String) : IO UInt32 := do
  let (world, args) := flagVal "--world" args
  let some world := world | IO.eprintln "obend analyze replay PAGE@FILE --world DIR"; return 64
  let [target] := args | IO.eprintln "obend analyze replay PAGE@FILE --world DIR"; return 64
  let some (page, file) := splitAt target | IO.eprintln "name the amendment as PAGE@FILE"; return 64
  if !(← Obend.Vault.Cli.isVault world) then
    IO.eprintln (world ++ " is not a vault (no .obend/log)"); return 2
  let s ← Obend.Vault.Cli.loadStore world
  let md ← IO.FS.readFile file
  match VaultWorld.replay s page md with
  | .error e => IO.eprintln e; return 2
  | .ok rs =>
    IO.println ("replay of " ++ page ++ " amended by " ++ file ++ " (vault " ++ world ++ "), each write as the owner's")
    let mut n := 0
    for r in rs do
      match r.divergence with
      | none => IO.println (r.page ++ ": " ++ toString r.agreed ++ " write(s) judged alike")
      | some (v, was, would) =>
        n := n + 1
        IO.println (r.page ++ ": v" ++ toString v ++ " diverges after " ++ toString r.agreed ++
          " write(s) judged alike; after it the history would differ")
        IO.println ("            in force: " ++ verdictWords was)
        IO.println ("            amended:  " ++ verdictWords would)
    IO.println (toString n ++ " of " ++ toString rs.length ++ " page(s) diverge")
    return 0

/-- `obend verify` of an impact receipt: decode the question and the list, and judge them by the
registered format. -/
def verifyImpact (j : Json) : IO UInt32 := do
  let obj := ((j.getObjVal? "object").toOption.getD Json.null).compress
  let cert := ((j.getObjVal? "certificate").toOption.getD Json.null).compress
  match format.checkBytes 0 obj cert with
  | .ok =>
    match questionOf obj, linesOf cert with
    | .ok q, .ok ls => for l in ls do IO.println (lineText q l)
    | _, _ => pure ()
    IO.println "verified (impact@1, decidable, compiled)"; return 0
  | .refused (.malformed m) _ => IO.eprintln ("refused: malformed " ++ m); return 3
  | .refused (.judge k) p => IO.eprintln (verdictText (.refused k p)); return 3
  | .uncovered => IO.eprintln "uncovered"; return 3

/-- `verify PATH`: an impact receipt here, anything else by `otherwise`. -/
def verifyOr (path : String) (otherwise : IO UInt32) : IO UInt32 := do
  let j? := Json.parse (← IO.FS.readFile path)
  match j? with
  | .ok j => if (j.getObjValAs? String "kind").toOption == some "impact" then verifyImpact j else otherwise
  | .error _ => otherwise

public def main? : List String → Option (IO UInt32)
  | "analyze" :: "impact" :: rest => some (impact rest)
  | "analyze" :: "replay" :: rest => some (replay rest)
  | _ => none

end Obend.Analysis.Cli

end
