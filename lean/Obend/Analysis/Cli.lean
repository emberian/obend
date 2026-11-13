module
/-
# Obend.Analysis.Worlds — two native worlds exported as impact questions

Each exporter reads a native world, names its cells and pins, and lists, for every support a
dependent reads, the pins at which it holds among the base pin of its cell and (for the moved cell)
the new pin, each computed by the native world's own read. The table world then reads every support
as the native world would at the base view and at the moved view (`Obend.Analysis.Format`).

**A vault** (`Obend.Vault`): a cell is a page, its pin the page's history (labelled `vN`, its
length: two histories of one page compared here are prefixes of one another or the current one
extended by a write, so the length names each); retired is no version. A support is a
`Obend.Doc.Fact`, whose cell is the page it reads (`cellOf`: `live`, `head`, `present` of their
page; `verifies` and `current` of the cited page). Dependents: every cite of every page's current
version (a candidate of the cite intention's slot, `Obend.Doc.cites`: `behind` is its blocked read,
`cite_stale_iff_blocked`), and every page's law row, which reads the page and its kinds' pages
(`Obend.Vault.lawsFor`): re-judged when one of them moves. A move is a version of the page's own
history (`PAGE@N`), its retirement, or the owner's write of a file (`ownerWrite`, the write `obend
open` would make; a refused write leaves the pin where it is).

**A workspace** (`Obend.Spec.Workspace`): a cell is a record line `NAME^MAJOR`, its pin what the line
names (`PIN names VERSION`, or `PIN retired`; no line, no pin). A support is a `Named` fact, which
holds exactly at the pin it names (`Ecosystem.holds`). Dependents of a turn: the turn (`stale`:
`Ecosystem.admit`'s refusal names the moved pin), each intention pin of it as a candidate of its
intention's slot (`intentionSlot`), and the effective law of the closure, which reads every pin.
-/
/-
# Obend.Analysis.Replay — the fold replayed under an amended law

`review/WORLD-ANALYSIS-20261101.md` §2.2 (T3). Two admissions over the same rows from the same root
agree until the first row their steps judge differently (`replay_divergence`): before it the two
folds are equal, at it they differ, and after it the counterfactual history is another history (the
refused write never happened), so a replay reports the first divergence and does not continue as if
it had. When the amended law only refuses more (`Narrows`), the divergence is a write it refuses
(`amend_refuses`).

On a vault (`vaultReplay`): every write of every page the amended page's laws judge (the page
itself, and the pages it is a kind of) is re-judged by `Obend.Vault.commit`, once with the laws in
force and once with the amended page in their place, replayed as the owner at the write's version;
the first write the two judge differently is reported with the amended verdict.
-/
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
public import Obend.Analysis.Impact
public import Obend.Vault.Cli
public import Obend.Spec.Workspace
public section


namespace Obend.Analysis

open Lean

/-- Export one support: its cell, its name, and the pins at which it holds. -/
def tfact (cell name : String) (base moved : Option String) (atBase atMoved isMoved : Bool) : TFact :=
  ⟨cell, name, (if atBase then base.toList else []) ++ (if isMoved && atMoved then moved.toList else [])⟩

namespace VaultWorld

open Obend.Doc Obend.Vault

/-- A page's name in the store. -/
def pageName (s : Store) (q : PageId) : String :=
  ((s.pages.find? (·.id == q)).map (·.name)).getD ("#" ++ toString q)

/-- A history's pin label: `vN`, its length; retired (no version) is no pin. -/
def label (h : List Graph) : Option String := if h.isEmpty then none else some ("v" ++ toString h.length)

/-- The page a support reads. -/
def cellOf : Obend.Doc.Fact → PageId
  | .live p _ => p
  | .head p _ _ => p
  | .present p => p
  | .verifies c => c.page
  | .current c => c.page

def spanText : Span → String
  | .identity => ""
  | .page => " (page)"
  | .block b => " (block ^" ++ b ++ ")"
  | .bytes r => " (bytes " ++ toString r.start ++ "+" ++ toString r.len ++ ")"

/-- A support, named for a person. -/
def factName (s : Store) : Obend.Doc.Fact → String
  | .live p a => "live " ++ pageName s p ++ "#" ++ toString a
  | .head p x a => "head " ++ pageName s p ++ "#" ++ toString x ++ " is " ++ toString a
  | .present p => "present " ++ pageName s p
  | .verifies c => "verifies " ++ pageName s c.page ++ spanText c.span ++ " at v" ++ toString (c.version + 1)
  | .current c => "current " ++ pageName s c.page ++ spanText c.span ++ " as at v" ++ toString (c.version + 1)

/-- A move of one page: its id, name, and the history it would have. -/
structure Move where
  id : PageId
  name : String
  history : List Graph
  /-- why a write left the pin where it was -/
  note : Option String := none

/-- The world with the page moved. -/
def Move.world (m : Move) (s : Store) : Obend.Doc.World := fun q => if q == m.id then m.history else s.world q

/-- Export a support at the base and at the moved world. -/
def factT (s : Store) (m : Move) (f : Obend.Doc.Fact) : TFact :=
  let q := cellOf f
  tfact (pageName s q) (factName s f) (label (s.world q)) (label m.history)
    (Obend.Doc.holds Obend.Vault.Cli.H s.world f) (Obend.Doc.holds Obend.Vault.Cli.H (m.world s) f) (q == m.id)

/-- Every cite of every page's current version. -/
def citeDeps (s : Store) (m : Move) : List (Dep TFact) :=
  s.pages.flatMap fun p => match p.current with
    | none => []
    | some G => (pieces G p.name p.who).filterMap fun pc => match pc with
      | .atom a txt => match G.label a with
        | some (.cite _ c) => some ⟨.cite, p.name ++ ": " ++ txt, true, (citeFacts c).map (factT s m)⟩
        | _ => none
      | _ => none

/-- The support a law row reads of a page: the page at its base version. -/
def versionFact (s : Store) (name : String) : TFact :=
  let base := ((s.page? name).bind fun p => label p.history)
  ⟨name, "version of " ++ name ++ " (" ++ base.getD "none" ++ ")", base.toList⟩

/-- Every page's law row: it reads the page and the pages of its kinds. -/
def lawDeps (s : Store) : List (Dep TFact) :=
  s.pages.filterMap fun p => p.current.map fun G =>
    let cells := p.name :: (kindChain s.entries p.name (settled G)).filter fun k => (s.page? k).isSome
    ⟨.law, "law of " ++ p.name, true, cells.map (versionFact s)⟩

/-- The base pins. -/
def base (s : Store) : TView :=
  ⟨s.pages.filterMap fun p => (label p.history).map (p.name, ·)⟩

/-- **The vault's impact question.** -/
def question (s : Store) (m : Move) : Question TView :=
  { base := base s, deps := citeDeps s m ++ lawDeps s, cell := m.name, pin := label m.history }

/-- Parse `SPEC` of `PAGE@SPEC` against the store: a version `N` (or `vN`), `retired`, or a file the
owner would write. -/
def move (s : Store) (page spec : String) : IO (Except String Move) := do
  let some p := s.page? page | return .error ("no page named " ++ page)
  let n? := (if spec.startsWith "v" then (spec.drop 1).toString else spec).toNat?
  if spec == "retired" then return .ok ⟨p.id, p.name, [], none⟩
  match n? with
  | some n =>
    if n == 0 || n > p.history.length then
      return .error (page ++ " has versions v1 to v" ++ toString p.history.length)
    return .ok ⟨p.id, p.name, p.history.take n, none⟩
  | none =>
    if !(← System.FilePath.pathExists spec) then
      return .error ("PIN is a version (N or vN), `retired`, `?`, or a file to write: " ++ spec)
    let md ← IO.FS.readFile spec
    let ch := ownerWrite Obend.Vault.Cli.H s.entries s.turn p md (env := s.environment)
    return .ok ⟨p.id, p.name, ch.history, ch.note⟩

end VaultWorld

namespace WorkspaceWorld

open Obend.Spec.Ecosystem

def cellName (n : String) (m : Nat) : String := n ++ "^" ++ toString m

/-- A record line's pin label. -/
def lineLabel (l : RecordLine) : String :=
  match l.fill with
  | some v => toString l.pin ++ " names " ++ v
  | none => toString l.pin ++ " retired"

/-- A `Named` support: it holds exactly where its line names its version at its pin. -/
def factT (f : Named) : TFact :=
  ⟨cellName f.name f.major, f.name ++ "^" ++ toString f.major ++ " names " ++ f.version ++ " at pin " ++ toString f.pin,
    [toString f.pin ++ " names " ++ f.version]⟩

/-- The base pins of a view. -/
def base (v : View) : TView := ⟨v.lines.map fun l => (cellName l.name l.major, lineLabel l)⟩

/-- **The dependents of a turn**: the turn, its intention pins, the closure's law. -/
def deps (t : Turn) : List (Dep TFact) :=
  let all := t.pins.flatMap fun p => p.supports.map factT
  [⟨.turn, "turn " ++ t.entry.name ++ "@" ++ t.entry.version, true, all⟩] ++
    t.pins.filterMap (fun p => match p with
      | .intention n m _ v _ => some ⟨.candidate, n ++ "@^" ++ toString m ++ " = " ++ v, true, p.supports.map factT⟩
      | .extension _ _ => none) ++
    [⟨.law, "law of " ++ t.entry.name ++ " (every package of its closure)", true, all⟩]

/-- **The workspace's impact question.** -/
def question (v : View) (t : Turn) (cell : String) (moved : Option RecordLine) : Question TView :=
  { base := base v, deps := deps t, cell := cell, pin := moved.map lineLabel }

end WorkspaceWorld

end Obend.Analysis


namespace Obend.Analysis

open Obend.Fold

set_option autoImplicit false

section
variable {W Rest Row Fact Clause : Type}

/-- **T3, the first divergence**: two admissions run over the same rows from the same root give the
same fold, or there is a first row their steps judge differently, at an accumulator both reached. -/
theorem replay_divergence (A A' : Admission W Rest Row Fact Clause) :
    ∀ (rows : List Row) (a : W × Rest), A.run a rows = A'.run a rows ∨
      ∃ pre r post b, rows = pre ++ r :: post ∧ A.run a pre = .ok b ∧ A'.run a pre = .ok b ∧
        A.step b r ≠ A'.step b r
  | [], _ => .inl rfl
  | r :: rs, a => by
    by_cases hs : A.step a r = A'.step a r
    · cases hst : A.step a r with
      | error e =>
        refine .inl ?_
        simp only [Admission.run, List.foldlM_cons, ← hs, hst]; rfl
      | ok b =>
        rcases replay_divergence A A' rs b with h | ⟨pre, r', post, b', he, h1, h2, hd⟩
        · refine .inl ?_
          simp only [Admission.run, List.foldlM_cons, ← hs, hst] at h ⊢
          exact h
        · refine .inr ⟨r :: pre, r', post, b', by rw [he]; rfl, ?_, ?_, hd⟩
          · simp only [Admission.run, List.foldlM_cons, hst] at h1 ⊢; exact h1
          · simp only [Admission.run, List.foldlM_cons, ← hs, hst] at h2 ⊢; exact h2
    · exact .inr ⟨[], r, rs, a, rfl, rfl, rfl, hs⟩

/-- The amended admission only refuses more. -/
def Narrows (A A' : Admission W Rest Row Fact Clause) : Prop :=
  ∀ b r x, A'.step b r = .ok x → A.step b r = .ok x

/-- **An amendment that narrows diverges by a refusal.** -/
theorem amend_refuses (A A' : Admission W Rest Row Fact Clause) (hn : Narrows A A') {b : W × Rest} {r : Row}
    (hd : A.step b r ≠ A'.step b r) : ∃ k, A'.step b r = .error k := by
  cases h : A'.step b r with
  | error k => exact ⟨k, rfl⟩
  | ok x => exact absurd (by rw [hn b r x h, h]) hd

end

namespace VaultWorld

open Obend.Doc Obend.Vault

/-- How one write is judged on replay. -/
def judgeWrite (es : List Entry) (p : Page) (i : Nat) (env : Environment := #[]) : Option (Except String Unit) :=
  p.history[i]?.map fun G =>
    (commit es { p with history := p.history.take i } G [] .owner i (env := env)).map fun _ => ()

def sameVerdict : Except String Unit → Except String Unit → Bool
  | .ok _, .ok _ => true
  | .error a, .error b => a == b
  | _, _ => false

/-- A page's replay: the writes judged alike, then the first the two laws judge differently (its
version, the verdict in force, the amended one). -/
structure PageReplay where
  page : String
  agreed : Nat
  divergence : Option (Nat × Except String Unit × Except String Unit)

/-- Replay one page's writes under the laws in force (`es`) and the amended ones (`es'`). -/
def replayPage (es es' : List Entry) (p : Page) (env : Environment := #[]) : PageReplay :=
  let rec go (i : Nat) (fuel : Nat) : PageReplay :=
    match fuel with
    | 0 => ⟨p.name, i, none⟩
    | fuel + 1 =>
      match judgeWrite es p i env, judgeWrite es' p i env with
      | some v, some v' => if sameVerdict v v' then go (i + 1) fuel else ⟨p.name, i, some (i + 1, v, v')⟩
      | _, _ => ⟨p.name, i, none⟩
  go 0 (p.history.length + 1)

/-- The pages a page's laws judge: itself, and every page it is a kind of. -/
def judgedBy (s : Store) (k : String) : List Page :=
  s.pages.filter fun p => p.name == k || match p.current with
    | some G => (kindChain s.entries p.name (settled G)).contains k
    | none => false

/-- **Replay a vault under an amended page**: the page's new version (the owner's write of `md`,
judged as any write), then every write of every page its laws judge, under both. -/
def replay (s : Store) (k : String) (md : String) : Except String (List PageReplay) := do
  let some p := s.page? k | throw ("no page named " ++ k)
  let ch := ownerWrite Obend.Vault.Cli.H s.entries s.turn p md (env := s.environment)
  if let some n := ch.note then throw ("the amendment itself is refused: " ++ n)
  let some G' := ch.history.getLast? | throw (k ++ " has no version")
  let es := s.entries
  let es' := es.map fun e => if e.name == k then { e with graph := G' } else e
  return (judgedBy s k).map fun p => replayPage es es' p s.environment

end VaultWorld

end Obend.Analysis


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
