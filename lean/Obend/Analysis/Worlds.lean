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
public import Obend.Analysis.Format
public import Obend.Vault.Cli
public import Obend.Spec.Workspace
@[expose] public section

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
    let cells := p.name :: (kindChain p.name (settled G)).filter fun k => (s.page? k).isSome
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
    let ch := ownerWrite Obend.Vault.Cli.H s.entries s.turn p md
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

end
