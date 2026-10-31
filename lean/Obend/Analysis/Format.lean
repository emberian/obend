module
/-
# Obend.Analysis.Format — the impact analysis as a registered format, on an exported table

A registered format judges bytes, so its objects are a concrete type. The impact question of any
world is exported as a TABLE (`TView`, `TFact`): cells and pins are names, and each support lists
the pins, among those the question names, at which it holds. The table is itself a `World`
(`tableWorld`: a support holds at a pin iff it lists it; a retired cell holds nothing; views do not
step), so every theorem of `Obend.Analysis.Impact` is a theorem about the exported question:
`line_blocked` at a table view holding the new pin is the dependent's blocked read naming the
support, `read_blocked_exact`'s. An exporter (`Obend.Analysis.Worlds`) computes each listed pin by
the native world's own read, at the base and at the moved pin.

`impact@1` (`format`): object the question, certificate the affected list with its openings;
decidable, compiled trust. The planted bad certificate names a dependent that does not read the
moved cell (`bad_refused`). The tooth `drop_read_misses`: an index that drops a dependent's last
read lists nothing for a cite whose bytes moved, and the checker refuses that list as `missing`.
-/
public import Obend.Analysis.Impact
public import Lean.Data.Json
@[expose] public section

namespace Obend.Analysis

open Obend.Slot Lean

set_option autoImplicit false

/-- A support in an exported table: the cell it names, its name, and the pins (among those the
question names) at which it holds. -/
structure TFact where
  cell : String
  name : String
  pins : List String
  deriving DecidableEq, Repr

/-- A view of an exported table: each cell's pin (a cell not listed is retired). -/
structure TView where
  pins : List (String × String)
  deriving DecidableEq, Repr

/-- **The table as a world.** -/
instance tableWorld : World TView TFact where
  Cell := String
  Pin := String
  cell f := f.cell
  pin v c := v.pins.lookup c
  holdsOfPin _ p f := match p with
    | some q => f.pins.contains q
    | none => false
  Step v v' := v = v'
  dead_none _ := rfl
  retired_step _ _ _ h hr := h ▸ hr
  Ver := Option String
  ver v c := v.pins.lookup c
  Past _ _ := False
  past_irrefl _ h := h
  past_trans _ _ _ h _ := h
  pinOf _ x := x
  pin_ver _ _ := rfl
  ver_step _ _ _ h := .inl (h ▸ rfl)

instance : DecidableEq (World.Cell TView) := inferInstanceAs (DecidableEq String)
instance : DecidableEq (World.Pin TView) := inferInstanceAs (DecidableEq String)

/-! ## The wire -/

def kindOf : String → Except String Kind
  | "candidate" => .ok .candidate
  | "turn" => .ok .turn
  | "cite" => .ok .cite
  | "receipt" => .ok .receipt
  | "law" => .ok .law
  | k => .error s!"unknown dependent kind {k}"

def goesName : Goes → String
  | .blocked => "blocked"
  | .restored => "restored"
  | .rejudge => "rejudge"

def goesOf : String → Except String Goes
  | "blocked" => .ok .blocked
  | "restored" => .ok .restored
  | "rejudge" => .ok .rejudge
  | g => .error s!"unknown line kind {g}"

def factJson (f : TFact) : Json :=
  Json.mkObj [("cell", toJson f.cell), ("name", toJson f.name), ("pins", toJson f.pins)]

def factOf (j : Json) : Except String TFact := do
  return ⟨← j.getObjValAs? String "cell", ← j.getObjValAs? String "name", ← j.getObjValAs? (List String) "pins"⟩

def depJson (d : Dep TFact) : Json :=
  Json.mkObj [("kind", toJson d.kind.name), ("name", toJson d.name), ("judge", toJson d.judge),
    ("reads", Json.arr (d.reads.map factJson).toArray)]

def depOf (j : Json) : Except String (Dep TFact) := do
  let reads ← (← j.getObjValAs? (Array Json) "reads").toList.mapM factOf
  return ⟨← kindOf (← j.getObjValAs? String "kind"), ← j.getObjValAs? String "name",
    ← j.getObjValAs? Bool "judge", reads⟩

def pinJson : Option String → Json
  | some p => toJson p
  | none => Json.null

def questionJson (q : Question TView) : Json :=
  Json.mkObj [("base", Json.arr (q.base.pins.map fun (c, p) => Json.arr #[toJson c, toJson p]).toArray),
    ("cell", toJson (show String from q.cell)), ("pin", pinJson q.pin),
    ("deps", Json.arr (q.deps.map depJson).toArray)]

def questionOfJson (j : Json) : Except String (Question TView) := do
  let base ← (← j.getObjValAs? (Array (Array String)) "base").toList.mapM fun a =>
    match a.toList with
    | [c, p] => .ok (c, p)
    | _ => .error "base: each entry is [cell, pin]"
  let deps ← (← j.getObjValAs? (Array Json) "deps").toList.mapM depOf
  let cell ← j.getObjValAs? String "cell"
  let pin : Option String := match j.getObjVal? "pin" with
    | .ok (.str p) => some p
    | _ => none
  return { base := ⟨base⟩, deps := deps, cell := cell, pin := pin }

def lineJson (l : Line TFact) : Json :=
  Json.mkObj [("dep", toJson l.dep), ("goes", toJson (goesName l.goes)), ("support", factJson l.support),
    ("value", toJson l.value)]

def lineOf (j : Json) : Except String (Line TFact) := do
  return ⟨← j.getObjValAs? String "dep", ← goesOf (← j.getObjValAs? String "goes"),
    ← factOf (← j.getObjVal? "support"), ← j.getObjValAs? Bool "value"⟩

def linesJson (ls : List (Line TFact)) : Json := Json.mkObj [("lines", Json.arr (ls.map lineJson).toArray)]

def linesOfJson (j : Json) : Except String (List (Line TFact)) := do
  (← j.getObjValAs? (Array Json) "lines").toList.mapM lineOf

def questionOf (s : String) : Except String (Question TView) := Json.parse s >>= questionOfJson
def linesOf (s : String) : Except String (List (Line TFact)) := Json.parse s >>= linesOfJson

/-! ## The planted bad certificate, and the tooth -/

/-- `a` reads cell `x`; the question moves `y`. -/
def badQuestion : Question TView :=
  { base := ⟨[("x", "1"), ("y", "1")]⟩, cell := "y", pin := some "2",
    deps := [⟨.candidate, "a", true, [⟨"x", "x is 1", ["1"]⟩]⟩] }

/-- A line naming `a` as blocked by a support that is not about the moved cell. -/
def badLines : List (Line TFact) := [⟨"a", .blocked, ⟨"x", "x is 1", ["1"]⟩, false⟩]

theorem bad_refused : check 0 badQuestion badLines = .refused (.doesNotRead "a") [0] := by decide +kernel

/-- A page `Beta` at version 1, a following embed of it in `Alpha` (its page present; its bytes the
same as at version 1), and Beta moved to version 2, whose bytes differ. -/
def embedQuestion : Question TView :=
  { base := ⟨[("Beta", "v1"), ("Alpha", "v1")]⟩, cell := "Beta", pin := some "v2",
    deps := [⟨.cite, "Alpha: ![[Beta]]", true,
      [⟨"Beta", "present Beta", ["v1", "v2"]⟩, ⟨"Beta", "current Beta@v1", ["v1"]⟩]⟩] }

/-- The honest prediction: the embed goes behind, resting on its `current` fact at v2. -/
theorem embed_behind :
    affected embedQuestion = [⟨"Alpha: ![[Beta]]", .blocked, ⟨"Beta", "current Beta@v1", ["v1"]⟩, false⟩] := by
  decide +kernel

/-- **The tooth**: an index that drops the dependent's last read predicts nothing for the embed,
and the checker refuses that prediction: the embed that goes behind is missing. -/
theorem drop_read_misses :
    affectedWith (fun d => d.reads.dropLast) embedQuestion = [] ∧
      ¬ Meaning embedQuestion (affectedWith (fun d => d.reads.dropLast) embedQuestion) := by
  have h : affectedWith (fun d => d.reads.dropLast) embedQuestion = [] := by decide +kernel
  refine ⟨h, fun hm => ?_⟩
  rw [h] at hm
  have := check_complete (r := 0) hm
  have e : check 0 embedQuestion [] = .refused (.missing "Alpha: ![[Beta]]") [] := by decide +kernel
  rw [e] at this; cases this

/-- **The registered format `impact@1`.** -/
def format : Judge.Format where
  name := "impact"
  version := "1"
  Obj := Question TView
  Cert := List (Line TFact)
  judge := impactJudge
  decodeObj := questionOf
  decodeCert := linesOf
  trust := .compiled
  regime := .decidable
  bad := (badQuestion, badLines)
  badGrade := 0
  bad_refused := ⟨_, _, bad_refused⟩

/-- The formats the analyses register. -/
def formats : List Judge.Format := [format]

end Obend.Analysis

end
