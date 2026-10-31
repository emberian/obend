module
/-
# Obend.Ledger.Json — the register on the wire: postings, rows, the journal, the root

A vault's register is kept in `.obend/ledger.json`: the rows the register accepted, in order (its
JOURNAL), and the digest of the last posting receipt (the head of the receipt chain). The register's
state is the journal replayed (`Obend.Ledger.Register.runFrom` from closed-through 0 and no
postings).

- `postingsRoot`: the root of a register, the digest (cSHAKE256, `Obend.Receipt.Negotiation.digest`)
  of its postings' canonical JSON. A posting receipt's pre and post roots and a trial balance's book
  root are this.
- `originOf`: a new posting's origin, the digest of the origin before it in the journal where it is
  made and the posting's content (document, period, reversed origin, lines). Two replicas that post
  the same content on the same history make the same row, and a stitch takes it once.
-/
public import Obend.Ledger.Register
public import Obend.Receipt.Negotiation
public import Lean.Data.Json
public section

namespace Obend.Ledger.Json

open Lean (Json toJson)
open Obend.Ledger

def movementJson (m : Movement) : Json :=
  Json.mkObj [("account", toJson m.account), ("debit", toJson m.debit), ("credit", toJson m.credit)]

def movementOf (j : Json) : Except String Movement := do
  return ⟨← j.getObjValAs? String "account", ← j.getObjValAs? Nat "debit", ← j.getObjValAs? Nat "credit"⟩

def optJson : Option String → Json
  | some s => toJson s
  | none => Json.null

def postingJson (p : Posting) : Json :=
  Json.mkObj [("id", toJson p.id), ("doc", toJson p.doc), ("period", toJson p.period),
    ("reverses", optJson p.reverses), ("lines", Json.arr (p.lines.map movementJson).toArray),
    ("origin", toJson p.origin)]

def postingOf (j : Json) : Except String Posting := do
  let rev : Option String := match j.getObjVal? "reverses" with
    | .ok (.str s) => some s
    | _ => none
  let lines ← (← j.getObjValAs? (Array Json) "lines").toList.mapM movementOf
  return ⟨← j.getObjValAs? String "id", ← j.getObjValAs? String "doc", ← j.getObjValAs? Nat "period", rev,
    lines, ← j.getObjValAs? String "origin"⟩

def rowJson : Row → Json
  | .post p => Json.mkObj [("post", postingJson p)]
  | .close n => Json.mkObj [("close", toJson n)]

def rowOf (j : Json) : Except String Row := do
  match j.getObjVal? "post" with
  | .ok pj => return .post (← postingOf pj)
  | .error _ => return .close (← j.getObjValAs? Nat "close")

def postingsJson (ps : List Posting) : Json := Json.arr (ps.map postingJson).toArray

def postingsOf (j : Json) : Except String (List Posting) := do
  (← j.getArr?).toList.mapM postingOf

/-- **The root of a register**: the digest of its postings. -/
def postingsRoot (ps : List Posting) : String := Obend.Receipt.Negotiation.digestJson (postingsJson ps)

/-- What a posting's origin is a digest of: what it posts, not where the register put it. -/
def contentJson (p : Posting) : Json :=
  Json.mkObj [("doc", toJson p.doc), ("period", toJson p.period), ("reverses", optJson p.reverses),
    ("lines", Json.arr (p.lines.map movementJson).toArray)]

/-- **A new posting's origin**: the origin before it, and its content. -/
def originOf (prev : String) (p : Posting) : String :=
  Obend.Receipt.Negotiation.digest (prev ++ "|" ++ (contentJson p).compress)

/-- The journal kept beside a vault. -/
structure Journal where
  rows : List Row
  /-- the digest of the last posting receipt -/
  head : String
  /-- the last origin this replica made or took -/
  last : String

def genesis : String := String.ofList (List.replicate 64 '0')

def Journal.empty : Journal := ⟨[], genesis, genesis⟩

def journalJson (J : Journal) : Json :=
  Json.mkObj [("rows", Json.arr (J.rows.map rowJson).toArray), ("head", toJson J.head), ("last", toJson J.last)]

def journalOf (j : Json) : Except String Journal := do
  let rows ← (← j.getObjValAs? (Array Json) "rows").toList.mapM rowOf
  return ⟨rows, ← j.getObjValAs? String "head", ← j.getObjValAs? String "last"⟩

end Obend.Ledger.Json

end
