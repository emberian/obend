module
/-
# Obend.Ledger.Commit — what committing a row of the register does, as a function

The register's laws read from the vault's `register/_kind.md`, the register a journal's rows hold,
and the commit of admitted rows: the journal after them, with each posting's receipt and its page
(`commitRows`, all or none). `Obend.Vault.Replay` replays a ledger turn of the log with it and
`Obend.Ledger.Cli` writes what it says; neither keeps a journal of its own. (Moved out of
`Obend.Ledger.Cli` on 2026-11-05, names kept, so that the vault's log can replay a ledger turn
without the command line.)
-/
public import Obend.Ledger.Report
public import Obend.Vault.Store
public section

namespace Obend.Ledger.Cli

open Lean (Json toJson)
open Obend.Ledger Obend.Ledger.Json Obend.Vault
open Obend.Spec.Law (LawExpr)

def registerKind : String := "register/_kind"

/-- A page the ledger writes and a merge leaves to the stitch: a posting page. -/
def ledgerOwned (name : String) : Bool := name.startsWith "register/" && name != registerKind

/-- The register a journal holds: its rows accumulated (each was judged when it was committed). -/
def stateOf (rows : List Row) : Nat × Reg :=
  rows.foldl (fun (a : Nat × Reg) r => match r with
    | .post p => (a.1, ⟨a.2.postings ++ [p]⟩)
    | .close n => (max a.1 n, a.2)) (0, ⟨[]⟩)

/-- The settled text of a page. -/
def srcOf (s : Store) (name : String) : Option String := (s.page? name).bind fun p => p.current.map settled

/-- The register's laws: the law lines of `register/_kind.md`. -/
def registerLaws (s : Store) : Except String (List (String × LawExpr × String)) :=
  match (s.page? registerKind).bind (·.current) with
  | some G => lawsIn registerKind G
  | none => .error "this vault has no ledger: write register/_kind.md, the register kind, with its laws"

def lawsText (laws : List (String × LawExpr × String)) : Json :=
  Json.arr (laws.map fun (n, _, t) => Json.arr #[toJson n, toJson t]).toArray

def lawDigest (laws : List (String × LawExpr × String)) : String :=
  Obend.Receipt.Negotiation.digestJson (lawsText laws)

def lawOf (laws : List (String × LawExpr × String)) : Law := kindLaw (laws.map fun (n, e, _) => (n, e))

def numberOf (g : Reg) (o : String) : String := ((g.find o).map (·.id)).getD o

def linesText (p : Posting) : String :=
  String.join (p.lines.map fun m =>
    if m.debit != 0 || m.credit == 0 then "- debit [[" ++ m.account ++ "]] " ++ toString m.debit ++ "\n"
    else "- credit [[" ++ m.account ++ "]] " ++ toString m.credit ++ "\n")

/-- The page of a posting: its fields (what the register's laws read: its own, and the totals after it
of the accounts it moves), the document it embeds, its lines. `g` is the register before it. -/
def postingPage (g : Reg) (p : Posting) : String :=
  let moved := (p.lines.map (·.account)).eraseDups
  let after := (accountMeasures g p).filter fun (k, _) => moved.any fun a =>
    k == shortName a ++ "_debits" || k == shortName a ++ "_credits"
  "---\nperiod: " ++ toString p.period ++ "\ndebits: " ++ toString p.debits ++ "\ncredits: " ++ toString p.credits ++
  "\nmovements: " ++ toString p.lines.length ++ String.join (after.map fun (k, v) => "\n" ++ k ++ ": " ++ toString v) ++
  "\n---\n# " ++ p.id ++ "\n\n" ++
  (match p.reverses with
    | some o => "Reverses [[register/" ++ numberOf g o ++ "]], of " ++ p.doc ++ ", in period " ++ toString p.period ++ ".\n\n"
    | none => "Posts " ++ p.doc ++ " in period " ++ toString p.period ++ ":\n\n![[" ++ p.doc ++ "]]\n\n") ++
  linesText p

/-- The receipt of a posting row, as JSON: the receipt (`postingReceipt`) and what a stranger needs
to re-judge it: the register before, the row, the closed-through period, the kind's law lines. -/
def receiptJson (laws : List (String × LawExpr × String)) (a : Nat × Reg) (r : Row) (prev : String) : Json :=
  let R := postingReceipt (lawOf laws) (lawDigest laws) a r prev
  Json.mkObj [("kind", toJson "posting"), ("format", toJson "posting@1"), ("pre", toJson R.pre), ("post", toJson R.post),
    ("row", toJson R.row), ("law", toJson R.law), ("laws", lawsText laws), ("closed", toJson a.1),
    ("before", postingsJson a.2.postings), ("posting", rowJson r),
    ("openings", Json.arr (R.openings.map fun (f, b) => match f with
      | .isOpen n => Json.arr #[toJson n, toJson b]).toArray),
    ("verdict", toJson (if R.verdict.isOk then "ok" else "refused")), ("prev", toJson R.prev),
    ("trust", toJson "register law: checked (obend-law@1, compiled)")]

/-- What committing an admitted posting leaves beside the journal: its number, its receipt (the
text of `.obend/receipts/NUMBER.json`) and its page (`register/NUMBER.md`). -/
structure RowFiles where
  id : String
  receipt : String
  page : String
deriving Repr

/-- Commit an admitted row: the journal after it (the row, numbered; the receipt's digest as the
journal's head) and the files it leaves. `a` is the register before it, `b` after. -/
def commitPure (laws : List (String × LawExpr × String)) (J : Journal) (a b : Nat × Reg) (r : Row) :
    Journal × List RowFiles :=
  match r, b.2.postings.getLast? with
  | .post p0, some p =>
    let rj := receiptJson laws a r J.head
    ({ J with rows := J.rows ++ [.post p], head := Obend.Receipt.Negotiation.digestJson rj, last := p0.origin },
      [⟨p.id, rj.pretty ++ "\n", postingPage a.2 p⟩])
  | .close n, _ => ({ J with rows := J.rows ++ [.close n] }, [])
  | _, _ => (J, [])

/-- **Commit rows** in order, each judged by the register (`Obend.Ledger.Register.step`) at the
register the rows before it left: the journal after all of them and their files, or, when any is
refused, nothing. -/
def commitRows (laws : List (String × LawExpr × String)) (J : Journal) : List Row → Except String (Journal × List RowFiles)
  | [] => .ok (J, [])
  | r :: rs =>
    let a := stateOf J.rows
    match step (lawOf laws) a r with
    | .error _ => .error "refused: the register refuses the row"
    | .ok b =>
      let (J', fs) := commitPure laws J a b r
      match commitRows laws J' rs with
      | .ok (J'', fs') => .ok (J'', fs ++ fs')
      | .error e => .error e

end Obend.Ledger.Cli

end
