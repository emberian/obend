module
/-
# Obend.Ledger.Cli — a vault with a ledger kind: `obend ledger`, `obend report`, the stitch in `obend merge`

A vault holds a ledger when it has a register kind, `register/_kind.md`: its `law` lines are the
register's laws (`balanced: new.debits == new.credits`, …), judged on every posting
(`Obend.Ledger.Vault.kindLaw`). Accounts are pages (the catalog); a document is a page whose kind's
`_kind.md` carries a POSTING TEMPLATE, lines

    - debit [[accounts/Receivables]] amount
    - credit [[accounts/Revenue]] amount

each an account page and the document field whose value it moves. The register itself is the
journal (`Obend.Ledger.Json`), part of the vault's world: rows are committed as turns of the vault's
log (`Obend.Vault.Replay`, `rows`; it was `.obend/ledger.json`), and each posting a turn admits is
written as a page `register/P-NNNN.md` that embeds the document it posted (so an edit of the document
after posting leaves the posting behind, by name), and its receipt as `.obend/receipts/P-NNNN.json`.

    obend ledger post DOC [--period N]
        the document's posting, by its kind's template, into its `period` field's period (or N),
        judged by the register (`Obend.Ledger.Register.step`): admitted with its receipt, or refused
        by name (the kind's law and clause, a closed period, a document posted already).
    obend ledger reverse P-NNNN [--period N]
        a correction: the posting's reversal (its lines with debit and credit swapped), into its
        period or N. After it the document may be posted again.
    obend ledger close N
        close every period through N: no posting into them after (a version law: closing never goes back).
    obend ledger status | obend ledger root
        the register (postings, what reversed what, the closed-through period, account balances) /
        its root (the digest a trial balance's book must have).
    obend report trial-balance P [--out FILE]
        the trial balance of period P (`Obend.Ledger.Report.tb`), checked by the registered
        `trial-balance@1` judge before it is printed, written as the page `reports/TB-P.md` (which
        links every posting it took) and, with `--out`, as a receipt an auditor re-checks with
        `obend verify FILE [--root ROOT]`.
    obend merge OTHER_DIR [--drop P-NNNN …]
        the vault merge of the documents (`Obend.Vault.Merge.mergeVault`), and the REGISTER's stitch: the
        other replica's rows this register does not have (by origin) are replayed in order through
        this register's step (`Obend.Run.Fork.stitch`), atomically: if any is refused, nothing of
        the other register is taken and every refusal is printed; otherwise each is renumbered here
        and committed with its receipt. `--drop P-NNNN` (the other's number) leaves a row out, by
        the owner's choice, said so.
    obend verify RECEIPT.json [--root ROOT]
        a posting receipt (`posting@1`: the row re-judged at the register before it, under the kind's
        law it carries) or a trial balance (`trial-balance@1`); with ROOT, the book's root must be it.
-/
public import Obend.Ledger.Commit
public import Obend.Vault.Cli
public section

namespace Obend.Ledger.Cli

open Lean (Json toJson)
open Obend.Ledger Obend.Ledger.Json Obend.Vault Obend.Vault.Cli
open Obend.Spec.Law (LawExpr)
open Obend.Analysis.Coverage (Said)

/-! ## Reading the vault -/


/-- The register's journal: part of the vault's world, replayed from its log (it was
`.obend/ledger.json`; a vault that has one adopts it into the log at its next command). -/
def loadJournal (dir : System.FilePath) : IO Journal := return (← readWorld dir).journal

/-- The text after a prefix. -/
def after (pre s : String) : Option String :=
  if s.startsWith pre then some (String.ofList (s.toList.drop pre.length)) else none

/-- A template line `- debit [[ACCOUNT]] FIELD`. -/
def templateLine (l : String) : Option (Bool × String × String) := do
  let l := trim l
  let (isDebit, rest) ← match after "- debit " l, after "- credit " l with
    | some r, _ => some (true, r)
    | _, some r => some (false, r)
    | _, _ => none
  let rest ← after "[[" (trim rest)
  let acct := String.ofList (rest.toList.takeWhile (· != ']'))
  let tail ← after "]]" (String.ofList (rest.toList.dropWhile (· != ']')))
  let field := trim tail
  if acct.isEmpty || field.isEmpty || field.contains ' ' then none else some (isDebit, acct, field)

/-- A kind page's posting template. -/
def templateOf (src : String) : Template :=
  let ls := ((splitFront src).2.splitOn "\n").filterMap templateLine
  ⟨ls.filterMap fun (d, a, f) => if d then some (a, f) else none,
   ls.filterMap fun (d, a, f) => if d then none else some (a, f)⟩

/-- The document's kind that carries a template, and the template. -/
def templateFor (s : Store) (doc src : String) : Option (String × Template) :=
  (kindChain s.entries doc src).findSome? fun k =>
    (srcOf s k).bind fun ks =>
      let t := templateOf ks
      if t.debits.isEmpty && t.credits.isEmpty then none else some (k, t)

/-! ## Saying a refusal -/

def clauseText (laws : List (String × LawExpr × String)) (g : Reg) (w : Nat) (page : String) (p : Posting) :
    Clause → String
  | .closedPeriod n => "refused (closed-period): period " ++ toString n ++ " is closed (the register is closed through " ++
      toString w ++ "); post it into an open period: --period " ++ toString (w + 1)
  | .again _ => "refused (again): the register has this posting already"
  | .law n r =>
    let vals := postingMeasures p ++ accountMeasures g p
    let lin := laws.map fun (n, e, _) => (n, e)
    let keys := postingKeys lin vals
    let st := stateOf' keys vals
    refusalText page laws n r postFacts none st []
  | .postedTwice d first => "refused (posted-once): " ++ d ++ " is posted already, as " ++ first ++
      "; correct it with a reversing posting first: obend ledger reverse " ++ first
  | .notLive o => "refused (not-live): " ++ numberOf g o ++ " is not a live posting (it is a reversal, or reversed already)"
  | .notInverse o => "refused (not-inverse): the lines are not those of " ++ numberOf g o ++ " with debit and credit swapped"
where stateOf' (keys : List String) (vals : List (String × Nat)) := Obend.Vault.stateOf keys vals

/-! ## Writing a posting -/

def movementsText (p : Posting) : String :=
  ", ".intercalate (p.lines.map fun m =>
    if m.debit != 0 || m.credit == 0 then "debit " ++ m.account ++ " " ++ toString m.debit
    else "credit " ++ m.account ++ " " ++ toString m.credit)

def receiptsDir (dir : System.FilePath) : System.FilePath := dir / ".obend" / "receipts"

/-- Write what committing rows leaves: each posting's receipt and its page. -/
def writeRowFiles (dir : System.FilePath) (fs : List RowFiles) : IO Unit :=
  for rf in fs do
    IO.FS.createDirAll (receiptsDir dir)
    Obend.Vault.Cost.writeFile (receiptsDir dir / (rf.id ++ ".json")) rf.receipt
    IO.FS.createDirAll (dir / "register")
    Obend.Vault.Cost.writeFile (dir / "register" / (rf.id ++ ".md")) rf.page

/-- **Commit rows** as one turn of the vault's log (`Obend.Vault.Replay.Turn.rows`, all or none) and
write their files. -/
def commitRowsTurn (dir : System.FilePath) (rows : List Row) : IO (Except String Unit) :=
  commitWith dir (.rows rows) fun _ o => do
    if let .rows fs := o then writeRowFiles dir fs

def fail (msg : String) : IO UInt32 := do IO.eprintln msg; return 3

def usage : String := "obend ledger post DOC [--period N] | reverse P-NNNN [--period N] | close N | status | root"

/-- The vault opened, its register's laws and journal and state. -/
def openLedger (dir : System.FilePath) : IO (Except String (Store × List (String × LawExpr × String) × Journal × (Nat × Reg))) := do
  let (w, _) ← openWorld dir false
  match registerLaws w.store with
  | .error e => return .error e
  | .ok laws => return .ok (w.store, laws, w.journal, stateOf w.journal.rows)

/-- Judge a posting and, if admitted, commit it. -/
def postRow (dir : System.FilePath) (s : Store) (laws : List (String × LawExpr × String)) (J : Journal)
    (a : Nat × Reg) (p : Posting) (what : String) : IO UInt32 := do
  let p := { p with origin := originOf J.last p }
  let page := "register/" ++ a.2.number
  match step (lawOf laws) a (.post p) with
  | .error c => fail (what ++ ": " ++ clauseText laws a.2 a.1 page (p.numbered a.2.number) c)
  | .ok b =>
    if let .error e ← commitRowsTurn dir [.post p] then return ← fail (what ++ ": " ++ e)
    let _ ← openDir dir false
    let _ := J
    let q := (b.2.postings.getLast?).getD p
    IO.println (what ++ ": posted as " ++ q.id ++ " (period " ++ toString q.period ++ "): " ++ movementsText q)
    IO.println ("receipt .obend/receipts/" ++ q.id ++ ".json")
    let _ := s
    return 0

def periodFlag (args : List String) : Option Nat × List String :=
  let (v, rest) := flag "--period" args
  (v.bind String.toNat?, rest)

def postDoc (dir : System.FilePath) (doc : String) (period : Option Nat) : IO UInt32 := do
  match ← openLedger dir with
  | .error e => fail e
  | .ok (s, laws, J, a) =>
    let some src := srcOf s doc | fail ("no page " ++ doc)
    let some (k, t) := templateFor s doc src
      | fail ("refused (no-template): no kind of " ++ doc ++ " has a posting template (lines `- debit [[ACCOUNT]] FIELD` in its _kind.md)")
    let fields := scalarFields src
    let accts := t.debits.map (·.1) ++ t.credits.map (·.1)
    if let some x := accts.find? (fun x => (s.page? x).all (·.history.isEmpty)) then
      return ← fail ("refused (catalog): the template of " ++ k ++ " names [[" ++ x ++ "]], which is not a page of this vault")
    let needed := t.debits.map (·.2) ++ t.credits.map (·.2)
    if let some f := needed.find? (fun f => fields.lookup f |>.isNone) then
      return ← fail ("refused (document): " ++ doc ++ " has no field `" ++ f ++ "`, which the template of " ++ k ++ " moves")
    let some per := period <|> fields.lookup "period" | fail ("refused (document): " ++ doc ++ " names no period; give one with --period N")
    let p : Posting := ⟨"", doc, per, none, t.lines fun f => (fields.lookup f).getD 0, ""⟩
    postRow dir s laws J a p doc

def reverse (dir : System.FilePath) (id : String) (period : Option Nat) : IO UInt32 := do
  match ← openLedger dir with
  | .error e => fail e
  | .ok (s, laws, J, a) =>
    let some q := a.2.postings.find? (·.id == id) | fail ("no posting " ++ id ++ " in the register")
    let p : Posting := ⟨"", q.doc, period.getD q.period, some q.origin, inverse q.lines, ""⟩
    postRow dir s laws J a p ("reversal of " ++ id)

def close (dir : System.FilePath) (n : Nat) : IO UInt32 := do
  match ← openLedger dir with
  | .error e => fail e
  | .ok (_, laws, J, a) =>
    if n ≤ a.1 then
      IO.println ("the register is closed through period " ++ toString a.1 ++ " already; closing never goes back")
      return 0
    match step (lawOf laws) a (.close n) with
    | .error _ => fail "refused"
    | .ok _ =>
      if let .error e ← commitRowsTurn dir [.close n] then return ← fail e
      let _ := J
      IO.println ("closed through period " ++ toString n ++ ": no posting into period " ++ toString n ++ " or before")
      return 0

def pad (s : String) (n : Nat) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')
def lpad (s : String) (n : Nat) : String := String.ofList (List.replicate (n - s.length) ' ') ++ s

def sortTotals (t : Totals) : Totals := t.mergeSort fun x y => decide (x.1 ≤ y.1)

def totalsLines (t : Totals) : List String :=
  let t := sortTotals t
  [pad "  account" 26 ++ lpad "debit" 8 ++ lpad "credit" 8] ++
    t.map (fun (a, d, c) => pad ("  " ++ a) 26 ++ lpad (toString d) 8 ++ lpad (toString c) 8) ++
    [pad "  total" 26 ++ lpad (toString (t.map (·.2.1)).sum) 8 ++ lpad (toString (t.map (·.2.2)).sum) 8]

def status (dir : System.FilePath) : IO UInt32 := do
  match ← openLedger dir with
  | .error e => fail e
  | .ok (_, _, _, (w, g)) =>
    IO.println ("register: " ++ toString g.postings.length ++ " posting(s), closed through period " ++ toString w)
    if !g.postings.isEmpty then
      IO.println ("  " ++ pad "number" 8 ++ pad "document" 22 ++ pad "period" 11 ++ lpad "amount" 6)
    for p in g.postings do
      let note := match p.reverses with
        | some o => "reverses " ++ numberOf g o
        | none => if g.reversed p.origin then
            "reversed by " ++ (((g.postings.find? (·.reverses == some p.origin)).map (·.id)).getD "?") else "live"
      IO.println ("  " ++ pad p.id 8 ++ pad p.doc 22 ++ "period " ++ pad (toString p.period) 4 ++ lpad (toString p.debits) 6 ++ "  " ++ note)
    IO.println "balances (every period):"
    for l in totalsLines (g.postings.foldl addPosting []) do IO.println l
    return 0

/-! ## The trial balance -/

def tbPage (P : Nat) (s : Said String Totals) : String :=
  let t := sortTotals s.total
  "---\nperiod: " ++ toString P ++ "\n---\n# Trial balance, period " ++ toString P ++ "\n\n| account | debit | credit |\n|---|---|---|\n" ++
  String.join (t.map fun (a, d, c) => "| " ++ a ++ " | " ++ toString d ++ " | " ++ toString c ++ " |\n") ++
  "| total | " ++ toString (t.map (·.2.1)).sum ++ " | " ++ toString (t.map (·.2.2)).sum ++ " |\n\nPostings: " ++
  ", ".intercalate (s.keys.map fun k => "[[register/" ++ k ++ "]]") ++ "\n"

def tbJson (o : TBObj) (s : Said String Totals) : Json :=
  Json.mkObj [("kind", toJson "trial-balance"), ("format", toJson "trial-balance@1"), ("object", tbObjJson o),
    ("certificate", saidJson s)]

def verdictText : Judge.Verdict (Obend.Analysis.Coverage.Clause String) → String
  | .ok => "checked (trial-balance@1, decidable, compiled)"
  | .refused (.omitted k) _ => "refused (omitted): " ++ k ++ " is a posting of the period and is not in the report"
  | .refused (.extra k) _ => "refused (extra): " ++ k ++ " is not a posting of the period"
  | .refused .order _ => "refused (order): the postings are not the register's, in its order"
  | .refused .total _ => "refused (total): the totals are not the sums of the period's postings"
  | .refused .root _ => "refused (root): the postings are not the ones the root commits"
  | .uncovered => "uncovered"

def trialBalance (dir : System.FilePath) (P : Nat) (out : Option String) : IO UInt32 := do
  match ← openLedger dir with
  | .error e => fail e
  | .ok (_, _, _, (_, g)) =>
    let said := (tb P).run g.postings
    let o : TBObj := ⟨P, ⟨g.postings, postingsRoot g.postings⟩⟩
    IO.println ("trial balance, period " ++ toString P ++ " (register root " ++ String.ofList (o.book.root.toList.take 12) ++
      "…, " ++ toString g.postings.length ++ " posting(s) in the register)")
    for l in totalsLines said.total do IO.println l
    IO.println ("postings: " ++ ", ".intercalate said.keys)
    let v := Obend.Analysis.Coverage.check (tb P) postingsRoot o.book said
    IO.println (verdictText v ++ ": every posting of period " ++ toString P ++ " is in it")
    IO.FS.createDirAll (dir / "reports")
    Obend.Vault.Cost.writeFile (dir / "reports" / ("TB-" ++ toString P ++ ".md")) (tbPage P said)
    let _ ← openDir dir false
    IO.println ("wrote reports/TB-" ++ toString P ++ ".md")
    if let some path := out then
      Obend.Vault.Cost.writeFile path ((tbJson o said).pretty ++ "\n")
      IO.println ("wrote " ++ path)
    return (if v == .ok then 0 else 3)

/-! ## The stitch -/

/-- The rows of another register this one does not have: its postings of origins not here, and its
closes past this one's closed-through period; `drop` leaves out postings by the other's number. -/
def forkRows (main other : List Row) (drop : List String) : List Row :=
  let here := main.filterMap fun | .post p => some p.origin | .close _ => none
  let w := (stateOf main).1
  other.filter fun
    | .post p => !here.contains p.origin && !drop.contains p.id
    | .close n => decide (w < n)

def rowText : Row → String
  | .post p => p.id ++ " (" ++ (if p.reverses.isSome then "reversal of " else "posting of ") ++ p.doc ++
      " in period " ++ toString p.period ++ ")"
  | .close n => "close through period " ++ toString n

def merge (dir : System.FilePath) (other : String) (drop : List String) : IO UInt32 := do
  let label := (System.FilePath.mk other).fileName.getD other
  let (_, V) ← openDir dir false
  let (o, _) ← openDir other false
  match ← finishTurn dir (.merged label o true) V with
  | .ok (_, .merged _ notes, rendered) =>
    for n in notes do IO.println n
    for l in rendered do IO.println l
  | .ok _ => return ← fail "the merge said what a merge does not"
  | .error e => return ← fail e
  let (s2, _) ← openDir dir false
  let laws ← match registerLaws s2 with
    | .ok l => pure l
    | .error e => return ← fail e
  let J ← loadJournal dir
  let JO ← loadJournal other
  let main := stateOf J.rows
  let rows := forkRows J.rows JO.rows drop
  for d in drop do IO.println ("dropped by the owner: " ++ label ++ "'s " ++ d)
  let F : Obend.Run.Fork.Fork Unit Unit Row := ⟨0, [], [], [], rows⟩
  let ((st, _), conflicts) := Obend.Run.Fork.stitch (rstep (lawOf laws)) (main, ([] : List Unit)) F
  if !conflicts.isEmpty then
    IO.println ("register: not stitched; " ++ toString conflicts.length ++ " of " ++ label ++ "'s " ++ toString rows.length ++
      " new row(s) refused, so none is taken")
    -- each refusal said at the state it was judged at
    let mut a := main
    for r in rows do
      match rstep (lawOf laws) a r with
      | .ok b => a := b
      | .error c =>
        let text := match r with
          | .post p => clauseText laws a.2 a.1 ("register/" ++ a.2.number) (p.numbered a.2.number) c
          | .close _ => "refused"
        IO.println ("  " ++ label ++ "'s " ++ rowText r ++ ": " ++ text)
    IO.println ("to stitch the rest without a row: obend merge " ++ other ++ " --drop P-NNNN")
    return 3
  if rows.isEmpty then
    IO.println ("register: nothing new from " ++ label)
    return 0
  if let .error e ← commitRowsTurn dir rows then return ← fail e
  let mut a := main
  for r in rows do
    match rstep (lawOf laws) a r with
    | .ok b =>
      match r, b.2.postings.getLast? with
      | .post _, some q => IO.println ("register: " ++ label ++ "'s " ++ rowText r ++ " is " ++ q.id ++ " here")
      | .close n, _ => if n > a.1 then IO.println ("register: closed through period " ++ toString n ++ " (from " ++ label ++ ")")
      | _, _ => pure ()
      a := b
    | .error _ => pure ()
  let _ := st
  let _ ← openDir dir false
  IO.println ("register: stitched " ++ toString rows.length ++ " row(s) from " ++ label)
  return 0

/-! ## Verification -/

def lawsOfJson (j : Json) : Except String (List (String × LawExpr × String)) := do
  (← j.getArr?).toList.mapM fun e => do
    let a ← e.getArr?
    match a.toList with
    | [n, t] =>
      let n ← n.getStr?
      let t ← t.getStr?
      return (n, ← Obend.Spec.Law.parse t, t)
    | _ => throw "laws: each is [name, text]"

/-- Re-check a posting receipt: the row re-judged at the register before it, under the law it carries. -/
def verifyPosting (j : Json) : Except String (List String) := do
  let laws ← lawsOfJson (← j.getObjVal? "laws")
  let law ← j.getObjValAs? String "law"
  unless lawDigest laws == law do throw "law: the law lines are not the ones the receipt's law digest names"
  let before ← postingsOf (← j.getObjVal? "before")
  let r ← rowOf (← j.getObjVal? "posting")
  let closed ← j.getObjValAs? Nat "closed"
  let openings ← (← j.getObjValAs? (Array Json) "openings").toList.mapM fun e => do
    let a ← e.getArr?
    match a.toList with
    | [n, b] => return (Fact.isOpen (← n.getNat?), ← b.getBool?)
    | _ => throw "openings: each is [period, open]"
  unless (← j.getObjValAs? String "verdict") == "ok" do throw "only an admitted posting's receipt is re-checked"
  let R : Obend.Receipt.Receipt String String Fact Clause :=
    { pre := ← j.getObjValAs? String "pre", post := ← j.getObjValAs? String "post", row := ← j.getObjValAs? String "row",
      law := law, pins := [], openings := openings, verdict := .ok, quantifier := .existsRun, trust := [],
      dated := closed, proofs := [], prev := ← j.getObjValAs? String "prev" }
  unless Obend.Receipt.recheck (register (lawOf laws)) (naming law) ⟨before⟩ r closed R do
    throw "the row, judged at the register before it, does not reach the receipt's verdict and post root"
  let g : Reg := ⟨before⟩
  return match r with
    | .post p => [g.number ++ ": " ++ p.doc ++ " in period " ++ toString p.period ++ ", admitted at closed-through " ++
        toString closed ++ " over " ++ toString before.length ++ " posting(s): " ++ movementsText p]
    | .close n => ["close through " ++ toString n]

def verifyTB (j : Json) (root : Option String) : IO UInt32 := do
  let obj := ((j.getObjVal? "object").toOption.getD Json.null).compress
  let cert := ((j.getObjVal? "certificate").toOption.getD Json.null).compress
  match tbObjOf obj, saidOf cert with
  | .ok o, .ok s =>
    if let some r := root then
      unless r == o.book.root do
        IO.eprintln "refused (root): the report's book is not the register whose root was given"; return 3
    let v := Obend.Analysis.Coverage.check (tb o.period) postingsRoot o.book s
    if v != .ok then IO.eprintln (verdictText v); return 3
    for l in totalsLines s.total do IO.println l
    IO.println ("verified (trial-balance@1, decidable, compiled): the " ++ toString s.keys.length ++
      " posting(s) of period " ++ toString o.period ++ " among the register's " ++ toString o.book.rows.length ++
      ", none left out" ++ (if root.isSome then "; the register is the one whose root was given" else ""))
    return 0
  | .error e, _ => IO.eprintln ("refused: malformed object: " ++ e); return 3
  | _, .error e => IO.eprintln ("refused: malformed certificate: " ++ e); return 3

/-- `obend verify PATH [--root ROOT]`: a ledger receipt here, anything else by `otherwise`. -/
def verifyOr (path : String) (rest : List String) (otherwise : IO UInt32) : IO UInt32 := do
  let j? := Json.parse (← Obend.Vault.Cost.readFile path)
  let root := match rest with
    | ["--root", r] => some r
    | _ => none
  match j? with
  | .ok j =>
    match (j.getObjValAs? String "kind").toOption with
    | some "posting" =>
      match verifyPosting j with
      | .ok ls => for l in ls do IO.println l
                  IO.println "verified (posting@1: the row re-judged under the register's law it carries)"; return 0
      | .error e => IO.eprintln ("refused: " ++ e); return 3
    | some "trial-balance" => verifyTB j root
    | _ => otherwise
  | .error _ => otherwise

/-! ## Dispatch -/

def hasLedger (dir : System.FilePath) : IO Bool := do
  if ← (dir / "register" / "_kind.md").pathExists then return true
  if !(← isVault dir) then return false
  return !(← loadJournal dir).rows.isEmpty

def run (dir : System.FilePath) (args : List String) : Option (IO UInt32) :=
  let (period, args) := periodFlag args
  match args with
  | ["ledger", "post", doc] => some (postDoc dir doc period)
  | ["ledger", "reverse", id] => some (reverse dir id period)
  | ["ledger", "close", n] => n.toNat?.map (close dir)
  | ["ledger", "status"] => some (status dir)
  | ["ledger", "root"] => some do
    match ← openLedger dir with
    | .error e => fail e
    | .ok (_, _, _, (_, g)) => IO.println (postingsRoot g.postings); return 0
  | "ledger" :: _ => some (do IO.eprintln usage; return 64)
  | ["report", "trial-balance", p] => p.toNat?.map (trialBalance dir · none)
  | ["report", "trial-balance", p, "--out", out] => p.toNat?.map (trialBalance dir · (some out))
  | "merge" :: other :: rest =>
    let drops := (rest.zip (rest.drop 1)).filterMap fun (f, v) => if f == "--drop" then some v else none
    some do
      if (← hasLedger dir) || (← hasLedger other) then merge dir other drops
      else ((Obend.Vault.Cli.main? (["-C", dir.toString, "merge", other])).getD (return 64))
  | _ => none

/-- `obend` ledger commands: `-C DIR` anywhere. -/
public def main? (args : List String) : Option (IO UInt32) :=
  let (dirFlag, args) := flag "-C" args
  run (System.FilePath.mk (dirFlag.getD ".")) args

end Obend.Ledger.Cli

end
