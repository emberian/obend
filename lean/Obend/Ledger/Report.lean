module
/-
# Obend.Ledger.Report — the trial balance as a judged fold, and the receipts a stranger re-checks

**The trial balance** of a period (`tb P`) is a report in the sense of `Obend.Analysis.Coverage`: over
the register's postings, it selects those of period `P`, keys each by its number, and adds its lines
into per-account debit and credit totals (`addPosting`). Its receipt is a BOOK (the register's
postings and their root, `Obend.Ledger.Json.postingsRoot`) and what the report SAID (the numbers it
took and the totals); an auditor recomputes it.

- `tb_totals`: the report's total for an account is the sum, over the period's postings, of what
  each debits and credits it (the register's total is the sum of its postings);
- `trial_balance_covers` (**non-omission**): a trial balance the judge accepts names every posting
  of the period in the book, and each account's totals are those postings' sums, so no posting of the
  period is left out of any total; `trial_balance_binds`: of every register whose root is the book's,
  when the root binds;
- `tbFormat`, `trial-balance@1`: the registered format (decidable, compiled trust), its planted bad
  certificate a report that drops a posting of the period (`tb_bad_refused`: refused `omitted`,
  naming the posting).

**A posting receipt** is `Obend.Receipt.issue` of the posting's row of the register's fold
(`Obend.Ledger.Register.register` under the kind's law, `Obend.Ledger.Vault.kindLaw`), named by the
register's roots (`naming`): pre and post are the register's roots before and after, the row's digest,
the law's digest (of the kind's law lines), the opening (whether the period is open at the
closed-through period the posting was judged at). `posting_receipt_checks`: a stranger's `recheck` of an
honestly issued posting receipt accepts it (`Obend.Receipt.recheck_issued_self`); `recheck_sound`
says what its acceptance establishes.
-/
public import Obend.Ledger.Vault
public import Obend.Ledger.Json
public import Obend.Analysis.Coverage
public import Obend.Receipt
@[expose] public section

namespace Obend.Ledger

set_option autoImplicit false

open Obend.Analysis.Coverage (Report Said Book)
open Lean (Json toJson)

/-! ## Totals per account -/

/-- Debit and credit totals per account. -/
abbrev Totals := List (String × Nat × Nat)

def Totals.get (t : Totals) (a : String) : Nat × Nat := (t.lookup a).getD (0, 0)

/-- Add a debit and a credit to an account. -/
def bump : Totals → String → Nat → Nat → Totals
  | [], a, d, c => [(a, d, c)]
  | (b, x, y) :: rest, a, d, c => if a = b then (b, x + d, y + c) :: rest else (b, x, y) :: bump rest a d c

theorem get_bump : ∀ (t : Totals) (a : String) (d c : Nat) (x : String),
    (bump t a d c).get x = if x = a then ((t.get x).1 + d, (t.get x).2 + c) else t.get x
  | [], a, d, c, x => by
    by_cases h : x = a
    · subst h; simp [bump, Totals.get, List.lookup]
    · have hb : (x == a) = false := by simpa using h
      simp [bump, Totals.get, List.lookup, h, hb]
  | (b, x0, y0) :: rest, a, d, c, x => by
    by_cases hab : a = b
    · subst hab
      by_cases hx : x = a
      · subst hx; simp [bump, Totals.get, List.lookup]
      · have hb : (x == a) = false := by simpa using hx
        simp [bump, Totals.get, List.lookup, hx, hb]
    · have ih := get_bump rest a d c x
      by_cases hx : x = b
      · subst hx
        have : ¬ x = a := fun e => hab e.symm
        simp [bump, Totals.get, List.lookup, hab, this]
      · simp only [bump, hab, ite_false]
        simp only [Totals.get, List.lookup, show (x == b) = false from by simpa using hx] at ih ⊢
        exact ih

/-- What a posting debits an account. -/
def debitOn (a : String) (p : Posting) : Nat := (p.lines.map fun m => if m.account = a then m.debit else 0).sum
/-- What a posting credits an account. -/
def creditOn (a : String) (p : Posting) : Nat := (p.lines.map fun m => if m.account = a then m.credit else 0).sum

/-- Add a posting's lines in. -/
def addPosting (t : Totals) (p : Posting) : Totals :=
  p.lines.foldl (fun t m => bump t m.account m.debit m.credit) t

theorem get_addLines (a : String) : ∀ (ls : List Movement) (t : Totals),
    (ls.foldl (fun t m => bump t m.account m.debit m.credit) t).get a =
      ((t.get a).1 + (ls.map fun m => if m.account = a then m.debit else 0).sum,
       (t.get a).2 + (ls.map fun m => if m.account = a then m.credit else 0).sum)
  | [], t => by simp
  | m :: ms, t => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [get_addLines a ms, get_bump]
    by_cases h : a = m.account
    · subst h; simp; omega
    · have : ¬ m.account = a := fun e => h e.symm
      simp [h, this]

theorem get_addPosting (t : Totals) (p : Posting) (a : String) :
    (addPosting t p).get a = ((t.get a).1 + debitOn a p, (t.get a).2 + creditOn a p) :=
  get_addLines a p.lines t

theorem get_addAll (a : String) : ∀ (ps : List Posting) (t : Totals),
    (ps.foldl addPosting t).get a =
      ((t.get a).1 + (ps.map (debitOn a)).sum, (t.get a).2 + (ps.map (creditOn a)).sum)
  | [], t => by simp
  | p :: ps, t => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [get_addAll a ps, get_addPosting]
    simp only [Prod.mk.injEq]
    omega

/-! ## The trial balance -/

/-- **The trial balance of period `P`**: the postings of `P`, keyed by number, added into totals. -/
def tb (P : Nat) : Report Posting String Totals := ⟨fun p => p.period == P, (·.id), addPosting, []⟩

/-- **The register's total is the sum of its postings**: the trial balance's total for an account is
what the period's postings debit and credit it. -/
theorem tb_totals (P : Nat) (rows : List Posting) (a : String) :
    ((tb P).run rows).total.get a =
      (((rows.filter (·.period == P)).map (debitOn a)).sum, ((rows.filter (·.period == P)).map (creditOn a)).sum) := by
  rw [Obend.Analysis.Coverage.run_total]
  simp only [tb]
  rw [get_addAll]
  simp [Totals.get, List.lookup]

/-- **Non-omission of the trial balance.** An accepted trial balance of period `P` names every posting
of `P` in its book, names no other, and every account's totals are the sums of those postings'
movements on it. -/
theorem trial_balance_covers {P : Nat} {b : Book Posting String} {s : Said String Totals}
    (h : Obend.Analysis.Coverage.check (tb P) Json.postingsRoot b s = .ok) :
    (∀ p ∈ b.rows, p.period = P → p.id ∈ s.keys) ∧
      (∀ k ∈ s.keys, ∃ p ∈ b.rows, p.period = P ∧ p.id = k) ∧
      ∀ a, s.total.get a = (((b.rows.filter (·.period == P)).map (debitOn a)).sum,
        ((b.rows.filter (·.period == P)).map (creditOn a)).sum) := by
  obtain ⟨hc, ho, _⟩ := Obend.Analysis.Coverage.check_covers h
  obtain ⟨_, hs⟩ := Obend.Analysis.Coverage.check_sound h
  refine ⟨fun p hp hP => hc p hp (by simp [tb, hP]), fun k hk => ?_, fun a => by rw [hs]; exact tb_totals P b.rows a⟩
  obtain ⟨p, hp, hsel, hk⟩ := ho k hk
  exact ⟨p, hp, by simpa [tb] using hsel, hk⟩

/-- Of every register whose root is the book's, when the root binds. -/
theorem trial_balance_binds {P : Nat} {b : Book Posting String} {s : Said String Totals}
    (h : Obend.Analysis.Coverage.check (tb P) Json.postingsRoot b s = .ok) (reg : List Posting)
    (hroot : Json.postingsRoot reg = b.root) (hbind : Json.postingsRoot reg = Json.postingsRoot b.rows → reg = b.rows) :
    ∀ p ∈ reg, p.period = P → p.id ∈ s.keys := fun p hp hP =>
  Obend.Analysis.Coverage.check_binds h reg hroot hbind p hp (by simp [tb, hP])

/-- The object of a trial balance: its period and its book. -/
structure TBObj where
  period : Nat
  book : Book Posting String

instance tbJudge : Judge TBObj (Said String Totals) where
  Clause := Obend.Analysis.Coverage.Clause String
  Meaning o s := Obend.Analysis.Coverage.Meaning (tb o.period) Json.postingsRoot o.book s
  check _ o s := Obend.Analysis.Coverage.check (tb o.period) Json.postingsRoot o.book s
  sound := Obend.Analysis.Coverage.check_sound
  refutes k := k == .root
  refuted := by
    intro _ o c k p h hk
    cases k <;> simp at hk
    exact Obend.Analysis.Coverage.check_root_refutes h
  Fragment _ := True
  complete := fun {o} _ ⟨c, hc⟩ => ⟨c, 0, Obend.Analysis.Coverage.check_complete hc⟩
  mono := by intro _ _ _ _ _ _; rfl

/-! ## The wire, and the registered format -/

def totalsJson (t : Totals) : Json :=
  Json.arr (t.map fun (a, d, c) => Json.arr #[toJson a, toJson d, toJson c]).toArray

def totalsOf (j : Json) : Except String Totals := do
  (← j.getArr?).toList.mapM fun e => do
    let a ← e.getArr?
    match a.toList with
    | [x, y, z] => return (← x.getStr?, ← y.getNat?, ← z.getNat?)
    | _ => throw "totals: each entry is [account, debit, credit]"

def tbObjJson (o : TBObj) : Json :=
  Json.mkObj [("period", toJson o.period), ("root", toJson o.book.root), ("postings", Json.postingsJson o.book.rows)]

def tbObjOf (s : String) : Except String TBObj := do
  let j ← Json.parse s
  return ⟨← j.getObjValAs? Nat "period", ⟨← Json.postingsOf (← j.getObjVal? "postings"), ← j.getObjValAs? String "root"⟩⟩

def saidJson (s : Said String Totals) : Json :=
  Json.mkObj [("postings", toJson s.keys), ("totals", totalsJson s.total)]

def saidOf (s : String) : Except String (Said String Totals) := do
  let j ← Json.parse s
  return ⟨← j.getObjValAs? (List String) "postings", ← totalsOf (← j.getObjVal? "totals")⟩

/-- Two postings of period 11 and one of 10. -/
def badPostings : List Posting :=
  [⟨"P-0001", "invoices/INV-1", 11, none, [⟨"Receivables", 500, 0⟩, ⟨"Revenue", 0, 500⟩], "a"⟩,
   ⟨"P-0002", "invoices/INV-2", 10, none, [⟨"Receivables", 70, 0⟩, ⟨"Revenue", 0, 70⟩], "b"⟩,
   ⟨"P-0003", "payments/PAY-1", 11, none, [⟨"Cash", 300, 0⟩, ⟨"Receivables", 0, 300⟩], "c"⟩]

/-- **The planted bad certificate**: a trial balance of period 11 that leaves out `P-0003`. -/
def badTB : TBObj × Said String Totals :=
  (⟨11, ⟨badPostings, ""⟩⟩, ⟨["P-0001"], [("Receivables", 500, 0), ("Revenue", 0, 500)]⟩)

theorem tb_bad_refused :
    Obend.Analysis.Coverage.check (tb 11) Json.postingsRoot badTB.1.book badTB.2 = .refused (.omitted "P-0003") [] := by
  decide +kernel

/-- **The registered format `trial-balance@1`.** -/
def tbFormat : Judge.Format where
  name := "trial-balance"
  version := "1"
  Obj := TBObj
  Cert := Said String Totals
  judge := tbJudge
  decodeObj := tbObjOf
  decodeCert := saidOf
  trust := .compiled
  regime := .decidable
  bad := badTB
  badGrade := 0
  bad_refused := ⟨_, _, tb_bad_refused⟩

/-- The formats the ledger registers. -/
def formats : List Judge.Format := [tbFormat]

/-! ## Posting receipts -/

/-- How the register names its roots, rows and view in a receipt. -/
def naming (lawDigest : String) : Obend.Receipt.Naming Nat Reg Row Fact String String where
  root g := Json.postingsRoot g.postings
  rowDigest r := Obend.Receipt.Negotiation.digestJson (Json.rowJson r)
  law := lawDigest
  pinsOf w _ := [("closed-through", some (toString w))]
  dated w := w
  proofsOf _ _ := []

/-- The trust a posting receipt names: the register's law, judged by the vault's compiled judge. -/
def postingTrust : List (String × Obend.Receipt.Trust) := [("register law", .checked "obend-law" "1" .compiled)]

/-- **The receipt of a posting row.** -/
def postingReceipt (law : Law) (lawDigest : String) (a : Nat × Reg) (r : Row) (prev : String) :
    Obend.Receipt.Receipt String String Fact Clause :=
  Obend.Receipt.issue (register law) (naming lawDigest) a r .existsRun postingTrust prev

/-- **A stranger accepts an honest posting receipt**: rechecking it against the register before and
the closed-through period it was judged at. -/
theorem posting_receipt_checks (law : Law) (d : String) (a : Nat × Reg) (p : Posting) (prev : String) :
    Obend.Receipt.recheck (register law) (naming d) a.2 (Row.post p) a.1 (postingReceipt law d a (Row.post p) prev) = true :=
  Obend.Receipt.recheck_issued_self _ _ a (Row.post p) rfl _ _ _

end Obend.Ledger

end
