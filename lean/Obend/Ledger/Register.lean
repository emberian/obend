module
/-
# Obend.Ledger.Register — the register: posting as a row of an audited fold, closing as a version law

`AMBITION.md` (platforms: catalogs, documents and registers are kinds with laws, posting is a turn,
period closing is a version law), `review/VISION-CLAUDE-20261031.md` §7.2, `astra/ASTRA-VISION-20261031.md`
§6.1 (purchase-to-payment: balanced per transaction, unique posting identity, correction by reversal)
and §6.2 (drafts merge, postings escalate).

A POSTING moves amounts between accounts: lines `(account, debit, credit)`, a document it posts, the
period it falls in, its number in the register and, for a correction, the posting it reverses. The
REGISTER is an audited fold (`Obend.Fold.Admission`, `register`) whose world component is the
CLOSED-THROUGH period (the version of the period calendar) and whose rest is the postings, in order.

- A posting row (`Row.post`) reads one fact, `isOpen period` (the period is past the closed-through
  one). It is refused, by name:
  `closedPeriod period` (no posting into a closed period), `again` (the register has the row), `law name text`
  (a law of the register's kind refused it: in a vault, `register/_kind.md`'s lines, `balanced` among
  them; the law is a parameter here, `Obend.Ledger.Vault` is the vault's), `postedTwice doc first`
  (the document has a live posting already), and for a reversal `notLive id` (no live posting of
  that number) or `notInverse id` (its lines are not that posting's, debit and credit swapped, or it
  posts another document).
- A close row (`Row.close n`) is the world MOVE: the closed-through period becomes the larger of the
  two. The register ALLOWS exactly the moves that do not decrease it: closing is monotone, a closed
  period never reopens.

Theorems:

- `register_append_only` (correction is not an edit): a run only appends postings, never changes or
  removes one; `register_monotone`: the closed-through period never decreases along a run;
- `closed_refused`, `closed_forever`: a posting into a period at or before the closed-through one is
  refused naming the period, at that state and at every state a run reaches from it;
- `reach_lawful`, `reach_balanced`, `conserved` (the register's total debits are its total credits,
  when its kind's law says each posting is balanced), `net_conserved` (the account nets sum to 0);
- `reach_once` (posted once): a reachable register has at most one live posting per document;
  `twice_refused`: posting a document with a live posting is refused `postedTwice`, naming it;
- `reversal_cancels`: a posting and its reversal net to zero on every account;
- `template_balanced`: a posting template whose debit fields are a rearrangement of its credit
  fields makes a balanced posting of every document (proved once, for every document);
- the offline door (`Obend.Run.Fork.stitch` over the register's step): `stitch_atomic` and
  `stitch_accounts` hold as they do of every step; `stitch_twice_refused`: a fork's posting of a
  document main has a live posting of is a conflict, and the stitch leaves main as it was.
-/
public import Obend.Fold
public import Obend.Run.Fork
@[expose] public section

namespace Obend.Ledger

set_option autoImplicit false

/-! ## Postings -/

/-- One line of a posting: an account, and the amount debited or credited to it. -/
structure Movement where
  account : String
  debit : Nat
  credit : Nat
  deriving DecidableEq, Repr

/-- A posting: its number in the register (given by the register when it is committed, `number`),
the document it posts, the period it falls in, the posting it reverses (a correction, named by its
origin), its lines, and its ORIGIN: the row's identity across replicas (the digest of the row and the
origin before it where it was made, `Obend.Ledger.Json`), kept when a fork's posting is stitched
into main and renumbered there. -/
structure Posting where
  id : String
  doc : String
  period : Nat
  reverses : Option String
  lines : List Movement
  origin : String
  deriving DecidableEq, Repr

def Posting.debits (p : Posting) : Nat := (p.lines.map (·.debit)).sum
def Posting.credits (p : Posting) : Nat := (p.lines.map (·.credit)).sum

/-- A line with debit and credit swapped. -/
def Movement.swap (m : Movement) : Movement := ⟨m.account, m.credit, m.debit⟩

/-- The lines of the reversal of a posting. -/
def inverse (ls : List Movement) : List Movement := ls.map Movement.swap

/-- What a posting does to one account: debits less credits. -/
def Posting.net (p : Posting) (a : String) : Int :=
  (p.lines.map fun m => if m.account = a then (m.debit : Int) - m.credit else 0).sum

theorem net_swap (ls : List Movement) (a : String) :
    (ls.map fun m => if m.account = a then (m.debit : Int) - m.credit else 0).sum +
      ((ls.map Movement.swap).map fun m => if m.account = a then (m.debit : Int) - m.credit else 0).sum = 0 := by
  induction ls with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases e : m.account = a <;> simp [Movement.swap, e] at ih ⊢ <;> omega

/-- **A reversal cancels**: a posting and its reversal net to zero on every account. -/
theorem reversal_cancels (p q : Posting) (h : q.lines = inverse p.lines) (a : String) :
    p.net a + q.net a = 0 := by
  simp only [Posting.net, h, inverse]
  exact net_swap p.lines a

theorem inverse_debits (p q : Posting) (h : q.lines = inverse p.lines) : q.debits = p.credits := by
  simp only [Posting.debits, Posting.credits, h, inverse, List.map_map]
  rfl

theorem inverse_credits (p q : Posting) (h : q.lines = inverse p.lines) : q.credits = p.debits := by
  simp only [Posting.debits, Posting.credits, h, inverse, List.map_map]
  rfl

/-! ## Posting templates, proved once -/

/-- A document kind's posting template: debit lines and credit lines, each an account and the
document field whose value it moves. -/
structure Template where
  debits : List (String × String)
  credits : List (String × String)
  deriving DecidableEq, Repr

/-- The lines a template makes of a document's fields. -/
def Template.lines (t : Template) (field : String → Nat) : List Movement :=
  t.debits.map (fun (a, f) => ⟨a, field f, 0⟩) ++ t.credits.map (fun (a, f) => ⟨a, 0, field f⟩)

theorem sum_map_perm {l l' : List String} (h : l.Perm l') (g : String → Nat) :
    (l.map g).sum = (l'.map g).sum := (h.map g).sum_nat

/-- **A template proved balanced once**: when its debit fields are a rearrangement of its credit
fields, every posting it makes, of every document, is balanced. -/
theorem template_balanced (t : Template) (h : (t.debits.map (·.2)).Perm (t.credits.map (·.2)))
    (field : String → Nat) (p : Posting) (hp : p.lines = t.lines field) : p.debits = p.credits := by
  have hd : p.debits = ((t.debits.map (·.2)).map field).sum := by
    simp only [Posting.debits, hp, Template.lines, List.map_append, List.map_map, List.sum_append]
    have : (t.credits.map ((·.debit) ∘ fun (x : String × String) => (⟨x.1, 0, field x.2⟩ : Movement))).sum = 0 := by
      induction t.credits with
      | nil => rfl
      | cons _ _ ih => simpa using ih
    rw [this, Nat.add_zero]; rfl
  have hc : p.credits = ((t.credits.map (·.2)).map field).sum := by
    simp only [Posting.credits, hp, Template.lines, List.map_append, List.map_map, List.sum_append]
    have : (t.debits.map ((·.credit) ∘ fun (x : String × String) => (⟨x.1, field x.2, 0⟩ : Movement))).sum = 0 := by
      induction t.debits with
      | nil => rfl
      | cons _ _ ih => simpa using ih
    rw [this, Nat.zero_add]; rfl
  rw [hd, hc]
  exact (h.map field).sum_nat

/-! ## The register -/

/-- The postings, in order. -/
structure Reg where
  postings : List Posting
  deriving DecidableEq, Repr

/-- Some posting reverses the one of origin `o`. -/
def Reg.reversed (g : Reg) (o : String) : Bool := g.postings.any (·.reverses == some o)

/-- A posting is LIVE when it is not a reversal and nothing reverses it. -/
def Reg.live (g : Reg) (p : Posting) : Bool := p.reverses.isNone && !g.reversed p.origin

/-- The live posting of a document, if any. -/
def Reg.liveOf (g : Reg) (doc : String) : Option Posting :=
  g.postings.find? fun p => p.doc == doc && g.live p

/-- The posting of origin `o`. -/
def Reg.find (g : Reg) (o : String) : Option Posting := g.postings.find? (·.origin == o)

/-- Four digits, at least. -/
def pad4 (n : Nat) : String := let s := toString n; String.ofList (List.replicate (4 - s.length) '0') ++ s

/-- The number the register gives its next posting. -/
def Reg.number (g : Reg) : String := "P-" ++ pad4 (g.postings.length + 1)

/-- A posting with its number. -/
def Posting.numbered (p : Posting) (id : String) : Posting := { p with id := id }

/-- A row of the register: a posting, or a close (the world move). -/
inductive Row where
  | post (p : Posting)
  | close (n : Nat)
  deriving DecidableEq, Repr

/-- The one fact a posting reads: its period is open. -/
inductive Fact where
  | isOpen (period : Nat)
  deriving DecidableEq, Repr

/-- Why the register refused a row, by name. -/
inductive Clause where
  /-- the period is closed -/
  | closedPeriod (period : Nat)
  /-- the register has this posting already (its origin) -/
  | again (origin : String)
  /-- a law of the register's kind refused it: the law's name, and what it said -/
  | law (name text : String)
  /-- the document has a live posting already, `first` -/
  | postedTwice (doc first : String)
  /-- a reversal of no live posting of that origin -/
  | notLive (origin : String)
  /-- a reversal whose lines are not the posting's swapped, or of another document -/
  | notInverse (origin : String)
  deriving DecidableEq, Repr

/-- A law of the register's kind: `none` admits a posting; `some (name, text)` refuses it. -/
abbrev Law := Posting → Option (String × String)

/-- What is checked of a posting once its period is open and its number is fresh: its kind's law,
then that it posts its document once (or reverses a live posting exactly). -/
def admitPost (law : Law) (g : Reg) (p : Posting) : Except Clause Reg :=
  match law p with
  | some (n, t) => .error (.law n t)
  | none =>
    match p.reverses with
    | some id =>
      match g.find id with
      | none => .error (.notLive id)
      | some q =>
        if !g.live q then .error (.notLive id)
        else if p.lines ≠ inverse q.lines ∨ p.doc ≠ q.doc then .error (.notInverse id)
        else .ok ⟨g.postings ++ [p]⟩
    | none =>
      match g.liveOf p.doc with
      | some q => .error (.postedTwice p.doc q.id)
      | none => .ok ⟨g.postings ++ [p]⟩

/-- **One row of the register.** -/
def step (law : Law) : Nat × Reg → Row → Except Clause (Nat × Reg)
  | (w, g), .close n => .ok (max w n, g)
  | (w, g), .post p =>
    if !decide (w < p.period) then .error (.closedPeriod p.period)
    else if g.postings.any (·.origin == p.origin) then .error (.again p.origin)
    else (admitPost law g (p.numbered g.number)).map fun g' => (w, g')

/-- What `admitPost` accepts: the posting appended, its law admitting it, and either a reversal of a
live posting with its lines swapped, or a document with no live posting. -/
theorem admitPost_ok {law : Law} {g g' : Reg} {p : Posting} (h : admitPost law g p = .ok g') :
    g' = ⟨g.postings ++ [p]⟩ ∧ law p = none ∧
      (∀ o, p.reverses = some o → ∃ q, g.find o = some q ∧ g.live q = true ∧ p.lines = inverse q.lines ∧ p.doc = q.doc) ∧
      (p.reverses = none → g.liveOf p.doc = none) := by
  unfold admitPost at h
  cases hl : law p with
  | some x => rw [hl] at h; cases h
  | none =>
    rw [hl] at h
    simp only at h
    cases hrv : p.reverses with
    | some o =>
      rw [hrv] at h
      simp only at h
      cases hf : g.find o with
      | none => rw [hf] at h; cases h
      | some q =>
        rw [hf] at h
        simp only at h
        by_cases hlive : g.live q = true
        · have hn : (!g.live q) = false := by simp [hlive]
          rw [hn] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          by_cases hinv : p.lines ≠ inverse q.lines ∨ p.doc ≠ q.doc
          · simp only [hinv, ↓reduceIte] at h; cases h
          · simp only [hinv, ↓reduceIte] at h; cases h
            simp only [ne_eq, not_or, Decidable.not_not] at hinv
            exact ⟨rfl, rfl, (fun o' ho => by cases ho; exact ⟨q, hf, hlive, hinv.1, hinv.2⟩), (fun e => by cases e)⟩
        · have hn : (!g.live q) = true := by simpa using hlive
          rw [hn] at h; cases h
    | none =>
      rw [hrv] at h
      simp only at h
      cases hlo : g.liveOf p.doc with
      | some q => rw [hlo] at h; cases h
      | none => rw [hlo] at h; cases h; exact ⟨rfl, rfl, (fun o ho => by cases ho), (fun _ => rfl)⟩

/-- What a posting row accepts: an open period, a new origin, and the posting numbered and admitted. -/
theorem step_post_ok {law : Law} {w : Nat} {g : Reg} {p : Posting} {b : Nat × Reg}
    (h : step law (w, g) (.post p) = .ok b) :
    w < p.period ∧ (∀ q ∈ g.postings, q.origin ≠ p.origin) ∧
      admitPost law g (p.numbered g.number) = .ok b.2 ∧ b.1 = w := by
  simp only [step] at h
  by_cases ho : w < p.period
  · have hd : (!decide (w < p.period)) = false := by simp [ho]
    rw [hd] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    by_cases ha : (g.postings.any fun x => x.origin == p.origin) = true
    · simp only [ha, ↓reduceIte] at h; cases h
    · simp only [ha] at h
      simp only [Bool.not_eq_true, List.any_eq_false, beq_iff_eq] at ha
      cases hp : admitPost law g (p.numbered g.number) with
      | error c => rw [hp] at h; cases h
      | ok g' => rw [hp] at h; cases h; exact ⟨ho, ha, rfl, rfl⟩
  · have hd : (!decide (w < p.period)) = true := by simp [ho]
    rw [hd] at h; cases h

/-- **The register as an audited fold.** The world is the closed-through period; a posting reads
whether its period is open; a close is the move, allowed when it does not decrease the period. -/
def register (law : Law) : Obend.Fold.Admission Nat Reg Row Fact Clause where
  step := step law
  reads _ r := match r with
    | .post p => [.isOpen p.period]
    | .close _ => []
  look w f := match f with
    | .isOpen n => decide (w < n)
  moves r := match r with
    | .post _ => false
    | .close _ => true
  observe w := .close w
  allowed w w' := decide (w ≤ w')
  keeps_world := by
    intro ⟨w, g⟩ r b hm hs
    cases r with
    | close n => cases hm
    | post p => exact (step_post_ok hs).2.2.2
  step_of_reads := by
    intro ⟨w, g⟩ w' r hm hr
    cases r with
    | close n => cases hm
    | post p =>
      have hl : decide (w < p.period) = decide (w' < p.period) := hr (.isOpen p.period) (by simp)
      simp only [step, hl]
      split
      · rfl
      · split
        · rfl
        · cases admitPost law g (p.numbered g.number) <;> rfl
  observe_ok := by
    intro w w' l h
    simp only [step]
    have : max w w' = w' := Nat.max_eq_right (of_decide_eq_true h)
    rw [this]

variable {law : Law}

/-! ## What every row keeps -/

/-- The postings a row leaves are the old ones with at most one appended. -/
theorem step_appends {a b : Nat × Reg} {r : Row} (h : step law a r = .ok b) :
    ∃ new, b.2.postings = a.2.postings ++ new := by
  obtain ⟨w, g⟩ := a
  cases r with
  | close n => simp only [step] at h; cases h; exact ⟨[], by simp⟩
  | post p =>
    obtain ⟨_, _, ha, _⟩ := step_post_ok h
    rw [(admitPost_ok ha).1]
    exact ⟨_, rfl⟩

theorem step_monotone {a b : Nat × Reg} {r : Row} (h : step law a r = .ok b) : a.1 ≤ b.1 := by
  obtain ⟨w, g⟩ := a
  cases r with
  | close n => simp only [step] at h; cases h; exact Nat.le_max_left _ _
  | post p => rw [(step_post_ok h).2.2.2]; exact Nat.le_refl _

/-- The registers a run of rows reaches from a state. -/
def runFrom (law : Law) (a : Nat × Reg) (rows : List Row) : Except Clause (Nat × Reg) :=
  (register law).run a rows

theorem run_induct (P : Nat × Reg → Nat × Reg → Prop) (refl : ∀ a, P a a)
    (trans : ∀ a b c, P a b → P b c → P a c)
    (one : ∀ a r b, step law a r = .ok b → P a b) :
    ∀ (rows : List Row) (a b : Nat × Reg), runFrom law a rows = .ok b → P a b
  | [], a, b, h => by simp only [runFrom, Obend.Fold.Admission.run, List.foldlM_nil] at h; cases h; exact refl a
  | r :: rs, a, b, h => by
    simp only [runFrom, Obend.Fold.Admission.run, List.foldlM_cons] at h
    cases hs : step law a r with
    | error c => simp only [register, hs] at h; cases h
    | ok a' =>
      simp only [register, hs] at h
      exact trans a a' b (one a r a' hs) (run_induct P refl trans one rs a' b h)

/-- **Correction is not an edit**: a run only appends postings. -/
theorem register_append_only {rows : List Row} {a b : Nat × Reg} (h : runFrom law a rows = .ok b) :
    ∃ new, b.2.postings = a.2.postings ++ new :=
  run_induct (fun a b => ∃ new, b.2.postings = a.2.postings ++ new) (fun _ => ⟨[], by simp⟩)
    (fun _ _ _ ⟨n1, h1⟩ ⟨n2, h2⟩ => ⟨n1 ++ n2, by rw [h2, h1, List.append_assoc]⟩)
    (fun _ _ _ hs => step_appends hs) rows a b h

/-- **Closing is monotone**: the closed-through period never decreases along a run. -/
theorem register_monotone {rows : List Row} {a b : Nat × Reg} (h : runFrom law a rows = .ok b) : a.1 ≤ b.1 :=
  run_induct (fun a b => a.1 ≤ b.1) (fun _ => Nat.le_refl _) (fun _ _ _ h1 h2 => Nat.le_trans h1 h2)
    (fun _ _ _ hs => step_monotone hs) rows a b h

/-- **No posting into a closed period**: the refusal names the period and the closed-through one. -/
theorem closed_refused (w : Nat) (g : Reg) (p : Posting) (h : p.period ≤ w) :
    step law (w, g) (.post p) = .error (.closedPeriod p.period) := by
  have : decide (w < p.period) = false := decide_eq_false (by omega)
  simp [step, this]

/-- **A closed period stays closed**: from a state closed through `w`, at every state a run reaches,
a posting into a period at or before `w` is refused naming its period. -/
theorem closed_forever {rows : List Row} {a b : Nat × Reg} (h : runFrom law a rows = .ok b) (p : Posting)
    (hp : p.period ≤ a.1) : step law b (.post p) = .error (.closedPeriod p.period) := by
  obtain ⟨w, g⟩ := b
  exact closed_refused w g p (Nat.le_trans hp (register_monotone h))

/-! ## The kind's law, balanced and conserved -/

/-- A posting a step appends passed the kind's law. -/
theorem step_lawful {a b : Nat × Reg} {r : Row} (h : step law a r = .ok b) :
    ∀ p ∈ b.2.postings, p ∈ a.2.postings ∨ law p = none := by
  obtain ⟨w, g⟩ := a
  cases r with
  | close n => simp only [step] at h; cases h; exact fun p hp => .inl hp
  | post q =>
    obtain ⟨_, _, ha, _⟩ := step_post_ok h
    obtain ⟨hg, hl, _, _⟩ := admitPost_ok ha
    rw [hg]
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact .inl hp
    · simp at hp; subst hp; exact .inr hl

/-- **Every posting a run appends passed the kind's law.** -/
theorem reach_lawful {rows : List Row} {a b : Nat × Reg} (h : runFrom law a rows = .ok b)
    (ha : ∀ p ∈ a.2.postings, law p = none) : ∀ p ∈ b.2.postings, law p = none :=
  run_induct (fun a b => (∀ p ∈ a.2.postings, law p = none) → ∀ p ∈ b.2.postings, law p = none)
    (fun _ h => h) (fun _ _ _ h1 h2 h => h2 (h1 h))
    (fun _ _ _ hs h p hp => (step_lawful hs p hp).elim (h p) id) rows a b h ha

/-- **Balanced**: when the kind's law admits only balanced postings, every posting of a register
reached from the empty one is balanced. -/
theorem reach_balanced (hbal : ∀ p, law p = none → p.debits = p.credits) {rows : List Row} {w : Nat}
    {b : Nat × Reg} (h : runFrom law (w, ⟨[]⟩) rows = .ok b) : ∀ p ∈ b.2.postings, p.debits = p.credits :=
  fun p hp => hbal p (reach_lawful h (fun _ hp => by cases hp) p hp)

def Reg.debits (g : Reg) : Nat := (g.postings.map Posting.debits).sum
def Reg.credits (g : Reg) : Nat := (g.postings.map Posting.credits).sum

theorem sum_eq_of_each (ps : List Posting) (h : ∀ p ∈ ps, p.debits = p.credits) :
    (ps.map Posting.debits).sum = (ps.map Posting.credits).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h p List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- **Conserved**: the register's total is the sum of its postings, and its total debits are its
total credits. -/
theorem conserved (hbal : ∀ p, law p = none → p.debits = p.credits) {rows : List Row} {w : Nat}
    {b : Nat × Reg} (h : runFrom law (w, ⟨[]⟩) rows = .ok b) : b.2.debits = b.2.credits :=
  sum_eq_of_each _ (reach_balanced hbal h)

theorem net_sum_lines (ls : List Movement) (accts : List String) (hall : ∀ m ∈ ls, m.account ∈ accts)
    (hnd : accts.Nodup) :
    (accts.map fun a => (ls.map fun m => if m.account = a then (m.debit : Int) - m.credit else 0).sum).sum =
      (ls.map (fun m => (m.debit : Int))).sum - (ls.map (fun m => (m.credit : Int))).sum := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    clear hall hnd
    induction accts with
    | nil => rfl
    | cons _ _ ih => simpa using ih
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    have ih' := ih fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have hsplit : (accts.map fun a => (if m.account = a then (m.debit : Int) - m.credit else 0) +
        (ms.map fun x => if x.account = a then (x.debit : Int) - x.credit else 0).sum).sum =
        (accts.map fun a => if m.account = a then (m.debit : Int) - m.credit else 0).sum +
        (accts.map fun a => (ms.map fun x => if x.account = a then (x.debit : Int) - x.credit else 0).sum).sum := by
      clear ih ih' hall hnd
      induction accts with
      | nil => rfl
      | cons b bs ih2 => simp only [List.map_cons, List.sum_cons, ih2]; omega
    rw [hsplit, ih']
    have hm : (accts.map fun a => if m.account = a then (m.debit : Int) - m.credit else 0).sum =
        (m.debit : Int) - m.credit := by
      have hin := hall m List.mem_cons_self
      clear ih ih' hsplit hall
      induction accts with
      | nil => cases hin
      | cons a as ih2 =>
        simp only [List.map_cons, List.sum_cons]
        rw [List.nodup_cons] at hnd
        by_cases e : m.account = a
        · subst e
          have : (as.map fun a => if m.account = a then (m.debit : Int) - m.credit else 0).sum = 0 := by
            have hn := hnd.1
            clear ih2 hin hnd
            induction as with
            | nil => rfl
            | cons b bs ih3 =>
              simp only [List.mem_cons, not_or] at hn
              simp only [List.map_cons, List.sum_cons, hn.1, ite_false]
              rw [ih3 hn.2]; rfl
          simp [this]
        · simp only [e, ite_false, Int.zero_add]
          exact ih2 hnd.2 ((List.mem_cons.1 hin).resolve_left e)
    rw [hm]
    omega

/-- **The account nets sum to zero**: over any list of distinct accounts naming every line, a
balanced posting's nets add up to nothing. -/
theorem net_conserved (p : Posting) (hb : p.debits = p.credits) (accts : List String)
    (hall : ∀ m ∈ p.lines, m.account ∈ accts) (hnd : accts.Nodup) : (accts.map p.net).sum = 0 := by
  have := net_sum_lines p.lines accts hall hnd
  show (accts.map fun a => (p.lines.map fun m => if m.account = a then (m.debit : Int) - m.credit else 0).sum).sum = 0
  rw [this]
  have hd : (p.lines.map fun m => (m.debit : Int)).sum = (p.debits : Int) := by
    simp only [Posting.debits]; induction p.lines with
    | nil => rfl
    | cons m ms ih => simp only [List.map_cons, List.sum_cons]; push_cast; omega
  have hc : (p.lines.map fun m => (m.credit : Int)).sum = (p.credits : Int) := by
    simp only [Posting.credits]; induction p.lines with
    | nil => rfl
    | cons m ms ih => simp only [List.map_cons, List.sum_cons]; push_cast; omega
  rw [hd, hc, hb]; omega

/-! ## Posted once -/

@[simp] theorem numbered_doc (p : Posting) (i : String) : (p.numbered i).doc = p.doc := rfl
@[simp] theorem numbered_origin (p : Posting) (i : String) : (p.numbered i).origin = p.origin := rfl
@[simp] theorem numbered_reverses (p : Posting) (i : String) : (p.numbered i).reverses = p.reverses := rfl
@[simp] theorem numbered_id (p : Posting) (i : String) : (p.numbered i).id = i := rfl

/-- **A second posting of a document is refused by name**, naming its live posting. -/
theorem twice_refused (w : Nat) (g : Reg) (p q : Posting) (hopen : w < p.period)
    (hfresh : ∀ x ∈ g.postings, x.origin ≠ p.origin) (hl : law (p.numbered g.number) = none)
    (hr : p.reverses = none) (hq : g.liveOf p.doc = some q) :
    step law (w, g) (.post p) = .error (.postedTwice p.doc q.id) := by
  have ha : (g.postings.any fun x => x.origin == p.origin) = false := by
    simp only [List.any_eq_false, beq_iff_eq]; exact hfresh
  simp [step, hopen, ha, admitPost, hl, hr, hq, Except.map]

/-- A posting of a document with a live posting is refused, whatever else holds of it. -/
theorem twice_error (w : Nat) (g : Reg) (p : Posting) (hr : p.reverses = none) (hq : (g.liveOf p.doc).isSome) :
    ∃ c, step law (w, g) (.post p) = .error c := by
  cases h : step law (w, g) (.post p) with
  | error c => exact ⟨c, rfl⟩
  | ok b =>
    obtain ⟨_, _, ha, _⟩ := step_post_ok h
    have := (admitPost_ok ha).2.2.2 (by simpa using hr)
    simp only [numbered_doc] at this
    rw [this] at hq; cases hq

/-- The live postings of a register. -/
def Reg.liveList (g : Reg) : List Posting := g.postings.filter g.live

/-- What a register keeps that makes "posted once" an invariant: origins are distinct, every
reversal names a posting of the register, and the live postings' documents are distinct. -/
structure Once (g : Reg) : Prop where
  origins : (g.postings.map (·.origin)).Nodup
  targets : ∀ p ∈ g.postings, ∀ o, p.reverses = some o → ∃ q ∈ g.postings, q.origin = o
  docs : (g.liveList.map (·.doc)).Nodup

theorem reversed_append (g : Reg) (p : Posting) (o : String) :
    (⟨g.postings ++ [p]⟩ : Reg).reversed o = (g.reversed o || p.reverses == some o) := by
  simp [Reg.reversed, List.any_append]

theorem find_some {g : Reg} {o : String} {q : Posting} (h : g.find o = some q) : q ∈ g.postings ∧ q.origin = o := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

theorem liveOf_none {g : Reg} {d : String} (h : g.liveOf d = none) : ∀ q ∈ g.postings, g.live q = true → q.doc ≠ d := by
  intro q hq hl he
  have := List.find?_eq_none.1 h q hq
  simp [he, hl] at this

/-- **Posted once is kept by every row.** -/
theorem step_once {a b : Nat × Reg} {r : Row} (h : step law a r = .ok b) (ho : Once a.2) : Once b.2 := by
  obtain ⟨w, g⟩ := a
  cases r with
  | close n => simp only [step] at h; cases h; exact ho
  | post p0 =>
    obtain ⟨_, hfresh, ha, _⟩ := step_post_ok h
    obtain ⟨hg, _, hrev, hnew⟩ := admitPost_ok ha
    rw [hg]
    generalize hp : p0.numbered g.number = p at hrev hnew
    have hpo : p.origin = p0.origin := by rw [← hp]; rfl
    have hfresh' : ∀ q ∈ g.postings, q.origin ≠ p.origin := hpo ▸ hfresh
    have hids : ((g.postings ++ [p]).map (·.origin)).Nodup := by
      rw [List.map_append, List.nodup_append]
      refine ⟨ho.origins, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_map] at hx
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      obtain ⟨q, hq, rfl⟩ := hx
      subst hy
      exact hfresh' q hq
    cases hrv : p.reverses with
    | some o =>
      obtain ⟨q, hf, hlive, _, _⟩ := hrev o hrv
      obtain ⟨hqm, hqo⟩ := find_some hf
      refine ⟨hids, ?_, ?_⟩
      · intro x hx i hi
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨y, hy, e⟩ := ho.targets x hx i hi
          exact ⟨y, List.mem_append.2 (.inl hy), e⟩
        · simp at hx; subst hx; rw [hrv] at hi; cases hi
          exact ⟨q, List.mem_append.2 (.inl hqm), hqo⟩
      · have hsub : (⟨g.postings ++ [p]⟩ : Reg).liveList = g.liveList.filter (·.origin != o) := by
          have hpl : (⟨g.postings ++ [p]⟩ : Reg).live p = false := by simp [Reg.live, hrv]
          simp only [Reg.liveList, List.filter_append, List.filter_cons, hpl, List.filter_nil,
            List.append_nil, List.filter_filter, Bool.false_eq_true, ↓reduceIte]
          apply List.filter_congr
          intro x _
          simp only [Reg.live, reversed_append, hrv]
          by_cases hx : x.origin = o
          · simp [hx]
          · have : (some o == some x.origin) = false := by simp [Ne.symm hx]
            simp [this, hx]
        rw [hsub]
        exact (List.filter_sublist).map _ |>.nodup ho.docs
    | none =>
      have hlo := hnew hrv
      refine ⟨hids, ?_, ?_⟩
      · intro x hx i hi
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨y, hy, e⟩ := ho.targets x hx i hi
          exact ⟨y, List.mem_append.2 (.inl hy), e⟩
        · simp at hx; subst hx; rw [hrv] at hi; cases hi
      · have hnr : g.reversed p.origin = false := by
          simp only [Reg.reversed, List.any_eq_false, beq_iff_eq]
          intro x hx e
          obtain ⟨y, hy, hyo⟩ := ho.targets x hx p.origin e
          exact hfresh' y hy hyo
        have hsame : ∀ x ∈ g.postings, (⟨g.postings ++ [p]⟩ : Reg).live x = g.live x := by
          intro x _
          simp [Reg.live, reversed_append, hrv]
        have hlist : (⟨g.postings ++ [p]⟩ : Reg).liveList = g.liveList ++ [p] := by
          simp only [Reg.liveList, List.filter_append]
          rw [List.filter_congr hsame]
          simp [Reg.live, reversed_append, hrv, hnr]
        rw [hlist, List.map_append, List.nodup_append]
        refine ⟨ho.docs, by simp, ?_⟩
        intro x hx y hy
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
        subst hy
        simp only [List.mem_map, Reg.liveList, List.mem_filter] at hx
        obtain ⟨q, ⟨hq, hql⟩, rfl⟩ := hx
        exact liveOf_none hlo q hq hql

theorem once_empty : Once ⟨[]⟩ := ⟨List.nodup_nil, (fun _ h => by cases h), List.nodup_nil⟩

/-- **Posted once**: a register reached from the empty one has at most one live posting per
document (and distinct origins, and every reversal names one of its postings). -/
theorem reach_once {rows : List Row} {w : Nat} {b : Nat × Reg} (h : runFrom law (w, ⟨[]⟩) rows = .ok b) :
    Once b.2 :=
  run_induct (law := law) (fun a b => Once a.2 → Once b.2) (fun _ h => h) (fun _ _ _ h1 h2 h => h2 (h1 h))
    (fun _ _ _ hs ho => step_once hs ho) rows _ b h once_empty

/-! ## The offline door: a fork's postings stitched through the register -/

/-- The register's step, on fork rows. -/
abbrev rstep (law : Law) : Nat × Reg → Row → Except Clause (Nat × Reg) := step law

/-- A live posting stays live while no row reverses anything. -/
theorem step_keeps_live {a b : Nat × Reg} {r : Row} (h : step law a r = .ok b)
    (hr : ∀ p, r = .post p → p.reverses = none) {d : String} (hd : (a.2.liveOf d).isSome) :
    (b.2.liveOf d).isSome := by
  obtain ⟨w, g⟩ := a
  cases r with
  | close n => simp only [step] at h; cases h; exact hd
  | post p0 =>
    have hrv : (p0.numbered g.number).reverses = none := by simpa using hr p0 rfl
    obtain ⟨_, _, ha, _⟩ := step_post_ok h
    rw [(admitPost_ok ha).1]
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hd
    have hqm := List.mem_of_find?_eq_some hq
    have hqp := List.find?_some hq
    simp only [Bool.and_eq_true, beq_iff_eq] at hqp
    simp only [Reg.liveOf]
    rw [List.find?_isSome]
    refine ⟨q, List.mem_append.2 (.inl hqm), ?_⟩
    simp only [Reg.live, reversed_append, hrv, Bool.and_eq_true, beq_iff_eq]
    simp only [Reg.live, Bool.and_eq_true, Bool.not_eq_true'] at hqp
    refine ⟨hqp.1, hqp.2.1, ?_⟩
    simp [hqp.2.2]


/-- **A double posting across the fork is refused, and main does not move.** Main has a live posting
of document `d`; a fork that reversed nothing posted `d` too while disconnected. At the stitch the
fork's posting of `d` is a conflict (returned with its refusal, never dropped), so the stitch is
refused whole and main's register is as it was (`Obend.Run.Fork.stitch_atomic`). -/
theorem stitch_twice_refused {M : Type} [DecidableEq M] {Tok : Type} (main : (Nat × Reg) × List M)
    (F : Obend.Run.Fork.Fork Tok M Row) (d : String) (hlive : (main.1.2.liveOf d).isSome)
    (hnorev : ∀ e ∈ F.escalated, ∀ p, e = .post p → p.reverses = none)
    (p : Posting) (hp : Row.post p ∈ F.escalated) (hd : p.doc = d) :
    (∃ c, (Row.post p, c) ∈ (Obend.Run.Fork.stitch (rstep law) main F).2) ∧
      (Obend.Run.Fork.stitch (rstep law) main F).1.1 = main.1 := by
  have hc : ∃ c, (Row.post p, c) ∈ (Obend.Run.Fork.replay (rstep law) main.1 F.escalated).2 :=
    Obend.Run.Fork.replay_conflicts (rstep law) (fun s => (s.2.liveOf d).isSome = true)
      (fun e => ∃ q, e = .post q ∧ q.doc = d) F.escalated
      (fun s e s' he hs hst => step_keeps_live (law := law) hst (hnorev e he) hs)
      (fun s e he hs ⟨q, hq, hqd⟩ => by
        subst hq
        obtain ⟨w, g⟩ := s
        exact twice_error w g q (hnorev _ he q rfl) (hqd ▸ hs))
      main.1 hlive (.post p) hp ⟨p, rfl, hd⟩
  obtain ⟨c, hc⟩ := hc
  rw [← Obend.Run.Fork.stitch_conflicts] at hc
  refine ⟨⟨c, hc⟩, ?_⟩
  rcases Obend.Run.Fork.stitch_atomic (rstep law) main F with ⟨hn, _⟩ | ⟨_, h⟩
  · rw [hn] at hc; cases hc
  · exact h

end Obend.Ledger

end
