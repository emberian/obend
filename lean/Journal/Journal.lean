module
/-
# Journal.Journal — each theorem a `Slot`; a redesign read as withdrawn supports

An EXPORT is one row per declaration of the `Obend` tree (`Journal.Export` writes it): name, module,
kind, visibility, the constants its type cites, the constants its value cites, a structural hash of
the type, a structural hash of the value, the axiom set. Two exports are two VIEWS of the library.

The MEANING of a constant, to anything that cites it, is what a kernel re-check of the citer would
read: for a theorem its statement and its axiom set (the proof is irrelevant to a consumer, and the
axiom set is what the tree pins); for everything else its type and its body (a definition's body is
its meaning; a constructor's or recursor's shape is its body here). A meaning is reached
TRANSITIVELY: a statement that cites `f` means whatever `f`'s body means, so the supports of a
theorem are the closure of its citations along meaning edges (types always; values except through
theorem proofs). This is the memo's contract graph (HOLES-FOR-PROOF-ENGINEERING §"A theorem as an
enduring obligation"): "a definition changing beneath an unchanged theorem type can change the
contract graph". The brief's flat `(name, typeHash)` would call `theorem T : f = 7 := rfl`
unaffected when `f`'s body changes from `g` to `g+1`; the closure does not.

Each theorem is a `Obend.Slot.Slot` whose single CANDIDATE is the proof the old export recorded and
whose SUPPORTS are `(name, meaning)` facts: a `.stmt` support for every constant the statement
reaches, a `.proof` support for every constant only the proof reaches. The new export is the view:
a support HOLDS when the new export has that name with that meaning. `Slot.read` of the candidate
then says `usable` (UNAFFECTED) or `blocked` with the dead supports by name; the journal splits the
dead list: any dead `.stmt` support puts the theorem under STATEMENT-CITED (its meaning may have
changed), dead `.proof` supports alone put it under PROOF-CITED (the proof must be re-checked, the
statement means what it meant). `verdict_unaffected_iff` and `verdict_blocked` are the bridge:
the journal's verdict is the slot's read and nothing else.

Where `Slot` does not fit, and what is outside it:
- The split of `dead` into statement/proof is a classification of the read's list; `Slot` knows one
  kind of fact. The two constructors of `Support` carry the role.
- One candidate per slot: `Slot.alternatives` and `Slot.resolve` have nothing to choose from. A
  second proof of the same statement would be a second candidate; none is recorded.
- `judge` is constant `true`: the kernel judged the candidate when the old export was taken, and no
  view-independent contract remains. `Reading.rejected` cannot occur.
- A theorem whose own statement meaning differs between the exports is REVISED: the obligation
  changed, which is not a support withdrawing from a fixed obligation. Reported outside the slot.
- `Permanent` has no instance here: an edit can be reverted, so no dead support stays dead along
  "later export". Clause (3) of `slot_repair` is unused; clauses (1), (2), (4) are what `verdict`
  rests on.
- A theorem new in the second export, or gone from it, has no slot to read.

Toolchain constants (`Init`, `Std`, `Lean`) are not rows: the export records the toolchain once and
the journal treats its constants as a fixed background. A toolchain bump is not a redesign this
journal reads.
-/
public import Obend.Slot
public import Std.Data.HashMap
public import Std.Data.HashSet
@[expose] public section

namespace Journal

/-- One exported declaration: the row `Journal.Export` writes. Names are the kernel's (private
names mangled, as in the environment); hashes are 64-bit structural hashes of the type and of the
value (`Journal.Export.hashExpr`); the citation lists hold only constants declared in the `Obend`
tree; the axioms are sorted. -/
structure Row where
  name : String
  module : String
  /-- `theorem`, `definition`, `opaque`, `axiom`, `inductive`, `constructor`, `recursor`, `quotient` -/
  kind : String
  /-- `public` or `private`; in a `module` file, the module system's notion -/
  visibility : String
  /-- the body is visible to importers (`@[expose]`, or a legacy file) -/
  exposed : Bool
  typeCites : List String
  valueCites : List String
  typeHash : UInt64
  valueHash : UInt64
  axioms : List String
  deriving Repr, BEq, Inhabited

/-- An export: rows by name. -/
abbrev Export := Std.HashMap String Row

def Export.ofRows (rows : List Row) : Export :=
  rows.foldl (fun m r => m.insert r.name r) {}

/-- The hash of a sorted axiom list. -/
def axiomsHash (axioms : List String) : UInt64 :=
  axioms.foldl (fun acc a => mixHash acc a.hash) 7

/-- The meaning of a constant to its citers: statement and axioms for a theorem (its proof is
irrelevant to them, its axiom footprint is not); type and body for everything else. -/
def Row.meaning (r : Row) : UInt64 :=
  if r.kind == "theorem" then mixHash r.typeHash (axiomsHash r.axioms)
  else mixHash r.typeHash r.valueHash

/-- The constants a constant's meaning depends on, one step: everything its type cites, and
everything its value cites unless the value is a proof. -/
def Row.meaningEdges (r : Row) : List String :=
  if r.kind == "theorem" then r.typeCites else r.typeCites ++ r.valueCites

/-- Every constant reachable from `seeds` along meaning edges in `E`, `seeds` included (names not
in `E` are toolchain background or vanished: kept as names, not followed). Depth-first with a
visited set; `fuel` bounds the walk by the export's size, which the closure cannot exceed. -/
def closure (E : Export) (seeds : List String) : List String :=
  let rec go (fuel : Nat) (stack : List String) (seen : Std.HashSet String) (acc : List String) :
      List String :=
    match fuel, stack with
    | 0, _ => acc.reverse
    | _, [] => acc.reverse
    | fuel + 1, n :: rest =>
      if seen.contains n then go fuel rest seen acc
      else
        let next := match E[n]? with
          | some r => r.meaningEdges
          | none => []
        go fuel (next ++ rest) (seen.insert n) (n :: acc)
  go (E.size + seeds.length + 1) seeds {} []

/-- A support: a constant at a meaning, in the role its citation plays for the theorem. -/
inductive Support where
  /-- the statement reaches this constant -/
  | stmt (name : String) (meaning : UInt64)
  /-- only the proof reaches this constant -/
  | proof (name : String) (meaning : UInt64)
  deriving Repr, BEq, Inhabited

def Support.name : Support → String
  | .stmt n _ | .proof n _ => n

def Support.meaning : Support → UInt64
  | .stmt _ m | .proof _ m => m

def Support.isStmt : Support → Bool
  | .stmt _ _ => true
  | .proof _ _ => false

/-- The stored candidate of a theorem's slot: the proof the old export recorded, with the supports
it cites, already closed and split by role. -/
structure Candidate where
  name : String
  stmtSupports : List Support
  proofSupports : List Support
  deriving Repr, BEq, Inhabited

/-- The candidate of theorem `r` in export `old`: statement supports are the closure of the type's
citations; proof supports are the closure of the value's citations minus the statement's. A name
the old export lacks (a toolchain constant that slipped the filter, or a vanished one) gets meaning
`0`; the citation lists are tree-only, so this does not occur on an export of the tree. -/
def candidateOf (old : Export) (r : Row) : Candidate :=
  let meaningIn (n : String) : UInt64 := match old[n]? with
    | some s => s.meaning
    | none => 0
  let stmtNames := closure old r.typeCites
  let stmtSet : Std.HashSet String := stmtNames.foldl (·.insert ·) {}
  let proofNames := (closure old r.valueCites).filter (fun n => !stmtSet.contains n)
  { name := r.name
    stmtSupports := stmtNames.map fun n => .stmt n (meaningIn n)
    proofSupports := proofNames.map fun n => .proof n (meaningIn n) }

/-- A support holds at a view when the view has the constant at that meaning. -/
def holdsIn (new : Export) (s : Support) : Bool :=
  match new[s.name]? with
  | some r => r.meaning == s.meaning
  | none => false

open Obend.Slot in
/-- The one slot every theorem instantiates: supports as recorded, judge constant (the kernel
judged the candidate at export time; nothing view-independent remains to check). -/
def slot : Slot Support Candidate where
  supports c := c.stmtSupports ++ c.proofSupports
  judge _ := true

/-- What the journal says of one theorem whose statement is what it was. -/
inductive Verdict where
  /-- every support holds -/
  | unaffected
  /-- a support the statement reaches is dead: the theorem's meaning may have changed -/
  | statementCited (dead : List Support)
  /-- only supports the proof alone reaches are dead: re-check the proof, the statement stands -/
  | proofCited (dead : List Support)
  deriving Repr, BEq, Inhabited

/-- The verdict is read off the slot's dead list at the new view. -/
def verdict (new : Export) (c : Candidate) : Verdict :=
  match slot.dead (holdsIn new) c with
  | [] => .unaffected
  | s :: d => if (s :: d).any Support.isStmt then .statementCited (s :: d) else .proofCited (s :: d)

/-! ## The verdict is the slot's read -/

open Obend.Slot

theorem verdict_eq_unaffected_iff_dead_nil (new : Export) (c : Candidate) :
    verdict new c = .unaffected ↔ slot.dead (holdsIn new) c = [] := by
  cases hd : slot.dead (holdsIn new) c with
  | nil => simp [verdict, hd]
  | cons s d =>
    simp only [verdict, hd]
    split <;> simp

/-- UNAFFECTED is exactly `slot_repair` (1): the read is `usable` iff every support holds at the
new view (the judge being constant, nothing else is asked). -/
theorem verdict_unaffected_iff (new : Export) (c : Candidate) :
    verdict new c = .unaffected ↔
      ∃ ev, slot.read (holdsIn new) (some c) = .usable c ev := by
  rw [verdict_eq_unaffected_iff_dead_nil, read_usable_iff, usable_iff, dead_eq_nil_iff]
  simp [slot]

/-- A verdict that names dead supports names exactly what the slot's read names: the list is the
read's `blocked` list, which (`slot_repair` (2)) holds every support of the candidate that does not
hold at the new view and nothing else. -/
theorem verdict_blocked (new : Export) (c : Candidate) (dead : List Support)
    (h : verdict new c = .statementCited dead ∨ verdict new c = .proofCited dead) :
    slot.read (holdsIn new) (some c) = .blocked c dead := by
  cases hd : slot.dead (holdsIn new) c with
  | nil => simp [verdict, hd] at h
  | cons s d =>
    simp only [verdict, hd] at h
    have hdead : dead = s :: d := by
      split at h <;> simp_all
    subst hdead
    simp only [Slot.read]
    rw [hd]
    simp [slot]

/-! ## The report over two exports -/

/-- A constant whose meaning the new export does not carry: gone, or changed. -/
inductive Withdrawn where
  | removed (name : String)
  | changed (name : String) (oldMeaning newMeaning : UInt64)
  deriving Repr, BEq, Inhabited

def Withdrawn.name : Withdrawn → String
  | .removed n | .changed n _ _ => n

/-- The journal of a redesign: what two exports say about every theorem of the first. -/
structure Report where
  /-- constants of the old export whose meaning the new one lacks, every kind -/
  withdrawn : List Withdrawn
  /-- theorems whose own statement meaning differs: the obligation itself changed -/
  revised : List (String × Verdict)
  statementCited : List (String × List Support)
  proofCited : List (String × List Support)
  unaffected : List String
  /-- unaffected, but the proof hash differs: the candidate was replaced under an intact view -/
  reproved : List String
  /-- theorems of the new export the old one lacks -/
  added : List String
  /-- theorems of the old export the new one lacks -/
  removed : List String
  deriving Repr, Inhabited

def Row.isTheorem (r : Row) : Bool := r.kind == "theorem"

/-- Rows of an export by name, sorted, so a report is deterministic. -/
def Export.sortedRows (E : Export) : List Row :=
  (E.fold (fun acc _ r => acc.push r) #[]).qsort (fun a b => a.name < b.name) |>.toList

def report (old new : Export) : Report :=
  let oldRows := old.sortedRows
  let withdrawn := oldRows.filterMap fun r =>
    match new[r.name]? with
    | none => some (.removed r.name)
    | some s => if s.meaning == r.meaning then none else some (.changed r.name r.meaning s.meaning)
  let thms := oldRows.filter Row.isTheorem
  let init : Report :=
    { withdrawn, revised := [], statementCited := [], proofCited := [], unaffected := [],
      reproved := [], added := [], removed := [] }
  let rep := thms.foldl (init := init) fun rep r =>
    match new[r.name]? with
    | none => { rep with removed := r.name :: rep.removed }
    | some s =>
      let v := verdict new (candidateOf old r)
      if s.meaning != r.meaning then { rep with revised := (r.name, v) :: rep.revised }
      else match v with
        | .unaffected =>
          if s.valueHash == r.valueHash then { rep with unaffected := r.name :: rep.unaffected }
          else { rep with reproved := r.name :: rep.reproved }
        | .statementCited d => { rep with statementCited := (r.name, d) :: rep.statementCited }
        | .proofCited d => { rep with proofCited := (r.name, d) :: rep.proofCited }
  let added := new.sortedRows.filterMap fun r =>
    if r.isTheorem && !old.contains r.name then some r.name else none
  { rep with
    revised := rep.revised.reverse, statementCited := rep.statementCited.reverse,
    proofCited := rep.proofCited.reverse, unaffected := rep.unaffected.reverse,
    reproved := rep.reproved.reverse, removed := rep.removed.reverse, added }

end Journal

end
