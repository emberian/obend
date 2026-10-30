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
The closure is a depth-first walk whose fuel is spent only on a name not yet visited, and is more
than the names it can find (the seeds plus every meaning-edge target of the export, with
repetition). `mem_closure_iff`: a name is in `closure E seeds` exactly when a finite meaning-edge
path from a seed ends at it. Until 2026-10-30 the fuel was `rows + seeds + 1` and every pop spent
one, repeats included, so a convergent graph could stop the walk with reachable names unvisited
(Kimi's seven-row graph, `tools/journal/ClosureTooth.lean`, by `decide`).

A MEANING is a 64-bit structural hash (`mixHash`, not cryptographic), so equal meanings are evidence
that two declarations mean the same, not proof. `holdsIn` compares hashes: a support it calls
holding may have changed under a collision, and an UNAFFECTED verdict inherits that. Nothing here
was chosen to resist an adversary who picks the edit; an accidental collision on one name between
two exports is the 2^-64 kind of event, a crafted one is not ruled out. A dead support is exact
(different hashes are different terms); only "holds" carries the caveat.
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

/-- What the walk asks of its visited set: membership, insertion, and the two laws the
completeness proof reads. -/
structure VisitSet (α σ : Type) where
  empty : σ
  contains : σ → α → Bool
  insert : σ → α → σ
  contains_empty : ∀ a, contains empty a = false
  contains_insert : ∀ s a b, contains (insert s a) b = true ↔ b = a ∨ contains s b = true

/-- The visited set the journal runs on. -/
def hashVisit : VisitSet String (Std.HashSet String) where
  empty := {}
  contains s a := s.contains a
  insert s a := s.insert a
  contains_empty _ := Std.HashSet.contains_empty
  contains_insert s a b := by
    show (s.insert a).contains b = true ↔ _
    rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    exact ⟨fun h => h.imp_left Eq.symm, fun h => h.imp_left Eq.symm⟩

/-- A list as a visited set: what a kernel `decide` can evaluate (the hash set's `String.hash` is
opaque to the kernel). -/
def listVisit (α : Type) [DecidableEq α] : VisitSet α (List α) where
  empty := []
  contains s a := s.contains a
  insert s a := a :: s
  contains_empty _ := rfl
  contains_insert s a b := by simp

section Walk
variable {α σ : Type}

/-- Depth-first from `stack`, with `seen` the names already in `acc`. A pop first skips the names
already seen (`dropWhile`), so `fuel` pays for a NEW name only: the walk stops early only if more
names are new than `fuel`, and `closureBy` gives it more fuel than there are names to find. -/
def walk (V : VisitSet α σ) (edges : α → List α) :
    Nat → List α → σ → List α → List α
  | 0, _, _, acc => acc.reverse
  | fuel + 1, stack, seen, acc =>
    match stack.dropWhile (V.contains seen) with
    | [] => acc.reverse
    | n :: rest => walk V edges fuel (edges n ++ rest) (V.insert seen n) (n :: acc)

/-- Everything reachable from `seeds` along `edges`, `seeds` included, in depth-first preorder.
`bound` is the length of a list holding every edge target (`closureBy_complete`): with
`seeds.length + bound + 1` fuel the walk cannot run dry before its stack does. -/
def closureBy (V : VisitSet α σ) (edges : α → List α) (bound : Nat) (seeds : List α) : List α :=
  walk V edges (seeds.length + bound + 1) seeds V.empty []

/-- `x` is reached from `seeds` by a finite path along `edges`: a seed, or one edge on from a
reached name. -/
inductive Reach (edges : α → List α) (seeds : List α) : α → Prop
  | seed {s : α} : s ∈ seeds → Reach edges seeds s
  | step {n m : α} : Reach edges seeds n → m ∈ edges n → Reach edges seeds m

/-! ## The walk is complete and sound -/

theorem dropWhile_mem {p : α → Bool} : ∀ {l : List α} {x : α},
    x ∈ l → x ∈ l.dropWhile p ∨ p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rw [List.dropWhile_cons]
    by_cases hy : p y = true
    · simp only [hy, if_true]
      rcases List.mem_cons.1 h with rfl | h
      · exact .inr hy
      · exact dropWhile_mem h
    · simp only [hy]
      exact .inl h

theorem mem_of_mem_dropWhile {p : α → Bool} : ∀ {l : List α} {x : α},
    x ∈ l.dropWhile p → x ∈ l
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile h)
    · exact h

theorem head_dropWhile {p : α → Bool} {l : List α} {n : α} {rest : List α}
    (h : l.dropWhile p = n :: rest) : p n = false := by
  have := List.head_dropWhile_not p (l := l) (by simp [h])
  simpa [h] using this

/-- Strictly fewer elements pass a filter that is weaker everywhere and fails somewhere it held. -/
theorem length_filter_lt {p q : α → Bool} : ∀ {U : List α},
    (∀ x ∈ U, q x = true → p x = true) → (∃ y ∈ U, p y = true ∧ q y = false) →
    (U.filter q).length < (U.filter p).length
  | [], _, ⟨_, hy, _⟩ => by simp at hy
  | u :: us, hqp, ⟨y, hy, hpy, hqy⟩ => by
    have hqp' : ∀ x ∈ us, q x = true → p x = true := fun x hx => hqp x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.1 hy with rfl | hy'
    · have := List.length_filter_le q us
      have hle : (us.filter q).length ≤ (us.filter p).length := by
        clear hy hqp hpy hqy this
        induction us with
        | nil => simp
        | cons v vs ih =>
          have hv := hqp' v (by simp)
          simp only [List.filter_cons]
          split <;> split <;> simp_all <;> omega
      simp [hpy, hqy]
      omega
    · have ih := length_filter_lt hqp' ⟨y, hy', hpy, hqy⟩
      simp only [List.filter_cons]
      have hu := hqp u (by simp)
      split <;> split <;> simp_all <;> omega

/-- The names of `U` not yet seen: the measure the walk's fuel outlasts. -/
def unseen (V : VisitSet α σ) (seen : σ) (U : List α) : Nat :=
  (U.filter (fun x => !V.contains seen x)).length

theorem walk_complete (V : VisitSet α σ) (edges : α → List α) (U : List α)
    (hU : ∀ n, ∀ m ∈ edges n, m ∈ U) :
    ∀ (fuel : Nat) (stack : List α) (seen : σ) (acc : List α),
      (∀ x, V.contains seen x = true ↔ x ∈ acc) →
      (∀ x ∈ stack, x ∈ U) →
      (∀ x ∈ acc, ∀ y ∈ edges x, y ∈ acc ∨ y ∈ stack) →
      unseen V seen U < fuel →
      ∃ R : List α, walk V edges fuel stack seen acc = R.reverse ∧ (∀ x ∈ acc, x ∈ R) ∧
        (∀ x ∈ stack, x ∈ R) ∧ (∀ x ∈ R, ∀ y ∈ edges x, y ∈ R)
  | 0, _, _, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, stack, seen, acc, hseen, hstack, hclosed, hf => by
    -- a name of `stack` the pop skips is already in `acc`
    have hskip : ∀ x ∈ stack, x ∈ stack.dropWhile (V.contains seen) ∨ x ∈ acc := fun x hx =>
      (dropWhile_mem hx).imp_right (hseen x).1
    unfold walk
    split
    · rename_i hnil
      refine ⟨acc, rfl, fun x hx => hx, fun x hx => ?_, fun x hx y hy => ?_⟩
      · simpa [hnil] using hskip x hx
      · rcases hclosed x hx y hy with h | h
        · exact h
        · simpa [hnil] using hskip y h
    · rename_i n rest hcons
      have hn : V.contains seen n = false := head_dropWhile hcons
      have hnU : n ∈ U := hstack n (mem_of_mem_dropWhile (by rw [hcons]; simp))
      have hrest : ∀ x ∈ rest, x ∈ stack := fun x hx =>
        mem_of_mem_dropWhile (by rw [hcons]; exact List.mem_cons_of_mem _ hx)
      obtain ⟨R, hw, hacc, hst, hR⟩ := walk_complete V edges U hU fuel (edges n ++ rest)
        (V.insert seen n) (n :: acc)
        (fun x => by rw [V.contains_insert, hseen]; simp)
        (fun x hx => by
          rcases List.mem_append.1 hx with h | h
          · exact hU n x h
          · exact hstack x (hrest x h))
        (fun x hx y hy => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact .inr (List.mem_append_left _ hy)
          · rcases hclosed x hx y hy with h | h
            · exact .inl (List.mem_cons_of_mem _ h)
            · rcases hskip y h with h | h
              · rw [hcons] at h
                rcases List.mem_cons.1 h with rfl | h
                · exact .inl (by simp)
                · exact .inr (List.mem_append_right _ h)
              · exact .inl (List.mem_cons_of_mem _ h))
        (by
          have : unseen V (V.insert seen n) U < unseen V seen U := by
            apply length_filter_lt
            · intro x _ hx
              simp only [Bool.not_eq_true'] at hx ⊢
              cases h : V.contains seen x
              · rfl
              · have := (V.contains_insert seen n x).2 (.inr h)
                simp_all
            · refine ⟨n, hnU, by simp [hn], ?_⟩
              simp [(V.contains_insert seen n n).2 (.inl rfl)]
          omega)
      refine ⟨R, hw, fun x hx => hacc x (List.mem_cons_of_mem _ hx), fun x hx => ?_, hR⟩
      rcases hskip x hx with h | h
      · rw [hcons] at h
        rcases List.mem_cons.1 h with rfl | h
        · exact hacc x (by simp)
        · exact hst x (List.mem_append_right _ h)
      · exact hacc x (List.mem_cons_of_mem _ h)

theorem walk_sound (V : VisitSet α σ) (edges : α → List α) (seeds : List α) :
    ∀ (fuel : Nat) (stack : List α) (seen : σ) (acc : List α),
      (∀ x ∈ acc, Reach edges seeds x) → (∀ x ∈ stack, Reach edges seeds x) →
      ∀ x ∈ walk V edges fuel stack seen acc, Reach edges seeds x
  | 0, _, _, _, hacc, _ => by simpa [walk] using hacc
  | fuel + 1, stack, seen, acc, hacc, hstack => by
    unfold walk
    split
    · simpa using hacc
    · rename_i n rest hcons
      have hn : Reach edges seeds n := hstack n (mem_of_mem_dropWhile (by rw [hcons]; simp))
      refine walk_sound V edges seeds fuel _ _ _ (fun x hx => ?_) (fun x hx => ?_)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hn
        · exact hacc x hx
      · rcases List.mem_append.1 hx with h | h
        · exact .step hn h
        · exact hstack x (mem_of_mem_dropWhile (by rw [hcons]; exact List.mem_cons_of_mem _ h))

/-- CLOSURE COMPLETENESS AND SOUNDNESS. When every edge target is in a list `T` of length at most
`bound`, a name is in `closureBy` exactly when a finite path along `edges` from a seed ends at it. -/
theorem mem_closureBy_iff (V : VisitSet α σ) (edges : α → List α) (bound : Nat) (seeds : List α)
    (T : List α) (hT : ∀ n, ∀ m ∈ edges n, m ∈ T) (hb : T.length ≤ bound) (x : α) :
    x ∈ closureBy V edges bound seeds ↔ Reach edges seeds x := by
  constructor
  · exact walk_sound V edges seeds _ _ _ _ (by simp) (fun _ h => .seed h) x
  · intro hx
    obtain ⟨R, hw, -, hst, hR⟩ := walk_complete V edges (seeds ++ T)
      (fun n m h => List.mem_append_right _ (hT n m h)) (seeds.length + bound + 1) seeds V.empty []
      (by simp [V.contains_empty]) (fun x h => List.mem_append_left _ h) (by simp)
      (by
        have : unseen V V.empty (seeds ++ T) ≤ (seeds ++ T).length := List.length_filter_le _ _
        simp at this; omega)
    unfold closureBy
    rw [hw, List.mem_reverse]
    induction hx with
    | seed h => exact hst _ h
    | step _ hm ih => exact hR _ ih _ hm

end Walk

/-! ## The closure of an export -/

/-- One step of meaning edges in `E`: a name not in `E` (toolchain background, or vanished) is kept
as a name and not followed. -/
def edgesIn (E : Export) (n : String) : List String :=
  match E[n]? with
  | some r => r.meaningEdges
  | none => []

/-- Every meaning-edge target in `E`, with repetition: its length bounds the names the closure can
find beyond its seeds. -/
def Export.targets (E : Export) : List String :=
  E.toList.flatMap fun p => p.2.meaningEdges

/-- `closure` with the bound computed once by the caller (`report` reads every theorem of one
export, and `E.targets` is a pass over all of it). -/
def closureWithin (E : Export) (bound : Nat) (seeds : List String) : List String :=
  closureBy hashVisit (edgesIn E) bound seeds

/-- Every constant reachable from `seeds` along meaning edges in `E`, `seeds` included, in
depth-first preorder. `mem_closure_iff`: exactly the names a finite meaning-edge path from a seed
ends at. -/
def closure (E : Export) (seeds : List String) : List String :=
  closureWithin E E.targets.length seeds

theorem edgesIn_sub_targets (E : Export) (n : String) : ∀ m ∈ edgesIn E n, m ∈ E.targets := by
  intro m hm
  unfold edgesIn at hm
  split at hm
  · rename_i r hr
    exact List.mem_flatMap.2 ⟨(n, r), Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hr, hm⟩
  · simp at hm

/-- CLOSURE COMPLETENESS (and soundness): a name is in `closureWithin E bound seeds`, for any
`bound` at least `E.targets.length`, exactly when a finite meaning-edge path in `E` from a seed ends
at it. -/
theorem mem_closureWithin_iff (E : Export) (bound : Nat) (hb : E.targets.length ≤ bound)
    (seeds : List String) (x : String) :
    x ∈ closureWithin E bound seeds ↔ Reach (edgesIn E) seeds x :=
  mem_closureBy_iff hashVisit (edgesIn E) bound seeds E.targets (edgesIn_sub_targets E) hb x

theorem mem_closure_iff (E : Export) (seeds : List String) (x : String) :
    x ∈ closure E seeds ↔ Reach (edgesIn E) seeds x :=
  mem_closureWithin_iff E _ (Nat.le_refl _) seeds x

/-- Every finite meaning-edge path from a seed ends in the closure. -/
theorem closure_complete (E : Export) (seeds : List String) (x : String)
    (h : Reach (edgesIn E) seeds x) : x ∈ closure E seeds :=
  (mem_closure_iff E seeds x).2 h

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
def candidateWithin (old : Export) (bound : Nat) (r : Row) : Candidate :=
  let meaningIn (n : String) : UInt64 := match old[n]? with
    | some s => s.meaning
    | none => 0
  let stmtNames := closureWithin old bound r.typeCites
  let stmtSet : Std.HashSet String := stmtNames.foldl (·.insert ·) {}
  let proofNames := (closureWithin old bound r.valueCites).filter (fun n => !stmtSet.contains n)
  { name := r.name
    stmtSupports := stmtNames.map fun n => .stmt n (meaningIn n)
    proofSupports := proofNames.map fun n => .proof n (meaningIn n) }

/-- The candidate of theorem `r` in export `old`, its supports closed by `closure`. -/
def candidateOf (old : Export) (r : Row) : Candidate :=
  candidateWithin old old.targets.length r

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
  let bound := old.targets.length
  let init : Report :=
    { withdrawn, revised := [], statementCited := [], proofCited := [], unaffected := [],
      reproved := [], added := [], removed := [] }
  let rep := thms.foldl (init := init) fun rep r =>
    match new[r.name]? with
    | none => { rep with removed := r.name :: rep.removed }
    | some s =>
      let v := verdict new (candidateWithin old bound r)
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
