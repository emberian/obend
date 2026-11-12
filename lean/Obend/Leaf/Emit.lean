module
/-
# Obend.Leaf.Emit — the flattened object as a leaf book

A book is a list of closed first-order definitions, one per member of the flattened row, whose only
recursion goes through `self`, plus the one dispatcher that ties them. The vtable of
`Obend.Leaf.Flatten` becomes such a book (`emit`). (Until 2026-11-04 this file called the book's
target "the leaf language (Bend, checked by BendTT)"; no translation to Bend ever existed and Bend
compatibility is no longer a goal. The book is a `Core4` term run by the demand machine, and the
input of `Obend.Hardware.Compiler`; `Obend.Leaf.Static` folds it.)

* **the kind's brand is metadata**: a kind's identity (`#kind`, `Obend.Core.Brand`) is one constant
  for every instance, so it takes no slot; the book holds it as a static entry (`Book.statics`) and
  the dispatcher answers it, so `book_sound` holds for it as for every member of the row;
* **slot indices**: rows are static, so member names are positions (`Book.slots`); a definition
  records the slots its body reads through `self` (`LeafDef.reads`), which is all a leaf dispatcher
  needs to route them;
* **acyclic method definitions**: one definition per slot, `λself. body`; no definition names
  another (each `code` is closed whenever the composition is, `emit_closed`), so every recursion
  goes through `self`;
* **a dispatcher**: `Book.link`, `fix (λself. λ_. {m₀ = def₀ self, …}) {}`, the one place where
  definitions meet: the single self-recursive definition; a strict target would have to tie this knot
  with a static table, which no backend does yet;
* **thunk cells**: a member whose entry is not a λ (a computed field) is emitted as an explicit cell
  `λself. λ_. body`, forced by the dispatcher with `{}`; method fields are already values and are
  emitted as they are (`DefKind`).

`emit_sound`: the linked book is `≈b` the flattened object (`link_ahead`: the dispatcher's entries
β-reduce to the vtable's), so with `flatten_sound` every member the book computes is the member the
machine's `fix (compose …) {seed}` computes (`book_sound`).

The typing side (`typeOf`, `emit_typed`): a definition's type is the row's member type with `self` at
the record type of the row, `Self → T` for a method and `Self → {} → T` for a cell.

The shape (`emit_of_digest`): the book is a function of the composition's code (`Composition.code`,
its layers in order and its seed), so two compositions with one content address have one book, or
the hash collides.
-/
public import Obend.Leaf.Flatten
public import Obend.Core.Ty
public import Obend.Core.Brand
import all Obend.Core.Code
import all Obend.Leaf.UpTo
import all Obend.Leaf.Flatten
public section
namespace Obend.Leaf
open Obend.Core.Term
open Obend.Core.Ty (Ty Quantity Reuse)
open Obend.Equiv
open Obend.Logic
set_option autoImplicit false

/-! ## The book -/

/-- A method field (already a value) or a computed field (an explicit thunk cell). -/
inductive DefKind where
  | method
  | cell
  deriving DecidableEq, Repr

/-- The kind of a vtable entry: a λ is a method; anything else is computed, and gets a cell. -/
@[expose] def kindOf : Term → DefKind
  | .lam _ => .method
  | _ => .cell

/-- The member names a body reads as `self.m`, `self` at index `d`. -/
@[expose] def selfReads (d : Nat) : Term → List String
  | .hole _ σ => (σ.attach.map fun ⟨t, _⟩ => selfReads d t).flatten
  | .bound _ => []
  | .lam b => selfReads (d + 1) b
  | .app f a => selfReads d f ++ selfReads d a
  | .mix l u => selfReads d l ++ selfReads d u
  | .fix s i => selfReads d s ++ selfReads d i
  | .specification m e => selfReads d m ++ selfReads d e
  | .prototype s g => selfReads d s ++ selfReads d g
  | .reflect p | .metadata p | .project p | .inject _ p | .perform p | .done p => selfReads d p
  | .nat _ | .boolean _ | .label _ => []
  | .binary _ l r => selfReads d l ++ selfReads d r
  | .extend i fs => selfReads d i ++ (fs.attach.map fun ⟨f, _⟩ => selfReads d f.2).flatten
  | .record fs => (fs.attach.map fun ⟨f, _⟩ => selfReads d f.2).flatten
  | .get (.bound i) m => if i == d then [m] else []
  | .get g _ => selfReads d g
  | .ifZero v z s => selfReads d v ++ selfReads d z ++ selfReads (d + 1) s
  | .case sc arms => selfReads d sc ++ (arms.attach.map fun ⟨a, _⟩ => selfReads (d + 1) a.2).flatten
  | .ifBool c x y => selfReads d c ++ selfReads d x ++ selfReads d y
  | .split t _ f => selfReads d t ++ selfReads d f
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)

/-- One definition of the book. -/
structure LeafDef where
  member : String
  slot : Nat
  kind : DefKind
  /-- `λself. body` (method) or `λself. λ_. body` (cell); closed when the composition is -/
  code : Term
  /-- the slots the body reads through `self`, in order of first read -/
  reads : List Nat

/-- An entry of the book, in row order: a slot's definition, or a static member. The kind's brand
(`#kind`, `Obend.Core.Brand`) is static: one constant for every instance of the kind, so it is the
book's metadata, served by the dispatcher, and takes no slot. -/
inductive BookItem where
  | slot (d : LeafDef)
  | static (member : String) (value : Term)

/-- A leaf book: its entries in row order. -/
structure Book where
  items : List BookItem

@[expose] def BookItem.def? : BookItem → Option LeafDef
  | .slot d => some d
  | .static _ _ => none

@[expose] def BookItem.static? : BookItem → Option (String × Term)
  | .slot _ => none
  | .static m v => some (m, v)

/-- One definition per slot, in slot order. -/
@[expose] def Book.defs (B : Book) : List LeafDef := B.items.filterMap BookItem.def?

/-- The slot table: member names in slot order. -/
@[expose] def Book.slots (B : Book) : List String := B.defs.map (·.member)

/-- The static members (the kind's brand), with their values under `self`. -/
@[expose] def Book.statics (B : Book) : List (String × Term) := B.items.filterMap BookItem.static?

/-- The definition of a vtable entry at a slot. -/
@[expose] def emitDef (slots : List String) (i : Nat) (f : String × Term) : LeafDef where
  member := f.1
  slot := i
  kind := kindOf f.2
  code := match kindOf f.2 with
    | .method => .lam f.2
    | .cell => .lam (.lam (f.2.rename Nat.succ))
  reads := ((selfReads 0 f.2).filterMap slots.idxOf?).eraseDups

def emitDefs (slots : List String) : Nat → List (String × Term) → List LeafDef
  | _, [] => []
  | i, f :: rest => emitDef slots i f :: emitDefs slots (i + 1) rest

/-- The entries: the brand static, every other member the next slot. -/
@[expose] def emitItems (slots : List String) : Nat → List (String × Term) → List BookItem
  | _, [] => []
  | i, f :: rest =>
    if Obend.Core.Brand.isBrand f.1 then .static f.1 f.2 :: emitItems slots i rest
    else .slot (emitDef slots i f) :: emitItems slots (i + 1) rest

/-- The members that take a slot. -/
abbrev slotted (vt : List (String × Term)) : List (String × Term) := vt.filter fun f => !Obend.Core.Brand.isBrand f.1

/-- **The emitter.** -/
abbrev emitVtable (vt : List (String × Term)) : Book :=
  { items := emitItems ((slotted vt).map (·.1)) 0 vt }

/-- The book of a composition: its vtable, emitted. -/
@[expose] def emit (C : Composition) : Book := emitVtable C.vtable

/-- How the dispatcher calls a definition, under its two binders (`self` at 1). -/
abbrev LeafDef.call (d : LeafDef) : Term :=
  match d.kind with
  | .method => .app (d.code.rename (· + 2)) (.bound 1)
  | .cell => .app (.app (d.code.rename (· + 2)) (.bound 1)) (.record [])

/-- The dispatcher's entry for an item: a slot's call, or the static value. -/
abbrev BookItem.entry : BookItem → String × Term
  | .slot d => (d.member, d.call)
  | .static m v => (m, v.rename Nat.succ)

/-- **The dispatcher**: the book linked into one term, `fix (λself. λ_. {m = def self, …}) {}`, with
the static members answered from the book's metadata. -/
@[expose] def Book.link (B : Book) : Term :=
  .fix (.lam (.lam (.record (B.items.map BookItem.entry)))) (.record [])

/-! ## The book computes the vtable -/

/-- A definition's call β-reduces to its entry, as the flattened object's spec body holds it. -/
theorem call_steps (slots : List String) (i : Nat) (f : String × Term) :
    Steps (emitDef slots i f).call (f.2.rename Nat.succ) := by
  unfold LeafDef.call emitDef
  cases hk : kindOf f.2
  · simp only
    rw [show (Term.lam f.2).rename (· + 2) = .lam (f.2.rename (liftRename (· + 2))) by simp only [Term.rename]]
    refine .next (.beta _ _) ?_
    have e : (f.2.rename (liftRename (· + 2))).substitute (single (.bound 1)) = f.2.rename Nat.succ := by
      rw [Obend.Core.TermTraverse.rename_substitute, rename_eq_substitute f.2 Nat.succ]
      congr 1; funext n; cases n <;> simp [liftRename, single]
    rw [instantiate_eq, e]
    exact .refl _
  · simp only
    rw [show (Term.lam (.lam (f.2.rename Nat.succ))).rename (· + 2) =
        .lam (.lam ((f.2.rename Nat.succ).rename (liftRename (liftRename (· + 2))))) by simp only [Term.rename]]
    have e : openTerm ((f.2.rename Nat.succ).rename (liftRename (liftRename (· + 2)))) (.bound 1) (.record []) =
        f.2.rename Nat.succ := by
      unfold openTerm
      rw [Obend.Core.TermTraverse.rename_comp, Obend.Core.TermTraverse.rename_substitute,
        rename_eq_substitute f.2 Nat.succ]
      congr 1; funext n; cases n <;> simp [liftRename, selfSuper]
    have := beta_two ((f.2.rename Nat.succ).rename (liftRename (liftRename (· + 2)))) (.bound 1) (.record [])
    rwa [e] at this

theorem emitItems_ahead (slots : List String) :
    ∀ (i : Nat) (vt : List (String × Term)),
      ((emitItems slots i vt).map BookItem.entry).map Prod.fst = (mapFields (·.rename Nat.succ) vt).map Prod.fst ∧
      ∀ p ∈ ((emitItems slots i vt).map BookItem.entry).zip (mapFields (·.rename Nat.succ) vt),
        Ahead p.1.2 p.2.2
  | _, [] => ⟨rfl, by simp [emitItems, mapFields]⟩
  | i, f :: rest => by
    unfold emitItems
    split
    · obtain ⟨n, r⟩ := emitItems_ahead slots i rest
      simp only [mapFields, List.map_cons, List.zip_cons_cons, List.mem_cons, BookItem.entry] at n r ⊢
      refine ⟨by simp only [n], ?_⟩
      rintro p (rfl | hp)
      · exact Ahead.refl _
      · exact r p hp
    · obtain ⟨n, r⟩ := emitItems_ahead slots (i + 1) rest
      simp only [mapFields, List.map_cons, List.zip_cons_cons, List.mem_cons, BookItem.entry] at n r ⊢
      refine ⟨by simp only [emitDef, n], ?_⟩
      rintro p (rfl | hp)
      · exact Ahead.ofStepsRefl (call_steps slots i f)
      · exact r p hp

/-- **The dispatcher is the flattened object, run ahead**: each entry `def self` β-reduces to the
vtable's entry. -/
theorem link_ahead (vt : List (String × Term)) : Ahead (emitVtable vt).link (flatObject vt) := by
  obtain ⟨n, r⟩ := emitItems_ahead ((slotted vt).map (·.1)) 0 vt
  exact .fix (.lam (.lam (.record n r))) (.refl _)

/-- The linked book is `≈b` the flattened object. -/
theorem emit_sound (C : Composition) : (emit C).link ≈b C.flatten := bequiv_of_ahead (link_ahead C.vtable)

/-- **The book computes what the machine's object computes**: for a closed composition, every
member read from the linked book is `≈b` the member of `fix (compose …) {seed}`. -/
theorem book_sound (C : Composition) (hc : C.closedB = true) (m : String) :
    .get (emit C).link m ≈b .get C.object m :=
  BEquiv.trans (bequiv_of_ahead (.get m (link_ahead C.vtable))) (flatten_sound C hc m)

/-! ## Slots -/

theorem emitDefs_get (slots : List String) :
    ∀ (i : Nat) (vt : List (String × Term)) (k : Nat) (d : LeafDef), (emitDefs slots i vt)[k]? = some d →
      d.slot = i + k ∧ vt[k]?.map (·.1) = some d.member
  | _, [], _, _, h => by simp [emitDefs] at h
  | i, f :: rest, 0, d, h => by
    simp only [emitDefs, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [emitDef]
  | i, f :: rest, k + 1, d, h => by
    simp only [emitDefs, List.getElem?_cons_succ] at h
    obtain ⟨hs, hm⟩ := emitDefs_get slots (i + 1) rest k d h
    exact ⟨by omega, by simpa using hm⟩

theorem emitItems_defs (slots : List String) :
    ∀ (i : Nat) (vt : List (String × Term)),
      (emitItems slots i vt).filterMap BookItem.def? = emitDefs slots i (slotted vt)
  | _, [] => rfl
  | i, f :: rest => by
    unfold emitItems
    split
    · rename_i hb
      simp only [List.filterMap_cons, BookItem.def?, slotted, List.filter_cons, hb, Bool.not_true,
        Bool.false_eq_true, ite_false]
      exact emitItems_defs slots i rest
    · rename_i hb
      have hb' : Obend.Core.Brand.isBrand f.1 = false := by simpa using hb
      simp only [List.filterMap_cons, BookItem.def?, slotted, List.filter_cons, hb', Bool.not_false, ite_true,
        emitDefs, List.cons.injEq, true_and]
      exact emitItems_defs slots (i + 1) rest

/-- **Slot indices**: the `k`-th definition is slot `k` and serves the `k`-th member of the slot
table, the row without its static members. -/
theorem emit_slot (C : Composition) (k : Nat) (d : LeafDef) (h : (emit C).defs[k]? = some d) :
    d.slot = k ∧ (emit C).slots[k]? = some d.member := by
  simp only [Book.defs, emit, emitVtable, emitItems_defs] at h
  obtain ⟨hs, hm⟩ := emitDefs_get _ 0 _ k d h
  refine ⟨by omega, ?_⟩
  simp only [Book.slots, Book.defs, emit, emitVtable, emitItems_defs, List.getElem?_map, h, Option.map_some]

/-- A well-formed book: every definition is closed, so no definition names another and the
dispatcher is the only place they meet. -/
abbrev Book.closedB (B : Book) : Bool := B.defs.all fun d => Obend.Law.closedB d.code

/-! ## Escaping-`self` syntactic guard (`checkNoEscapingSelf`) & `reads` frame soundness -/

/-- Leaf expression AST (`Core4` `Term` under `self` at De Bruijn binder depth `d`). -/
abbrev LeafExpr := Term

/-- Runtime `self` record environment mapping member names to closed `Core4` terms. -/
abbrev SelfEnv := List (String × Term)

/-- Non-`self` check on a bare bound variable `.bound i` when `self` is at De Bruijn depth `d`. -/
def checkBoundNotSelf (d i : Nat) : Bool :=
  i != d

/-- Syntactic predicate recognizing `.bound _` targets in `.get target field`. -/
def isBoundTerm : Term → Bool
  | .bound _ => true
  | _ => false

mutual
  /-- Executable syntactic guard (`checkNoEscapingSelfAt d e`):
  Accepts `self` (`.bound d`) **only** as the immediate target of a static field projection
  `.get (.bound d) field`, rejecting bare `.bound d` anywhere else. -/
  def checkNoEscapingSelfAt (d : Nat) : LeafExpr → Bool
    | .hole _ σ => checkNoEscapingSelfList d σ
    | .bound i => checkBoundNotSelf d i
    | .lam b => checkNoEscapingSelfAt (d + 1) b
    | .app f a | .mix f a | .fix f a | .specification f a | .prototype f a
    | .binary _ f a | .split f _ a =>
      checkNoEscapingSelfAt d f && checkNoEscapingSelfAt d a
    | .reflect p | .metadata p | .project p | .inject _ p | .perform p | .done p =>
      checkNoEscapingSelfAt d p
    | .nat _ | .boolean _ | .label _ => true
    | .extend i fs => checkNoEscapingSelfAt d i && checkNoEscapingSelfFields d fs
    | .record fs => checkNoEscapingSelfFields d fs
    | .get g _ => isBoundTerm g || checkNoEscapingSelfAt d g
    | .ifZero v z s =>
      checkNoEscapingSelfAt d v && checkNoEscapingSelfAt d z && checkNoEscapingSelfAt (d + 1) s
    | .case sc arms =>
      checkNoEscapingSelfAt d sc && checkNoEscapingSelfFields (d + 1) arms
    | .ifBool c x y =>
      checkNoEscapingSelfAt d c && checkNoEscapingSelfAt d x && checkNoEscapingSelfAt d y

  def checkNoEscapingSelfList (d : Nat) : List Term → Bool
    | [] => true
    | t :: ts => checkNoEscapingSelfAt d t && checkNoEscapingSelfList d ts

  def checkNoEscapingSelfFields (d : Nat) : List (String × Term) → Bool
    | [] => true
    | (_, t) :: fs => checkNoEscapingSelfAt d t && checkNoEscapingSelfFields d fs
end

/-- Top-level syntactic guard rejecting bare escaping `self` (`.bound 0` outside `.get (.bound 0) m`). -/
def checkNoEscapingSelf (e : LeafExpr) : Bool :=
  checkNoEscapingSelfAt 0 e

/-- Alias matching the `selfProjOnly` naming convention. -/
abbrev selfProjOnly : LeafExpr → Bool := checkNoEscapingSelf

/-- Proposition witnessing that `e : LeafExpr` contains no bare escaping `self`. -/
def NoEscapingSelf (e : LeafExpr) : Prop :=
  checkNoEscapingSelf e = true

/-- Check that an emitted `LeafDef`'s body contains no bare escaping `self`. -/
def checkLeafDefNoEscapingSelf (d : LeafDef) : Bool :=
  match d.kind, d.code with
  | .method, .lam body => checkNoEscapingSelfAt 0 body
  | .cell, .lam (.lam body) => checkNoEscapingSelfAt 1 body
  | _, _ => false

/-- Check that every slot definition in a `Book` satisfies `checkLeafDefNoEscapingSelf`. -/
def Book.noEscapingSelf (B : Book) : Bool :=
  B.defs.all checkLeafDefNoEscapingSelf

/-- Look up field `m` in `env : SelfEnv` (first-match semantics matching `Core4` `Step.field`). -/
def lookupSelfEnv (env : SelfEnv) (m : String) : Option Term :=
  (env.find? (fun field => field.1 == m)).map (·.2)

/-- Resolve static projection `self.m` at binder depth `d` against `env`.
Missing fields map to stuck `.get (.record []) m`, matching `Core4` missing-field semantics. -/
def resolveSelfFieldAt (d : Nat) (env : SelfEnv) (m : String) : Term :=
  match lookupSelfEnv env m with
  | some v => v.rename (· + d)
  | none => .get (.record []) m

/-- Local variable substitution for `locals : List Term` (`self` sits at index `locals.length`). -/
def localsSubst (locals : List Term) (i : Nat) : Term :=
  if i < locals.length then
    locals[i]?.getD (.bound i)
  else
    .bound (i - 1)

mutual
  /-- Bind local variables `σ` and `self` environment `env` (at De Bruijn depth `d`) across `e`:
  - `.get (.bound i) m` with `i == d` resolves `m` from `env`,
  - bare `.bound i` with `i == d` (escaping `self`) substitutes the entire `.record env`. -/
  def bindLeafEnvAt (d : Nat) (σ : Nat → Term) (env : SelfEnv) : LeafExpr → Term
    | .hole n ts => .hole n (bindLeafEnvList d σ env ts)
    | .bound i =>
      if i == d then (Term.record env).rename (· + d)
      else σ i
    | .lam b => .lam (bindLeafEnvAt (d + 1) (liftSubstitution σ) env b)
    | .app f a => .app (bindLeafEnvAt d σ env f) (bindLeafEnvAt d σ env a)
    | .mix l u => .mix (bindLeafEnvAt d σ env l) (bindLeafEnvAt d σ env u)
    | .fix s i => .fix (bindLeafEnvAt d σ env s) (bindLeafEnvAt d σ env i)
    | .specification m e => .specification (bindLeafEnvAt d σ env m) (bindLeafEnvAt d σ env e)
    | .prototype s g => .prototype (bindLeafEnvAt d σ env s) (bindLeafEnvAt d σ env g)
    | .reflect p => .reflect (bindLeafEnvAt d σ env p)
    | .metadata p => .metadata (bindLeafEnvAt d σ env p)
    | .project p => .project (bindLeafEnvAt d σ env p)
    | .nat v => .nat v
    | .boolean b => .boolean b
    | .label s => .label s
    | .binary op l r => .binary op (bindLeafEnvAt d σ env l) (bindLeafEnvAt d σ env r)
    | .extend i fs => .extend (bindLeafEnvAt d σ env i) (bindLeafEnvFields d σ env fs)
    | .record fs => .record (bindLeafEnvFields d σ env fs)
    | .get (.bound i) m =>
      if i == d then resolveSelfFieldAt d env m
      else .get (σ i) m
    | .get g m => .get (bindLeafEnvAt d σ env g) m
    | .ifZero v z s =>
      .ifZero (bindLeafEnvAt d σ env v) (bindLeafEnvAt d σ env z)
        (bindLeafEnvAt (d + 1) (liftSubstitution σ) env s)
    | .inject tag p => .inject tag (bindLeafEnvAt d σ env p)
    | .case sc arms =>
      .case (bindLeafEnvAt d σ env sc) (bindLeafEnvFields (d + 1) (liftSubstitution σ) env arms)
    | .ifBool c x y =>
      .ifBool (bindLeafEnvAt d σ env c) (bindLeafEnvAt d σ env x) (bindLeafEnvAt d σ env y)
    | .perform p => .perform (bindLeafEnvAt d σ env p)
    | .done p => .done (bindLeafEnvAt d σ env p)
    | .split t ns f => .split (bindLeafEnvAt d σ env t) ns (bindLeafEnvAt d σ env f)

  def bindLeafEnvList (d : Nat) (σ : Nat → Term) (env : SelfEnv) : List Term → List Term
    | [] => []
    | t :: ts => bindLeafEnvAt d σ env t :: bindLeafEnvList d σ env ts

  def bindLeafEnvFields (d : Nat) (σ : Nat → Term) (env : SelfEnv) :
      List (String × Term) → List (String × Term)
    | [] => []
    | (k, t) :: fs => (k, bindLeafEnvAt d σ env t) :: bindLeafEnvFields d σ env fs
end

/-- Bind local variable bindings `locals` (`self` at depth `locals.length`) and `self` record `env`. -/
def bindLeafEnv (locals : List Term) (env : SelfEnv) (e : LeafExpr) : Term :=
  bindLeafEnvAt locals.length (localsSubst locals) env e

/-- Evaluate `e : LeafExpr` under local bindings `locals` and `self` environment `env` for up to
`fuel` steps of the `Core4` reference operational semantics (`Obend.Law.run`). -/
def evalLeafExpr (fuel : Nat) (locals : List Term) (env : SelfEnv) (e : LeafExpr) : Option Term :=
  Obend.Law.run fuel (bindLeafEnv locals env e)

private theorem attach_map_eq_map_emit {α β : Type} (l : List α) (g : α → β) :
    (l.attach.map fun ⟨x, _⟩ => g x) = l.map g := by
  conv => rhs; rw [← List.attach_map_subtype_val l]
  rw [List.map_map]; rfl

private theorem selfReads_get_nonBound {d : Nat} {g : Term} {m : String}
    (hnb : isBoundTerm g = false) :
    selfReads d (.get g m) = selfReads d g := by
  cases g <;> first | contradiction | simp [selfReads]

private theorem bindLeafEnvAt_get_nonBound (d : Nat) (σ : Nat → Term) (env : SelfEnv)
    {g : Term} (m : String) (hnb : isBoundTerm g = false) :
    bindLeafEnvAt d σ env (.get g m) = .get (bindLeafEnvAt d σ env g) m := by
  cases g <;> first | contradiction | simp [bindLeafEnvAt]

mutual
  /-- **Core Frame Congruence Lemma (`bindLeafEnvAt_congr_of_noEscapingSelf`)**:
  Whenever `checkNoEscapingSelfAt d e = true` and `env₁, env₂` agree on every member in `selfReads d e`,
  binding `env₁` vs `env₂` at depth `d` under identical local bindings `σ` yields the exact same `Term`. -/
  theorem bindLeafEnvAt_congr_of_noEscapingSelf :
      ∀ (e : LeafExpr) (d : Nat) (σ : Nat → Term) {env₁ env₂ : SelfEnv},
        checkNoEscapingSelfAt d e = true →
        (∀ m ∈ selfReads d e, lookupSelfEnv env₁ m = lookupSelfEnv env₂ m) →
        bindLeafEnvAt d σ env₁ e = bindLeafEnvAt d σ env₂ e
    | .hole n ts, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo
      simp only [selfReads, attach_map_eq_map_emit ts (fun t => selfReads d t)] at hAg
      simp only [bindLeafEnvAt, Term.hole.injEq, true_and]
      exact bindLeafEnvList_congr_of_noEscapingSelf ts d σ hNo hAg
    | .bound i, d, σ, _, _, hNo, _ => by
      simp only [checkNoEscapingSelfAt, checkBoundNotSelf, bne_iff_ne] at hNo
      have hbeq : (i == d) = false := beq_eq_false_iff_ne.mpr hNo
      simp [bindLeafEnvAt, hbeq]
    | .lam b, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo
      simp only [selfReads] at hAg
      simp [bindLeafEnvAt, bindLeafEnvAt_congr_of_noEscapingSelf b (d + 1) (liftSubstitution σ) hNo hAg]
    | .app f a, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf f d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvAt_congr_of_noEscapingSelf a d σ hNo.2 (fun m hm => hAg m (.inr hm))]
    | .mix l u, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf l d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvAt_congr_of_noEscapingSelf u d σ hNo.2 (fun m hm => hAg m (.inr hm))]
    | .fix s i, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf s d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvAt_congr_of_noEscapingSelf i d σ hNo.2 (fun m hm => hAg m (.inr hm))]
    | .specification m e, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf m d σ hNo.1 (fun m' hm => hAg m' (.inl hm)),
        bindLeafEnvAt_congr_of_noEscapingSelf e d σ hNo.2 (fun m' hm => hAg m' (.inr hm))]
    | .prototype s g, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf s d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvAt_congr_of_noEscapingSelf g d σ hNo.2 (fun m hm => hAg m (.inr hm))]
    | .reflect p, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo; simp only [selfReads] at hAg
      simp [bindLeafEnvAt, bindLeafEnvAt_congr_of_noEscapingSelf p d σ hNo hAg]
    | .metadata p, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo; simp only [selfReads] at hAg
      simp [bindLeafEnvAt, bindLeafEnvAt_congr_of_noEscapingSelf p d σ hNo hAg]
    | .project p, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo; simp only [selfReads] at hAg
      simp [bindLeafEnvAt, bindLeafEnvAt_congr_of_noEscapingSelf p d σ hNo hAg]
    | .nat _, _, _, _, _, _, _ => rfl
    | .boolean _, _, _, _, _, _, _ => rfl
    | .label _, _, _, _, _, _, _ => rfl
    | .binary op l r, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf l d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvAt_congr_of_noEscapingSelf r d σ hNo.2 (fun m hm => hAg m (.inr hm))]
    | .extend i fs, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, attach_map_eq_map_emit fs (fun f : String × Term => selfReads d f.2),
        List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf i d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvFields_congr_of_noEscapingSelf fs d σ hNo.2 (fun m hm => hAg m (.inr hm))]
    | .record fs, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo
      simp only [selfReads, attach_map_eq_map_emit fs (fun f : String × Term => selfReads d f.2)] at hAg
      simp [bindLeafEnvAt, bindLeafEnvFields_congr_of_noEscapingSelf fs d σ hNo hAg]
    | .get g m, d, σ, env₁, env₂, hNo, hAg => by
      cases hbg : isBoundTerm g
      · simp only [checkNoEscapingSelfAt, hbg, Bool.false_or] at hNo
        rw [selfReads_get_nonBound hbg] at hAg
        rw [bindLeafEnvAt_get_nonBound d σ env₁ m hbg, bindLeafEnvAt_get_nonBound d σ env₂ m hbg]
        rw [bindLeafEnvAt_congr_of_noEscapingSelf g d σ hNo hAg]
      · cases g <;> try contradiction
        rename_i i
        by_cases hid : (i == d) = true
        · simp only [selfReads, hid, ite_true, List.mem_singleton] at hAg
          simp [bindLeafEnvAt, hid, resolveSelfFieldAt, hAg m rfl]
        · simp [bindLeafEnvAt, hid]
    | .ifZero v z s, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf v d σ hNo.1.1 (fun m hm => hAg m (.inl (.inl hm))),
        bindLeafEnvAt_congr_of_noEscapingSelf z d σ hNo.1.2 (fun m hm => hAg m (.inl (.inr hm))),
        bindLeafEnvAt_congr_of_noEscapingSelf s (d + 1) (liftSubstitution σ) hNo.2
          (fun m hm => hAg m (.inr hm))]
    | .inject tag p, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo; simp only [selfReads] at hAg
      simp [bindLeafEnvAt, bindLeafEnvAt_congr_of_noEscapingSelf p d σ hNo hAg]
    | .case sc arms, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads,
        attach_map_eq_map_emit arms (fun a : String × Term => selfReads (d + 1) a.2),
        List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf sc d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvFields_congr_of_noEscapingSelf arms (d + 1) (liftSubstitution σ) hNo.2
          (fun m hm => hAg m (.inr hm))]
    | .ifBool c x y, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf c d σ hNo.1.1 (fun m hm => hAg m (.inl (.inl hm))),
        bindLeafEnvAt_congr_of_noEscapingSelf x d σ hNo.1.2 (fun m hm => hAg m (.inl (.inr hm))),
        bindLeafEnvAt_congr_of_noEscapingSelf y d σ hNo.2 (fun m hm => hAg m (.inr hm))]
    | .perform p, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo; simp only [selfReads] at hAg
      simp [bindLeafEnvAt, bindLeafEnvAt_congr_of_noEscapingSelf p d σ hNo hAg]
    | .done p, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt] at hNo; simp only [selfReads] at hAg
      simp [bindLeafEnvAt, bindLeafEnvAt_congr_of_noEscapingSelf p d σ hNo hAg]
    | .split t ns f, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfAt, Bool.and_eq_true] at hNo
      simp only [selfReads, List.mem_append] at hAg
      simp [bindLeafEnvAt,
        bindLeafEnvAt_congr_of_noEscapingSelf t d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvAt_congr_of_noEscapingSelf f d σ hNo.2 (fun m hm => hAg m (.inr hm))]

  theorem bindLeafEnvList_congr_of_noEscapingSelf :
      ∀ (ts : List Term) (d : Nat) (σ : Nat → Term) {env₁ env₂ : SelfEnv},
        checkNoEscapingSelfList d ts = true →
        (∀ m ∈ (ts.map (selfReads d)).flatten, lookupSelfEnv env₁ m = lookupSelfEnv env₂ m) →
        bindLeafEnvList d σ env₁ ts = bindLeafEnvList d σ env₂ ts
    | [], _, _, _, _, _, _ => rfl
    | t :: ts, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfList, Bool.and_eq_true] at hNo
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at hAg
      simp [bindLeafEnvList,
        bindLeafEnvAt_congr_of_noEscapingSelf t d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvList_congr_of_noEscapingSelf ts d σ hNo.2 (fun m hm => hAg m (.inr hm))]

  theorem bindLeafEnvFields_congr_of_noEscapingSelf :
      ∀ (fs : List (String × Term)) (d : Nat) (σ : Nat → Term) {env₁ env₂ : SelfEnv},
        checkNoEscapingSelfFields d fs = true →
        (∀ m ∈ (fs.map (fun f => selfReads d f.2)).flatten, lookupSelfEnv env₁ m = lookupSelfEnv env₂ m) →
        bindLeafEnvFields d σ env₁ fs = bindLeafEnvFields d σ env₂ fs
    | [], _, _, _, _, _, _ => rfl
    | (k, t) :: fs, d, σ, _, _, hNo, hAg => by
      simp only [checkNoEscapingSelfFields, Bool.and_eq_true] at hNo
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at hAg
      simp [bindLeafEnvFields,
        bindLeafEnvAt_congr_of_noEscapingSelf t d σ hNo.1 (fun m hm => hAg m (.inl hm)),
        bindLeafEnvFields_congr_of_noEscapingSelf fs d σ hNo.2 (fun m hm => hAg m (.inr hm))]
end

/-- **Frame Soundness at Arbitrary Binder Depth (`leafExpr_reads_frame_sound_at`)**:
For any `e : LeafExpr` with `checkNoEscapingSelfAt locals.length e = true`, evaluating `e` on two
`self` environments `env₁, env₂` that agree on every field in `selfReads locals.length e` (under
identical local variable bindings `locals`) produces the exact same result. -/
theorem leafExpr_reads_frame_sound_at
    (fuel : Nat) (locals : List Term) (env₁ env₂ : SelfEnv) (e : LeafExpr)
    (hNoEscape : checkNoEscapingSelfAt locals.length e = true)
    (hAgree : ∀ m ∈ selfReads locals.length e, lookupSelfEnv env₁ m = lookupSelfEnv env₂ m) :
    evalLeafExpr fuel locals env₁ e = evalLeafExpr fuel locals env₂ e := by
  unfold evalLeafExpr bindLeafEnv
  rw [bindLeafEnvAt_congr_of_noEscapingSelf e locals.length (localsSubst locals) hNoEscape hAgree]

/-- **Top-Level `LeafExpr` Frame Soundness (`leafExpr_reads_frame_sound`)**:
For any `e : LeafExpr` with `checkNoEscapingSelf e = true`, evaluating `e` on two `self`
environments `env₁, env₂` that agree on every field in `selfReads 0 e` produces the exact same result. -/
theorem leafExpr_reads_frame_sound
    (fuel : Nat) (env₁ env₂ : SelfEnv) (e : LeafExpr)
    (hNoEscape : checkNoEscapingSelf e = true)
    (hAgree : ∀ m ∈ selfReads 0 e, lookupSelfEnv env₁ m = lookupSelfEnv env₂ m) :
    evalLeafExpr fuel [] env₁ e = evalLeafExpr fuel [] env₂ e :=
  leafExpr_reads_frame_sound_at fuel [] env₁ env₂ e hNoEscape hAgree

/-- Check that every projected `self.m` member read in `e` resolves to a slot in `slots`. -/
def checkSelfReadsInSlots (slots : List String) (e : LeafExpr) : Bool :=
  (selfReads 0 e).all (fun m => slots.contains m)

/-- Two `self` environments agree on all slot indices listed in `reads : List Nat`. -/
def AgreeOnSlotReads (slots : List String) (reads : List Nat) (env₁ env₂ : SelfEnv) : Prop :=
  ∀ idx ∈ reads, ∀ m : String, slots[idx]? = some m → lookupSelfEnv env₁ m = lookupSelfEnv env₂ m

private theorem findIdxGo_some_of_mem {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (xs : List α) (acc : Nat), a ∈ xs →
      ∃ k, List.findIdx?.go (· == a) xs acc = some (acc + k) ∧ xs[k]? = some a
  | [], _, h => by cases h
  | x :: xs, acc, h => by
    simp only [List.findIdx?.go]
    by_cases hxa : (x == a) = true
    · refine ⟨0, ?_, ?_⟩
      · simp [hxa]
      · simp [beq_iff_eq.mp hxa]
    · have hne : x ≠ a := fun heq => hxa (beq_iff_eq.mpr heq)
      have hmem : a ∈ xs := by
        rcases List.mem_cons.mp h with rfl | hrest
        · exact absurd rfl hne
        · exact hrest
      obtain ⟨k, hk, hget⟩ := findIdxGo_some_of_mem a xs (acc + 1) hmem
      refine ⟨k + 1, ?_, by simpa using hget⟩
      simp only [hxa, Bool.false_eq_true, ↓reduceIte]
      rw [show acc + (k + 1) = (acc + 1) + k by omega]
      exact hk

private theorem idxOf?_some_of_mem {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) (h : a ∈ xs) :
    ∃ idx, xs.idxOf? a = some idx ∧ xs[idx]? = some a := by
  obtain ⟨k, hk, hget⟩ := findIdxGo_some_of_mem a xs 0 h
  exact ⟨k, by simpa [List.idxOf?, List.findIdx?] using hk, hget⟩

private theorem mem_eraseDupsLoop {α : Type} [BEq α] [LawfulBEq α] {x : α} :
    ∀ (xs acc : List α), (x ∈ xs ∨ x ∈ acc) → x ∈ List.eraseDupsBy.loop (· == ·) xs acc
  | [], acc, h => by
    simp only [List.eraseDupsBy.loop, List.mem_reverse]
    rcases h with hnil | hacc
    · cases hnil
    · exact hacc
  | y :: ys, acc, h => by
    simp only [List.eraseDupsBy.loop]
    split
    · rename_i hcontains
      have hyacc : y ∈ acc := by
        rcases List.any_eq_true.mp hcontains with ⟨z, hz, hbeq⟩
        rwa [beq_iff_eq.mp hbeq]
      apply mem_eraseDupsLoop ys acc
      rcases h with hcons | hacc
      · rcases List.mem_cons.mp hcons with rfl | hys
        · exact .inr hyacc
        · exact .inl hys
      · exact .inr hacc
    · apply mem_eraseDupsLoop ys (y :: acc)
      rcases h with hcons | hacc
      · rcases List.mem_cons.mp hcons with rfl | hys
        · exact .inr List.mem_cons_self
        · exact .inl hys
      · exact .inr (List.mem_cons_of_mem y hacc)

private theorem mem_eraseDups_of_mem {α : Type} [BEq α] [LawfulBEq α] {x : α} {xs : List α}
    (h : x ∈ xs) : x ∈ xs.eraseDups :=
  mem_eraseDupsLoop xs [] (.inl h)

/-- Companion inhabitedness witness for `checkNoEscapingSelf`, `checkSelfReadsInSlots`, and `AgreeOnSlotReads`. -/
theorem leafFrame_premises_inhabited (v u₁ u₂ : Nat) :
    (∃ e : LeafExpr, checkNoEscapingSelf e = true) ∧
    (∃ (slots : List String) (body : LeafExpr), checkSelfReadsInSlots slots body = true) ∧
    (∃ (slots : List String) (i : Nat) (member : String) (body : LeafExpr) (env₁ env₂ : SelfEnv),
      checkNoEscapingSelf body = true ∧
      checkSelfReadsInSlots slots body = true ∧
      AgreeOnSlotReads slots (emitDef slots i (member, body)).reads env₁ env₂) := by
  refine ⟨⟨.get (.bound 0) "x", rfl⟩,
          ⟨["x", "unused"], .get (.bound 0) "x", by simp [checkSelfReadsInSlots, selfReads]⟩,
          ⟨["x", "unused"], 0, "f", .get (.bound 0) "x",
           [("x", .nat v), ("unused", .nat u₁)], [("x", .nat v), ("unused", .nat u₂)],
           rfl, by simp [checkSelfReadsInSlots, selfReads], ?_⟩⟩
  have hreads : (emitDef ["x", "unused"] 0 ("f", .get (.bound 0) "x")).reads = [0] := by
    simp [emitDef, selfReads, List.idxOf?, List.findIdx?, List.findIdx?.go,
      List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  intro idx hidx m hm
  rw [hreads, List.mem_singleton] at hidx
  subst hidx
  injection hm with hmEq
  subst hmEq
  rfl

/-- **Slot-Indexed `LeafDef.reads` Frame Soundness (`leafDef_reads_frame_sound`)**:
For any vtable member `(member, body)` with `checkNoEscapingSelf body = true` and well-scoped slot
reads (`checkSelfReadsInSlots slots body = true`), if `env₁` and `env₂` agree on every slot index
`idx ∈ (emitDef slots i (member, body)).reads`, then `evalLeafExpr` on `env₁` and `env₂` produces
the exact same result (under arbitrary local bindings when `locals = []` and arbitrary fuel). -/
theorem leafDef_reads_frame_sound
    (fuel : Nat) (slots : List String) (i : Nat) (member : String) (body : LeafExpr)
    (env₁ env₂ : SelfEnv)
    (hNoEscape : checkNoEscapingSelf body = true)
    (hScoped : checkSelfReadsInSlots slots body = true)
    (hSlotAgree : AgreeOnSlotReads slots (emitDef slots i (member, body)).reads env₁ env₂) :
    evalLeafExpr fuel [] env₁ body = evalLeafExpr fuel [] env₂ body := by
  apply leafExpr_reads_frame_sound fuel env₁ env₂ body hNoEscape
  intro m hm
  have hcontains : slots.contains m = true := by
    unfold checkSelfReadsInSlots at hScoped
    exact List.all_eq_true.mp hScoped m hm
  have hmSlots : m ∈ slots := List.contains_iff_mem.mp hcontains
  obtain ⟨idx, hidx, hget⟩ := idxOf?_some_of_mem slots m hmSlots
  have hmemFilter : idx ∈ (selfReads 0 body).filterMap slots.idxOf? :=
    List.mem_filterMap.mpr ⟨m, hm, hidx⟩
  have hmemReads : idx ∈ (emitDef slots i (member, body)).reads :=
    mem_eraseDups_of_mem hmemFilter
  exact hSlotAgree idx hmemReads m hget

/-- **Escaping-`self` Counterexample (`bare_self_falsifies_frame_without_guard`)**:
Without `checkNoEscapingSelf`, bare `self` (`.bound 0`) and record destructuring of bare `self`
(`.split (.bound 0) ["secret"] (.lam (.bound 0))`) both report `reads = []`, so `env₁` and `env₂`
vacuously agree on all `reads`, yet `evalLeafExpr` yields distinct results whenever `v₁ ≠ v₂`. -/
theorem bare_self_falsifies_frame_without_guard (v₁ v₂ : Nat) (hne : v₁ ≠ v₂) :
    let bareSelf : LeafExpr := .bound 0
    let splitSelf : LeafExpr := .split (.bound 0) ["secret"] (.lam (.bound 0))
    let env₁ : SelfEnv := [("secret", .nat v₁)]
    let env₂ : SelfEnv := [("secret", .nat v₂)]
    checkNoEscapingSelf bareSelf = false ∧
    checkNoEscapingSelf splitSelf = false ∧
    selfReads 0 bareSelf = [] ∧
    selfReads 0 splitSelf = [] ∧
    (∀ m ∈ selfReads 0 bareSelf, lookupSelfEnv env₁ m = lookupSelfEnv env₂ m) ∧
    (∀ m ∈ selfReads 0 splitSelf, lookupSelfEnv env₁ m = lookupSelfEnv env₂ m) ∧
    evalLeafExpr 4 [] env₁ bareSelf ≠ evalLeafExpr 4 [] env₂ bareSelf ∧
    evalLeafExpr 8 [] env₁ splitSelf ≠ evalLeafExpr 8 [] env₂ splitSelf := by
  refine ⟨rfl, rfl, by simp [selfReads], by simp [selfReads], ?_, ?_, ?_, ?_⟩
  · intro _ hm; simp [selfReads] at hm
  · intro _ hm; simp [selfReads] at hm
  · intro heq
    have hval1 : evalLeafExpr 4 [] [("secret", .nat v₁)] (.bound 0) =
        some (.record [("secret", .nat v₁)]) := by
      simp [evalLeafExpr, bindLeafEnv, bindLeafEnvAt, Term.rename,
        Obend.Law.run, Obend.Law.isValueB]
    have hval2 : evalLeafExpr 4 [] [("secret", .nat v₂)] (.bound 0) =
        some (.record [("secret", .nat v₂)]) := by
      simp [evalLeafExpr, bindLeafEnv, bindLeafEnvAt, Term.rename,
        Obend.Law.run, Obend.Law.isValueB]
    rw [hval1, hval2] at heq
    injection heq with hrec
    injection hrec with hcons
    injection hcons with hhd _
    injection hhd with _ hnat
    injection hnat with hv
    exact hne hv
  · intro heq
    have hs1 : evalLeafExpr 8 [] [("secret", .nat v₁)] (.split (.bound 0) ["secret"] (.lam (.bound 0))) =
        some (.nat v₁) := by
      simp [evalLeafExpr, bindLeafEnv, bindLeafEnvAt, liftSubstitution, Term.rename,
        Obend.Law.run, Obend.Law.isValueB, Obend.Law.step?,
        splitValues, applyAll, instantiate]
    have hs2 : evalLeafExpr 8 [] [("secret", .nat v₂)] (.split (.bound 0) ["secret"] (.lam (.bound 0))) =
        some (.nat v₂) := by
      simp [evalLeafExpr, bindLeafEnv, bindLeafEnvAt, liftSubstitution, Term.rename,
        Obend.Law.run, Obend.Law.isValueB, Obend.Law.step?,
        splitValues, applyAll, instantiate]
    rw [hs1, hs2] at heq
    injection heq with hnat
    injection hnat with hv
    exact hne hv

/-! ## The typing side -/

/-- The record type of a row. -/
def rowType : List (String × Ty) → Ty
  | [] => .emptyRow
  | (n, t) :: r => .field n t (rowType r)

/-- A reusable, unrestricted arrow. -/
def arrowTy (a b : Ty) : Ty := .arrow .reusable .unrestricted a b

/-- A definition's type: `Self → T` for a method, `Self → {} → T` for a cell. -/
def defType (self : Ty) : DefKind → Ty → Ty
  | .method, T => arrowTy self T
  | .cell, T => arrowTy self (arrowTy .emptyRow T)

/-- The type of a definition at a row: the row's member type, with `self` at the row's record type. -/
def LeafDef.type (row : List (String × Ty)) (d : LeafDef) : Option Ty :=
  (row.lookup d.member).map (defType (rowType row) d.kind)

/-- **Every emitted definition's type is the row's member type with `self` at the record type.** -/
theorem emit_typed (C : Composition) (row : List (String × Ty)) (d : LeafDef) (_ : d ∈ (emit C).defs)
    (T : Ty) (hT : row.lookup d.member = some T) : d.type row = some (defType (rowType row) d.kind T) := by
  simp [LeafDef.type, hT]

/-! ## The book is a function of the composition's digest -/

/-- A layer as a term: exactly what the emitter reads of it (its key, its fields, its shape). The
spec metadata and the compose step's metadata are not read: the vtable has no reflection. -/
abbrev _root_.Obend.Logic.Layer.code (L : Layer) : Term :=
  .record [("name", .label L.name), ("fields", .record L.fields), ("flat", .boolean L.flat)]

/-- A composition as a term: its layers in order, outermost first, and its seed. -/
abbrev _root_.Obend.Logic.Composition.code (C : Composition) : Term :=
  .record [("layers", .record (C.layers.map fun L => (L.name, L.code))), ("seed", .record C.seed)]

/-- What the flattening reads of a layer. -/
def _root_.Obend.Logic.Layer.shape (L : Layer) : List (String × Term) × Bool := (L.fields, L.flat)

theorem flatRow_congr (seed : List (String × Term)) :
    ∀ {ls ls' : List Layer}, ls.map Layer.shape = ls'.map Layer.shape → flatRow seed ls = flatRow seed ls'
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | L :: ls, L' :: ls', h => by
    simp only [List.map_cons, List.cons.injEq, Layer.shape, Prod.mk.injEq] at h
    obtain ⟨⟨hf, hfl⟩, hr⟩ := h
    simp only [flatRow, hf, hfl, flatRow_congr seed hr]

theorem layers_code_shape :
    ∀ {ls ls' : List Layer}, ls.map (fun L => (L.name, L.code)) = ls'.map (fun L => (L.name, L.code)) →
      ls.map Layer.shape = ls'.map Layer.shape
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | L :: ls, L' :: ls', h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, hc⟩, hr⟩ := h
    simp only [Layer.code, Term.record.injEq, List.cons.injEq, Prod.mk.injEq, Term.label.injEq,
      Term.boolean.injEq, true_and, and_true] at hc
    simp only [List.map_cons, Layer.shape, hc.2.1, hc.2.2, layers_code_shape hr]

/-- **Two compositions with one code have one book.** -/
theorem emit_congr {C C' : Composition} (h : C.code = C'.code) : emit C = emit C' := by
  simp only [Composition.code, Term.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  have hs := flatRow_congr C.seed (layers_code_shape h.1)
  unfold emit Composition.vtable Composition.flatRaw
  rw [hs, h.2]

def charsPreimages (H : Obend.Digest.HashBytes.Hash) : List Char → List (List UInt8)
  | [] => [Obend.Core.Digest.preimage 6 0]
  | c :: cs =>
    let r := Obend.Core.Code.charsDigest H cs
    Obend.Core.Digest.preimage 7 (Obend.Core.Digest.digestWith H c.toNat r) ::
    Obend.Core.Digest.preimage c.toNat r ::
    charsPreimages H cs

def textPreimages (H : Obend.Digest.HashBytes.Hash) (s : String) : List (List UInt8) :=
  charsPreimages H s.toList

mutual
def dataPreimages (H : Obend.Digest.HashBytes.Hash) : Obend.Core.Data.Data → List (List UInt8)
  | .natural n => [Obend.Core.Digest.preimage 0 n]
  | .boolean b => [Obend.Core.Digest.preimage 1 (if b then 1 else 0)]
  | .label s => Obend.Core.Digest.preimage 2 (Obend.Core.Code.textDigest H s) :: textPreimages H s
  | .record fs => Obend.Core.Digest.preimage 3 (Obend.Core.Code.fieldsDigest H fs) :: fieldsPreimages H fs
  | .variant l p =>
    let dl := Obend.Core.Code.textDigest H l
    let dp := Obend.Core.Code.dataDigest H p
    Obend.Core.Digest.preimage 4 (Obend.Core.Digest.digestWith H dl dp) ::
    Obend.Core.Digest.preimage dl dp ::
    (textPreimages H l ++ dataPreimages H p)
def fieldsPreimages (H : Obend.Digest.HashBytes.Hash) : List (String × Obend.Core.Data.Data) → List (List UInt8)
  | [] => [Obend.Core.Digest.preimage 8 0]
  | (n, d) :: rest =>
    let dn := Obend.Core.Code.textDigest H n
    let dd := Obend.Core.Code.dataDigest H d
    let dr := Obend.Core.Code.fieldsDigest H rest
    Obend.Core.Digest.preimage 9 (Obend.Core.Digest.digestWith H dn (Obend.Core.Digest.digestWith H dd dr)) ::
    Obend.Core.Digest.preimage dn (Obend.Core.Digest.digestWith H dd dr) ::
    Obend.Core.Digest.preimage dd dr ::
    (textPreimages H n ++ dataPreimages H d ++ fieldsPreimages H rest)
end

/-- Finite list of all Merkle preimages hashed when computing `addressWith H t`. -/
def codePreimages (H : Obend.Digest.HashBytes.Hash) (t : Term) : List (List UInt8) :=
  dataPreimages H (Obend.Core.Code.quote t)

private theorem node_binds_among {H : Obend.Digest.HashBytes.Hash} {a b a' b' : Nat}
    (l₁ l₂ : List (List UInt8))
    (h : Obend.Core.Digest.digestWith H a b = Obend.Core.Digest.digestWith H a' b')
    (ha : Obend.Core.Digest.Admissible a) (ha' : Obend.Core.Digest.Admissible a')
    (hp1 : Obend.Core.Digest.preimage a b ∈ l₁)
    (hp2 : Obend.Core.Digest.preimage a' b' ∈ l₂) :
    (a = a' ∧ b = b') ∨ Obend.Digest.HashBytes.CollisionAmong H (fun x => x ∈ l₁ ∨ x ∈ l₂) := by
  rcases Obend.Core.Digest.binds_or_collides H ha ha' h with e | c
  · exact .inl e
  · exact .inr (c.mono fun x hx => by rcases hx with rfl | rfl; exact .inl hp1; exact .inr hp2)

private theorem charsDigest_binds_among {H : Obend.Digest.HashBytes.Hash} (hH : Obend.Core.Code.Short H) :
    ∀ {cs cs' : List Char}, Obend.Core.Code.charsDigest H cs = Obend.Core.Code.charsDigest H cs' →
      cs = cs' ∨ Obend.Digest.HashBytes.CollisionAmong H (fun x => x ∈ charsPreimages H cs ∨ x ∈ charsPreimages H cs')
  | [], [], _ => .inl rfl
  | [], c' :: cs', h => by
    simp only [Obend.Core.Code.charsDigest] at h
    rcases node_binds_among (charsPreimages H []) (charsPreimages H (c' :: cs')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [charsPreimages]) (by simp [charsPreimages]) with ⟨e, _⟩ | c
    · simp at e
    · exact .inr c
  | c :: cs, [], h => by
    simp only [Obend.Core.Code.charsDigest] at h
    rcases node_binds_among (charsPreimages H (c :: cs)) (charsPreimages H []) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [charsPreimages]) (by simp [charsPreimages]) with ⟨e, _⟩ | c
    · simp at e
    · exact .inr c
  | c :: cs, c' :: cs', h => by
    simp only [Obend.Core.Code.charsDigest] at h
    rcases node_binds_among (charsPreimages H (c :: cs)) (charsPreimages H (c' :: cs')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [charsPreimages]) (by simp [charsPreimages]) with ⟨_, e⟩ | col
    · rcases node_binds_among (charsPreimages H (c :: cs)) (charsPreimages H (c' :: cs')) e
          (Obend.Core.Code.char_admissible c) (Obend.Core.Code.char_admissible c')
          (by simp [charsPreimages]) (by simp [charsPreimages]) with ⟨ec, er⟩ | col
      · rcases charsDigest_binds_among hH er with rfl | col
        · exact .inl (by rw [Char.toNat_inj.1 ec])
        · exact .inr (col.mono fun x hx => by
            rcases hx with hx | hx
            · exact .inl (by simp [charsPreimages, hx])
            · exact .inr (by simp [charsPreimages, hx]))
      · exact .inr col
    · exact .inr col

private theorem textDigest_binds_among {H : Obend.Digest.HashBytes.Hash} (hH : Obend.Core.Code.Short H) {s s' : String}
    (h : Obend.Core.Code.textDigest H s = Obend.Core.Code.textDigest H s') :
    s = s' ∨ Obend.Digest.HashBytes.CollisionAmong H (fun x => x ∈ textPreimages H s ∨ x ∈ textPreimages H s') := by
  rcases charsDigest_binds_among hH h with e | c
  · exact .inl (String.toList_inj.1 e)
  · exact .inr c

private theorem off_diag_binds_among {H : Obend.Digest.HashBytes.Hash} {t t' b b' : Nat}
    (d d' : Obend.Core.Data.Data)
    (ht : t < 2 ^ 256) (ht' : t' < 2 ^ 256) (hne : t ≠ t')
    (h : Obend.Core.Digest.digestWith H t b = Obend.Core.Digest.digestWith H t' b')
    (hp1 : Obend.Core.Digest.preimage t b ∈ dataPreimages H d)
    (hp2 : Obend.Core.Digest.preimage t' b' ∈ dataPreimages H d') :
    d = d' ∨ Obend.Digest.HashBytes.CollisionAmong H (fun x => x ∈ dataPreimages H d ∨ x ∈ dataPreimages H d') := by
  rcases node_binds_among (dataPreimages H d) (dataPreimages H d') h
      (Obend.Core.Code.small_admissible ht) (Obend.Core.Code.small_admissible ht') hp1 hp2 with ⟨e, _⟩ | c
  · exact absurd e hne
  · exact .inr c

mutual
private theorem dataDigest_binds_among {H : Obend.Digest.HashBytes.Hash} (hH : Obend.Core.Code.Short H) :
    ∀ (d d' : Obend.Core.Data.Data), Obend.Core.Code.dataDigest H d = Obend.Core.Code.dataDigest H d' →
      d = d' ∨ Obend.Digest.HashBytes.CollisionAmong H (fun x => x ∈ dataPreimages H d ∨ x ∈ dataPreimages H d')
  | .natural n, .natural n', h => by
    simp only [Obend.Core.Code.dataDigest] at h
    rcases node_binds_among (dataPreimages H (.natural n)) (dataPreimages H (.natural n')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [dataPreimages]) (by simp [dataPreimages]) with ⟨_, e⟩ | c
    · exact .inl (by rw [e])
    · exact .inr c
  | .boolean b, .boolean b', h => by
    simp only [Obend.Core.Code.dataDigest] at h
    rcases node_binds_among (dataPreimages H (.boolean b)) (dataPreimages H (.boolean b')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [dataPreimages]) (by simp [dataPreimages]) with ⟨_, e⟩ | c
    · left; cases b <;> cases b' <;> simp_all
    · exact .inr c
  | .label s, .label s', h => by
    simp only [Obend.Core.Code.dataDigest] at h
    rcases node_binds_among (dataPreimages H (.label s)) (dataPreimages H (.label s')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [dataPreimages]) (by simp [dataPreimages]) with ⟨_, e⟩ | c
    · rcases textDigest_binds_among hH e with rfl | c
      · exact .inl rfl
      · exact .inr (c.mono fun x hx => by
          rcases hx with hx | hx
          · exact .inl (by simp [dataPreimages, hx])
          · exact .inr (by simp [dataPreimages, hx]))
    · exact .inr c
  | .record fs, .record fs', h => by
    simp only [Obend.Core.Code.dataDigest] at h
    rcases node_binds_among (dataPreimages H (.record fs)) (dataPreimages H (.record fs')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [dataPreimages]) (by simp [dataPreimages]) with ⟨_, e⟩ | c
    · rcases fieldsDigest_binds_among hH fs fs' e with rfl | c
      · exact .inl rfl
      · exact .inr (c.mono fun x hx => by
          rcases hx with hx | hx
          · exact .inl (by simp [dataPreimages, hx])
          · exact .inr (by simp [dataPreimages, hx]))
    · exact .inr c
  | .variant l p, .variant l' p', h => by
    simp only [Obend.Core.Code.dataDigest] at h
    rcases node_binds_among (dataPreimages H (.variant l p)) (dataPreimages H (.variant l' p')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [dataPreimages]) (by simp [dataPreimages]) with ⟨_, e⟩ | c
    · rcases node_binds_among (dataPreimages H (.variant l p)) (dataPreimages H (.variant l' p')) e
          (Obend.Core.Code.textDigest_admissible hH _) (Obend.Core.Code.textDigest_admissible hH _)
          (by simp [dataPreimages]) (by simp [dataPreimages]) with ⟨el, ep⟩ | c
      · rcases textDigest_binds_among hH el with rfl | c
        · rcases dataDigest_binds_among hH p p' ep with rfl | c
          · exact .inl rfl
          · exact .inr (c.mono fun x hx => by
              rcases hx with hx | hx
              · exact .inl (by simp [dataPreimages, hx])
              · exact .inr (by simp [dataPreimages, hx]))
        · exact .inr (c.mono fun x hx => by
            rcases hx with hx | hx
            · exact .inl (by simp [dataPreimages, hx])
            · exact .inr (by simp [dataPreimages, hx]))
      · exact .inr c
    · exact .inr c
  | .natural _, .boolean _, h | .natural _, .label _, h
  | .natural _, .record _, h  | .natural _, .variant _ _, h
  | .boolean _, .natural _, h | .boolean _, .label _, h
  | .boolean _, .record _, h  | .boolean _, .variant _ _, h
  | .label _,   .natural _, h | .label _,   .boolean _, h
  | .label _,   .record _, h  | .label _,   .variant _ _, h
  | .record _,  .natural _, h | .record _,  .boolean _, h
  | .record _,  .label _, h   | .record _,  .variant _ _, h
  | .variant _ _, .natural _, h | .variant _ _, .boolean _, h
  | .variant _ _, .label _, h   | .variant _ _, .record _, h => by
    simp only [Obend.Core.Code.dataDigest] at h
    exact off_diag_binds_among _ _ (by decide) (by decide) (by decide) h
      (by simp [dataPreimages]) (by simp [dataPreimages])
private theorem fieldsDigest_binds_among {H : Obend.Digest.HashBytes.Hash} (hH : Obend.Core.Code.Short H) :
    ∀ (fs fs' : List (String × Obend.Core.Data.Data)),
      Obend.Core.Code.fieldsDigest H fs = Obend.Core.Code.fieldsDigest H fs' →
      fs = fs' ∨ Obend.Digest.HashBytes.CollisionAmong H (fun x => x ∈ fieldsPreimages H fs ∨ x ∈ fieldsPreimages H fs')
  | [], [], _ => .inl rfl
  | [], kv' :: rest', h => by
    simp only [Obend.Core.Code.fieldsDigest] at h
    rcases node_binds_among (fieldsPreimages H []) (fieldsPreimages H (kv' :: rest')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [fieldsPreimages]) (by simp [fieldsPreimages]) with ⟨e, _⟩ | c
    · simp at e
    · exact .inr c
  | kv :: rest, [], h => by
    simp only [Obend.Core.Code.fieldsDigest] at h
    rcases node_binds_among (fieldsPreimages H (kv :: rest)) (fieldsPreimages H []) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [fieldsPreimages]) (by simp [fieldsPreimages]) with ⟨e, _⟩ | c
    · simp at e
    · exact .inr c
  | (n, d) :: rest, (n', d') :: rest', h => by
    simp only [Obend.Core.Code.fieldsDigest] at h
    rcases node_binds_among (fieldsPreimages H ((n, d) :: rest)) (fieldsPreimages H ((n', d') :: rest')) h
        (Obend.Core.Code.small_admissible (by decide)) (Obend.Core.Code.small_admissible (by decide))
        (by simp [fieldsPreimages]) (by simp [fieldsPreimages]) with ⟨_, e⟩ | c
    · rcases node_binds_among (fieldsPreimages H ((n, d) :: rest)) (fieldsPreimages H ((n', d') :: rest')) e
          (Obend.Core.Code.textDigest_admissible hH _) (Obend.Core.Code.textDigest_admissible hH _)
          (by simp [fieldsPreimages]) (by simp [fieldsPreimages]) with ⟨en, e⟩ | c
      · rcases node_binds_among (fieldsPreimages H ((n, d) :: rest)) (fieldsPreimages H ((n', d') :: rest')) e
            (Obend.Core.Code.dataDigest_admissible hH _) (Obend.Core.Code.dataDigest_admissible hH _)
            (by simp [fieldsPreimages]) (by simp [fieldsPreimages]) with ⟨ed, er⟩ | c
        · rcases textDigest_binds_among hH en with rfl | c
          · rcases dataDigest_binds_among hH d d' ed with rfl | c
            · rcases fieldsDigest_binds_among hH rest rest' er with rfl | c
              · exact .inl rfl
              · exact .inr (c.mono fun x hx => by
                  rcases hx with hx | hx
                  · exact .inl (by simp [fieldsPreimages, hx])
                  · exact .inr (by simp [fieldsPreimages, hx]))
            · exact .inr (c.mono fun x hx => by
                rcases hx with hx | hx
                · exact .inl (by simp [fieldsPreimages, hx])
                · exact .inr (by simp [fieldsPreimages, hx]))
          · exact .inr (c.mono fun x hx => by
              rcases hx with hx | hx
              · exact .inl (by simp [fieldsPreimages, hx])
              · exact .inr (by simp [fieldsPreimages, hx]))
        · exact .inr c
      · exact .inr c
    · exact .inr c
end

/-- **The book is a function of the composition's content address**: two compositions with one
address under a short hash have one book, or `H` collides on the finite set of Merkle preimages
hashed for `C.code` and `C'.code`. -/
theorem emit_of_digest {H : Obend.Digest.HashBytes.Hash} (hH : Obend.Core.Code.Short H) {C C' : Composition}
    (h : Obend.Core.Code.addressWith H C.code = Obend.Core.Code.addressWith H C'.code) :
    emit C = emit C' ∨
      Obend.Digest.HashBytes.CollisionAmong H
        (fun x => x ∈ codePreimages H C.code ∨ x ∈ codePreimages H C'.code) := by
  rcases dataDigest_binds_among hH (Obend.Core.Code.quote C.code) (Obend.Core.Code.quote C'.code) h with e | c
  · exact .inl (emit_congr (Obend.Core.Code.quote_injective e))
  · exact .inr c

/-- The same under the deployed cSHAKE256. -/
theorem emit_of_address {C C' : Composition}
    (h : Obend.Core.Code.address C.code = Obend.Core.Code.address C'.code) :
    emit C = emit C' ∨
      Obend.Digest.HashBytes.CollisionAmong Obend.Core.Digest.deployed
        (fun x => x ∈ codePreimages Obend.Core.Digest.deployed C.code ∨
                  x ∈ codePreimages Obend.Core.Digest.deployed C'.code) :=
  emit_of_digest Obend.Core.Code.deployed_short h

/-- Read a layer back from its code (no metadata: the code does not carry it). -/
def layerOfCode : Term → Option Layer
  | .record [("name", .label n), ("fields", .record fs), ("flat", .boolean fl)] =>
    some { name := n, metadata := .record [], fields := fs, flat := fl }
  | _ => none

/-- Read a composition back from its code (what a recorded book pins). -/
def compositionOfCode : Term → Option Composition
  | .record [("layers", .record ls), ("seed", .record seed)] =>
    match ls.mapM (layerOfCode ·.2) with
    | some (top :: below) => some ⟨top, below, seed⟩
    | _ => none
  | _ => none

/-- The layer read back has the same code. -/
def _root_.Obend.Logic.Layer.erase (L : Layer) : Layer := { name := L.name, metadata := .record [], fields := L.fields, flat := L.flat }

theorem layerOfCode_code (L : Layer) : layerOfCode L.code = some L.erase := by rfl

theorem mapM_layerOfCode : ∀ ls : List Layer,
    (ls.map fun L => (L.name, L.code)).mapM (layerOfCode ·.2) = some (ls.map Layer.erase)
  | [] => by rfl
  | L :: ls => by simp [List.mapM_cons, layerOfCode_code, mapM_layerOfCode ls]

/-- **A recorded book's composition reads back with the same code**, so it emits the same book. -/
theorem compositionOfCode_code (C : Composition) :
    ∃ C', compositionOfCode C.code = some C' ∧ C'.code = C.code := by
  obtain ⟨top, below, seed⟩ := C
  have := mapM_layerOfCode (top :: below)
  refine ⟨⟨top.erase, below.map Layer.erase, seed⟩, ?_, ?_⟩
  · simp only [List.map_cons] at this
    simp only [Composition.code, Composition.layers, compositionOfCode, List.map_cons, this]
  · simp [Composition.code, Composition.layers, Layer.code, Layer.erase, Function.comp_def]

end Obend.Leaf
end
