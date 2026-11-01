module
/-
# Obend.Leaf.Emit — the flattened object as a leaf book

The leaf language (Bend, checked by BendTT) is strict and affine, and its books are lists of
definitions whose calls go to earlier definitions or descend. The vtable of `Obend.Leaf.Flatten`
becomes such a book (`emit`):

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
  definitions meet; in the leaf it is the single self-recursive definition (fuel, or a descending
  column, is BendTT's live-check obligation, `REPORT-LEAF-20261101.md`);
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
@[expose] public section
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
def kindOf : Term → DefKind
  | .lam _ => .method
  | _ => .cell

/-- The member names a body reads as `self.m`, `self` at index `d`. -/
def selfReads (d : Nat) : Term → List String
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

def BookItem.def? : BookItem → Option LeafDef
  | .slot d => some d
  | .static _ _ => none

def BookItem.static? : BookItem → Option (String × Term)
  | .slot _ => none
  | .static m v => some (m, v)

/-- One definition per slot, in slot order. -/
def Book.defs (B : Book) : List LeafDef := B.items.filterMap BookItem.def?

/-- The slot table: member names in slot order. -/
def Book.slots (B : Book) : List String := B.defs.map (·.member)

/-- The static members (the kind's brand), with their values under `self`. -/
def Book.statics (B : Book) : List (String × Term) := B.items.filterMap BookItem.static?

/-- The definition of a vtable entry at a slot. -/
def emitDef (slots : List String) (i : Nat) (f : String × Term) : LeafDef where
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
def emitItems (slots : List String) : Nat → List (String × Term) → List BookItem
  | _, [] => []
  | i, f :: rest =>
    if Obend.Core.Brand.isBrand f.1 then .static f.1 f.2 :: emitItems slots i rest
    else .slot (emitDef slots i f) :: emitItems slots (i + 1) rest

/-- The members that take a slot. -/
def slotted (vt : List (String × Term)) : List (String × Term) := vt.filter fun f => !Obend.Core.Brand.isBrand f.1

/-- **The emitter.** -/
def emitVtable (vt : List (String × Term)) : Book :=
  { items := emitItems ((slotted vt).map (·.1)) 0 vt }

/-- The book of a composition: its vtable, emitted. -/
def emit (C : Composition) : Book := emitVtable C.vtable

/-- How the dispatcher calls a definition, under its two binders (`self` at 1). -/
def LeafDef.call (d : LeafDef) : Term :=
  match d.kind with
  | .method => .app (d.code.rename (· + 2)) (.bound 1)
  | .cell => .app (.app (d.code.rename (· + 2)) (.bound 1)) (.record [])

/-- The dispatcher's entry for an item: a slot's call, or the static value. -/
def BookItem.entry : BookItem → String × Term
  | .slot d => (d.member, d.call)
  | .static m v => (m, v.rename Nat.succ)

/-- **The dispatcher**: the book linked into one term, `fix (λself. λ_. {m = def self, …}) {}`, with
the static members answered from the book's metadata. -/
def Book.link (B : Book) : Term :=
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
def Book.closedB (B : Book) : Bool := B.defs.all fun d => Obend.Law.closedB d.code

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
def _root_.Obend.Logic.Layer.code (L : Layer) : Term :=
  .record [("name", .label L.name), ("fields", .record L.fields), ("flat", .boolean L.flat)]

/-- A composition as a term: its layers in order, outermost first, and its seed. -/
def _root_.Obend.Logic.Composition.code (C : Composition) : Term :=
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

/-- **The book is a function of the composition's content address**: two compositions with one
address under a short hash have one book, or the hash collides. -/
theorem emit_of_digest {H : Obend.Digest.HashBytes.Hash} (hH : Obend.Core.Code.Short H) {C C' : Composition}
    (h : Obend.Core.Code.addressWith H C.code = Obend.Core.Code.addressWith H C'.code) :
    emit C = emit C' ∨ Obend.Digest.HashBytes.Collision H := by
  rcases Obend.Core.Code.addressWith_binds hH h with e | c
  · exact .inl (emit_congr e)
  · exact .inr c

/-- The same under the deployed cSHAKE256 (`digest_of_quote`). -/
theorem emit_of_address {C C' : Composition}
    (h : Obend.Core.Code.address C.code = Obend.Core.Code.address C'.code) :
    emit C = emit C' ∨ Obend.Digest.HashBytes.Collision Obend.Core.Digest.deployed := by
  rcases Obend.Core.Code.digest_of_quote h with e | c
  · exact .inl (emit_congr e)
  · exact .inr c

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

theorem layerOfCode_code (L : Layer) : layerOfCode L.code = some L.erase := rfl

theorem mapM_layerOfCode : ∀ ls : List Layer,
    (ls.map fun L => (L.name, L.code)).mapM (layerOfCode ·.2) = some (ls.map Layer.erase)
  | [] => rfl
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
