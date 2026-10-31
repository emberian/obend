module
/-
# Obend.Doc.Graph — a page's state as a graph of atoms with stable identities

DESIGN §5: a page's versioned state is rows of runs. Underneath, as in breadstuffs' `dregg-doc`
(Pijul's model, Mimram–Di Giusto's category made concrete), a page is a GRAPH:

* ATOMS, each with a stable identity (`AtomId`) and a content: a text run, a cite (a wikilink's
  support), or a field assignment. An identity names one atom forever; nothing renumbers.
* a DEAD set: a deleted atom is tombstoned, never removed, so a delete is monotone and the atom
  still conducts order (its successors stay reachable through it).
* ORDER EDGES `a → b`, "a comes before b". The order a page shows is their transitive closure
  (`Before`); where two live atoms are unordered, the page carries an antichain, a conflict.

Every component is a list that the forward operations only append to; the observations a theorem
reads (`label`, `isDead`, `edge`) are functions of the lists, and `Same` is equality of the
observations. That is the equality the patch theorems are stated in (`Obend.Doc.Patch`): two graphs
that store the same facts in a different list order are the same page.

`beforeB` decides the order by a forward cone of bounded depth; it is SOUND for every graph
(`beforeB_sound`) and COMPLETE wherever the cone is closed under the edges (`beforeB_complete`), a
condition `Closed` checks. Statements about a concrete page discharge `Closed` by `decide`; the
general completeness of the bounded cone (a pigeonhole on the edge count) is not proved here.
-/
public section

namespace Obend.Doc

set_option autoImplicit false

/-- A stable atom identity. -/
abbrev AtomId := Nat
/-- A page identity. -/
abbrev PageId := Nat

/-- The sentinel every page's order starts from. No atom is stored at it; the first run of a page
is added after it. -/
@[expose] def root : AtomId := 0

/-- How a byte cite tracks its source: a PINNED cite quotes a version and stays verified when the
source moves on; a FOLLOWING cite also claims to be current, and that claim fails when the bytes it
quotes change at the source's current version (`Obend.Doc.Section`, rule (b)). -/
inductive Mode
  | pinned
  | following
deriving DecidableEq, Repr

/-- A range of a page's rendered text, in bytes. -/
structure Range where
  start : Nat
  len : Nat
deriving DecidableEq, Repr

/-- What of its source a cite quotes (the range of DESIGN §5's cite, made optional and addressable).
`identity` quotes no bytes: `[[Beta]]`, a cite of the page itself, current while the page exists.
The others are BYTE cites: `page` the page's whole text (`![[Beta]]`, an embed), `block b` the line
marked `^b` (`[[Beta#^b]]`, a block reference, found by its marker in each version, so an edit
elsewhere in the page does not move it), `bytes r` a byte range. -/
inductive Span
  | identity
  | page
  | block (id : String)
  | bytes (r : Range)
deriving @[expose] DecidableEq, Repr

/-- A cite: `(page, span, version, byte commitment)` of another page (DESIGN §5), with the mode a
byte cite tracks its source in. An identity cite's version, commitment and mode are inert. -/
structure Cite where
  page : PageId
  span : Span
  version : Nat
  commitment : List UInt8
  mode : Mode
deriving DecidableEq, Repr

/-- What an atom carries. -/
inductive Content
  /-- a run of text -/
  | text (s : String)
  /-- a cite; `name` is the wikilink's text between its brackets, as written (`Beta`, `Beta#^b`) -/
  | cite (name : String) (c : Cite)
  /-- an assignment to a single-valued field (outside the order: it has no edges) -/
  | field (name value : String)
deriving @[expose] DecidableEq, Repr

/-- A page's state. -/
structure Graph where
  atoms : List (AtomId × Content) := []
  dead : List AtomId := []
  edges : List (AtomId × AtomId) := []
deriving DecidableEq, Repr

namespace Graph

/-- The empty page: no atoms, no edges. -/
@[expose] def empty : Graph := {}

/-- The content stored at an identity (the first stored, if a list holds two). -/
@[expose] def label (G : Graph) (a : AtomId) : Option Content := G.atoms.lookup a

/-- Whether an identity is tombstoned. -/
@[expose] def isDead (G : Graph) (a : AtomId) : Bool := G.dead.contains a

/-- Whether the order edge `a → b` is stored. -/
@[expose] def edge (G : Graph) (a b : AtomId) : Bool := G.edges.contains (a, b)

/-- An atom is present when some content is stored at it. -/
@[expose] def present (G : Graph) (a : AtomId) : Bool := (G.label a).isSome

/-- An atom is alive when it is present and not tombstoned. -/
@[expose] def alive (G : Graph) (a : AtomId) : Bool := G.present a && !G.isDead a

/-- Two graphs are the SAME page when every observation agrees. -/
@[expose] def Same (G H : Graph) : Prop := G.label = H.label ∧ G.isDead = H.isDead ∧ G.edge = H.edge

theorem Same.refl (G : Graph) : G.Same G := ⟨rfl, rfl, rfl⟩
theorem Same.symm {G H : Graph} (h : G.Same H) : H.Same G := ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
theorem Same.trans {G H K : Graph} (h : G.Same H) (k : H.Same K) : G.Same K :=
  ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.trans k.2.2⟩

/-! ## The order -/

/-- `a` comes strictly before `b`: a nonempty path of order edges (through atoms alive or dead). -/
inductive Before (G : Graph) : AtomId → AtomId → Prop
  | edge {a b : AtomId} : G.edge a b = true → Before G a b
  | trans {a b c : AtomId} : G.edge a b = true → Before G b c → Before G a c

theorem Before.tail {G : Graph} {a b c : AtomId} (h : G.Before a b) (e : G.edge b c = true) :
    G.Before a c := by
  induction h with
  | edge h => exact .trans h (.edge e)
  | trans h _ ih => exact .trans h (ih e)

theorem Before.trans' {G : Graph} {a b c : AtomId} (h : G.Before a b) (k : G.Before b c) :
    G.Before a c := by
  induction h with
  | edge h => exact .trans h k
  | trans h _ ih => exact .trans h (ih k)

/-- The direct successors of `a`. -/
@[expose] def succs (G : Graph) (a : AtomId) : List AtomId :=
  G.edges.filterMap fun e => if e.1 = a then some e.2 else none

theorem mem_succs {G : Graph} {a b : AtomId} : b ∈ G.succs a ↔ G.edge a b = true := by
  simp only [succs, List.mem_filterMap, edge, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨x, y⟩, hm, h⟩
    by_cases hx : x = a
    · subst hx; simp at h; subst h; exact hm
    · simp [hx] at h
  · intro h; exact ⟨(a, b), h, by simp⟩

/-- One step of the forward cone: `S` and every successor of a member of `S`. -/
@[expose] def grow (G : Graph) (S : List AtomId) : List AtomId :=
  S ++ (G.edges.filter fun e => S.contains e.1).map Prod.snd

/-- `n` steps of the forward cone. -/
@[expose] def coneN (G : Graph) : Nat → List AtomId → List AtomId
  | 0, S => S
  | n + 1, S => G.coneN n (G.grow S)

/-- The strict forward cone of `a`, to depth the number of edges. -/
@[expose] def cone (G : Graph) (a : AtomId) : List AtomId := G.coneN G.edges.length (G.succs a)

/-- The decided order: `b` is in the strict forward cone of `a`. -/
@[expose] def beforeB (G : Graph) (a b : AtomId) : Bool := (G.cone a).contains b

/-- `S` is closed under the order edges. -/
@[expose] def Closed (G : Graph) (S : List AtomId) : Bool :=
  G.edges.all fun e => !S.contains e.1 || S.contains e.2

theorem mem_grow {G : Graph} {S : List AtomId} {y : AtomId} :
    y ∈ G.grow S ↔ y ∈ S ∨ ∃ x ∈ S, G.edge x y = true := by
  simp only [grow, List.mem_append, List.mem_map, List.mem_filter, List.contains_iff_mem, edge]
  constructor
  · rintro (h | ⟨⟨x, y'⟩, ⟨hm, hx⟩, rfl⟩)
    · exact .inl h
    · exact .inr ⟨x, hx, hm⟩
  · rintro (h | ⟨x, hx, hm⟩)
    · exact .inl h
    · exact .inr ⟨(x, y), ⟨hm, hx⟩, rfl⟩

theorem coneN_sound {G : Graph} {a : AtomId} :
    ∀ (n : Nat) (S : List AtomId), (∀ x ∈ S, G.Before a x) → ∀ y ∈ G.coneN n S, G.Before a y
  | 0, _, hS => hS
  | n + 1, S, hS => coneN_sound n (G.grow S) fun y hy => by
      rcases mem_grow.1 hy with h | ⟨x, hx, he⟩
      · exact hS y h
      · exact (hS x hx).tail he

/-- The decided order is sound on every graph. -/
theorem beforeB_sound {G : Graph} {a b : AtomId} (h : G.beforeB a b = true) : G.Before a b := by
  simp only [beforeB, List.contains_iff_mem] at h
  exact coneN_sound _ _ (fun x hx => .edge (mem_succs.1 hx)) b h

theorem subset_coneN {G : Graph} : ∀ (n : Nat) (S : List AtomId), ∀ x ∈ S, x ∈ G.coneN n S
  | 0, _, _, hx => hx
  | n + 1, _, x, hx => subset_coneN n _ x (mem_grow.2 (.inl hx))

/-- A set closed under the edges and holding the successors of `a` holds everything after `a`. -/
theorem mem_of_closed {G : Graph} {S : List AtomId} (hc : G.Closed S = true) {a b : AtomId}
    (hs : ∀ x, G.edge a x = true → x ∈ S) (h : G.Before a b) : b ∈ S := by
  have step : ∀ x y, x ∈ S → G.edge x y = true → y ∈ S := by
    intro x y hx he
    simp only [Closed, List.all_eq_true] at hc
    have := hc (x, y) (by simpa [edge] using he)
    simp at this
    exact this.resolve_left (by simpa using hx)
  induction h with
  | edge he => exact hs _ he
  | trans he _ ih => exact ih fun x hx => step _ x (hs _ he) hx

/-- The decided order is complete wherever the cone it computes is closed. -/
theorem beforeB_complete {G : Graph} {a b : AtomId} (hc : G.Closed (G.cone a) = true)
    (h : G.Before a b) : G.beforeB a b = true := by
  simp only [beforeB, List.contains_iff_mem]
  exact mem_of_closed hc (fun x hx => subset_coneN _ _ x (mem_succs.2 hx)) h

/-- Where the cone is closed, the decided order is the order. -/
theorem beforeB_iff {G : Graph} {a b : AtomId} (hc : G.Closed (G.cone a) = true) :
    G.beforeB a b = true ↔ G.Before a b :=
  ⟨beforeB_sound, beforeB_complete hc⟩

/-- A certified negative: an atom outside a closed cone is not after `a`. -/
theorem not_before_of_closed {G : Graph} {a b : AtomId} (hc : G.Closed (G.cone a) = true)
    (h : G.beforeB a b = false) : ¬ G.Before a b := fun hb => by
  rw [beforeB_complete hc hb] at h; cases h

/-! ### Teeth: the decided order on a three-atom page with one fork -/

/-- `1 → 2`, `1 → 3`: 2 and 3 both after 1, unordered. -/
def fork : Graph :=
  { atoms := [(1, .text "a"), (2, .text "b"), (3, .text "c")], edges := [(1, 2), (1, 3)] }

example : fork.Before 1 3 := beforeB_sound (by decide)
example : ¬ fork.Before 2 3 := not_before_of_closed (by decide) (by decide)
example : ¬ fork.Before 3 1 := not_before_of_closed (by decide) (by decide)
example : fork.alive 2 = true ∧ fork.alive 4 = false := by decide

end Graph
end Obend.Doc

end
