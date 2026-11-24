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
public import Obend.Core.Data
public import Obend.Run.Core4
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
deriving DecidableEq, Repr

/-- A cite: `(page, span, version, byte commitment)` of another page (DESIGN §5), with the mode a
byte cite tracks its source in. An identity cite's version, commitment and mode are inert. -/
structure Cite where
  page : PageId
  span : Span
  version : Nat
  commitment : List UInt8
  mode : Mode
deriving DecidableEq, Repr

/-- Constructive decidable equality on `ByteArray`. -/
def decByteArray (a b : ByteArray) : Decidable (a = b) :=
  match decEq a.data b.data with
  | isTrue h => isTrue (by cases a; cases b; simp at h; subst h; rfl)
  | isFalse h => isFalse (by intro e; cases e; exact h rfl)

instance : DecidableEq ByteArray := decByteArray

instance : Repr ByteArray where
  reprPrec b p := reprPrec b.data p

/-- Discriminated structured cell projection kinds (Milestone 5 Feature 34 + Houyhnhnm CAE/PDE/Custody). -/
inductive ProjectionKind where
  | prose
  | obendCode
  | casSymbolic
  | leanBridge
  | lawContract
  | deosAffordance
  | hardwareSchematic
  | hardwareTiming
  | hardwareLayout
  | ledgerSeat
  | pdeConservation
  | feecSimplicialFem
  | pcbMultiphysicsDfm
  | vehicle6DofTrajectory
  | zkCustodyReceipt
  | frustumRedactedView
deriving DecidableEq, Repr

/-- What an atom carries. -/
inductive Content
  /-- a run of text -/
  | text (s : String)
  /-- a cite; `name` is the wikilink's text between its brackets, as written (`Beta`, `Beta#^b`) -/
  | cite (name : String) (c : Cite)
  /-- an assignment to a single-valued field (outside the order: it has no edges) -/
  | field (name value : String)
  /-- a structured quotation cell carrying Core.Data, footprint pins, and Merkle receipt -/
  | cell (id : String) (kind : ProjectionKind) (ast : Obend.Core.Data.Data)
         (pins : List (String × ByteArray)) (receipt : Option ByteArray)
deriving DecidableEq, Repr

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
def succs (G : Graph) (a : AtomId) : List AtomId :=
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
def grow (G : Graph) (S : List AtomId) : List AtomId :=
  S ++ (G.edges.filter fun e => S.contains e.1).map Prod.snd

/-- `n` steps of the forward cone. -/
def coneN (G : Graph) : Nat → List AtomId → List AtomId
  | 0, S => S
  | n + 1, S => G.coneN n (G.grow S)

/-- The strict forward cone of `a`, to depth the number of edges. -/
def cone (G : Graph) (a : AtomId) : List AtomId := G.coneN G.edges.length (G.succs a)

/-- The decided order: `b` is in the strict forward cone of `a`. -/
@[expose] def beforeB (G : Graph) (a b : AtomId) : Bool := (G.cone a).contains b

/-- `S` is closed under the order edges. -/
def Closed (G : Graph) (S : List AtomId) : Bool :=
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

/-! ### The cone, computed in $O(V + E)$ via `Array` adjacency & visited bitset

`coneN` grows the whole set by every edge at every step, keeping repeats: on a page of `E` edges it
does `E` steps over a list that can reach `E²` entries. On dense atom IDs (all authored pages),
`beforeBDense` builds an `Array (List AtomId)` adjacency table in one pass and runs a frontier BFS
with an in-place `Array Bool` visited table so each vertex and edge is visited at most once ($O(V + E)$),
falling back to `coneFrom` only if an unauthored graph carries sparse astronomical `AtomId`s. Both
hold the exact same atoms as `cone` (`beforeB_eq_fast`, `@[csimp]`). -/

/-- The successors of `fr` that `seen` does not hold, without repeats. -/
def fresh (G : Graph) (seen fr : List AtomId) : List AtomId :=
  ((fr.flatMap G.succs).filter fun y => !seen.contains y).eraseDups

/-- `n` steps of the cone from `seen`, growing from its frontier `fr`. -/
def coneFrom (G : Graph) : Nat → List AtomId → List AtomId → List AtomId
  | 0, seen, _ => seen
  | n + 1, seen, fr =>
    let new := G.fresh seen fr
    if new.isEmpty then seen else G.coneFrom n (seen ++ new) new

/-- Maximum endpoint `AtomId` appearing in `edges`. -/
def maxEdgeAtom : List (AtomId × AtomId) → Nat
  | [] => 0
  | (u, v) :: es => max (max u v) (maxEdgeAtom es)

theorem edges_lt_succ_maxEdgeAtom {es : List (AtomId × AtomId)} :
    ∀ e ∈ es, e.1 < maxEdgeAtom es + 1 ∧ e.2 < maxEdgeAtom es + 1 := by
  induction es with
  | nil => intro _ h; cases h
  | cons hd tl ih =>
    obtain ⟨u, v⟩ := hd
    intro e he
    obtain ⟨e1, e2⟩ := e
    simp only [maxEdgeAtom]
    rcases List.mem_cons.mp he with heq | htl
    · injection heq with h1 h2
      subst h1 h2
      exact ⟨Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_left e1 e2) (Nat.le_max_left _ _)),
        Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_right e1 e2) (Nat.le_max_left _ _))⟩
    · have ⟨h1, h2⟩ := ih (e1, e2) htl
      exact ⟨Nat.lt_of_lt_of_le h1 (Nat.add_le_add_right (Nat.le_max_right _ _) 1),
        Nat.lt_of_lt_of_le h2 (Nat.add_le_add_right (Nat.le_max_right _ _) 1)⟩

private theorem getElem?_set_any {α : Type} (arr : Array α) (x : Nat) (hx : x < arr.size)
    (v : α) (u : Nat) :
    (arr.set x v)[u]? = if x = u then some v else arr[u]? := by
  by_cases hu : u < arr.size
  · have hu' : u < (arr.set x v).size := by rw [Array.size_set]; exact hu
    rw [Array.getElem?_eq_getElem hu', Array.getElem?_eq_getElem hu, Array.getElem_set]
    by_cases hxu : x = u <;> simp only [hxu, ↓reduceIte]
  · have hu' : ¬(u < (arr.set x v).size) := by rw [Array.size_set]; exact hu
    have hne : x ≠ u := by omega
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hu'), Array.getElem?_eq_none (Nat.le_of_not_lt hu)]
    simp only [hne, ↓reduceIte]

/-- Build an adjacency `Array (List AtomId)` of size `bound` in a single $O(V + E)$ pass. -/
def buildAdj (bound : Nat) (edges : List (AtomId × AtomId)) : Array (List AtomId) :=
  edges.foldl (fun adj e =>
    if h : e.1 < adj.size then adj.set e.1 (e.2 :: adj[e.1]'h) else adj)
    (Array.replicate bound [])

private theorem buildAdj_fold_spec :
    ∀ (es : List (AtomId × AtomId)) (adj : Array (List AtomId)),
      (es.foldl (fun a e => if h : e.1 < a.size then a.set e.1 (e.2 :: a[e.1]'h) else a) adj).size = adj.size ∧
      ∀ u, u < adj.size → ∀ y,
        y ∈ ((es.foldl (fun a e => if h : e.1 < a.size then a.set e.1 (e.2 :: a[e.1]'h) else a) adj)[u]?.getD []) ↔
          y ∈ (adj[u]?.getD []) ∨ (u, y) ∈ es
  | [], adj => ⟨rfl, fun _ _ _ => ⟨Or.inl, fun h => h.elim id (fun hm => nomatch hm)⟩⟩
  | (x, v) :: rest, adj => by
    dsimp only [List.foldl_cons]
    by_cases hx : x < adj.size
    · simp only [hx, ↓reduceDIte]
      have hsz1 : (adj.set x (v :: adj[x]'hx)).size = adj.size := Array.size_set ..
      obtain ⟨hsz, hmem⟩ := buildAdj_fold_spec rest (adj.set x (v :: adj[x]'hx))
      refine ⟨hsz.trans hsz1, fun u hu y => ?_⟩
      rw [hmem u (hsz1.symm ▸ hu) y, getElem?_set_any adj x hx (v :: adj[x]'hx) u]
      by_cases hux : x = u
      · subst hux
        rw [Array.getElem?_eq_getElem hx]
        simp only [↓reduceIte, Option.getD_some, List.mem_cons, Prod.mk.injEq, true_and]
        exact ⟨fun h => h.elim (fun h1 => h1.elim (fun hv => .inr (.inl hv)) .inl) (fun hr => .inr (.inr hr)),
          fun h => h.elim (fun hl => .inl (.inr hl)) (fun hr => hr.elim (fun hv => .inl (.inl hv)) .inr)⟩
      · simp only [hux, ↓reduceIte, List.mem_cons, Prod.mk.injEq, Ne.symm hux, false_and, false_or]
    · simp only [hx, ↓reduceDIte]
      obtain ⟨hsz, hmem⟩ := buildAdj_fold_spec rest adj
      refine ⟨hsz, fun u hu y => ?_⟩
      rw [hmem u hu y]
      have hux : u ≠ x := fun heq => hx (heq ▸ hu)
      simp only [List.mem_cons, Prod.mk.injEq, hux, false_and, false_or]

theorem buildAdj_size (bound : Nat) (edges : List (AtomId × AtomId)) :
    (buildAdj bound edges).size = bound := by
  unfold buildAdj
  exact (buildAdj_fold_spec edges (Array.replicate bound [])).1.trans (Array.size_replicate ..)

theorem mem_buildAdj {bound : Nat} {G : Graph} {u : AtomId} (hu : u < bound) {y : AtomId} :
    y ∈ (buildAdj bound G.edges)[u]'(by rw [buildAdj_size]; exact hu) ↔ G.edge u y = true := by
  have hu' : u < (Array.replicate bound ([] : List AtomId)).size := by
    rw [Array.size_replicate]; exact hu
  have hspec := (buildAdj_fold_spec G.edges (Array.replicate bound [])).2 u hu' y
  have hub : u < (buildAdj bound G.edges).size := by rw [buildAdj_size]; exact hu
  change y ∈ ((buildAdj bound G.edges)[u]?.getD []) ↔ _ at hspec
  rw [Array.getElem?_eq_getElem hub, Array.getElem?_eq_getElem hu', Array.getElem_replicate] at hspec
  simp only [Option.getD_some, List.not_mem_nil, false_or] at hspec
  rw [edge, List.contains_iff_mem]
  exact hspec

/-- Mark unvisited neighbors in `vis` (in-place when unshared) and push newly discovered ones to `next`. -/
def pushNeighbors : List AtomId → Array Bool → List AtomId → Array Bool × List AtomId
  | [], vis, next => (vis, next)
  | y :: ys, vis, next =>
    if hy : y < vis.size then
      if vis[y]'hy then pushNeighbors ys vis next
      else pushNeighbors ys (vis.set y true) (y :: next)
    else pushNeighbors ys vis next

theorem pushNeighbors_size : ∀ (ys : List AtomId) (vis : Array Bool) (next : List AtomId),
    (pushNeighbors ys vis next).1.size = vis.size
  | [], _, _ => rfl
  | y :: ys, vis, next => by
    unfold pushNeighbors
    by_cases hy : y < vis.size
    · simp only [hy, ↓reduceDIte]
      split
      · exact pushNeighbors_size ys vis next
      · exact (pushNeighbors_size ys (vis.set y true) (y :: next)).trans (Array.size_set ..)
    · simp only [hy, ↓reduceDIte]
      exact pushNeighbors_size ys vis next

theorem pushNeighbors_spec :
    ∀ (ys : List AtomId) (vis : Array Bool) (next : List AtomId),
      (∀ y ∈ ys, y < vis.size) →
      (∀ z, z < vis.size → ((pushNeighbors ys vis next).1[z]? = some true ↔ vis[z]? = some true ∨ z ∈ ys)) ∧
      (∀ z, z ∈ (pushNeighbors ys vis next).2 ↔
        z ∈ next ∨ (z ∈ ys ∧ vis[z]? = some false))
  | [], vis, next, _ => by
    refine ⟨fun z _ => by simp [pushNeighbors], fun z => by simp [pushNeighbors]⟩
  | y :: ys, vis, next, hys => by
    have hy : y < vis.size := hys y List.mem_cons_self
    have hys' : ∀ w ∈ ys, w < vis.size := fun w hw => hys w (List.mem_cons_of_mem _ hw)
    unfold pushNeighbors
    simp only [hy, ↓reduceDIte]
    cases hvy : vis[y]'hy with
    | true =>
      have hvy? : vis[y]? = some true := by rw [Array.getElem?_eq_getElem hy, hvy]
      simp only [↓reduceIte]
      obtain ⟨ih1, ih2⟩ := pushNeighbors_spec ys vis next hys'
      refine ⟨fun z hz => ?_, fun z => ?_⟩
      · rw [ih1 z hz, List.mem_cons]
        constructor
        · rintro (hv | hmem)
          · exact .inl hv
          · exact .inr (.inr hmem)
        · rintro (hv | rfl | hmem)
          · exact .inl hv
          · exact .inl hvy?
          · exact .inr hmem
      · rw [ih2 z, List.mem_cons]
        constructor
        · rintro (hn | ⟨hmem, hvz⟩)
          · exact .inl hn
          · exact .inr ⟨.inr hmem, hvz⟩
        · rintro (hn | ⟨rfl | hmem, hvz⟩)
          · exact .inl hn
          · rw [hvy?] at hvz; cases hvz
          · exact .inr ⟨hmem, hvz⟩
    | false =>
      have hvy? : vis[y]? = some false := by rw [Array.getElem?_eq_getElem hy, hvy]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hsz : (vis.set y true).size = vis.size := Array.size_set ..
      obtain ⟨ih1, ih2⟩ := pushNeighbors_spec ys (vis.set y true) (y :: next) (by rwa [hsz])
      refine ⟨fun z hz => ?_, fun z => ?_⟩
      · rw [ih1 z (hsz.symm ▸ hz), getElem?_set_any vis y hy true z, List.mem_cons]
        by_cases hzy : y = z
        · subst hzy; simp only [↓reduceIte, true_or, or_true]
        · simp only [hzy, ↓reduceIte, Ne.symm hzy, false_or]
      · rw [ih2 z, getElem?_set_any vis y hy true z, List.mem_cons, List.mem_cons]
        by_cases hzy : z = y
        · subst hzy
          exact ⟨fun _ => .inr ⟨.inl rfl, hvy?⟩, fun _ => .inl (.inl rfl)⟩
        · have hne : y ≠ z := Ne.symm hzy
          simp only [hne, ↓reduceIte, hzy, false_or]

/-- Expand one frontier layer over `adj` using `vis` as an $O(1)$ visited table. -/
def bfsLayer (adj : Array (List AtomId)) : List AtomId → Array Bool → List AtomId → Array Bool × List AtomId
  | [], vis, next => (vis, next)
  | f :: fs, vis, next =>
    let nbrs := if hf : f < adj.size then adj[f]'hf else []
    let step := pushNeighbors nbrs vis next
    bfsLayer adj fs step.1 step.2

theorem bfsLayer_size (adj : Array (List AtomId)) :
    ∀ (fr : List AtomId) (vis : Array Bool) (next : List AtomId),
      (bfsLayer adj fr vis next).1.size = vis.size
  | [], _, _ => rfl
  | f :: fs, vis, next => by
    simp only [bfsLayer]
    exact (bfsLayer_size adj fs _ _).trans (pushNeighbors_size ..)

private theorem bool_getElem?_false_iff {arr : Array Bool} {z : Nat} (hz : z < arr.size) :
    arr[z]? = some false ↔ arr[z]? ≠ some true := by
  rw [Array.getElem?_eq_getElem hz]
  cases arr[z]'hz <;> simp

theorem bfsLayer_spec {bound : Nat} {G : Graph}
    (hbnd : ∀ e ∈ G.edges, e.1 < bound ∧ e.2 < bound) :
    ∀ (fr : List AtomId) (vis : Array Bool) (next : List AtomId),
      vis.size = bound →
      (∀ f ∈ fr, f < bound) →
      (∀ z, z < bound →
        ((bfsLayer (buildAdj bound G.edges) fr vis next).1[z]? = some true ↔
          vis[z]? = some true ∨ ∃ f ∈ fr, G.edge f z = true)) ∧
      (∀ z, z ∈ (bfsLayer (buildAdj bound G.edges) fr vis next).2 ↔
        z ∈ next ∨ ((∃ f ∈ fr, G.edge f z = true) ∧ vis[z]? = some false))
  | [], vis, next, _, _ => by
    refine ⟨fun z _ => by simp [bfsLayer], fun z => by simp [bfsLayer]⟩
  | f :: fs, vis, next, hvis, hfr => by
    have hf : f < bound := hfr f List.mem_cons_self
    have hfs : ∀ x ∈ fs, x < bound := fun x hx => hfr x (List.mem_cons_of_mem _ hx)
    have hf_adj : f < (buildAdj bound G.edges).size := by rw [buildAdj_size]; exact hf
    let nbrs := (buildAdj bound G.edges)[f]'hf_adj
    have hnbrs_mem : ∀ y, y ∈ nbrs ↔ G.edge f y = true := fun y => mem_buildAdj hf
    have hnbrs_lt : ∀ y ∈ nbrs, y < vis.size := by
      intro y hy
      rw [hvis]
      have he : (f, y) ∈ G.edges := List.contains_iff_mem.mp ((hnbrs_mem y).mp hy)
      exact (hbnd (f, y) he).2
    obtain ⟨hp1, hp2⟩ := pushNeighbors_spec nbrs vis next hnbrs_lt
    have hsz1 : (pushNeighbors nbrs vis next).1.size = bound :=
      (pushNeighbors_size ..).trans hvis
    obtain ⟨ih1, ih2⟩ := bfsLayer_spec hbnd fs (pushNeighbors nbrs vis next).1
      (pushNeighbors nbrs vis next).2 hsz1 hfs
    have hstep_eq : bfsLayer (buildAdj bound G.edges) (f :: fs) vis next =
        bfsLayer (buildAdj bound G.edges) fs (pushNeighbors nbrs vis next).1 (pushNeighbors nbrs vis next).2 := by
      simp only [bfsLayer, hf_adj, ↓reduceDIte, nbrs]
    refine ⟨fun z hz => ?_, fun z => ?_⟩
    · rw [hstep_eq, ih1 z hz, hp1 z (hvis.symm ▸ hz), hnbrs_mem z]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]
    · rw [hstep_eq, ih2 z, hp2 z, hnbrs_mem z]
      constructor
      · rintro ((hn | ⟨hef, hvz⟩) | ⟨⟨g, hg, heg⟩, hv1⟩)
        · exact .inl hn
        · exact .inr ⟨⟨f, List.mem_cons_self, hef⟩, hvz⟩
        · have hz_lt : z < bound := (hbnd (g, z) (List.contains_iff_mem.mp heg)).2
          have hn1 : (pushNeighbors nbrs vis next).1[z]? ≠ some true :=
            (bool_getElem?_false_iff (hsz1.symm ▸ hz_lt)).mp hv1
          have hnot_or : ¬(vis[z]? = some true ∨ G.edge f z = true) := by
            rw [← hnbrs_mem z, ← hp1 z (hvis.symm ▸ hz_lt)]
            exact hn1
          have hvz : vis[z]? = some false :=
            (bool_getElem?_false_iff (hvis.symm ▸ hz_lt)).mpr (fun ht => hnot_or (.inl ht))
          exact .inr ⟨⟨g, List.mem_cons_of_mem _ hg, heg⟩, hvz⟩
      · rintro (hn | ⟨⟨g, hg, heg⟩, hvz⟩)
        · exact .inl (.inl hn)
        · by_cases hef : G.edge f z = true
          · exact .inl (.inr ⟨hef, hvz⟩)
          · rcases List.mem_cons.mp hg with rfl | hg'
            · exact absurd heg hef
            · right
              have hz_lt : z < bound := (hbnd (g, z) (List.contains_iff_mem.mp heg)).2
              refine ⟨⟨g, hg', heg⟩, (bool_getElem?_false_iff (hsz1.symm ▸ hz_lt)).mpr ?_⟩
              intro hc
              rw [hp1 z (hvis.symm ▸ hz_lt), hnbrs_mem z] at hc
              rcases hc with ht | ht
              · rw [hvz] at ht; cases ht
              · exact hef ht

/-- Iterate `bfsLayer` up to `n` steps, stopping as soon as the frontier empties. -/
def bfsLoop (adj : Array (List AtomId)) : Nat → Array Bool → List AtomId → Array Bool
  | 0, vis, _ => vis
  | n + 1, vis, fr =>
    let step := bfsLayer adj fr vis []
    if step.2.isEmpty then step.1 else bfsLoop adj n step.1 step.2

theorem bfsLoop_size (adj : Array (List AtomId)) :
    ∀ (n : Nat) (vis : Array Bool) (fr : List AtomId),
      (bfsLoop adj n vis fr).size = vis.size
  | 0, _, _ => rfl
  | n + 1, vis, fr => by
    simp only [bfsLoop]
    split
    · exact bfsLayer_size ..
    · exact (bfsLoop_size adj n _ _).trans (bfsLayer_size ..)

/-- $O(V + E)$ `Array`-indexed cone membership check when all edge endpoints lie below `bound`. -/
def beforeBDense (bound : Nat) (G : Graph) (a b : AtomId) : Bool :=
  if hb : a < bound ∧ b < bound then
    let adj := buildAdj bound G.edges
    let nbrs := adj[a]'(by rw [buildAdj_size]; exact hb.1)
    let init := pushNeighbors nbrs (Array.replicate bound false) []
    if init.2.isEmpty then false
    else
      let vis := bfsLoop adj G.edges.length init.1 init.2
      vis[b]'(by rw [bfsLoop_size, pushNeighbors_size, Array.size_replicate]; exact hb.2)
  else false

/-- The decided order: $O(V + E)$ `Array`+bitset BFS on dense graphs, `coneFrom` on sparse IDs. -/
def beforeBFast (G : Graph) (a b : AtomId) : Bool :=
  let bound := maxEdgeAtom G.edges + 1
  if bound ≤ 8 * G.edges.length + 257 then
    beforeBDense bound G a b
  else
    (G.coneFrom G.edges.length (G.succs a) (G.succs a)).contains b

theorem mem_fresh {G : Graph} {seen fr : List AtomId} {y : AtomId} :
    y ∈ G.fresh seen fr ↔ y ∉ seen ∧ ∃ f ∈ fr, G.edge f y = true := by
  simp only [fresh, List.mem_eraseDups, List.mem_filter, List.mem_flatMap, mem_succs,
    Bool.not_eq_true']
  constructor
  · rintro ⟨⟨f, hf, he⟩, hn⟩
    refine ⟨fun hm => ?_, f, hf, he⟩
    rw [List.contains_iff_mem.2 hm] at hn
    exact Bool.noConfusion hn
  · rintro ⟨hn, f, hf, he⟩
    exact ⟨⟨f, hf, he⟩, Bool.eq_false_iff.2 fun h => hn (List.contains_iff_mem.1 h)⟩

/-- The cone's atoms depend only on the atoms it starts from. -/
theorem coneN_congr {G : Graph} : ∀ (n : Nat) {S T : List AtomId}, (∀ y, y ∈ S ↔ y ∈ T) →
    ∀ y, y ∈ G.coneN n S ↔ y ∈ G.coneN n T
  | 0, _, _, h => h
  | n + 1, S, T, h => coneN_congr n (S := G.grow S) (T := G.grow T) fun y => by
      simp only [mem_grow, h]

/-- A set closed under the edges is its own cone. -/
theorem coneN_closed {G : Graph} {S : List AtomId} (hc : ∀ x ∈ S, ∀ y, G.edge x y = true → y ∈ S) :
    ∀ (n : Nat) y, y ∈ G.coneN n S ↔ y ∈ S
  | 0, _ => Iff.rfl
  | n + 1, y => by
      have hg : ∀ z, z ∈ G.grow S ↔ z ∈ S := fun z => by
        rw [mem_grow]
        exact ⟨fun h => h.elim id fun ⟨x, hx, he⟩ => hc x hx z he, .inl⟩
      show y ∈ G.coneN n (G.grow S) ↔ y ∈ S
      rw [coneN_congr n hg y]
      exact coneN_closed hc n y

theorem coneN_lt_bound {G : Graph} {bound : Nat}
    (hbnd : ∀ e ∈ G.edges, e.1 < bound ∧ e.2 < bound) :
    ∀ (n : Nat) {S : List AtomId}, (∀ x ∈ S, x < bound) → ∀ y ∈ G.coneN n S, y < bound
  | 0, _, hS, y, hy => hS y hy
  | n + 1, _, hS, y, hy => by
    refine coneN_lt_bound hbnd n (fun z hz => ?_) y hy
    rcases mem_grow.mp hz with hzS | ⟨x, _, hxz⟩
    · exact hS z hzS
    · exact (hbnd (x, z) (List.contains_iff_mem.mp hxz)).2

theorem bfsLoop_coneN {G : Graph} {bound : Nat}
    (hbnd : ∀ e ∈ G.edges, e.1 < bound ∧ e.2 < bound) :
    ∀ (n : Nat) (vis : Array Bool) (fr S : List AtomId),
      vis.size = bound →
      (∀ x ∈ S, x < bound) →
      (∀ z, z < bound → (vis[z]? = some true ↔ z ∈ S)) →
      (∀ f ∈ fr, f ∈ S) →
      (∀ x ∈ S, ∀ z, G.edge x z = true → z ∈ S ∨ ∃ f ∈ fr, G.edge f z = true) →
      ∀ z, z < bound →
        ((bfsLoop (buildAdj bound G.edges) n vis fr)[z]? = some true ↔ z ∈ G.coneN n S)
  | 0, _, _, _, _, _, hs, _, _, z, hz => hs z hz
  | n + 1, vis, fr, S, hvis, hS_lt, hs, hfr_sub, hi, z, hz => by
    have hfr_lt : ∀ f ∈ fr, f < bound := fun f hf => hS_lt f (hfr_sub f hf)
    obtain ⟨hl1, hl2⟩ := bfsLayer_spec hbnd fr vis [] hvis hfr_lt
    let step := bfsLayer (buildAdj bound G.edges) fr vis []
    have hstep_sz : step.1.size = bound := (bfsLayer_size ..).trans hvis
    have hgrow_lt : ∀ w ∈ G.grow S, w < bound := by
      intro w hw
      rcases mem_grow.mp hw with hwS | ⟨x, _, hxw⟩
      · exact hS_lt w hwS
      · exact (hbnd (x, w) (List.contains_iff_mem.mp hxw)).2
    have hstep_mem : ∀ w, w < bound → (step.1[w]? = some true ↔ w ∈ G.grow S) := by
      intro w hw
      rw [hl1 w hw, hs w hw, mem_grow]
      constructor
      · rintro (hwS | ⟨f, hf, he⟩)
        · exact .inl hwS
        · exact .inr ⟨f, hfr_sub f hf, he⟩
      · rintro (hwS | ⟨x, hx, he⟩)
        · exact .inl hwS
        · rcases hi x hx w he with hwS | ⟨f, hf, hfw⟩
          · exact .inl hwS
          · exact .inr ⟨f, hf, hfw⟩
    unfold bfsLoop
    dsimp only
    by_cases hempty : (bfsLayer (buildAdj bound G.edges) fr vis []).2.isEmpty = true
    · simp only [hempty, ↓reduceIte]
      have hnil : step.2 = [] := List.isEmpty_iff.mp hempty
      have hclosed : ∀ x ∈ G.grow S, ∀ w, G.edge x w = true → w ∈ G.grow S := by
        intro x hx w hxw
        by_cases hxS : x ∈ S
        · exact mem_grow.mpr (.inr ⟨x, hxS, hxw⟩)
        · rcases mem_grow.mp hx with hxS' | ⟨u, huS, hux⟩
          · exact absurd hxS' hxS
          · rcases hi u huS x hux with hxS' | ⟨f, hf, hfx⟩
            · exact absurd hxS' hxS
            · have hx_lt : x < bound := hgrow_lt x hx
              have hvx_false : vis[x]? = some false :=
                (bool_getElem?_false_iff (hvis.symm ▸ hx_lt)).mpr (fun ht => hxS ((hs x hx_lt).mp ht))
              have hx_in2 : x ∈ step.2 :=
                (hl2 x).mpr (.inr ⟨⟨f, hf, hfx⟩, hvx_false⟩)
              rw [hnil] at hx_in2; cases hx_in2
      show step.1[z]? = some true ↔ z ∈ G.coneN n (G.grow S)
      rw [coneN_closed hclosed n z]
      exact hstep_mem z hz
    · simp only [hempty, Bool.false_eq_true, ↓reduceIte]
      show (bfsLoop (buildAdj bound G.edges) n step.1 step.2)[z]? = some true ↔
        z ∈ G.coneN n (G.grow S)
      refine bfsLoop_coneN hbnd n step.1 step.2 (G.grow S) hstep_sz hgrow_lt hstep_mem ?_ ?_ z hz
      · intro f hf
        obtain ⟨⟨g, hg, heg⟩, _⟩ := ((hl2 f).mp hf).resolve_left List.not_mem_nil
        exact mem_grow.mpr (.inr ⟨g, hfr_sub g hg, heg⟩)
      · intro x hx w hxw
        by_cases hxS : x ∈ S
        · exact .inl (mem_grow.mpr (.inr ⟨x, hxS, hxw⟩))
        · right
          refine ⟨x, ?_, hxw⟩
          rcases mem_grow.mp hx with hxS' | ⟨u, huS, hux⟩
          · exact absurd hxS' hxS
          · rcases hi u huS x hux with hxS' | ⟨f, hf, hfx⟩
            · exact absurd hxS' hxS
            · have hx_lt : x < bound := hgrow_lt x hx
              have hvx_false : vis[x]? = some false :=
                (bool_getElem?_false_iff (hvis.symm ▸ hx_lt)).mpr (fun ht => hxS ((hs x hx_lt).mp ht))
              exact (hl2 x).mpr (.inr ⟨⟨f, hf, hfx⟩, hvx_false⟩)

theorem beforeBDense_eq {bound : Nat} {G : Graph}
    (hbnd : ∀ e ∈ G.edges, e.1 < bound ∧ e.2 < bound) (a b : AtomId) :
    beforeBDense bound G a b = G.beforeB a b := by
  unfold beforeBDense beforeB cone
  by_cases hab : a < bound ∧ b < bound
  · rw [dif_pos hab]
    dsimp only
    have hnbrs_succs : ∀ y, y ∈ (buildAdj bound G.edges)[a]'(by rw [buildAdj_size]; exact hab.1) ↔
        y ∈ G.succs a := by
      intro y; rw [mem_buildAdj hab.1, mem_succs]
    have hsuccs_lt : ∀ y ∈ G.succs a, y < bound := by
      intro y hy
      exact (hbnd (a, y) (List.contains_iff_mem.mp (mem_succs.mp hy))).2
    have hnbrs_lt : ∀ y ∈ (buildAdj bound G.edges)[a]'(by rw [buildAdj_size]; exact hab.1),
        y < (Array.replicate bound false).size := by
      intro y hy; rw [Array.size_replicate]; exact hsuccs_lt y ((hnbrs_succs y).mp hy)
    obtain ⟨hp1, hp2⟩ := pushNeighbors_spec
      ((buildAdj bound G.edges)[a]'(by rw [buildAdj_size]; exact hab.1))
      (Array.replicate bound false) [] hnbrs_lt
    let init := pushNeighbors
      ((buildAdj bound G.edges)[a]'(by rw [buildAdj_size]; exact hab.1))
      (Array.replicate bound false) []
    have hinit_sz : init.1.size = bound :=
      (pushNeighbors_size ..).trans (Array.size_replicate ..)
    have hinit_mem : ∀ z, z < bound → (init.1[z]? = some true ↔ z ∈ G.succs a) := by
      intro z hz
      have hzr : z < (Array.replicate bound false).size := by rw [Array.size_replicate]; exact hz
      rw [hp1 z hzr, Array.getElem?_eq_getElem hzr, Array.getElem_replicate]
      simp only [Option.some.injEq, Bool.false_eq_true, false_or, hnbrs_succs]
    have hinit_fr : ∀ z, z ∈ init.2 ↔ z ∈ G.succs a := by
      intro z
      rw [hp2 z, hnbrs_succs]
      simp only [List.not_mem_nil, false_or]
      constructor
      · exact And.left
      · intro hz
        have hzr : z < (Array.replicate bound false).size := by
          rw [Array.size_replicate]; exact hsuccs_lt z hz
        exact ⟨hz, by rw [Array.getElem?_eq_getElem hzr, Array.getElem_replicate]⟩
    by_cases hemp : (pushNeighbors
        ((buildAdj bound G.edges)[a]'(by rw [buildAdj_size]; exact hab.1))
        (Array.replicate bound false) []).2.isEmpty = true
    · simp only [hemp, ↓reduceIte]
      have hnil2 : init.2 = [] := List.isEmpty_iff.mp hemp
      have hsuccs_nil : G.succs a = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro z hz
        have := (hinit_fr z).mpr hz
        rw [hnil2] at this; exact List.not_mem_nil this
      have hclosed_nil : ∀ x ∈ ([] : List AtomId), ∀ y, G.edge x y = true → y ∈ ([] : List AtomId) :=
        fun _ hx => nomatch hx
      rw [hsuccs_nil]
      symm
      apply Bool.eq_false_iff.mpr
      intro hcont
      have hmem := (coneN_closed hclosed_nil G.edges.length b).mp (List.contains_iff_mem.mp hcont)
      exact List.not_mem_nil hmem
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      have hloop := bfsLoop_coneN hbnd G.edges.length init.1 init.2 (G.succs a)
        hinit_sz hsuccs_lt hinit_mem
        (fun f hf => (hinit_fr f).mp hf)
        (fun x hx z hxz => .inr ⟨x, (hinit_fr x).mpr hx, hxz⟩)
        b hab.2
      have hb_sz : b < (bfsLoop (buildAdj bound G.edges) G.edges.length init.1 init.2).size := by
        rw [bfsLoop_size, hinit_sz]; exact hab.2
      rw [Array.getElem?_eq_getElem hb_sz, Option.some.injEq] at hloop
      exact Bool.eq_iff_iff.mpr (hloop.trans List.contains_iff_mem.symm)
  · rw [dif_neg hab]
    symm
    apply Bool.eq_false_iff.mpr
    intro hcont
    have hmem := List.contains_iff_mem.mp hcont
    by_cases ha : a < bound
    · have hb_ge : ¬(b < bound) := fun hb => hab ⟨ha, hb⟩
      have hsuccs_lt : ∀ y ∈ G.succs a, y < bound := by
        intro y hy
        exact (hbnd (a, y) (List.contains_iff_mem.mp (mem_succs.mp hy))).2
      exact hb_ge (coneN_lt_bound hbnd G.edges.length hsuccs_lt b hmem)
    · have hsuccs_nil : G.succs a = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro y hy
        exact ha (hbnd (a, y) (List.contains_iff_mem.mp (mem_succs.mp hy))).1
      rw [hsuccs_nil] at hmem
      have hclosed_nil : ∀ x ∈ ([] : List AtomId), ∀ y, G.edge x y = true → y ∈ ([] : List AtomId) :=
        fun _ hx => nomatch hx
      exact List.not_mem_nil ((coneN_closed hclosed_nil G.edges.length b).mp hmem)

theorem mem_coneFrom {G : Graph} : ∀ (n : Nat) (seen fr S : List AtomId),
    (∀ y, y ∈ seen ↔ y ∈ S) → (∀ f ∈ fr, f ∈ S) →
    (∀ x ∈ S, ∀ y, G.edge x y = true → y ∈ S ∨ ∃ f ∈ fr, G.edge f y = true) →
    ∀ y, y ∈ G.coneFrom n seen fr ↔ y ∈ G.coneN n S
  | 0, seen, _, S, hs, _, _, y => hs y
  | n + 1, seen, fr, S, hs, hf, hi, y => by
      simp only [coneFrom]
      by_cases hn : (G.fresh seen fr).isEmpty
      · rw [ite_eq_left hn]
        have he : G.fresh seen fr = [] := List.isEmpty_iff.1 hn
        have hc : ∀ x ∈ S, ∀ z, G.edge x z = true → z ∈ S := by
          intro x hx z hxz
          rcases hi x hx z hxz with h | ⟨f, hfr, hfz⟩
          · exact h
          · exact Decidable.byContradiction fun hz => by
              have : z ∈ G.fresh seen fr := mem_fresh.2 ⟨fun h => hz ((hs z).1 h), f, hfr, hfz⟩
              rw [he] at this; cases this
        show y ∈ seen ↔ y ∈ G.coneN n (G.grow S)
        have hg : ∀ z, z ∈ G.grow S ↔ z ∈ S := fun z => by
          rw [mem_grow]; exact ⟨fun h => h.elim id fun ⟨x, hx, he⟩ => hc x hx z he, .inl⟩
        rw [coneN_congr n hg y, coneN_closed hc n y, hs y]
      · rw [ite_eq_right hn]
        show y ∈ G.coneFrom n (seen ++ G.fresh seen fr) (G.fresh seen fr) ↔ y ∈ G.coneN n (G.grow S)
        apply mem_coneFrom n _ _ (G.grow S)
        · intro z
          rw [List.mem_append, mem_fresh, mem_grow, hs]
          constructor
          · rintro (h | ⟨_, f, hfr, he⟩)
            · exact .inl h
            · exact .inr ⟨f, hf f hfr, he⟩
          · rintro (h | ⟨x, hx, he⟩)
            · exact .inl h
            · rcases hi x hx z he with h | ⟨f, hfr, hfz⟩
              · exact .inl h
              · by_cases hz : z ∈ S
                · exact .inl hz
                · exact .inr ⟨hz, f, hfr, hfz⟩
        · intro f hfr
          obtain ⟨_, g, hg, he⟩ := mem_fresh.1 hfr
          exact mem_grow.2 (.inr ⟨g, hf g hg, he⟩)
        · intro x hx z hxz
          by_cases hxS : x ∈ S
          · exact .inl (mem_grow.2 (.inr ⟨x, hxS, hxz⟩))
          · right
            refine ⟨x, ?_, hxz⟩
            rcases mem_grow.1 hx with h | ⟨s, hsS, hsx⟩
            · exact absurd h hxS
            · rcases hi s hsS x hsx with h | ⟨f, hfr, hfx⟩
              · exact absurd h hxS
              · exact mem_fresh.2 ⟨fun h => hxS ((hs x).1 h), f, hfr, hfx⟩

/-- **The $O(V + E)$ `Array`+bitset cone is the cone**: `beforeB` compiled through `beforeBFast`. -/
@[csimp] theorem beforeB_eq_fast : @beforeB = @beforeBFast := by
  funext G a b
  unfold beforeBFast
  dsimp only
  split
  · exact (beforeBDense_eq edges_lt_succ_maxEdgeAtom a b).symm
  · simp only [beforeB, cone]
    have := mem_coneFrom (G := G) G.edges.length (G.succs a) (G.succs a) (G.succs a)
      (fun _ => Iff.rfl) (fun _ h => h) (fun x _ y he => .inr ⟨x, by assumption, he⟩) b
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, this]

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
