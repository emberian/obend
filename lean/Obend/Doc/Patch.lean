module
/-
# Obend.Doc.Patch — the four operations, `apply`, `compose`, `invert`

breadstuffs `dregg-doc/src/patch.rs`'s grammar: `Add | Delete | Connect | SetField`, each forward
operation APPENDS (a vertex, a tombstone, an edge, a field assignment), so applying never fails and
never destroys. Each has a DUAL that undoes it on the graph it acted on (`unadd`, `resurrect`,
`disconnect`, `unsetField`); `invert` reverses a patch and dualises each operation, so it is an
involution (`invert_invert`).

Two differences from the Rust, each because a theorem needed it:

* `SetField` carries an atom identity and stores the assignment as an atom of content `.field`.
  The Rust's superseding flag becomes `supersede`, a patch that assigns and tombstones the field's
  live assignments: monotone like every other forward operation, which is what puts fields inside
  the pushout of `Obend.Doc.Merge` instead of beside it (the Rust needs a base-reading three-way
  merge for them).
* the dual of `Add` removes the atom (`unadd`), where the Rust only disconnects its edge and leaves
  it alive and unreachable; with the removal `apply_invert` is a round trip on every observation,
  not only on the walk.

`apply_compose`: applying a composite is applying one then the other. `apply_invert`: a patch
EFFECTIVE on a graph (each operation changes the observation it targets, the RCCS caveat the Rust
names: `invert` is contextual) followed by its inverse is the same page. `apply_frame`: an atom the
patch does not touch keeps its content and status, so the round trip is the patch's business only on
the atoms it touches.
-/
public import Obend.Doc.Graph
public import Obend.Tactic.Tooth
@[expose] public section

namespace Obend.Doc

set_option autoImplicit false

/-- One edit. The first four are the authored grammar; the last four are their duals, which only
`invert` writes. -/
inductive Op
  /-- add the atom `id` with content `c`, ordered after `after` -/
  | add (id : AtomId) (c : Content) (after : AtomId)
  /-- tombstone `id` -/
  | delete (id : AtomId)
  /-- order `src` before `dst` -/
  | connect (src dst : AtomId)
  /-- assign `value` to the field `name`, as the assignment atom `id` -/
  | setField (id : AtomId) (name value : String)
  /-- the dual of `add`: remove the atom and its edge from `after` -/
  | unadd (id : AtomId) (c : Content) (after : AtomId)
  /-- the dual of `delete` -/
  | resurrect (id : AtomId)
  /-- the dual of `connect` -/
  | disconnect (src dst : AtomId)
  /-- the dual of `setField` -/
  | unsetField (id : AtomId) (name value : String)
deriving DecidableEq, Repr

/-- A patch: operations applied left to right. -/
abbrev Patch := List Op

namespace Op

/-- The operation that undoes this one. -/
def dual : Op → Op
  | .add i c a => .unadd i c a
  | .delete i => .resurrect i
  | .connect s d => .disconnect s d
  | .setField i n v => .unsetField i n v
  | .unadd i c a => .add i c a
  | .resurrect i => .delete i
  | .disconnect s d => .connect s d
  | .unsetField i n v => .setField i n v

@[simp] theorem dual_dual (o : Op) : o.dual.dual = o := by cases o <;> rfl

/-- An authored operation (one of the four). -/
def forward : Op → Bool
  | .add .. | .delete .. | .connect .. | .setField .. => true
  | _ => false

/-- The atoms an operation touches: whose content, status or incoming order it changes. -/
def touches : Op → List AtomId
  | .add i _ a | .unadd i _ a => [i, a]
  | .delete i | .resurrect i => [i]
  | .connect s d | .disconnect s d => [s, d]
  | .setField i _ _ | .unsetField i _ _ => [i]

/-- The operation changes the observation it targets: the RCCS condition under which its dual
undoes it. -/
def Effective (G : Graph) : Op → Prop
  | .add i _ a => G.label i = none ∧ G.edge a i = false
  | .delete i => G.isDead i = false
  | .connect s d => G.edge s d = false
  | .setField i _ _ => G.label i = none
  | .unadd i c a => G.label i = some c ∧ G.edge a i = true
  | .resurrect i => G.isDead i = true
  | .disconnect s d => G.edge s d = true
  | .unsetField i n v => G.label i = some (.field n v)

instance decEffective (G : Graph) (o : Op) : Decidable (o.Effective G) := by
  cases o <;> unfold Effective <;> infer_instance

end Op

namespace Graph

/-- Apply one operation. -/
def step (G : Graph) : Op → Graph
  | .add i c a => { G with atoms := G.atoms ++ [(i, c)], edges := G.edges ++ [(a, i)] }
  | .delete i => { G with dead := G.dead ++ [i] }
  | .connect s d => { G with edges := G.edges ++ [(s, d)] }
  | .setField i n v => { G with atoms := G.atoms ++ [(i, .field n v)] }
  | .unadd i _ a =>
    { G with atoms := G.atoms.filter (·.1 != i), edges := G.edges.filter (· != (a, i)) }
  | .resurrect i => { G with dead := G.dead.filter (· != i) }
  | .disconnect s d => { G with edges := G.edges.filter (· != (s, d)) }
  | .unsetField i _ _ => { G with atoms := G.atoms.filter (·.1 != i) }

/-- Apply a patch. -/
def apply (G : Graph) (p : Patch) : Graph := p.foldl step G

/-! ### Each operation, read through the observations -/

theorem lookup_cons_ne {β : Type} (l : List (AtomId × β)) {a k : AtomId} (v : β) (h : a ≠ k) :
    ((k, v) :: l).lookup a = l.lookup a := by
  have : (a == k) = false := by simpa using h
  simp [List.lookup, this]

theorem lookup_append_single {β : Type} (l : List (AtomId × β)) (i a : AtomId) (c : β) :
    (l ++ [(i, c)]).lookup a = match l.lookup a with
      | some x => some x
      | none => if a = i then some c else none := by
  induction l with
  | nil =>
    by_cases h : a = i
    · subst h; simp [List.lookup]
    · simp [lookup_cons_ne _ _ h, h, List.lookup]
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    by_cases h : a = k
    · subst h; simp [List.lookup]
    · rw [List.cons_append, lookup_cons_ne _ _ h, lookup_cons_ne _ _ h]; exact ih

theorem lookup_filter_ne {β : Type} (l : List (AtomId × β)) (i a : AtomId) :
    (l.filter (·.1 != i)).lookup a = if a = i then none else l.lookup a := by
  induction l with
  | nil => simp [List.lookup]
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : k = i
    · subst hk
      have : ((k, v).1 != k) = false := by simp
      rw [List.filter_cons, if_neg (by simp), ih]
      by_cases ha : a = k
      · simp [ha]
      · simp [ha, lookup_cons_ne _ _ ha]
    · rw [List.filter_cons, if_pos (by simpa using hk)]
      by_cases ha : a = k
      · subst ha; simp [List.lookup, hk]
      · rw [lookup_cons_ne _ _ ha, ih, lookup_cons_ne _ _ ha]

theorem lookup_append_or {β : Type} (l : List (AtomId × β)) (i a : AtomId) (c : β) :
    (l ++ [(i, c)]).lookup a = (l.lookup a).or (if a = i then some c else none) := by
  rw [lookup_append_single]; cases l.lookup a <;> rfl

section
variable (G : Graph) (a b i s d x : AtomId) (c : Content) (n v : String)

@[simp] theorem label_add : (G.step (.add i c x)).label a =
    (G.label a).or (if a = i then some c else none) := lookup_append_or ..
@[simp] theorem label_setField : (G.step (.setField i n v)).label a =
    (G.label a).or (if a = i then some (.field n v) else none) := lookup_append_or ..
@[simp] theorem label_unadd : (G.step (.unadd i c x)).label a = if a = i then none else G.label a :=
  lookup_filter_ne ..
@[simp] theorem label_unsetField : (G.step (.unsetField i n v)).label a =
    if a = i then none else G.label a := lookup_filter_ne ..
@[simp] theorem label_delete : (G.step (.delete i)).label a = G.label a := rfl
@[simp] theorem label_resurrect : (G.step (.resurrect i)).label a = G.label a := rfl
@[simp] theorem label_connect : (G.step (.connect s d)).label a = G.label a := rfl
@[simp] theorem label_disconnect : (G.step (.disconnect s d)).label a = G.label a := rfl

@[simp] theorem isDead_delete : (G.step (.delete i)).isDead a = (G.isDead a || decide (a = i)) := by
  simp [step, isDead]
@[simp] theorem isDead_resurrect :
    (G.step (.resurrect i)).isDead a = (G.isDead a && !decide (a = i)) := by
  simp only [step, isDead]; by_cases h : a = i <;> simp [h]
@[simp] theorem isDead_add : (G.step (.add i c x)).isDead a = G.isDead a := rfl
@[simp] theorem isDead_setField : (G.step (.setField i n v)).isDead a = G.isDead a := rfl
@[simp] theorem isDead_unadd : (G.step (.unadd i c x)).isDead a = G.isDead a := rfl
@[simp] theorem isDead_unsetField : (G.step (.unsetField i n v)).isDead a = G.isDead a := rfl
@[simp] theorem isDead_connect : (G.step (.connect s d)).isDead a = G.isDead a := rfl
@[simp] theorem isDead_disconnect : (G.step (.disconnect s d)).isDead a = G.isDead a := rfl

@[simp] theorem edge_add :
    (G.step (.add i c x)).edge a b = (G.edge a b || decide (a = x) && decide (b = i)) := by
  simp [step, edge]
@[simp] theorem edge_connect :
    (G.step (.connect s d)).edge a b = (G.edge a b || decide (a = s) && decide (b = d)) := by
  simp [step, edge]
@[simp] theorem edge_unadd :
    (G.step (.unadd i c x)).edge a b = (G.edge a b && !(decide (a = x) && decide (b = i))) := by
  simp only [step, edge]; by_cases h1 : a = x <;> by_cases h2 : b = i <;> simp [h1, h2]
@[simp] theorem edge_disconnect :
    (G.step (.disconnect s d)).edge a b = (G.edge a b && !(decide (a = s) && decide (b = d))) := by
  simp only [step, edge]; by_cases h1 : a = s <;> by_cases h2 : b = d <;> simp [h1, h2]
@[simp] theorem edge_delete : (G.step (.delete i)).edge a b = G.edge a b := rfl
@[simp] theorem edge_resurrect : (G.step (.resurrect i)).edge a b = G.edge a b := rfl
@[simp] theorem edge_setField : (G.step (.setField i n v)).edge a b = G.edge a b := rfl
@[simp] theorem edge_unsetField : (G.step (.unsetField i n v)).edge a b = G.edge a b := rfl

end

/-- An operation's effect depends only on the observations. -/
theorem Same.step {G H : Graph} (h : G.Same H) (o : Op) : (G.step o).Same (H.step o) := by
  obtain ⟨hl, hd, he⟩ := h
  refine ⟨funext fun a => ?_, funext fun a => ?_, funext fun a => funext fun b => ?_⟩ <;>
    cases o <;> simp [hl, hd, he]

theorem Same.apply {G H : Graph} (h : G.Same H) (p : Patch) : (G.apply p).Same (H.apply p) := by
  induction p generalizing G H with
  | nil => exact h
  | cons o p ih => exact ih (h.step o)

/-- The dual of an effective operation undoes it, and is effective on the graph it acts on. -/
theorem step_dual {G : Graph} {o : Op} (h : o.Effective G) :
    ((G.step o).step o.dual).Same G ∧ o.dual.Effective (G.step o) := by
  refine ⟨⟨funext fun a => ?_, funext fun a => ?_, funext fun a => funext fun b => ?_⟩, ?_⟩ <;>
  rcases o with ⟨i, c, x⟩ | i | ⟨x, i⟩ | ⟨i, n, v⟩ | ⟨i, c, x⟩ | i | ⟨x, i⟩ | ⟨i, n, v⟩ <;>
  simp only [Op.dual, Op.Effective] at h ⊢
  all_goals first
    | (simp; done)
    | (by_cases ha : a = x <;> by_cases hb : b = i <;> simp_all <;> done)
    | (by_cases ha : a = i <;> simp_all <;> done)
    | (by_cases ha : a = i <;> simp_all <;> cases hl : G.label a <;> simp_all <;> done)
    | (simp_all; done)

end Graph

namespace Patch

/-- Apply `p`, then `q`. As the Rust's: the forward operations append, so composition is
concatenation. -/
def compose (p q : Patch) : Patch := p ++ q

/-- The patch that undoes `p`: its operations reversed, each dualised. -/
def invert (p : Patch) : Patch := (p.map Op.dual).reverse

/-- Every operation of `p` is effective on the graph it acts on. -/
def Effective : Graph → Patch → Prop
  | _, [] => True
  | G, o :: p => o.Effective G ∧ Effective (G.step o) p

instance decEffective : (G : Graph) → (p : Patch) → Decidable (Effective G p)
  | _, [] => isTrue trivial
  | G, o :: p =>
    have := decEffective (G.step o) p
    inferInstanceAs (Decidable (_ ∧ _))

/-- The atoms a patch touches. -/
def touches (p : Patch) : List AtomId := p.flatMap Op.touches

/-- An authored patch: only the four forward operations. -/
def forward (p : Patch) : Bool := p.all Op.forward

/-- A field assignment that supersedes the field's live assignments in `G`: assign, and tombstone
the rest. -/
def supersede (G : Graph) (i : AtomId) (name value : String) : Patch :=
  .setField i name value ::
    (G.atoms.filterMap fun e => match e.2 with
      | .field n _ => if n = name && G.alive e.1 then some (.delete e.1) else none
      | _ => none)

end Patch

open Graph Patch

/-- **apply_compose.** Applying a composite is applying its parts in order. -/
theorem apply_compose (G : Graph) (p q : Patch) : G.apply (compose p q) = (G.apply p).apply q :=
  List.foldl_append

@[simp] theorem invert_invert (p : Patch) : invert (invert p) = p := by
  simp [invert, List.map_reverse, List.map_map, Function.comp_def]

theorem invert_cons (o : Op) (p : Patch) : invert (o :: p) = invert p ++ [o.dual] := by
  simp [invert]

theorem Op.effective_congr {G H : Graph} (h : G.Same H) (o : Op) :
    o.Effective G ↔ o.Effective H := by
  obtain ⟨hl, hd, he⟩ := h
  cases o <;> simp [Op.Effective, hl, hd, he]

theorem Patch.effective_congr {G H : Graph} (h : G.Same H) (p : Patch) :
    Patch.Effective G p ↔ Patch.Effective H p := by
  induction p generalizing G H with
  | nil => exact Iff.rfl
  | cons o p ih =>
    exact and_congr (Op.effective_congr h o) (ih (h.step o))

theorem Patch.effective_append (G : Graph) (p q : Patch) :
    Patch.Effective G (p ++ q) ↔ Patch.Effective G p ∧ Patch.Effective (G.apply p) q := by
  induction p generalizing G with
  | nil => simp [Patch.Effective, Graph.apply]
  | cons o p ih =>
    simp only [List.cons_append, Patch.Effective, ih, Graph.apply, List.foldl_cons, and_assoc]

/-- **apply_invert.** An effective patch followed by its inverse is the same page, on every
observation; and the inverse is effective where it acts, so the round trip runs the other way too. -/
theorem apply_invert {G : Graph} {p : Patch} (h : Patch.Effective G p) :
    ((G.apply p).apply (invert p)).Same G ∧ Patch.Effective (G.apply p) (invert p) := by
  induction p generalizing G with
  | nil => exact ⟨Same.refl G, trivial⟩
  | cons o p ih =>
    obtain ⟨ho, hp⟩ := h
    obtain ⟨ihs, ihe⟩ := ih hp
    have ⟨hd, hde⟩ := step_dual ho
    refine ⟨?_, ?_⟩
    · rw [invert_cons, Graph.apply, List.foldl_append]
      exact (ihs.step o.dual).trans hd
    · rw [invert_cons, Patch.effective_append]
      refine ⟨ihe, ?_⟩
      have hs : (((G.step o).apply p).apply (invert p)).Same (G.step o) := ihs
      exact ⟨(Op.effective_congr hs _).2 hde, trivial⟩

/-- **apply_frame.** An atom a patch does not touch keeps its content and its status. -/
theorem apply_frame (G : Graph) (p : Patch) {a : AtomId} (h : a ∉ touches p) :
    (G.apply p).label a = G.label a ∧ (G.apply p).isDead a = G.isDead a := by
  induction p generalizing G with
  | nil => exact ⟨rfl, rfl⟩
  | cons o p ih =>
    simp only [touches, List.flatMap_cons, List.mem_append, not_or] at h
    obtain ⟨ho, hp⟩ := h
    obtain ⟨h1, h2⟩ := ih (G.step o) hp
    rw [Graph.apply, List.foldl_cons]
    refine ⟨h1.trans ?_, h2.trans ?_⟩ <;>
      cases o <;> simp_all [Op.touches]

/-! ### Teeth -/

namespace Teeth

/-- Two runs, a delete, a reorder and a title. -/
def edit : Patch :=
  [.add 1 (.text "Hello, ") root, .add 2 (.text "world.") 1, .delete 1, .connect root 2,
    .setField 9 "title" "Greeting"]

example : Patch.Effective Graph.empty edit := by decide
example : (Graph.empty.apply edit).label 2 = some (.text "world.") ∧
    (Graph.empty.apply edit).alive 1 = false ∧ (Graph.empty.apply edit).alive 2 = true := by decide
/-- The round trip lands where it started on every atom the patch touches. -/
example : ∀ a ∈ touches edit, ((Graph.empty.apply edit).apply (invert edit)).label a = none ∧
    ((Graph.empty.apply edit).apply (invert edit)).isDead a = false := by decide
example : ((Graph.empty.apply edit).apply (invert edit)).edge root 2 = false := by decide

/-- The effectiveness premise has teeth: connecting an edge already there, then inverting, loses
the edge the page had. -/
def base : Graph := Graph.empty.apply [.add 1 (.text "a") root, .add 2 (.text "b") 1]
example : ¬ Patch.Effective base [.connect 1 2] := by decide
example : base.edge 1 2 = true ∧
    ((base.apply [.connect 1 2]).apply (invert [.connect 1 2])).edge 1 2 = false := by decide
example : ¬ ((base.apply [.connect 1 2]).apply (invert [.connect 1 2])).Same base := fun h => by
  have := congrFun (congrFun h.2.2 1) 2
  revert this; decide

end Teeth

#tooth apply_compose by mutation Patch.compose := fun p _ => p
#tooth apply_invert by mutation Patch.invert := fun p => p
#tooth apply_frame by mutation Op.touches := fun _ => []

end Obend.Doc

end
