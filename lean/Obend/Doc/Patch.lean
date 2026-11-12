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
import all Obend.Doc.Graph
public section

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
@[expose] def forward : Op → Bool
  | .add .. | .delete .. | .connect .. | .setField .. => true
  | _ => false

/-- The atoms an operation touches: whose content, status or incoming order it changes. -/
@[expose] def touches : Op → List AtomId
  | .add i _ a | .unadd i _ a => [i, a]
  | .delete i | .resurrect i => [i]
  | .connect s d | .disconnect s d => [s, d]
  | .setField i _ _ | .unsetField i _ _ => [i]

/-- The operation changes the observation it targets: the RCCS condition under which its dual
undoes it. -/
@[expose] def Effective (G : Graph) : Op → Prop
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
@[expose] def step (G : Graph) : Op → Graph
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
@[expose] def apply (G : Graph) (p : Patch) : Graph := p.foldl step G

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
@[expose] def Effective : Graph → Patch → Prop
  | _, [] => True
  | G, o :: p => o.Effective G ∧ Effective (G.step o) p

instance decEffective : (G : Graph) → (p : Patch) → Decidable (Effective G p)
  | _, [] => isTrue trivial
  | G, o :: p =>
    have := decEffective (G.step o) p
    inferInstanceAs (Decidable (_ ∧ _))

/-- The atoms a patch touches. -/
@[expose] def touches (p : Patch) : List AtomId := p.flatMap Op.touches

/-- An authored patch: only the four forward operations. -/
@[expose] def forward (p : Patch) : Bool := p.all Op.forward

/-- The atoms a patch tombstones, in order. -/
@[expose] def deletes : Patch → List AtomId
  | [] => []
  | .delete i :: p => i :: deletes p
  | _ :: p => deletes p

/-- The atoms a patch adds (runs, cites, cells and field assignments), in order. -/
@[expose] def adds : Patch → List AtomId
  | [] => []
  | .add i _ _ :: p => i :: adds p
  | .setField i _ _ :: p => i :: adds p
  | _ :: p => adds p

theorem forward_cons {o : Op} {p : Patch} : forward (o :: p) = (o.forward && forward p) := by
  simp [forward, List.all_cons]

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

/-- **A forward patch tombstones what it deletes and nothing else**: after an authored patch an
atom is dead when it was dead before or the patch deletes it. What a write's `deletions` measure
counts (`Obend.Vault.deletions`) is read through this. -/
theorem isDead_apply_forward (G : Graph) (p : Patch) (hf : forward p = true) (a : AtomId) :
    (G.apply p).isDead a = (G.isDead a || (deletes p).contains a) := by
  induction p generalizing G with
  | nil => simp [apply, deletes]
  | cons o p ih =>
    rw [forward_cons, Bool.and_eq_true] at hf
    have h := ih (G.step o) hf.2
    simp only [apply, List.foldl_cons] at h ⊢
    rw [h]
    cases o with
    | delete i => simp [step, isDead, deletes, List.contains_append, List.contains_cons, Bool.or_assoc]
    | add i c b => simp [step, isDead, deletes]
    | connect s d => simp [step, isDead, deletes]
    | setField i n v => simp [step, isDead, deletes]
    | unadd i c b => simp [Op.forward] at hf
    | resurrect i => simp [Op.forward] at hf
    | disconnect s d => simp [Op.forward] at hf
    | unsetField i n v => simp [Op.forward] at hf

-- Forgetting the deletions makes the theorem claim a delete leaves the atom alive.
#tooth isDead_apply_forward by mutation deletes := fun _ => []

/-- **A forward patch makes present what it adds and nothing else.** -/
theorem present_apply_forward (G : Graph) (p : Patch) (hf : forward p = true) (a : AtomId) :
    (G.apply p).present a = (G.present a || (adds p).contains a) := by
  induction p generalizing G with
  | nil => simp [apply, adds]
  | cons o p ih =>
    rw [forward_cons, Bool.and_eq_true] at hf
    have h := ih (G.step o) hf.2
    simp only [apply, List.foldl_cons] at h ⊢
    rw [h]
    cases o with
    | add i c b =>
      simp only [step, present, label, adds, lookup_append_single]
      cases G.atoms.lookup a with
      | some x => simp
      | none =>
        by_cases hi : a = i
        · subst hi; simp
        · simp [hi, Ne.symm hi]
    | setField i n v =>
      simp only [step, present, label, adds, lookup_append_single]
      cases G.atoms.lookup a with
      | some x => simp
      | none =>
        by_cases hi : a = i
        · subst hi; simp
        · simp [hi, Ne.symm hi]
    | delete i => simp [step, present, label, adds]
    | connect s d => simp [step, present, label, adds]
    | unadd i c b => simp [Op.forward] at hf
    | resurrect i => simp [Op.forward] at hf
    | disconnect s d => simp [Op.forward] at hf
    | unsetField i n v => simp [Op.forward] at hf

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

/-! ### Keyed Structured Cells (`Content.cell`) & Cell-Level Patching -/

mutual
/-- Constructive decidable equality on `Obend.Core.Data.Data` for 3-way cell diffs and merges. -/
def decDataExposed : (a b : Obend.Core.Data.Data) → Decidable (a = b)
  | .natural x, .natural y =>
    if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .natural _, .boolean _ => isFalse (by intro h; cases h)
  | .natural _, .label _ => isFalse (by intro h; cases h)
  | .natural _, .record _ => isFalse (by intro h; cases h)
  | .natural _, .variant _ _ => isFalse (by intro h; cases h)
  | .boolean _, .natural _ => isFalse (by intro h; cases h)
  | .boolean x, .boolean y =>
    if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .boolean _, .label _ => isFalse (by intro h; cases h)
  | .boolean _, .record _ => isFalse (by intro h; cases h)
  | .boolean _, .variant _ _ => isFalse (by intro h; cases h)
  | .label _, .natural _ => isFalse (by intro h; cases h)
  | .label _, .boolean _ => isFalse (by intro h; cases h)
  | .label x, .label y =>
    if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .label _, .record _ => isFalse (by intro h; cases h)
  | .label _, .variant _ _ => isFalse (by intro h; cases h)
  | .record _, .natural _ => isFalse (by intro h; cases h)
  | .record _, .boolean _ => isFalse (by intro h; cases h)
  | .record _, .label _ => isFalse (by intro h; cases h)
  | .record fs, .record gs =>
    match decFieldsExposed fs gs with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .record _, .variant _ _ => isFalse (by intro h; cases h)
  | .variant _ _, .natural _ => isFalse (by intro h; cases h)
  | .variant _ _, .boolean _ => isFalse (by intro h; cases h)
  | .variant _ _, .label _ => isFalse (by intro h; cases h)
  | .variant _ _, .record _ => isFalse (by intro h; cases h)
  | .variant l p, .variant m q =>
    if hl : l = m then
      match decDataExposed p q with
      | isTrue h => isTrue (by rw [hl, h])
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hl rfl)

def decFieldsExposed :
    (fs gs : List (String × Obend.Core.Data.Data)) → Decidable (fs = gs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | (n, a) :: fs, (m, b) :: gs =>
    if hn : n = m then
      match decDataExposed a b, decFieldsExposed fs gs with
      | isTrue h, isTrue h' => isTrue (by rw [hn, h, h'])
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hn rfl)
end

instance (priority := high) instDecidableEqDataExposed :
    DecidableEq Obend.Core.Data.Data := decDataExposed

namespace Graph

/-- Extract all live structured `.cell` atoms of `G` as a keyed `(cellId, Data)` association list. -/
@[expose] def keyedCells (G : Graph) : List (String × Obend.Core.Data.Data) :=
  G.atoms.filterMap fun e => match e.2 with
    | .cell id _ ast _ _ => if G.alive e.1 then some (id, ast) else none
    | _ => none

end Graph

namespace Patch

/-- A structured cell assignment that supersedes any live `.cell` atom with the same `cellId` in `G`:
adds the new cell atom `i` after `after`, and tombstones previous live cells with key `cellId`. -/
def supersedeCell (G : Graph) (i after : AtomId) (cellId : String)
    (kind : ProjectionKind) (ast : Obend.Core.Data.Data)
    (pins : List (String × ByteArray)) (receipt : Option ByteArray) : Patch :=
  .add i (.cell cellId kind ast pins receipt) after ::
    (G.atoms.filterMap fun e => match e.2 with
      | .cell id' _ _ _ _ => if id' = cellId && G.alive e.1 then some (.delete e.1) else none
      | _ => none)

/-- `supersedeCell` produces an authored forward patch (`Patch.forward = true`). -/
theorem supersedeCell_forward (G : Graph) (i after : AtomId) (cellId : String)
    (kind : ProjectionKind) (ast : Obend.Core.Data.Data)
    (pins : List (String × ByteArray)) (receipt : Option ByteArray) :
    (supersedeCell G i after cellId kind ast pins receipt).forward = true := by
  simp only [supersedeCell, forward, List.all_cons, Op.forward, Bool.true_and, List.all_eq_true,
    List.mem_filterMap]
  rintro o ⟨e, _, he⟩
  cases h2 : e.2 with
  | text _ => simp [h2] at he
  | cite _ _ => simp [h2] at he
  | field _ _ => simp [h2] at he
  | cell id' k' ast' pins' rec' =>
    simp only [h2] at he
    split at he
    · simp only [Option.some.injEq] at he; subst he; rfl
    · cases he

/-- Deduplicate a list of string keys, keeping the first occurrence of each key in order. -/
def dedupStringKeys : List String → List String
  | [] => []
  | k :: rest => k :: (dedupStringKeys rest).filter (· != k)

@[simp] theorem mem_dedupStringKeys {l : List String} {x : String} :
    x ∈ dedupStringKeys l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupStringKeys]
  | cons k rest ih =>
    simp only [dedupStringKeys, List.mem_cons, List.mem_filter, ih, bne_iff_ne]
    constructor
    · rintro (rfl | ⟨hIn, _⟩)
      · exact .inl rfl
      · exact .inr hIn
    · rintro (rfl | hIn)
      · exact .inl rfl
      · by_cases hEq : x = k
        · exact .inl hEq
        · exact .inr ⟨hIn, hEq⟩

theorem lookup_eq_none_of_not_mem_map_fst {β : Type} {l : List (String × β)} {k : String}
    (h : k ∉ l.map Prod.fst) :
    l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨k', v'⟩ := x
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hNe : (k == k') = false := beq_eq_false_iff_ne.2 h.1
    simp only [List.lookup, hNe]
    exact ih h.2

/-- Compute the keyed cell diff between `base` and `branch`: returns `(k, branch.lookup k)` for every
key `k` in `base` or `branch` whose value changed (`branch.lookup k ≠ base.lookup k`). -/
def diffKeyedCells
    (base branch : List (String × Obend.Core.Data.Data)) :
    List (String × Option Obend.Core.Data.Data) :=
  let keys := dedupStringKeys ((base.map Prod.fst) ++ (branch.map Prod.fst))
  keys.filterMap fun k =>
    let bVal := base.lookup k
    let brVal := branch.lookup k
    if brVal = bVal then none else some (k, brVal)

/-- Diffing any keyed cell state against itself produces zero changed keys. -/
@[simp] theorem diffKeyedCells_self (cells : List (String × Obend.Core.Data.Data)) :
    diffKeyedCells cells cells = [] := by
  simp [diffKeyedCells]

/-- Exact characterization of `diffKeyedCells`: `(k, v)` is in `diffKeyedCells base branch` iff
`branch.lookup k ≠ base.lookup k` and `v = branch.lookup k`. -/
theorem mem_diffKeyedCells
    (base branch : List (String × Obend.Core.Data.Data))
    (k : String) (v : Option Obend.Core.Data.Data) :
    (k, v) ∈ diffKeyedCells base branch ↔
      branch.lookup k ≠ base.lookup k ∧ v = branch.lookup k := by
  simp only [diffKeyedCells, List.mem_filterMap, mem_dedupStringKeys, List.mem_append]
  constructor
  · rintro ⟨k', _, hIf⟩
    by_cases hEq : branch.lookup k' = base.lookup k'
    · simp [hEq] at hIf
    · simp only [hEq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hIf
      obtain ⟨rfl, rfl⟩ := hIf
      exact ⟨hEq, rfl⟩
  · rintro ⟨hNe, rfl⟩
    refine ⟨k, ?_, by simp [hNe]⟩
    by_cases hInB : k ∈ base.map Prod.fst
    · exact .inl hInB
    · by_cases hInBr : k ∈ branch.map Prod.fst
      · exact .inr hInBr
      · exfalso
        apply hNe
        rw [lookup_eq_none_of_not_mem_map_fst hInBr, lookup_eq_none_of_not_mem_map_fst hInB]

end Patch

end Obend.Doc

end

