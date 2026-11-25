module
public import Obend.Doc.GroveLiveObject
public import Std.Data.TreeMap.Raw.Basic
public import Obend.Tactic.DataRefinement
import all Obend.Tactic.DataRefinement
import Std.Data.TreeMap.Raw.WF
import Std.Data.TreeMap.Raw.Lemmas

public section
namespace Obend.Doc.Grove
open Obend.Core.Term Obend.Core.Ty Obend.Core.Check Obend.Core.Machine
open Obend.Tactic.DataRefinement
open Std (TreeMap)
set_option autoImplicit false
attribute [local instance] lexOrd

abbrev Port := AtomId × Nat
/-- An immutable edge identity includes its occurrence UID, parent/slot and target. -/
abbrev Edge := Nat × Port × AtomId
abbrev Edge.port (e : Edge) : Port := e.2.1
abbrev Edge.target (e : Edge) : AtomId := e.2.2

/-- A delete records the live edges its author saw. This causal context distinguishes
pre-existing children from concurrent insertions below the severed edge. -/
abbrev Cut := Edge × List Edge

@[instance_reducible] def orderOn {A B : Type} [o : StrictLinearOrder B] (key : A → B)
    (inj : ∀ x y, key x = key y → x = y) : StrictLinearOrder A where
  lt x y := o.lt (key x) (key y)
  irrefl _ := o.irrefl _
  trans _ _ _ := o.trans _ _ _
  tri x y h k := inj x y (o.tri _ _ h k)

instance edgeOrder : StrictLinearOrder Edge :=
  orderOn (fun e => [e.1, e.port.1, e.port.2, e.target]) (by
    rintro ⟨i, ⟨p, s⟩, v⟩ ⟨j, ⟨q, t⟩, w⟩ h
    simpa [Edge.port, Edge.target, and_assoc] using h)

instance cutOrder : StrictLinearOrder Cut :=
  orderOn (fun cut => cut.1 :: cut.2) (by rintro ⟨_, _⟩ ⟨_, _⟩ h; simpa using h)

private def singleton {A : Type} [StrictLinearOrder A] (a : A) : SortedArraySet A :=
  ⟨#[a], List.pairwise_singleton ..⟩

structure StructurePatch where
  inserted : SortedArraySet Edge := SortedArraySet.empty
  removed : SortedArraySet Cut := SortedArraySet.empty

def apply (p g : StructurePatch) : StructurePatch :=
  ⟨SortedArraySet.union p.inserted g.inserted, SortedArraySet.union p.removed g.removed⟩

theorem apply_comm (p q g : StructurePatch) : apply p (apply q g) = apply q (apply p g) := by
  unfold apply
  congr 1
  · rw [← SortedArraySet.union_assoc, SortedArraySet.union_comm p.1 q.1, SortedArraySet.union_assoc]
  · rw [← SortedArraySet.union_assoc, SortedArraySet.union_comm p.2 q.2, SortedArraySet.union_assoc]

theorem apply_idem (p g : StructurePatch) : apply p (apply p g) = apply p g := by
  unfold apply
  congr 1 <;> rw [← SortedArraySet.union_assoc, SortedArraySet.union_idem]

def insert (e : Edge) : StructurePatch := ⟨singleton e, SortedArraySet.empty⟩

private def edgeIndex : List Edge → TreeMap.Raw Edge Unit compare
  | [] => ∅
  | e :: es => (edgeIndex es).insert e ()

private theorem edgeIndex_wf (edges : List Edge) : (edgeIndex edges).WF := by
  induction edges with
  | nil => exact Std.TreeMap.Raw.WF.emptyc
  | cons _ _ ih => exact ih.insert

private theorem edgeIndex_contains (edges : List Edge) (e : Edge) :
    (edgeIndex edges).contains e = edges.contains e := by
  induction edges with
  | nil => rfl
  | cons x xs ih =>
    have eq : (compare x e == Ordering.eq) = decide (e = x) := by
      rw [Bool.eq_iff_iff]
      rw [beq_iff_eq, decide_eq_true_eq, Std.compare_eq_iff_eq]
      exact eq_comm
    simp [edgeIndex, Std.TreeMap.Raw.contains_insert (edgeIndex_wf xs), ih, eq]

def liveEdges (g : StructurePatch) : List Edge :=
  let dead := edgeIndex (g.removed.val.toList.map Prod.fst)
  g.inserted.val.toList.filter fun e => !dead.contains e

def remove (g : StructurePatch) (e : Edge) : StructurePatch :=
  ⟨SortedArraySet.empty, singleton (e, liveEdges g)⟩

private theorem union_mem {A : Type} [StrictLinearOrder A] (a b : SortedArraySet A) (x : A) :
    x ∈ (SortedArraySet.union a b).val.toList ↔ x ∈ a.val.toList ∨ x ∈ b.val.toList := by
  simp only [← memB_iff]
  change (SortedArraySet.union a b).toSpec.mem x = true ↔ a.toSpec.mem x = true ∨ b.toSpec.mem x = true
  rw [SortedArraySet.unionFast_toSpec, FinSetSpec.mem_union, Bool.or_eq_true]

/-- Two indexes over the same canonical edge enumeration. -/
structure Adjacency where
  slots : TreeMap.Raw Port (List Edge) compare := ∅
  parents : TreeMap.Raw AtomId (List Edge) compare := ∅

def indexEdges : List Edge → Adjacency
  | [] => {}
  | e :: es =>
    let rest := indexEdges es
    ⟨rest.slots.insert e.port (e :: rest.slots.getD e.port []),
     rest.parents.insert e.target (e :: rest.parents.getD e.target [])⟩

private theorem index_wf (edges : List Edge) :
    (indexEdges edges).slots.WF ∧ (indexEdges edges).parents.WF := by
  induction edges with
  | nil => exact ⟨Std.TreeMap.Raw.WF.emptyc, Std.TreeMap.Raw.WF.emptyc⟩
  | cons e es ih => exact ⟨ih.1.insert, ih.2.insert⟩

theorem index_slot (edges : List Edge) (p : Port) :
    (indexEdges edges).slots.getD p [] = edges.filter (fun e => e.port == p) := by
  induction edges with
  | nil => simp [indexEdges]
  | cons e es ih =>
    by_cases h : e.port = p
    · simp [indexEdges, h, ih, (index_wf es).1]
    · simp [indexEdges, Std.TreeMap.Raw.getD_insert (index_wf es).1, h, ih, beq_eq_false_iff_ne.mpr h]

theorem index_parent (edges : List Edge) (v : Nat) :
    (indexEdges edges).parents.getD v [] = edges.filter (fun e => e.target == v) := by
  induction edges with
  | nil => simp [indexEdges]
  | cons e es ih =>
    by_cases h : e.target = v
    · simp [indexEdges, h, ih, (index_wf es).2]
    · simp [indexEdges, Std.TreeMap.Raw.getD_insert (index_wf es).2, h, ih, beq_eq_false_iff_ne.mpr h]

/-- Vertices are immutable. Replacing a subtree allocates vertices and edits edges.
The catalog certificate checks every leaf and application boundary before freezing. -/
inductive Vertex where
  | leaf (type : Ty) (term : Term)
  | app (reuse : Reuse) (quantity : Quantity) (domain range : Ty)

def Vertex.type : Vertex → Ty
  | .leaf t _ => t
  | .app _ _ _ t => t

def Vertex.Valid : Vertex → Prop
  | .leaf ty term => PartialTyping {} [] term ty []
  | .app _ q dom _ => argumentAllowed {} q [] dom [] = true

abbrev Catalog := TreeMap.Raw AtomId Vertex compare

/-- A certificate concerns the exact vertices that lookup can return. -/
def Catalog.Valid (nodes : Catalog) : Prop :=
  ∀ id v, nodes.get? id = some v → v.Valid

def catalogOf : List (AtomId × {v : Vertex // v.Valid}) → Catalog
  | [] => ∅
  | (id, v) :: rest => (catalogOf rest).insert id v.val

private theorem catalogOf_wf (entries : List (AtomId × {v : Vertex // v.Valid})) :
    (catalogOf entries).WF := by
  induction entries with
  | nil => exact Std.TreeMap.Raw.WF.emptyc
  | cons e _ ih => exact ih.insert

theorem catalogOf_valid (entries : List (AtomId × {v : Vertex // v.Valid})) :
    (catalogOf entries).Valid := by
  induction entries with
  | nil => intro id v lookup; simp [catalogOf, Std.TreeMap.Raw.get?_eq_getElem?] at lookup
  | cons e rest ih =>
    intro id v lookup
    obtain ⟨k, w, valid⟩ := e
    simp only [catalogOf, Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_insert (catalogOf_wf rest)] at lookup
    split at lookup
    · cases lookup; exact valid
    · exact ih id v lookup

inductive Conflict where
  | empty
  | alternatives (edges : List Edge)
  | multiParent (vertex : AtomId) (incoming : List Edge)
  | mismatch (vertex : AtomId) (actual : Ty)
  | unknownVertex (vertex : AtomId)
  | cycle (vertex : AtomId)
  | deletedParentModifiedChild (cut edit : Edge)
  deriving Repr

structure ConflictHole where
  port : Port
  expected : Ty
  reason : Conflict
  deriving Repr

inductive Marked where
  | code (term : Term)
  | app (fn arg : Marked)
  | hole (h : ConflictHole)

/-- A covered root consists of the ordinary program and independently demandable
conflicts. Even a cut below a now unreachable ancestor remains visible here. -/
structure LiveRoot where
  program : Marked
  detached : List ConflictHole

/-- Bounded structural projection. A simple path cannot use more edges than the
live set contains. Revisiting a vertex identifies a cycle before descending. -/
def project (nodes : Catalog) (idx : Adjacency) :
    Nat → List AtomId → Port → Ty → Marked
  | fuel, seen, p, expected =>
    match idx.slots.getD p [] with
    | [] => .hole ⟨p, expected, .empty⟩
    | [e] =>
      let v := e.target
      match idx.parents.getD v [] with
      | a :: b :: more => .hole ⟨p, expected, .multiParent v (a :: b :: more)⟩
      | _ =>
        match nodes.get? v with
        | none => .hole ⟨p, expected, .unknownVertex v⟩
        | some node =>
          if node.type != expected then .hole ⟨p, expected, .mismatch v node.type⟩
          else if seen.contains v then .hole ⟨p, expected, .cycle v⟩
          else match node with
          | .leaf _ t => .code t
          | .app reuse q dom ran =>
            match fuel with
            | 0 => .hole ⟨p, expected, .cycle v⟩
            | n + 1 => .app (project nodes idx n (v :: seen) (v, 0) (.arrow reuse q dom ran))
                             (project nodes idx n (v :: seen) (v, 1) dom)
    | a :: b :: more => .hole ⟨p, expected, .alternatives (a :: b :: more)⟩

/-- The transitive descendant set, including the starting vertex. Each vertex's
outgoing edges are expanded only on its first visit. -/
private def visit (children : TreeMap.Raw Nat (List Nat) compare) : Nat → List Nat → TreeMap.Raw Nat Unit compare → TreeMap.Raw Nat Unit compare
  | 0, _, seen => seen
  | _, [], seen => seen
  | n + 1, v :: todo, seen =>
    if seen.contains v then visit children n todo seen
    else visit children n (children.getD v [] ++ todo) (seen.insert v ())

private def childrenIndex : List Edge → TreeMap.Raw Nat (List Nat) compare
  | [] => ∅
  | e :: es =>
    let rest := childrenIndex es
    rest.insert e.port.1 (e.target :: rest.getD e.port.1 [])

private theorem children_wf (edges : List Edge) : (childrenIndex edges).WF := by
  induction edges with
  | nil => exact Std.TreeMap.Raw.WF.emptyc
  | cons _ _ ih => exact ih.insert

private theorem children_at (edges : List Edge) (v : Nat) :
    (childrenIndex edges).getD v [] = (edges.filter (fun e => e.port.1 == v)).map Edge.target := by
  induction edges with
  | nil => simp [childrenIndex]
  | cons e es ih =>
    by_cases h : e.port.1 = v
    · simp [childrenIndex, h, ih, children_wf]
    · simp [childrenIndex, Std.TreeMap.Raw.getD_insert (children_wf es), h, ih, beq_eq_false_iff_ne.mpr h]

private abbrev Visited := TreeMap.Raw Nat Unit compare

private def below (children : TreeMap.Raw Nat (List Nat) compare) (count : Nat) (child : Nat) : Visited :=
  visit children (count + 1) [child] ∅

private theorem visit_keeps (children : TreeMap.Raw Nat (List Nat) compare) (n : Nat) (todo : List Nat)
    (seen : Visited) (wf : seen.WF) {v : Nat} (h : v ∈ seen) : v ∈ visit children n todo seen := by
  induction n generalizing todo seen with
  | zero => exact h
  | succ n ih =>
    cases todo with
    | nil => exact h
    | cons x xs =>
      simp only [visit]; split
      · exact ih _ _ wf h
      · exact ih _ _ wf.insert ((Std.TreeMap.Raw.mem_insert wf).mpr (Or.inr h))

private def unopened (edges : List Edge) (seen : Visited) :=
  (edges.filter fun e => !seen.contains e.port.1).length

/-- Opening a fresh vertex moves exactly its outgoing edges to the worklist. -/
private theorem opening_cost (edges : List Edge) (seen : Visited) (wf : seen.WF)
    (v : Nat) (fresh : seen.contains v = false) :
    ((edges.filter fun e => e.port.1 == v).length + unopened edges (seen.insert v ())) =
      unopened edges seen := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    by_cases eq : e.port.1 = v
    · simp [unopened, eq, fresh, wf, Nat.add_assoc] at ih ⊢
      omega
    · simp [unopened, Std.TreeMap.Raw.contains_insert wf, beq_eq_false_iff_ne.mpr eq,
        show (compare v e.port.1 == .eq) = false by simpa [Std.compare_eq_iff_eq] using Ne.symm eq,
        List.filter_cons] at ih ⊢
      split <;> simp_all <;> omega

private def Pending (edges : List Edge) (seen : Visited) (todo : List Nat) : Prop :=
  ∀ e ∈ edges, e.port.1 ∈ seen → e.target ∈ seen ∨ e.target ∈ todo

private theorem visit_closes (edges : List Edge) (fuel : Nat) (todo : List Nat) (seen : Visited)
    (wf : seen.WF) (enough : todo.length + unopened edges seen ≤ fuel) (pending : Pending edges seen todo) :
    let out := visit (childrenIndex edges) fuel todo seen
    (∀ v ∈ todo, v ∈ out) ∧ ∀ e ∈ edges, e.port.1 ∈ out → e.target ∈ out := by
  induction fuel generalizing todo seen with
  | zero =>
    have hn : todo = [] := List.length_eq_zero_iff.mp (by omega)
    subst todo
    exact ⟨by simp, fun e he hv => (pending e he hv).resolve_right (by simp)⟩
  | succ n ih =>
    cases todo with
    | nil => exact ⟨by simp, fun e he hv => (pending e he hv).resolve_right (by simp)⟩
    | cons x xs =>
      simp only [List.length_cons] at enough
      simp only [visit]
      split
      · rename_i hx
        have member := Std.TreeMap.Raw.contains_iff_mem.mp hx
        have tail : Pending edges seen xs := by
          intro e he hv
          rcases pending e he hv with done | todo
          · exact .inl done
          · rcases List.mem_cons.mp todo with eq | rest
            · exact .inl (eq ▸ member)
            · exact .inr rest
        obtain ⟨covered, closed⟩ := ih xs seen wf (by omega) tail
        refine ⟨?_, closed⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | rest
        · exact visit_keeps _ _ _ _ wf member
        · exact covered _ rest
      · rename_i hx
        have fresh := Bool.eq_false_iff.mpr hx
        have added : x ∈ seen.insert x () := Std.TreeMap.Raw.mem_insert_self wf
        have restBudget := opening_cost edges seen wf x fresh
        have budget : ((childrenIndex edges).getD x [] ++ xs).length +
            unopened edges (seen.insert x ()) ≤ n := by
          rw [List.length_append, children_at, List.length_map]
          omega
        have tail : Pending edges (seen.insert x ()) ((childrenIndex edges).getD x [] ++ xs) := by
          intro e he hv
          rcases (Std.TreeMap.Raw.mem_insert wf).mp hv with same | prior
          · have eq : x = e.port.1 := Std.compare_eq_iff_eq.mp same
            apply Or.inr ∘ List.mem_append_left _
            rw [children_at]
            exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, beq_iff_eq.mpr eq.symm⟩, rfl⟩
          · rcases pending e he prior with done | todo
            · exact .inl ((Std.TreeMap.Raw.mem_insert wf).mpr (.inr done))
            · rcases List.mem_cons.mp todo with eq | rest
              · exact .inl (eq ▸ added)
              · exact .inr (List.mem_append_right _ rest)
        obtain ⟨covered, closed⟩ := ih _ _ wf.insert budget tail
        refine ⟨?_, closed⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | rest
        · exact visit_keeps _ _ _ _ wf.insert added
        · exact covered _ (List.mem_append_right _ rest)

inductive EdgePath (edges : List Edge) (start : Nat) : Nat → Prop where
  | here : EdgePath edges start start
  | next {e : Edge} : EdgePath edges start e.port.1 → e ∈ edges → EdgePath edges start e.target

private theorem EdgePath.incoming {edges : List Edge} {start v : Nat} (path : EdgePath edges start v) :
    start = v ∨ ∃ e ∈ edges, e.target = v := by
  cases path with
  | here => exact .inl rfl
  | next _ he => exact .inr ⟨_, he, rfl⟩

private theorem below_path {edges : List Edge} {start v : Nat} (path : EdgePath edges start v) :
    v ∈ below (childrenIndex edges) edges.length start := by
  have result := visit_closes edges (edges.length + 1) [start] ∅ Std.TreeMap.Raw.WF.emptyc
    (by have bound := List.length_filter_le (fun e : Edge => !(∅ : Visited).contains e.port.1) edges
        change 1 + _ ≤ _; unfold unopened; omega) (by intro e _ h; simp at h)
  induction path with
  | here => exact result.1 _ (.head _)
  | next _ he ih => exact result.2 _ he ih

/-- Reachability from any live occurrence at the selected document port. -/
def RootPath (edges : List Edge) (port : Port) (v : AtomId) : Prop :=
  ∃ e ∈ edges, e.port = port ∧ EdgePath edges e.target v

private theorem visit_sound (edges : List Edge) (P : Nat → Prop)
    (step : ∀ e ∈ edges, P e.port.1 → P e.target)
    (fuel : Nat) (todo : List Nat) (seen : Visited) (wf : seen.WF)
    (queued : ∀ v ∈ todo, P v) (known : ∀ v ∈ seen, P v) :
    ∀ v ∈ visit (childrenIndex edges) fuel todo seen, P v := by
  induction fuel generalizing todo seen with
  | zero => exact known
  | succ n ih =>
    cases todo with
    | nil => exact known
    | cons x xs =>
      simp only [visit]
      have head := queued x (.head _)
      have tail := fun v (h : v ∈ xs) => queued v (.tail _ h)
      split
      · exact ih xs seen wf tail known
      · apply ih _ _ wf.insert
        · intro v hv
          rcases List.mem_append.mp hv with child | rest
          · rw [children_at] at child
            obtain ⟨e, mem, rfl⟩ := List.mem_map.mp child
            obtain ⟨live, src⟩ := List.mem_filter.mp mem
            exact step _ live ((beq_iff_eq.mp src) ▸ head)
          · exact tail _ rest
        · intro v hv
          rcases (Std.TreeMap.Raw.mem_insert wf).mp hv with eq | old
          · exact (Std.compare_eq_iff_eq.mp eq) ▸ head
          · exact known _ old

private def reachableFrom (edges : List Edge) (children : TreeMap.Raw Nat (List Nat) compare)
    (idx : Adjacency) (port : Port) : Visited :=
  let starts := (idx.slots.getD port []).map Edge.target
  visit children (edges.length + starts.length) starts ∅

private theorem reachable_from_iff (edges : List Edge) (p : Port) (v : Nat) :
    v ∈ reachableFrom edges (childrenIndex edges) (indexEdges edges) p ↔ RootPath edges p v := by
  let starts := ((indexEdges edges).slots.getD p []).map Edge.target
  have start_mem (x : Nat) : x ∈ starts ↔ ∃ e ∈ edges, e.port = p ∧ e.target = x := by
    simp only [starts, index_slot, List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨e, ⟨he, port⟩, target⟩
      exact ⟨e, he, port, target⟩
    · rintro ⟨e, he, port, target⟩
      exact ⟨e, ⟨he, port⟩, target⟩
  constructor
  · apply visit_sound edges (RootPath edges p) _ _ starts ∅ Std.TreeMap.Raw.WF.emptyc _ (by simp)
    · rintro e he ⟨first, hf, hp, path⟩
      exact ⟨first, hf, hp, path.next he⟩
    · intro x h
      obtain ⟨first, hf, hp, rfl⟩ := (start_mem x).mp h
      exact ⟨first, hf, hp, .here⟩
  · rintro ⟨first, hf, hp, path⟩
    have budget : starts.length + unopened edges ∅ ≤ edges.length + starts.length := by
      have bound := List.length_filter_le (fun e : Edge => !(∅ : Visited).contains e.port.1) edges
      unfold unopened; omega
    have covers := visit_closes edges _ starts ∅ Std.TreeMap.Raw.WF.emptyc budget (by intro e _ h; simp at h)
    induction path with
    | here => exact covers.1 _ ((start_mem _).mpr ⟨first, hf, hp, rfl⟩)
    | next _ he ih => exact covers.2 _ he ih

private def cutHoles (expected : Port → Ty) (edges : List Edge)
    (children : TreeMap.Raw Nat (List Nat) compare) (reachable : Visited)
    (live : TreeMap.Raw Edge Unit compare) (cut : Cut) : List ConflictHole :=
  if reachable.contains cut.1.target then [] else
    let region := below children edges.length cut.1.target
    let known := edgeIndex cut.2
    let added := edges.filter fun e => region.contains e.port.1 && !known.contains e
    let removed := cut.2.filter fun e => region.contains e.port.1 && e != cut.1 && !live.contains e
    (added ++ removed).map fun edit =>
      ⟨cut.1.port, expected cut.1.port, .deletedParentModifiedChild cut.1 edit⟩

/-- Entry ports get their type from the document. Internal application slots get
the domain or function type declared on their immutable parent vertex. -/
def portType (nodes : Catalog) (entry : Port → Ty) (p : Port) : Ty :=
  match nodes.get? p.1, p.2 with
  | some (.app r q dom ran), 0 => .arrow r q dom ran
  | some (.app _ _ dom _), 1 => dom
  | _, _ => entry p

def liveRoot (nodes : Catalog) (expected : Port → Ty) (rootPort : Port)
    (g : StructurePatch) : LiveRoot :=
  let edges := liveEdges g
  let live := edgeIndex edges
  let idx := indexEdges edges
  let children := childrenIndex edges
  let reachable := reachableFrom edges children idx rootPort
  let portTy := portType nodes expected
  ⟨project nodes idx nodes.size [] rootPort (portTy rootPort),
   g.removed.val.toList.flatMap (cutHoles portTy edges children reachable live)⟩

/-- A new or withdrawn edge at any depth below a disconnected child is visible
from the selected root, including when the child has incoming edges from other orphans. -/
theorem DeleteModifyCover (nodes : Catalog) (expected : Port → Ty)
    (rootPort : Port) (g : StructurePatch) (cut : Cut) (edit : Edge)
    (deleted : cut ∈ g.removed.val.toList)
    (changed : (edit ∈ liveEdges g ∧ edit ∉ cut.2) ∨ (edit ∈ cut.2 ∧ edit ≠ cut.1 ∧ edit ∉ liveEdges g))
    (inside : EdgePath (liveEdges g) cut.1.target edit.port.1)
    (detached : ¬ RootPath (liveEdges g) rootPort cut.1.target) :
    ⟨cut.1.port, portType nodes expected cut.1.port, .deletedParentModifiedChild cut.1 edit⟩ ∈
      (liveRoot nodes expected rootPort g).detached := by
  apply List.mem_flatMap.mpr
  refine ⟨cut, deleted, ?_⟩
  have unreachable := fun h => detached ((reachable_from_iff _ _ _).mp h)
  unfold cutHoles
  rw [ite_eq_right (fun h => unreachable (Std.TreeMap.Raw.contains_iff_mem.mp h))]
  apply List.mem_map.mpr
  refine ⟨edit, ?_, rfl⟩
  have region := Std.TreeMap.Raw.contains_iff_mem.mpr (below_path inside)
  rcases changed with ⟨live, unseen⟩ | ⟨known, other, gone⟩
  · apply List.mem_append_left _ (List.mem_filter.mpr ⟨live, ?_⟩)
    simp [region, edgeIndex_contains, unseen]
  · apply List.mem_append_right _ (List.mem_filter.mpr ⟨known, ?_⟩)
    simp [region, edgeIndex_contains, other, gone]

private theorem mem_live (g : StructurePatch) (e : Edge) :
    e ∈ liveEdges g ↔ e ∈ g.inserted.val.toList ∧ ∀ cut ∈ g.removed.val.toList, cut.1 ≠ e := by
  simp [liveEdges, edgeIndex_contains, Array.mem_toList_iff]
  intro _
  constructor
  · intro missing i v slot dst context member eq
    exact missing context (eq ▸ member)
  · rintro no context member
    obtain ⟨i, ⟨v, slot⟩, dst⟩ := e
    exact no i v slot dst context member rfl

/-- Both delivery orders surface a simultaneous delete and previously unseen child
insertion. In the base the cut was the child's only incoming edge. -/
theorem concurrent_delete_insert (nodes : Catalog) (expected : Port → Ty)
    (rootPort : Port) (base : StructurePatch) (edge edit : Edge)
    (parentLive : edge ∈ liveEdges base)
    (onlyParent : ∀ other ∈ liveEdges base, other.target = edge.target → other = edge)
    (fresh : edit ∉ base.inserted.val.toList) (neverDeleted : ∀ cut ∈ base.removed.val.toList, cut.1 ≠ edit)
    (childEdit : edit.port.1 = edge.target) (noLoop : edit.target ≠ edge.target) :
    let d := remove base edge
    let p := insert edit
    let h : ConflictHole := ⟨edge.port, portType nodes expected edge.port, .deletedParentModifiedChild edge edit⟩
    h ∈ (liveRoot nodes expected rootPort (apply d (apply p base))).detached ∧
    h ∈ (liveRoot nodes expected rootPort (apply p (apply d base))).detached := by
  dsimp only
  rw [apply_comm (insert edit) (remove base edge)]
  apply (fun proof => And.intro proof proof)
  apply DeleteModifyCover (cut := (edge, liveEdges base))
  · simp only [apply, remove, union_mem]
    simp [singleton]
  · left
    refine ⟨?_, fun h => fresh ((mem_live base edit).mp h).1⟩
    rw [mem_live]
    constructor
    · simp only [apply, insert, union_mem]
      simp [singleton]
    · intro cut member
      simp only [apply, insert, remove, union_mem] at member
      simp [singleton, SortedArraySet.empty] at member
      rcases member with rfl | hm
      · intro eq; exact fresh (eq ▸ ((mem_live base edge).mp parentLive).1)
      · exact neverDeleted cut (by simpa using hm)
  · rw [childEdit]; exact .here
  · rintro ⟨first, hf, _, path⟩
    have orphan : ∀ e ∈ liveEdges (apply (remove base edge) (apply (insert edit) base)), e.target ≠ edge.target := by
      intro e he eq
      obtain ⟨added, alive⟩ := (mem_live _ e).mp he
      simp only [apply, insert, remove, union_mem] at added
      simp [singleton, SortedArraySet.empty] at added
      rcases added with rfl | old
      · exact noLoop eq
      · have liveOld : e ∈ liveEdges base := (mem_live _ _).mpr ⟨by simpa using old, fun c hc =>
          alive c (by simp only [apply, remove, insert, union_mem]; exact Or.inr (Or.inr hc))⟩
        obtain rfl := onlyParent e liveOld eq
        exact alive (e, liveEdges base) (by simp only [apply, remove, union_mem]; simp [singleton]) rfl
    rcases path.incoming with eq | ⟨last, hl, eq⟩
    · exact orphan first hf eq
    · exact orphan last hl eq

/-- Typing for a projection with holes. A hole inhabits its recorded expected type. -/
inductive HasType : Marked → Ty → Prop where
  | code {t ty} : PartialTyping {} [] t ty [] → HasType (.code t) ty
  | hole (h : ConflictHole) : HasType (.hole h) h.expected
  | app {f a r q dom ran} : HasType f (.arrow r q dom ran) → HasType a dom →
    argumentAllowed {} q [] dom [] = true → HasType (.app f a) ran

theorem project_typed (nodes : Catalog) (valid : nodes.Valid) (idx : Adjacency)
    (fuel : Nat) (seen : List Nat) (p : Port) (ty : Ty) :
    HasType (project nodes idx fuel seen p ty) ty := by
  induction fuel generalizing seen p ty with
  | zero | succ _ ih =>
    unfold project
    split <;> try exact .hole _
    dsimp only
    split <;> try exact .hole _
    split <;> try exact .hole _
    split <;> try exact .hole _
    rename_i node lookup agrees
    split <;> try exact .hole _
    have eq : node.type = ty := by simpa using agrees
    subst ty
    have checked := valid _ _ lookup
    cases node with
    | leaf _ _ => exact .code checked
    | app r q dom ran => first | exact .hole _ | exact .app (ih ..) (ih ..) checked

/-- Only edges incident on the queried region contribute to either local index.
The incoming half is essential for detecting a splice from a different parent. -/
private theorem live_sorted (g : StructurePatch) : SortedList (liveEdges g) :=
  List.Pairwise.filter _ g.inserted.property

private theorem filter_frame (a b : StructurePatch) (test : Edge → Bool)
    (same : ∀ e, test e = true → (e ∈ liveEdges a ↔ e ∈ liveEdges b)) :
    (liveEdges a).filter test = (liveEdges b).filter test := by
  apply SortedList.ext_memB ((live_sorted a).filter _) ((live_sorted b).filter _)
  intro e
  rw [Bool.eq_iff_iff, memB_iff, memB_iff, List.mem_filter, List.mem_filter]
  by_cases h : test e = true <;> simp_all

theorem project_frame (nodes : Catalog) (a b : StructurePatch)
    (region : Nat → Prop)
    (incident : ∀ e : Edge, region e.port.1 ∨ region e.target →
      (e ∈ liveEdges a ↔ e ∈ liveEdges b))
    (closed : ∀ e ∈ liveEdges a, region e.port.1 → region e.target)
    (fuel : Nat) (seen : List Nat) (p : Port) (ty : Ty) (hp : region p.1) :
    project nodes (indexEdges (liveEdges a)) fuel seen p ty =
    project nodes (indexEdges (liveEdges b)) fuel seen p ty := by
  induction fuel generalizing seen p ty with
  | zero | succ _ ih =>
    unfold project
    rw [index_slot, index_slot]
    have slots := filter_frame a b (fun e => e.port == p) (by
      intro e he; exact incident e (.inl (by rwa [show e.port = p from beq_iff_eq.mp he])))
    change (liveEdges a).filter _ = (liveEdges b).filter _ at slots
    rw [← slots]
    split <;> try rfl
    rename_i e alone
    have he := List.mem_filter.mp (show e ∈ (liveEdges a).filter (fun e => e.port == p) by
      rw [alone]; exact .head _)
    have hv := closed e he.1 (by rwa [show e.port = p from beq_iff_eq.mp he.2])
    dsimp only
    rw [index_parent, index_parent]
    have parents := filter_frame a b (fun edge => edge.target == e.target) (by
      intro edge h; exact incident edge (.inr (by rwa [show edge.target = e.target from beq_iff_eq.mp h])))
    change (liveEdges a).filter _ = (liveEdges b).filter _ at parents
    rw [← parents]
    all_goals
      have left := fun t => ih (e.target :: seen) (e.target, 0) t hv
      have right := fun t => ih (e.target :: seen) (e.target, 1) t hv
      simp only [left, right]

end Obend.Doc.Grove
