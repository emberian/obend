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
open Obend.Core.Data Obend.Tactic.DataRefinement
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

/-! ## Collaborative `Core.Term` Vertices, Typed Ports & Projection -/

/-- Build a closed Core4 record row type from a field-type list. -/
def recordRow : List (String × Ty) → Ty
  | [] => .emptyRow
  | (n, t) :: rest => .field n t (recordRow rest)

/-- Immutable collaborative Grove vertices spanning Core4 constructors:
leaves (with optional lambda-annotation tables), lexical variables, lambdas,
applications, `let`-bindings, open-recursive `fix` & `mix`, `prototype`/`project`/`reflect`,
n-ary `record`s & field `get`, scalar `binary` primitives, and `ifBool`. -/
inductive Vertex where
  | leaf (type : Ty) (term : Term) (anns : LiveObject.AnnTable := [])
  | var (index : Nat) (type : Ty)
  | lam (reuse : Reuse) (domain codomain : Ty)
  | app (reuse : Reuse) (quantity : Quantity) (domain range : Ty)
  | letBind (boundTy bodyTy : Ty)
  | fix (inherited target : Ty)
  | mix (self inherited middle provided : Ty)
  | prototype (specType targetType : Ty)
  | projectProto (specType targetType : Ty)
  | reflectProto (specType targetType : Ty)
  | record (fields : List (String × Ty))
  | get (row : Ty) (fieldName : String) (member : Ty)
  | binary (primitive : Primitive)
  | ifBool (branchTy : Ty)

def Vertex.type : Vertex → Ty
  | .leaf t _ _ => t
  | .var _ t => t
  | .lam r dom cod => .arrow r .unrestricted dom cod
  | .app _ _ _ t => t
  | .letBind _ bodyTy => bodyTy
  | .fix _ target => target
  | .mix self inh _ prov =>
    .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inh prov)
  | .prototype s t => .prototype s t
  | .projectProto _ t => t
  | .reflectProto s _ => s
  | .record fields => recordRow fields
  | .get _ _ m => m
  | .binary prim => (primitiveTypes prim).2
  | .ifBool t => t

def Vertex.Valid : Vertex → Prop
  | .leaf ty term _ => PartialTyping {} [] term ty []
  | .var _ _ => True
  | .lam _ dom _ => dom.shareable = true
  | .app _ q dom _ => argumentAllowed {} q [] dom [] = true
  | .letBind boundTy _ => boundTy.shareable = true
  | .fix inh target => target.shareable = true ∧ inh.shareable = true
  | .mix self inh mid _ => self.shareable = true ∧ inh.shareable = true ∧ mid.shareable = true
  | .prototype s t => s.isComputation = false ∧ t.isComputation = false
  | .projectProto _ _ => True
  | .reflectProto _ _ => True
  | .record fields => (fields.map Prod.fst).Nodup ∧ ∀ f ∈ fields, f.2.isComputation = false
  | .get row name member => ∃ fuel, row.lookup [] fuel name = some member
  | .binary _ => True
  | .ifBool _ => True

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
  | unboundVar (vertex : AtomId) (index : Nat)
  | cycle (vertex : AtomId)
  | deletedParentModifiedChild (cut edit : Edge)
  deriving Repr

structure ConflictHole where
  port : Port
  expected : Ty
  reason : Conflict
  deriving Repr

/-- Marked collaborative AST over Core4 constructors, with localized conflict holes at any port. -/
inductive Marked where
  | code (term : Term) (anns : LiveObject.AnnTable := [])
  | var (index : Nat)
  | lam (reuse : Reuse) (domain codomain : Ty) (body : Marked)
  | app (fn arg : Marked)
  | letBind (boundTy bodyTy : Ty) (val body : Marked)
  | fix (spec inherited : Marked)
  | mix (lower upper : Marked)
  | prototype (spec target : Marked)
  | projectProto (target : Marked)
  | reflectProto (target : Marked)
  | record (fields : List (String × Marked))
  | get (target : Marked) (fieldName : String)
  | binary (primitive : Primitive) (left right : Marked)
  | ifBool (cond whenTrue whenFalse : Marked)
  | hole (h : ConflictHole)

/-- A covered root consists of the projected program (with every reachable detached cut
localized as a first-class conflict hole at its exact port) plus the complete list of
detached delete-modify conflicts across all cuts for root audit and freezing. -/
structure LiveRoot where
  program : Marked
  detached : List ConflictHole

/-- Index detached conflict holes by the source port `h.port` where the severed edge lived. -/
def indexCuts : List ConflictHole → TreeMap.Raw Port (List ConflictHole) compare
  | [] => ∅
  | h :: hs =>
    let rest := indexCuts hs
    rest.insert h.port (h :: rest.getD h.port [])

private theorem indexCuts_wf (holes : List ConflictHole) : (indexCuts holes).WF := by
  induction holes with
  | nil => exact Std.TreeMap.Raw.WF.emptyc
  | cons _ _ ih => exact ih.insert

theorem indexCuts_port (holes : List ConflictHole) (p : Port) :
    (indexCuts holes).getD p [] = holes.filter (fun h => h.port == p) := by
  induction holes with
  | nil => simp [indexCuts]
  | cons h hs ih =>
    by_cases hp : h.port = p
    · simp [indexCuts, hp, ih, indexCuts_wf hs]
    · simp [indexCuts, Std.TreeMap.Raw.getD_insert (indexCuts_wf hs), hp, ih, beq_eq_false_iff_ne.mpr hp]

/-- Bounded structural projection over full Core4 vertices with lexical context tracking
and localized detached-cut holes at their affected ports. -/
def project (nodes : Catalog) (idx : Adjacency)
    (cuts : TreeMap.Raw Port (List ConflictHole) compare := ∅) :
    Nat → List AtomId → Context → Port → Ty → Marked
  | fuel, seen, ctx, p, expected =>
    match cuts.getD p [] with
    | h :: _ => .hole { h with expected := expected }
    | [] =>
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
            | .leaf _ t anns => .code t anns
            | .var i ty =>
              match ctx[i]? with
              | some b => if b.type == ty then .var i else .hole ⟨p, expected, .mismatch v b.type⟩
              | none => .hole ⟨p, expected, .unboundVar v i⟩
            | .lam reuse dom cod =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .lam reuse dom cod
                  (project nodes idx cuts n (v :: seen) (⟨dom, .unrestricted⟩ :: ctx) (v, 0) cod)
            | .app reuse q dom ran =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .app (project nodes idx cuts n (v :: seen) ctx (v, 0) (.arrow reuse q dom ran))
                     (project nodes idx cuts n (v :: seen) ctx (v, 1) dom)
            | .letBind boundTy bodyTy =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .letBind boundTy bodyTy
                  (project nodes idx cuts n (v :: seen) ctx (v, 0) boundTy)
                  (project nodes idx cuts n (v :: seen) (⟨boundTy, .unrestricted⟩ :: ctx) (v, 1) bodyTy)
            | .fix inh target =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .fix
                  (project nodes idx cuts n (v :: seen) ctx (v, 0)
                    (.arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inh target)))
                  (project nodes idx cuts n (v :: seen) ctx (v, 1) inh)
            | .mix self inh mid prov =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .mix
                  (project nodes idx cuts n (v :: seen) ctx (v, 0)
                    (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inh mid)))
                  (project nodes idx cuts n (v :: seen) ctx (v, 1)
                    (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted mid prov)))
            | .prototype s t =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .prototype (project nodes idx cuts n (v :: seen) ctx (v, 0) s)
                           (project nodes idx cuts n (v :: seen) ctx (v, 1) t)
            | .projectProto s t =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .projectProto (project nodes idx cuts n (v :: seen) ctx (v, 0) (.prototype s t))
            | .reflectProto s t =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .reflectProto (project nodes idx cuts n (v :: seen) ctx (v, 0) (.prototype s t))
            | .record fields =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .record (fields.zipIdx.map fun (field, slot) =>
                  (field.1, project nodes idx cuts n (v :: seen) ctx (v, slot) field.2))
            | .get row fname _ =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .get (project nodes idx cuts n (v :: seen) ctx (v, 0) row) fname
            | .binary prim =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                let inTy := (primitiveTypes prim).1
                .binary prim (project nodes idx cuts n (v :: seen) ctx (v, 0) inTy)
                             (project nodes idx cuts n (v :: seen) ctx (v, 1) inTy)
            | .ifBool bTy =>
              match fuel with
              | 0 => .hole ⟨p, expected, .cycle v⟩
              | n + 1 =>
                .ifBool (project nodes idx cuts n (v :: seen) ctx (v, 0) .boolean)
                        (project nodes idx cuts n (v :: seen) ctx (v, 1) bTy)
                        (project nodes idx cuts n (v :: seen) ctx (v, 2) bTy)
      | a :: b :: more => .hole ⟨p, expected, .alternatives (a :: b :: more)⟩

/-! ## Transitive Reachability & Delete-Modify Coverage -/

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

theorem EdgePath.trans {edges : List Edge} {a b c : Nat}
    (p : EdgePath edges a b) (q : EdgePath edges b c) : EdgePath edges a c := by
  induction q with
  | here => exact p
  | next _ he ih => exact ih.next he

theorem EdgePath.mono {e₁ e₂ : List Edge} (hsub : ∀ e ∈ e₁, e ∈ e₂) {a b : Nat}
    (p : EdgePath e₁ a b) : EdgePath e₂ a b := by
  induction p with
  | here => exact .here
  | next _ he ih => exact ih.next (hsub _ he)

private theorem EdgePath.incoming {edges : List Edge} {start v : Nat} (path : EdgePath edges start v) :
    start = v ∨ ∃ e ∈ edges, e.target = v := by
  cases path with
  | here => exact .inl rfl
  | next _ he => exact .inr ⟨_, he, rfl⟩

/-- Any path starting at `e0.target` has a simple-prefix subpath avoiding `e0` itself. -/
private theorem edgePath_avoid_target {edges : List Edge} {start v : Nat} (e0 : Edge)
    (ht : e0.target = start) (p : EdgePath edges start v) :
    EdgePath (edges.filter (· != e0)) start v := by
  induction p with
  | here => exact .here
  | @next e _ he ih =>
    by_cases h : e = e0
    · subst h; rw [ht]; exact .here
    · exact ih.next (List.mem_filter.mpr ⟨he, bne_iff_ne.mpr h⟩)

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

/-- Entry ports get their type from the document. Internal vertex slots get
the exact expected type declared by their immutable parent vertex constructor. -/
def portType (nodes : Catalog) (entry : Port → Ty) (p : Port) : Ty :=
  match nodes.get? p.1, p.2 with
  | some (.lam _ _ cod), 0 => cod
  | some (.app r q dom ran), 0 => .arrow r q dom ran
  | some (.app _ _ dom _), 1 => dom
  | some (.letBind bTy _), 0 => bTy
  | some (.letBind _ bodyTy), 1 => bodyTy
  | some (.fix inh target), 0 =>
    .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inh target)
  | some (.fix inh _), 1 => inh
  | some (.mix self inh mid _), 0 =>
    .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inh mid)
  | some (.mix self _ mid prov), 1 =>
    .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted mid prov)
  | some (.prototype s _), 0 => s
  | some (.prototype _ t), 1 => t
  | some (.projectProto s t), 0 => .prototype s t
  | some (.reflectProto s t), 0 => .prototype s t
  | some (.record fields), slot => (fields[slot]?.map Prod.snd).getD (entry p)
  | some (.get row _ _), 0 => row
  | some (.binary prim), 0 => (primitiveTypes prim).1
  | some (.binary prim), 1 => (primitiveTypes prim).1
  | some (.ifBool _), 0 => .boolean
  | some (.ifBool t), 1 => t
  | some (.ifBool t), 2 => t
  | _, _ => entry p

/-- Project a document root, localizing every detached delete-modify cut at its exact
source port `cut.1.port` inside `program` while also publishing all covered detached cuts. -/
def liveRoot (nodes : Catalog) (expected : Port → Ty) (rootPort : Port)
    (g : StructurePatch) : LiveRoot :=
  let edges := liveEdges g
  let live := edgeIndex edges
  let idx := indexEdges edges
  let children := childrenIndex edges
  let reachable := reachableFrom edges children idx rootPort
  let portTy := portType nodes expected
  let detached := g.removed.val.toList.flatMap (cutHoles portTy edges children reachable live)
  let cutIdx := indexCuts detached
  ⟨project nodes idx cutIdx nodes.size [] [] rootPort (portTy rootPort), detached⟩

/-- Transitive delete-modify coverage: a new or withdrawn edge at ANY depth (`EdgePath`)
below a disconnected child is surfaced in `(liveRoot ...).detached`. -/
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

/-- Localization guarantee: whenever a detached delete-modify conflict covers port `p`,
projecting port `p` under `indexCuts (liveRoot ...).detached` produces a localized
`.hole` at port `p` (never discarding unrelated branches of the program!). -/
theorem DeleteModifyLocalized (nodes : Catalog) (expected : Port → Ty)
    (rootPort : Port) (g : StructurePatch) (cut : Cut) (edit : Edge)
    (deleted : cut ∈ g.removed.val.toList)
    (changed : (edit ∈ liveEdges g ∧ edit ∉ cut.2) ∨ (edit ∈ cut.2 ∧ edit ≠ cut.1 ∧ edit ∉ liveEdges g))
    (inside : EdgePath (liveEdges g) cut.1.target edit.port.1)
    (detached : ¬ RootPath (liveEdges g) rootPort cut.1.target)
    (fuel : Nat) (seen : List AtomId) (ctx : Context) (ty : Ty) :
    ∃ h, h ∈ (liveRoot nodes expected rootPort g).detached ∧
      h.port = cut.1.port ∧
      project nodes (indexEdges (liveEdges g)) (indexCuts (liveRoot nodes expected rootPort g).detached)
        fuel seen ctx cut.1.port ty = .hole { h with expected := ty } := by
  have hmem := DeleteModifyCover nodes expected rootPort g cut edit deleted changed inside detached
  have hne : ((liveRoot nodes expected rootPort g).detached.filter (fun x => x.port == cut.1.port)) ≠ [] := by
    intro hemp
    have : ⟨cut.1.port, portType nodes expected cut.1.port, .deletedParentModifiedChild cut.1 edit⟩ ∈
        (liveRoot nodes expected rootPort g).detached.filter (fun x => x.port == cut.1.port) :=
      List.mem_filter.mpr ⟨hmem, beq_self_eq_true _⟩
    rw [hemp] at this; cases this
  cases hfilt : (liveRoot nodes expected rootPort g).detached.filter (fun x => x.port == cut.1.port) with
  | nil => exact absurd hfilt hne
  | cons h rest =>
    have hh : h ∈ (liveRoot nodes expected rootPort g).detached ∧ h.port = cut.1.port := by
      have hm := List.mem_filter.mp (hfilt ▸ List.mem_cons_self ..)
      exact ⟨hm.1, beq_iff_eq.mp hm.2⟩
    refine ⟨h, hh.1, hh.2, ?_⟩
    unfold project
    rw [indexCuts_port, hfilt]

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

/-- Transitive concurrent delete-insert coverage: BOTH delivery orders surface a simultaneous
ancestor edge deletion and a previously unseen descendant insertion at ANY depth
(`EdgePath (liveEdges base) edge.target edit.port.1`, multi-hop!). -/
theorem concurrent_delete_insert (nodes : Catalog) (expected : Port → Ty)
    (rootPort : Port) (base : StructurePatch) (edge edit : Edge)
    (parentLive : edge ∈ liveEdges base)
    (onlyParent : ∀ other ∈ liveEdges base, other.target = edge.target → other = edge)
    (fresh : edit ∉ base.inserted.val.toList) (neverDeleted : ∀ cut ∈ base.removed.val.toList, cut.1 ≠ edit)
    (descendant : EdgePath (liveEdges base) edge.target edit.port.1) (noLoop : edit.target ≠ edge.target) :
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
  · have hsub : ∀ e ∈ (liveEdges base).filter (· != edge),
        e ∈ liveEdges (apply (remove base edge) (apply (insert edit) base)) := by
      intro e he
      obtain ⟨heBase, hne⟩ := List.mem_filter.mp he
      have hne' : e ≠ edge := bne_iff_ne.mp hne
      obtain ⟨hins, hnotdel⟩ := (mem_live base e).mp heBase
      rw [mem_live]
      refine ⟨?_, ?_⟩
      · simp only [apply, remove, insert, union_mem]
        exact Or.inr (Or.inr hins)
      · intro cut hc
        simp only [apply, remove, insert, union_mem] at hc
        simp [singleton, SortedArraySet.empty] at hc
        rcases hc with rfl | hbase
        · exact Ne.symm hne'
        · exact hnotdel cut (by simpa using hbase)
    exact EdgePath.mono hsub (edgePath_avoid_target edge rfl descendant)
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

/-! ## Static Typing & Frame Invariance for Full Core4 Projection -/

mutual
/-- Typing for projected Grove trees with localized conflict holes across all Core4 constructors. -/
inductive HasType : Context → Marked → Ty → Prop where
  | code {ctx t anns ty} : PartialTyping {} [] t ty [] → HasType ctx (.code t anns) ty
  | var {ctx i b ty} : ctx[i]? = some b → b.type = ty → HasType ctx (.var i) ty
  | hole {ctx} (h : ConflictHole) : HasType ctx (.hole h) h.expected
  | lam {ctx r dom cod body} :
      dom.shareable = true →
      HasType (⟨dom, .unrestricted⟩ :: ctx) body cod →
      HasType ctx (.lam r dom cod body) (.arrow r .unrestricted dom cod)
  | app {ctx f a r q dom ran} :
      HasType ctx f (.arrow r q dom ran) → HasType ctx a dom →
      argumentAllowed {} q [] dom [] = true → HasType ctx (.app f a) ran
  | letBind {ctx bTy bodyTy val body} :
      bTy.shareable = true →
      HasType ctx val bTy →
      HasType (⟨bTy, .unrestricted⟩ :: ctx) body bodyTy →
      HasType ctx (.letBind bTy bodyTy val body) bodyTy
  | fix {ctx inh target spec inhTerm} :
      target.shareable = true → inh.shareable = true →
      HasType ctx spec (.arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inh target)) →
      HasType ctx inhTerm inh →
      HasType ctx (.fix spec inhTerm) target
  | mix {ctx self inh mid prov lo hi} :
      self.shareable = true → inh.shareable = true → mid.shareable = true →
      HasType ctx lo (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inh mid)) →
      HasType ctx hi (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted mid prov)) →
      HasType ctx (.mix lo hi) (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inh prov))
  | prototype {ctx s t sp tg} :
      s.isComputation = false → t.isComputation = false →
      HasType ctx sp s → HasType ctx tg t →
      HasType ctx (.prototype sp tg) (.prototype s t)
  | projectProto {ctx s t tg} :
      HasType ctx tg (.prototype s t) → HasType ctx (.projectProto tg) t
  | reflectProto {ctx s t tg} :
      HasType ctx tg (.prototype s t) → HasType ctx (.reflectProto tg) s
  | record {ctx fields row} :
      (fields.map Prod.fst).Nodup →
      HasFieldTypes ctx fields row →
      HasType ctx (.record fields) row
  | get {ctx row name member tg} :
      (∃ fuel, row.lookup [] fuel name = some member) →
      HasType ctx tg row →
      HasType ctx (.get tg name) member
  | binary {ctx prim l r} :
      HasType ctx l (primitiveTypes prim).1 →
      HasType ctx r (primitiveTypes prim).1 →
      HasType ctx (.binary prim l r) (primitiveTypes prim).2
  | ifBool {ctx ty c wt wf} :
      HasType ctx c .boolean → HasType ctx wt ty → HasType ctx wf ty →
      HasType ctx (.ifBool c wt wf) ty

inductive HasFieldTypes : Context → List (String × Marked) → Ty → Prop where
  | nil {ctx} : HasFieldTypes ctx [] .emptyRow
  | cons {ctx name m rest ty row} :
      ty.isComputation = false →
      HasType ctx m ty → HasFieldTypes ctx rest row →
      HasFieldTypes ctx ((name, m) :: rest) (.field name ty row)
end

private theorem zipIdx_map_fst (fields : List (String × Ty)) (f : Nat → Ty → Marked) (k : Nat) :
    ((fields.zipIdx k).map fun (field, slot) => (field.1, f slot field.2)).map Prod.fst =
      fields.map Prod.fst := by
  induction fields generalizing k with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    exact congrArg (hd.1 :: ·) (ih (k + 1))

private theorem project_fields_typed {ctx : Context} {f : Nat → Ty → Marked}
    (ih : ∀ (slot : Nat) (fty : Ty), HasType ctx (f slot fty) fty) :
    ∀ (fields : List (String × Ty)) (k : Nat),
      (∀ fld ∈ fields, fld.2.isComputation = false) →
      HasFieldTypes ctx ((fields.zipIdx k).map fun (field, slot) => (field.1, f slot field.2))
        (recordRow fields)
  | [], _, _ => .nil
  | (fname, fty) :: rest, k, hpure => by
    simp only [List.zipIdx_cons, List.map_cons, recordRow]
    exact .cons (hpure (fname, fty) (List.mem_cons_self ..)) (ih k fty)
      (project_fields_typed ih rest (k + 1) (fun fld hfld => hpure fld (List.mem_cons_of_mem _ hfld)))

theorem project_typed (nodes : Catalog) (valid : nodes.Valid) (idx : Adjacency)
    (cuts : TreeMap.Raw Port (List ConflictHole) compare)
    (fuel : Nat) (seen : List Nat) (ctx : Context) (p : Port) (ty : Ty) :
    HasType ctx (project nodes idx cuts fuel seen ctx p ty) ty := by
  induction fuel generalizing seen ctx p ty with
  | zero =>
    unfold project
    split
    · exact .hole _
    · split <;> try exact .hole _
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
      | leaf _ _ _ => exact .code checked
      | var i t =>
        dsimp only
        split
        · rename_i b hb
          split
          · rename_i hbt; exact .var hb (by dsimp [Vertex.type]; simpa using hbt)
          · exact .hole _
        · exact .hole _
      | _ => exact .hole _
  | succ n ih =>
    unfold project
    split
    · exact .hole _
    · split <;> try exact .hole _
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
      | leaf _ _ _ => exact .code checked
      | var i t =>
        dsimp only
        split
        · rename_i b hb
          split
          · rename_i hbt; exact .var hb (by dsimp [Vertex.type]; simpa using hbt)
          · exact .hole _
        · exact .hole _
      | lam r dom cod => exact .lam checked (ih ..)
      | app r q dom ran => exact .app (ih ..) (ih ..) checked
      | letBind bTy bodyTy => exact .letBind checked (ih ..) (ih ..)
      | fix inh target => exact .fix checked.1 checked.2 (ih ..) (ih ..)
      | mix self inh mid prov => exact .mix checked.1 checked.2.1 checked.2.2 (ih ..) (ih ..)
      | prototype s t => exact .prototype checked.1 checked.2 (ih ..) (ih ..)
      | projectProto s t => exact .projectProto (ih ..)
      | reflectProto s t => exact .reflectProto (ih ..)
      | record fields =>
        dsimp [Vertex.type]
        exact .record
          (by rw [zipIdx_map_fst fields (fun slot fty => project nodes idx cuts n (_ :: seen) ctx (_, slot) fty) 0]; exact checked.1)
          (project_fields_typed (ctx := ctx) (f := fun slot fty => project nodes idx cuts n (_ :: seen) ctx (_, slot) fty)
            (fun slot fty => ih _ _ _ _) fields 0 checked.2)
      | get row fname member => exact .get checked (ih ..)
      | binary prim => exact .binary (ih ..) (ih ..)
      | ifBool bTy => exact .ifBool (ih ..) (ih ..) (ih ..)

/-- Only edges incident on the queried region (and cut holes anchored inside it) contribute
to projection. The incoming half is essential for detecting a splice from a different parent. -/
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
    (cutsA cutsB : TreeMap.Raw Port (List ConflictHole) compare)
    (region : Nat → Prop)
    (incident : ∀ e : Edge, region e.port.1 ∨ region e.target →
      (e ∈ liveEdges a ↔ e ∈ liveEdges b))
    (closed : ∀ e ∈ liveEdges a, region e.port.1 → region e.target)
    (cutsSame : ∀ p : Port, region p.1 → cutsA.getD p [] = cutsB.getD p [])
    (fuel : Nat) (seen : List Nat) (ctx : Context) (p : Port) (ty : Ty) (hp : region p.1) :
    project nodes (indexEdges (liveEdges a)) cutsA fuel seen ctx p ty =
    project nodes (indexEdges (liveEdges b)) cutsB fuel seen ctx p ty := by
  induction fuel generalizing seen ctx p ty with
  | zero =>
    unfold project
    rw [cutsSame p hp]
    split
    · rfl
    · rw [index_slot, index_slot]
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
  | succ n ih =>
    unfold project
    rw [cutsSame p hp]
    split
    · rfl
    · rw [index_slot, index_slot]
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
      have hrec : ∀ (ctx' : Context) (slot : Nat) (t' : Ty),
          project nodes (indexEdges (liveEdges a)) cutsA n (e.target :: seen) ctx' (e.target, slot) t' =
          project nodes (indexEdges (liveEdges b)) cutsB n (e.target :: seen) ctx' (e.target, slot) t' :=
        fun ctx' slot t' => ih (e.target :: seen) ctx' (e.target, slot) t' hv
      simp only [hrec]

/-! ## StructurePatch ↔ `Obend.Doc.Graph` Bridge (Lossless Round-Trip & Reachability) -/

private def edgeToData (e : Edge) : Data :=
  .record [("uid", .natural e.1), ("src", .natural e.2.1.1),
    ("slot", .natural e.2.1.2), ("dst", .natural e.2.2)]

private def dataToEdge? : Data → Option Edge
  | .record [("uid", .natural u), ("src", .natural s), ("slot", .natural sl), ("dst", .natural d)] =>
    some (u, (s, sl), d)
  | _ => none

private theorem dataToEdge?_edgeToData (e : Edge) : dataToEdge? (edgeToData e) = some e := rfl

private def edgeListToData : List Edge → Data
  | [] => .variant "nil" (.record [])
  | e :: es => .variant "cons" (.record [("h", edgeToData e), ("t", edgeListToData es)])

private def dataToEdgeList? : Data → Option (List Edge)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("h", h), ("t", t)]) => do
    pure ((← dataToEdge? h) :: (← dataToEdgeList? t))
  | _ => none

private theorem dataToEdgeList?_edgeListToData : ∀ es : List Edge,
    dataToEdgeList? (edgeListToData es) = some es
  | [] => rfl
  | e :: es => by simp [edgeListToData, dataToEdgeList?, dataToEdge?_edgeToData, dataToEdgeList?_edgeListToData es]

private def cutToData (c : Cut) : Data :=
  .record [("edge", edgeToData c.1), ("snap", edgeListToData c.2)]

private def dataToCut? : Data → Option Cut
  | .record [("edge", e), ("snap", s)] => do
    pure (← dataToEdge? e, ← dataToEdgeList? s)
  | _ => none

private theorem dataToCut?_cutToData (c : Cut) : dataToCut? (cutToData c) = some c := by
  simp [cutToData, dataToCut?, dataToEdge?_edgeToData, dataToEdgeList?_edgeListToData]

private def insertAll {A : Type} [StrictLinearOrder A] : List A → SortedArraySet A
  | [] => SortedArraySet.empty
  | x :: xs => SortedArraySet.union (singleton x) (insertAll xs)

private theorem insertAll_mem {A : Type} [StrictLinearOrder A] (xs : List A) (x : A) :
    x ∈ (insertAll xs).val.toList ↔ x ∈ xs := by
  induction xs with
  | nil => simp [insertAll, SortedArraySet.empty]
  | cons y ys ih =>
    rw [insertAll, union_mem]
    simp [singleton, ih]

private theorem insertAll_of_sorted {A : Type} [StrictLinearOrder A] (s : SortedArraySet A) :
    insertAll s.val.toList = s := by
  apply SortedArraySet.eq_iff_toSpec.mpr
  apply FinSetSpec.ext_iff.mpr
  intro x
  have h1 : (insertAll s.val.toList).toSpec.mem x = true ↔ x ∈ (insertAll s.val.toList).val.toList :=
    memB_iff
  have h2 : s.toSpec.mem x = true ↔ x ∈ s.val.toList := memB_iff
  rw [Bool.eq_iff_iff, h1, h2]
  exact insertAll_mem s.val.toList x

/-- Materialize a Grove `StructurePatch` as a genuine `Obend.Doc.Graph`:
- Each inserted edge `e` is stored as a `.cell` atom (`grove.edge/1`) at odd ID `2 * i + 1`
  and tombstoned in `G.dead` iff `e` has been cut in `g.removed`.
- Each cut `(e, snap)` is stored as a tombstoned `.cell` atom (`grove.cut/1`) at even ID `2 * i + 2`.
- `G.edges` carries the exact structural order edges `(e.port.1, e.target)` of `liveEdges g`. -/
def toDocGraph (g : StructurePatch) : Graph :=
  let deadIdx := edgeIndex (g.removed.val.toList.map Prod.fst)
  let insList := g.inserted.val.toList.zipIdx
  let remList := g.removed.val.toList.zipIdx
  let insAtoms : List (AtomId × Content) := insList.map fun (e, i) =>
    (2 * i + 1, .cell ("grove.edge/" ++ toString e.1) .obendCode (.variant "grove.edge/1" (edgeToData e)) [] none)
  let remAtoms : List (AtomId × Content) := remList.map fun (c, i) =>
    (2 * i + 2, .cell ("grove.cut/" ++ toString c.1.1) .obendCode (.variant "grove.cut/1" (cutToData c)) [] none)
  let insDead : List AtomId := insList.filterMap fun (e, i) =>
    if deadIdx.contains e then some (2 * i + 1) else none
  let remDead : List AtomId := remList.map fun (_, i) => 2 * i + 2
  { atoms := insAtoms ++ remAtoms
    dead := insDead ++ remDead
    edges := (liveEdges g).map fun e => (e.port.1, e.target) }

/-- Reconstruct a Grove `StructurePatch` from its `Obend.Doc.Graph` representation. -/
def ofDocGraph (G : Graph) : Option StructurePatch := do
  let rec go : List (AtomId × Content) → List Edge → List Cut → Option (List Edge × List Cut)
    | [], ins, rem => some (ins.reverse, rem.reverse)
    | (_, .cell _ .obendCode (.variant "grove.edge/1" d) _ _) :: rest, ins, rem => do
      let e ← dataToEdge? d
      go rest (e :: ins) rem
    | (_, .cell _ .obendCode (.variant "grove.cut/1" d) _ _) :: rest, ins, rem => do
      let c ← dataToCut? d
      go rest ins (c :: rem)
    | _ :: rest, ins, rem => go rest ins rem
  let (ins, rem) ← go G.atoms [] []
  some ⟨insertAll ins, insertAll rem⟩

private theorem ofDocGraph_go_ins (es : List (Edge × Nat)) (tail : List (AtomId × Content))
    (ins : List Edge) (rem : List Cut) :
    ofDocGraph.go
      ((es.map fun (e, i) =>
        (2 * i + 1, Content.cell ("grove.edge/" ++ toString e.1) .obendCode
          (.variant "grove.edge/1" (edgeToData e)) [] none)) ++ tail) ins rem =
      ofDocGraph.go tail ((es.map Prod.fst).reverse ++ ins) rem := by
  induction es generalizing ins with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨e, i⟩ := hd
    simp only [List.map_cons, List.cons_append, ofDocGraph.go, dataToEdge?_edgeToData,
      bind, Option.bind, List.reverse_cons, List.append_assoc]
    exact ih (e :: ins)

private theorem ofDocGraph_go_rem (cs : List (Cut × Nat)) (ins : List Edge) (rem : List Cut) :
    ofDocGraph.go
      (cs.map fun (c, i) =>
        (2 * i + 2, Content.cell ("grove.cut/" ++ toString c.1.1) .obendCode
          (.variant "grove.cut/1" (cutToData c)) [] none)) ins rem =
      some (ins.reverse, rem.reverse ++ cs.map Prod.fst) := by
  induction cs generalizing rem with
  | nil => simp [ofDocGraph.go]
  | cons hd tl ih =>
    obtain ⟨c, i⟩ := hd
    simp only [List.map_cons, ofDocGraph.go, dataToCut?_cutToData, bind, Option.bind]
    rw [ih (c :: rem)]
    simp [List.reverse_cons, List.append_assoc]

private theorem zipIdx_map_fst_eq {α : Type} (xs : List α) (k : Nat) :
    (xs.zipIdx k).map Prod.fst = xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    exact congrArg (hd :: ·) (ih (k + 1))

/-- Lossless round-trip: translating a `StructurePatch` to `Obend.Doc.Graph` and reading it
back yields the exact canonical `StructurePatch`. -/
theorem ofDocGraph_toDocGraph (g : StructurePatch) :
    ofDocGraph (toDocGraph g) = some g := by
  unfold ofDocGraph toDocGraph
  dsimp only
  rw [ofDocGraph_go_ins, ofDocGraph_go_rem]
  simp only [List.append_nil, List.reverse_reverse, List.reverse_nil, List.nil_append,
    zipIdx_map_fst_eq, bind, Option.bind, insertAll_of_sorted]

/-- Direct order-edge correspondence: `(toDocGraph g).edge u v = true` iff `liveEdges g` has
a live edge from vertex `u` to vertex `v`. -/
theorem toDocGraph_edge_iff (g : StructurePatch) (u v : AtomId) :
    (toDocGraph g).edge u v = true ↔ ∃ e ∈ liveEdges g, e.port.1 = u ∧ e.target = v := by
  simp only [Graph.edge, toDocGraph, List.contains_iff_mem, List.mem_map, Prod.mk.injEq]

/-- Transitive reachability equivalence: `Obend.Doc.Graph.Before` on `toDocGraph g` is
identically nonempty `EdgePath` reachability over `liveEdges g`. -/
theorem toDocGraph_before_iff (g : StructurePatch) (u v : AtomId) :
    (toDocGraph g).Before u v ↔ ∃ e ∈ liveEdges g, e.port.1 = u ∧ EdgePath (liveEdges g) e.target v := by
  constructor
  · intro hb
    induction hb with
    | edge h =>
      obtain ⟨e, he, hu, hv⟩ := (toDocGraph_edge_iff g _ _).mp h
      exact ⟨e, he, hu, hv ▸ .here⟩
    | trans h _ ih =>
      obtain ⟨e₁, he₁, hu₁, hv₁⟩ := (toDocGraph_edge_iff g _ _).mp h
      obtain ⟨e₂, he₂, hu₂, hp₂⟩ := ih
      have hstep : EdgePath (liveEdges g) e₁.target e₂.target := by
        have hstart : EdgePath (liveEdges g) e₁.target e₂.port.1 := by
          rw [hv₁, ← hu₂]; exact EdgePath.here
        exact hstart.next he₂
      exact ⟨e₁, he₁, hu₁, EdgePath.trans hstep hp₂⟩
  · rintro ⟨e, he, hu, hp⟩
    have hfirst : (toDocGraph g).Before u e.target :=
      .edge ((toDocGraph_edge_iff g u e.target).mpr ⟨e, he, hu, rfl⟩)
    induction hp with
    | here => exact hfirst
    | next _ he' ih =>
      exact ih.tail ((toDocGraph_edge_iff g _ _).mpr ⟨_, he', rfl, rfl⟩)

end Obend.Doc.Grove
