module
public import Obend.Core.TermTraverse
public import Std.Data.HashMap
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
public section

namespace Obend.SemanticKG.Slotted
open Obend.Core
open Obend.Core.Term (Term Primitive)
set_option autoImplicit false

deriving instance Hashable for Primitive
deriving instance DecidableEq, Hashable for TermTraverse.Tag

inductive Op where
  | var | bind | node (tag : TermTraverse.Tag)
  deriving DecidableEq, Hashable

/-- An application lists the actual names of a class's formal slots in formal order.
At an e-node edge, `none` names the enclosing binder. -/
structure Applied (Name : Type) where
  id : Nat
  slots : Array Name
  deriving DecidableEq, Hashable, Repr

/-- An equation equates two applied e-classes under all assignments to external slot names. -/
abbrev Equation := Applied Nat × Applied Nat

structure Node where
  arity : Nat
  op : Op
  children : Array (Applied (Option Nat))
  deriving DecidableEq, Hashable

structure Graph where
  nodes : Array Node := #[]
  index : Std.HashMap Node Nat := {}

private def internGo (n : Node) (g : Graph) : Nat × Graph :=
  match g.index[n]? with
  | some id => (id, g)
  | none =>
    let id := g.nodes.size
    (id, ⟨g.nodes.push n, g.index.insert n id⟩)

private def addSlot (binder : Option Nat) (name : Nat)
    (st : Array Nat × Std.HashMap Nat Nat) :
    Option Nat × (Array Nat × Std.HashMap Nat Nat) :=
  if binder == some name then (none, st)
  else match st.2[name]? with
    | some i => (some i, st)
    | none =>
      let i := st.1.size
      (some i, (st.1.push name, st.2.insert name i))

private def addChild (binder : Option Nat) (child : Applied Nat)
    (st : Array Nat × Std.HashMap Nat Nat) :
    Applied (Option Nat) × (Array Nat × Std.HashMap Nat Nat) :=
  let (slots, st') := child.slots.foldl (fun (acc, s) name =>
    let (slot, s') := addSlot binder name s
    (acc.push slot, s')) (#[], st)
  (⟨child.id, slots⟩, st')

private def addNodeGo (op : Op) (binder : Option Nat) (children : Array (Applied Nat))
    (g : Graph) : Applied Nat × Graph :=
  let (edges, (names, _)) := children.foldl (fun (acc, s) child =>
    let (edge, s') := addChild binder child s
    (acc.push edge, s')) (#[], (#[], {}))
  let (id, g') := internGo ⟨names.size, op, edges⟩ g
  (⟨id, names⟩, g')

mutual
private def insertShapeGo (depth : Nat) (freeName : Nat → Nat) :
    TermTraverse.Shape → Graph → Applied Nat × Graph
  | .var i, g =>
    let name := if i < depth then 2 * (depth - 1 - i) + 1 else 2 * freeName (i - depth)
    let (id, g') := internGo ⟨1, .var, #[]⟩ g
    (⟨id, #[name]⟩, g')
  | .bind body, g =>
    let (child, g1) := insertShapeGo (depth + 1) freeName body g
    addNodeGo .bind (some (2 * depth + 1)) #[child] g1
  | .node tag cs, g =>
    let (children, g1) := insertShapesGo depth freeName cs g
    addNodeGo (.node tag) none children.toArray g1
termination_by structural t => t

private def insertShapesGo (depth : Nat) (freeName : Nat → Nat) :
    List TermTraverse.Shape → Graph → List (Applied Nat) × Graph
  | [], g => ([], g)
  | x :: xs, g =>
    let (child, g1) := insertShapeGo depth freeName x g
    let (rest, g2) := insertShapesGo depth freeName xs g1
    (child :: rest, g2)
termination_by structural ts => ts
end

def insertCore (term : Term) (freeName : Nat → Nat := id) : StateM Graph (Applied Nat) :=
  fun g => insertShapeGo 0 freeName (TermTraverse.encode term) g

/-! ## Slot Renormalization (`shape`) & Symmetry-Aware Rebuilding -/

private def shapeSlot (s : Option Nat) (st : Array Nat × Std.HashMap Nat Nat) :
    Option Nat × (Array Nat × Std.HashMap Nat Nat) :=
  match s with
  | none => (none, st)
  | some k =>
    match st.2[k]? with
    | some j => (some j, st)
    | none =>
      let j := st.1.size
      (some j, (st.1.push k, st.2.insert k j))

private def shapeEdge (e : Applied (Option Nat)) (st : Array Nat × Std.HashMap Nat Nat) :
    Applied (Option Nat) × (Array Nat × Std.HashMap Nat Nat) :=
  let (slots, st') := e.slots.foldl (fun (acc, s) slot =>
    let (slot', s') := shapeSlot slot s
    (acc.push slot', s')) (#[], st)
  (⟨e.id, slots⟩, st')

/-- Canonicalize formal slot numbering by first occurrence across `n.children`, dropping any
unreferenced (redundant) formal slots. Returns `(canonicalNode, usedSlots)` where `usedSlots[j]`
is the original formal slot of `n` mapped to formal slot `j` of `canonicalNode`. -/
def shape (n : Node) : Node × Array Nat :=
  match n.op with
  | .var => (⟨1, .var, #[]⟩, #[0])
  | op =>
    let (children, (used, _)) := n.children.foldl (fun (acc, s) e =>
      let (e', s') := shapeEdge e s
      (acc.push e', s')) (#[], (#[], {}))
    (⟨used.size, op, children⟩, used)

private def optNatLt : Option Nat → Option Nat → Bool
  | none, some _ => true
  | some a, some b => decide (a < b)
  | _, _ => false

private def slotsLtGo (a b : Array (Option Nat)) (i : Nat) : Bool :=
  if h : i < a.size then
    if hb : i < b.size then
      let x := a[i]'h
      let y := b[i]'hb
      if x == y then slotsLtGo a b (i + 1) else optNatLt x y
    else false
  else decide (i < b.size)
termination_by a.size - i

private def slotsLt (a b : Array (Option Nat)) : Bool := slotsLtGo a b 0

private def natArrayLtGo (a b : Array Nat) (i : Nat) : Bool :=
  if h : i < a.size then
    if hb : i < b.size then
      let x := a[i]'h
      let y := b[i]'hb
      if x == y then natArrayLtGo a b (i + 1) else decide (x < y)
    else false
  else decide (i < b.size)
termination_by a.size - i

private def natArrayLt (a b : Array Nat) : Bool := natArrayLtGo a b 0

/-- Replace child `e` by its slotted representative `rep e.id` (composing slot projections and
bijections) and canonicalize the resulting slots to the lexicographically smallest equivalent
permutation under `perms (rep e.id).id`. -/
def rebuildEdge (rep : Nat → Applied Nat) (perms : Nat → Array (Array Nat))
    (e : Applied (Option Nat)) : Applied (Option Nat) :=
  let r := rep e.id
  let base := r.slots.map fun j => (e.slots[j]?.join)
  let best := (perms r.id).foldl (fun cur π =>
    if π.size == base.size then
      let cand := π.map fun j => (base[j]?.join)
      if slotsLt cand cur then cand else cur
    else cur) base
  ⟨r.id, best⟩

/-- Substitute child representatives (projecting redundant slots and applying symmetry permutations)
and canonicalize formal slots via `shape`. Returns `(canonicalNode, usedSlots)`. -/
def rebuildNode (rep : Nat → Applied Nat) (perms : Nat → Array (Array Nat))
    (n : Node) : Node × Array Nat :=
  let subst : Node := match n.op with
    | .var => n
    | op => ⟨n.arity, op, n.children.map (rebuildEdge rep perms)⟩
  shape subst

private def appFromUsed (id arity : Nat) (used : Array Nat) (freshBase : Nat) : Applied Nat :=
  let slots := (Array.range arity).map fun k =>
    match used.idxOf? k with
    | some j => j
    | none => freshBase + k
  ⟨id, slots⟩

private def usedInBounds (arity : Nat) (used : Array Nat) : Bool :=
  used.all (· < arity)

private abbrev Work := Std.HashMap Node (Nat × Array Nat) × Array Equation

private def rebuildStep (arityOf : Nat → Nat) (rep : Nat → Applied Nat)
    (perms : Nat → Array (Array Nat)) (s : Work) (item : Nat × Node) : Work :=
  let (key, used) := rebuildNode rep perms item.2
  let ar := arityOf item.1
  if !usedInBounds ar used then s else
  let freshBase := key.arity
  let eqs := if used.size < ar then
      s.2.push (appFromUsed item.1 ar used freshBase,
        appFromUsed item.1 ar used (freshBase + ar))
    else s.2
  match s.1[key]? with
  | some (earlier, earlierUsed) =>
    let arE := arityOf earlier
    if !usedInBounds arE earlierUsed then (s.1, eqs) else
      (s.1, eqs.push (appFromUsed item.1 ar used freshBase,
        appFromUsed earlier arE earlierUsed (freshBase + ar)))
  | none => (s.1.insert key (item.1, used), eqs)

/-- One slotted congruence + redundant-slot shrinking rebuild pass over `entries`. -/
def slottedRebuild (arityOf : Nat → Nat) (rep : Nat → Applied Nat)
    (perms : Nat → Array (Array Nat)) (entries : Array (Nat × Node)) : Array Equation :=
  (entries.foldl (rebuildStep arityOf rep perms) ({}, #[])).2

/-! ## Slotted Union-Find with Redundant-Slot Projection & Symmetry Groups -/

structure Closure where
  parent : Array (Applied Nat)
  arity : Array Nat
  perms : Array (Array (Array Nat))

private def walkUF (parent : Array (Applied Nat)) : Nat → Applied Nat → Applied Nat
  | 0, a => a
  | fuel + 1, a =>
    match parent[a.id]? with
    | none => a
    | some p =>
      if p.id == a.id then a
      else walkUF parent fuel ⟨p.id, p.slots.map fun j => a.slots[j]?.getD 0⟩

def Closure.find (cl : Closure) (a : Applied Nat) : Applied Nat :=
  walkUF cl.parent cl.parent.size a

def Closure.canonApplied (cl : Closure) (a : Applied Nat) : Applied Nat :=
  let r := cl.find a
  let ps := cl.perms[r.id]?.getD #[]
  let best := ps.foldl (fun cur π =>
    if π.size == r.slots.size then
      let cand := π.map fun j => r.slots[j]?.getD 0
      if natArrayLt cand cur then cand else cur
    else cur) r.slots
  ⟨r.id, best⟩

def Closure.repOf (cl : Closure) (i : Nat) : Applied Nat :=
  cl.find ⟨i, Array.range (cl.arity[i]?.getD 0)⟩

def Closure.equiv (cl : Closure) (a b : Applied Nat) : Bool :=
  cl.canonApplied a == cl.canonApplied b

def Closure.arityOf (cl : Closure) (i : Nat) : Nat :=
  cl.arity[i]?.getD 0

private def arrayNodup (xs : Array Nat) : Bool :=
  (Array.range xs.size).all fun i => xs.idxOf? (xs[i]?.getD 0) == some i

private def composePerm (p q : Array Nat) : Array Nat :=
  q.map fun j => p[j]?.getD 0

private def addPerm (ps : Array (Array Nat)) (π : Array Nat) : Array (Array Nat) × Bool :=
  if ps.contains π || ps.size ≥ 24 then (ps, false)
  else
    let ps1 := ps.push π
    let ps2 := ps1.foldl (fun acc ρ =>
      if acc.size ≥ 24 then acc else
      let c1 := composePerm π ρ
      let acc1 := if acc.contains c1 || acc.size ≥ 24 then acc else acc.push c1
      let c2 := composePerm ρ π
      if acc1.contains c2 || acc1.size ≥ 24 then acc1 else acc1.push c2) ps1
    (ps2, true)

private def isSubsetSlots (sub sup : Array Nat) : Bool :=
  sub.all (sup.contains ·)

private def projectIndices (sup sub : Array Nat) : Array Nat :=
  sub.map fun x => (sup.idxOf? x).getD 0

private def pushShrunk (cl : Closure) (id1 id2 : Nat) (map1 map2 : Array Nat) (arNew : Nat) : Closure :=
  let newId := cl.arity.size
  let idPerm := Array.range arNew
  let p1 := (cl.parent.push ⟨newId, idPerm⟩).setIfInBounds id1 ⟨newId, map1⟩
  let p2 := if id1 == id2 then p1 else p1.setIfInBounds id2 ⟨newId, map2⟩
  ⟨p2, cl.arity.push arNew, cl.perms.push #[idPerm]⟩

private def unionStep (state : Closure × Bool) (eqn : Equation) : Closure × Bool :=
  let (cl, ch) := state
  let r1 := cl.find eqn.1
  let r2 := cl.find eqn.2
  if !(decide (r1.id < cl.arity.size) && decide (r2.id < cl.arity.size)) then (cl, ch) else
  let ar1 := cl.arity[r1.id]?.getD 0
  let ar2 := cl.arity[r2.id]?.getD 0
  if !(r1.slots.size == ar1 && r2.slots.size == ar2 &&
      arrayNodup r1.slots && arrayNodup r2.slots) then (cl, ch) else
  if r1.id == r2.id then
    if r1.slots == r2.slots then (cl, ch)
    else if isSubsetSlots r2.slots r1.slots then
      let π := projectIndices r1.slots r2.slots
      let (ps', added) := addPerm (cl.perms[r1.id]?.getD #[]) π
      if added then ({ cl with perms := cl.perms.setIfInBounds r1.id ps' }, true)
      else (cl, ch)
    else
      let common := r1.slots.filter (r2.slots.contains ·)
      let map1 := projectIndices r1.slots common
      (pushShrunk cl r1.id r1.id map1 map1 common.size, true)
  else if isSubsetSlots r2.slots r1.slots &&
      (decide (r2.slots.size < r1.slots.size) || (r2.slots.size == r1.slots.size && decide (r2.id < r1.id))) then
    let map := projectIndices r1.slots r2.slots
    ({ cl with parent := cl.parent.setIfInBounds r1.id ⟨r2.id, map⟩ }, true)
  else if isSubsetSlots r1.slots r2.slots then
    let map := projectIndices r2.slots r1.slots
    ({ cl with parent := cl.parent.setIfInBounds r2.id ⟨r1.id, map⟩ }, true)
  else
    let common := r1.slots.filter (r2.slots.contains ·)
    let map1 := projectIndices r1.slots common
    let map2 := projectIndices r2.slots common
    (pushShrunk cl r1.id r2.id map1 map2 common.size, true)

private def unionClasses (cl : Closure) (eqs : Array Equation) : Closure × Bool :=
  eqs.foldl unionStep (cl, false)

private def closeLoop (entries : Array (Nat × Node)) : Nat → Closure → Closure
  | 0, cl => cl
  | fuel + 1, cl =>
    let found := slottedRebuild cl.arityOf cl.repOf (fun i => cl.perms[i]?.getD #[]) entries
    let (next, changed) := unionClasses cl found
    if changed then closeLoop entries fuel next else cl

def Graph.initClosure (g : Graph) : Closure where
  parent := (Array.range g.nodes.size).map fun i => ⟨i, Array.range (g.nodes[i]?.map (·.arity) |>.getD 0)⟩
  arity := g.nodes.map (·.arity)
  perms := g.nodes.map fun n => #[Array.range n.arity]

def Graph.close (g : Graph) (equations : Array Equation) : Closure :=
  let entries := (Array.range g.nodes.size).zip g.nodes
  let (base, _) := unionClasses g.initClosure equations
  closeLoop entries (g.nodes.size * 4 + 8) base

/-! ## Semantics, `shape` Soundness, `slottedRebuild_sound`, and `Graph.close_sound` -/

structure Algebra (V R : Type) where
  variableValue : V → R
  apply : Op → Array (V → R) → R

def DependsOnly {V R : Type} (arity : Nat) (f : (Nat → V) → R) : Prop :=
  ∀ env₁ env₂, (∀ j, j < arity → env₁ j = env₂ j) → f env₁ = f env₂

def evalEdgeSlot {V : Type} (env : Nat → V) (fresh : V) : Option Nat → V
  | none => fresh
  | some k => env k

def evalApplied {V R : Type} (interpret : Nat → (Nat → V) → R)
    (a : Applied Nat) (env : Nat → V) : R :=
  interpret a.id (fun j => env (a.slots[j]?.getD 0))

def meaning {V R : Type} (alg : Algebra V R) (interpret : Nat → (Nat → V) → R)
    (n : Node) (env : Nat → V) : R :=
  match n.op with
  | .var => alg.variableValue (env 0)
  | op => alg.apply op (n.children.map fun e fresh =>
      interpret e.id (fun j => evalEdgeSlot env fresh (e.slots[j]?.join)))

private theorem meaning_nonvar {V R : Type} (alg : Algebra V R) (interpret : Nat → (Nat → V) → R)
    (n : Node) (h : n.op ≠ .var) (env : Nat → V) :
    meaning alg interpret n env =
      alg.apply n.op (n.children.map fun e fresh =>
        interpret e.id (fun j => evalEdgeSlot env fresh (e.slots[j]?.join))) := by
  cases n with
  | mk ar op ch => cases op <;> first | exact absurd rfl h | rfl

private def RenStateWF (used : Array Nat) (ren : Std.HashMap Nat Nat) : Prop :=
  (∀ (k j : Nat), ren[k]? = some j → used[j]? = some k) ∧
  (∀ (j k : Nat), used[j]? = some k → ren[k]? = some j)

private def ArrayExtends (old new : Array Nat) : Prop :=
  old.size ≤ new.size ∧ ∀ (j : Nat), j < old.size → new[j]? = old[j]?

private theorem ArrayExtends.refl (a : Array Nat) : ArrayExtends a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem ArrayExtends.trans {a b c : Array Nat} (h1 : ArrayExtends a b) (h2 : ArrayExtends b c) :
    ArrayExtends a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun j hj => (h2.2 j (Nat.lt_of_lt_of_le hj h1.1)).trans (h1.2 j hj)⟩

private theorem ArrayExtends.push (a : Array Nat) (x : Nat) : ArrayExtends a (a.push x) :=
  ⟨by simp, fun j hj => by rw [Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj]⟩

private theorem ArrayExtends.get_some {old new : Array Nat} (he : ArrayExtends old new)
    {j k : Nat} (h : old[j]? = some k) : new[j]? = some k := by
  have hj : j < old.size := by
    by_cases hlt : j < old.size; · exact hlt
    · rw [Array.getElem?_eq_none (by omega)] at h; cases h
  exact (he.2 j hj).trans h

private theorem renStateWF_nodup {used : Array Nat} {ren : Std.HashMap Nat Nat}
    (h : RenStateWF used ren) : used.toList.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hlt heq
  have hi' : i < used.size := by simpa using hi
  have hj' : j < used.size := by simpa using hj
  have h1 := h.2 i (used[i]'hi') (Array.getElem?_eq_getElem hi')
  have h2 := h.2 j (used[j]'hj') (Array.getElem?_eq_getElem hj')
  have heq' : used[i]'hi' = used[j]'hj' := by simpa [Array.getElem_toList] using heq
  rw [heq', h2] at h1
  have hij := Option.some.inj h1
  omega

private def SlotMaps (used : Array Nat) (orig mapped : Option Nat) : Prop :=
  (orig = none → mapped = none) ∧
  (∀ k, orig = some k → ∃ j, mapped = some j ∧ used[j]? = some k)

private theorem SlotMaps.mono {u1 u2 : Array Nat} {o m : Option Nat}
    (hm : SlotMaps u1 o m) (he : ArrayExtends u1 u2) : SlotMaps u2 o m :=
  ⟨hm.1, fun k hk => let ⟨j, hmj, hu⟩ := hm.2 k hk; ⟨j, hmj, he.get_some hu⟩⟩

private theorem shapeSlot_spec (s : Option Nat) (st : Array Nat × Std.HashMap Nat Nat)
    (hwf : RenStateWF st.1 st.2) :
    let r := shapeSlot s st
    RenStateWF r.2.1 r.2.2 ∧ ArrayExtends st.1 r.2.1 ∧ SlotMaps r.2.1 s r.1 := by
  cases s with
  | none => exact ⟨hwf, ArrayExtends.refl _, ⟨fun _ => rfl, fun _ h => by cases h⟩⟩
  | some k =>
    unfold shapeSlot
    cases h : st.2[k]? with
    | some j =>
      simp only [h]
      exact ⟨hwf, ArrayExtends.refl _, ⟨fun h' => (by cases h'), fun k' hk' => ⟨j, rfl, (Option.some.inj hk') ▸ hwf.1 k j h⟩⟩⟩
    | none =>
      simp only [h]
      refine ⟨⟨?_, ?_⟩, ArrayExtends.push st.1 k, ⟨fun h' => (by cases h'), fun k' hk' => ?_⟩⟩
      · intro k' j' hk'
        by_cases he : k = k'
        · subst he; simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hk'
          subst hk'; exact Array.getElem?_push_size
        · rw [Std.HashMap.getElem?_insert, beq_false_of_ne he] at hk'
          exact (ArrayExtends.push st.1 k).get_some (hwf.1 k' j' hk')
      · intro j' k' hj'
        by_cases hlt : j' < st.1.size
        · rw [Array.getElem?_push_lt hlt] at hj'
          injection hj' with hk'; subst hk'
          have hne : k ≠ st.1[j']'hlt := fun heq => by
            have := hwf.2 j' (st.1[j']'hlt) (Array.getElem?_eq_getElem hlt)
            rw [← heq, h] at this; cases this
          rw [Std.HashMap.getElem?_insert, beq_false_of_ne hne]
          exact hwf.2 j' (st.1[j']'hlt) (Array.getElem?_eq_getElem hlt)
        · by_cases heq : j' = st.1.size
          · subst heq; rw [Array.getElem?_push_size] at hj'
            injection hj' with hk'; subst hk'; simp
          · rw [Array.getElem?_eq_none (by simp; omega)] at hj'; cases hj'
      · injection hk' with hkeq; subst hkeq; exact ⟨st.1.size, rfl, Array.getElem?_push_size⟩

private def EdgeMatchesOpt (e e' : Applied (Option Nat)) (used : Array Nat) : Prop :=
  e'.id = e.id ∧ e'.slots.size = e.slots.size ∧
  ∀ (i : Nat), ∀ s s', e.slots[i]? = some s → e'.slots[i]? = some s' → SlotMaps used s s'

private theorem EdgeMatchesOpt.mono {e e' : Applied (Option Nat)} {u1 u2 : Array Nat}
    (hm : EdgeMatchesOpt e e' u1) (he : ArrayExtends u1 u2) : EdgeMatchesOpt e e' u2 :=
  ⟨hm.1, hm.2.1, fun i s s' h1 h2 => (hm.2.2 i s s' h1 h2).mono he⟩

private theorem shapeEdge_spec (e : Applied (Option Nat)) (st : Array Nat × Std.HashMap Nat Nat)
    (hwf : RenStateWF st.1 st.2) :
    let r := shapeEdge e st
    RenStateWF r.2.1 r.2.2 ∧ ArrayExtends st.1 r.2.1 ∧ EdgeMatchesOpt e r.1 r.2.1 := by
  let inv := fun (idx : Nat) (p : Array (Option Nat) × (Array Nat × Std.HashMap Nat Nat)) =>
    RenStateWF p.2.1 p.2.2 ∧ ArrayExtends st.1 p.2.1 ∧ p.1.size = idx ∧
    ∀ (i : Nat) s s', i < idx → e.slots[i]? = some s → p.1[i]? = some s' → SlotMaps p.2.1 s s'
  have hfold : inv e.slots.size (e.slots.foldl (fun (acc, s) slot =>
      let (slot', s') := shapeSlot slot s; (acc.push slot', s')) (#[], st)) := by
    apply Array.foldl_induction (motive := inv)
    · exact ⟨hwf, ArrayExtends.refl _, rfl, fun _ _ _ h => by omega⟩
    · intro idx ⟨acc, s⟩ ⟨hsw, hext, hsz, hall⟩
      have hss := shapeSlot_spec e.slots[idx] s hsw
      refine ⟨hss.1, hext.trans hss.2.1, by simp [hsz], fun i s1 s2 hi hs1 hs2 => ?_⟩
      by_cases hilt : i < idx.val
      · have hiacc : i < acc.size := by rw [hsz]; exact hilt
        rw [Array.getElem?_push_lt hiacc, ← Array.getElem?_eq_getElem hiacc] at hs2
        exact (hall i s1 s2 hilt hs1 hs2).mono hss.2.1
      · have hiEq : i = idx.val := by omega
        subst hiEq
        have h1 : e.slots[idx.val]? = some e.slots[idx] := Array.getElem?_eq_getElem idx.isLt
        rw [h1] at hs1; injection hs1 with h1eq; subst h1eq
        have h2 : (acc.push (shapeSlot e.slots[idx] s).1)[acc.size]? = some (shapeSlot e.slots[idx] s).1 :=
          Array.getElem?_push_size
        rw [hsz] at h2; rw [h2] at hs2; injection hs2 with h2eq; subst h2eq
        exact hss.2.2
  refine ⟨hfold.1, hfold.2.1, rfl, hfold.2.2.1, fun i s1 s2 hs1 hs2 => ?_⟩
  have hi : i < e.slots.size := by
    by_cases hlt : i < e.slots.size; · exact hlt
    · rw [Array.getElem?_eq_none (by omega)] at hs1; cases hs1
  exact hfold.2.2.2 i s1 s2 hi hs1 hs2

private theorem shape_children_spec (children : Array (Applied (Option Nat))) :
    let res := children.foldl (fun (acc, s) e =>
      let (e', s') := shapeEdge e s; (acc.push e', s')) (#[], (#[], {}))
    RenStateWF res.2.1 res.2.2 ∧ res.1.size = children.size ∧
    ∀ (i : Nat) e e', children[i]? = some e → res.1[i]? = some e' → EdgeMatchesOpt e e' res.2.1 := by
  let inv := fun (idx : Nat) (p : Array (Applied (Option Nat)) × (Array Nat × Std.HashMap Nat Nat)) =>
    RenStateWF p.2.1 p.2.2 ∧ p.1.size = idx ∧
    ∀ (i : Nat) e e', i < idx → children[i]? = some e → p.1[i]? = some e' → EdgeMatchesOpt e e' p.2.1
  have hinit : RenStateWF (#[] : Array Nat) ({} : Std.HashMap Nat Nat) :=
    ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩
  have hfold : inv children.size (children.foldl (fun (acc, s) e =>
      let (e', s') := shapeEdge e s; (acc.push e', s')) (#[], (#[], {}))) := by
    apply Array.foldl_induction (motive := inv)
    · exact ⟨hinit, rfl, fun _ _ _ h => by omega⟩
    · intro idx ⟨acc, s⟩ ⟨hsw, hsz, hall⟩
      have hse := shapeEdge_spec children[idx] s hsw
      refine ⟨hse.1, by simp [hsz], fun i e1 e2 hi he1 he2 => ?_⟩
      by_cases hilt : i < idx.val
      · have hiacc : i < acc.size := by rw [hsz]; exact hilt
        rw [Array.getElem?_push_lt hiacc, ← Array.getElem?_eq_getElem hiacc] at he2
        exact (hall i e1 e2 hilt he1 he2).mono hse.2.1
      · have hiEq : i = idx.val := by omega
        subst hiEq
        have h1 : children[idx.val]? = some children[idx] := Array.getElem?_eq_getElem idx.isLt
        rw [h1] at he1; injection he1 with h1eq; subst h1eq
        have h2 : (acc.push (shapeEdge children[idx] s).1)[acc.size]? = some (shapeEdge children[idx] s).1 :=
          Array.getElem?_push_size
        rw [hsz] at h2; rw [h2] at he2; injection he2 with h2eq; subst h2eq
        exact hse.2.2
  refine ⟨hfold.1, hfold.2.1, fun i e1 e2 he1 he2 => ?_⟩
  have hi : i < children.size := by
    by_cases hlt : i < children.size; · exact hlt
    · rw [Array.getElem?_eq_none (by omega)] at he1; cases he1
  exact hfold.2.2 i e1 e2 hi he1 he2

private theorem shape_spec (n : Node) :
    let r := shape n
    r.2.size = r.1.arity ∧ r.2.toList.Nodup ∧
    (n.op = .var → r.1 = ⟨1, .var, #[]⟩ ∧ r.2 = #[0]) ∧
    (n.op ≠ .var → r.1.op = n.op ∧ r.1.children.size = n.children.size ∧
      ∀ (i : Nat) e e', n.children[i]? = some e → r.1.children[i]? = some e' → EdgeMatchesOpt e e' r.2) := by
  cases n with
  | mk ar op ch =>
    cases op with
    | var => simp [shape]
    | bind =>
      have hf := shape_children_spec ch
      exact ⟨rfl, renStateWF_nodup hf.1, fun h => by simp at h, fun _ => ⟨rfl, hf.2.1, hf.2.2⟩⟩
    | node tag =>
      have hf := shape_children_spec ch
      exact ⟨rfl, renStateWF_nodup hf.1, fun h => by simp at h, fun _ => ⟨rfl, hf.2.1, hf.2.2⟩⟩

private theorem edgeMatches_eval {V : Type} {e e' : Applied (Option Nat)} {used : Array Nat}
    (hm : EdgeMatchesOpt e e' used) (env : Nat → V) (fresh : V) (j : Nat) :
    evalEdgeSlot (fun k => env (used[k]?.getD 0)) fresh (e'.slots[j]?.join) =
      evalEdgeSlot env fresh (e.slots[j]?.join) := by
  by_cases hj : j < e.slots.size
  · have hj' : j < e'.slots.size := by rw [hm.2.1]; exact hj
    have hsm := hm.2.2 j (e.slots[j]'hj) (e'.slots[j]'hj') (Array.getElem?_eq_getElem hj) (Array.getElem?_eq_getElem hj')
    rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_getElem hj']
    simp only [Option.join]
    cases hs : e.slots[j]'hj with
    | none => rw [hsm.1 hs]; rfl
    | some k =>
      obtain ⟨idx, hidx, hu⟩ := hsm.2 k hs
      rw [hidx]; simp [evalEdgeSlot, hu]
  · have hj' : ¬ (j < e'.slots.size) := by rw [hm.2.1]; exact hj
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hj), Array.getElem?_eq_none (Nat.le_of_not_lt hj')]
    rfl

/-- `shape` preserves node meaning up to projection/renaming by its `used` slot map. -/
theorem shape_meaning {V R : Type} (alg : Algebra V R) (val : Nat → (Nat → V) → R)
    (n : Node) (env : Nat → V) :
    meaning alg val n env = meaning alg val (shape n).1 (fun j => env ((shape n).2[j]?.getD 0)) := by
  have hs := shape_spec n
  by_cases hvar : n.op = .var
  · obtain ⟨hn', hu⟩ := hs.2.2.1 hvar
    cases n with | mk ar op ch =>
      simp only at hvar; subst hvar
      rw [hn', hu]; simp [meaning]
  · obtain ⟨hop', hsz, hedge⟩ := hs.2.2.2 hvar
    rw [meaning_nonvar alg val n hvar, meaning_nonvar alg val (shape n).1 (hop' ▸ hvar), hop']
    congr 1
    apply Array.ext (by simp [hsz])
    intro i hi1 hi2
    have hi : i < n.children.size := by simpa using hi1
    have hi' : i < (shape n).1.children.size := by simpa using hi2
    simp only [Array.getElem_map]
    funext fresh
    have hm := hedge i (n.children[i]'hi) ((shape n).1.children[i]'hi')
      (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hi')
    rw [hm.1]
    congr 1; funext j
    exact (edgeMatches_eval hm env fresh j).symm

private theorem rebuildEdge_meaning {V R : Type}
    (arityOf : Nat → Nat) (val : Nat → (Nat → V) → R)
    (rep : Nat → Applied Nat) (perms : Nat → Array (Array Nat))
    (hDep : ∀ i, DependsOnly (arityOf i) (val i))
    (hRep : ∀ i, (rep i).slots.size = arityOf (rep i).id ∧
      ∀ env, val i env = val (rep i).id (fun j => env ((rep i).slots[j]?.getD 0)))
    (hPerm : ∀ c π, π ∈ perms c → π.size = arityOf c ∧
      ∀ env, val c env = val c (fun j => env (π[j]?.getD 0)))
    (e : Applied (Option Nat)) (env : Nat → V) (fresh : V) :
    val (rebuildEdge rep perms e).id (fun j => evalEdgeSlot env fresh ((rebuildEdge rep perms e).slots[j]?.join)) =
      val e.id (fun j => evalEdgeSlot env fresh (e.slots[j]?.join)) := by
  unfold rebuildEdge
  dsimp only
  let r := rep e.id
  let base := r.slots.map fun j => (e.slots[j]?.join)
  have hbaseSz : base.size = arityOf r.id := by simp [base, r, (hRep e.id).1]
  have hbaseEq : val r.id (fun j => evalEdgeSlot env fresh (base[j]?.join)) =
      val e.id (fun j => evalEdgeSlot env fresh (e.slots[j]?.join)) := by
    rw [(hRep e.id).2]
    apply hDep r.id
    intro j hj
    have hjr : j < r.slots.size := by rw [(hRep e.id).1]; exact hj
    simp only [base, r, Array.getElem?_map, Array.getElem?_eq_getElem hjr, Option.map_some, Option.join_some, Option.getD_some]
  let inv := fun (_ : Nat) (cur : Array (Option Nat)) =>
    cur.size = arityOf r.id ∧
    val r.id (fun j => evalEdgeSlot env fresh (cur[j]?.join)) =
      val r.id (fun j => evalEdgeSlot env fresh (base[j]?.join))
  have hfold : inv (perms r.id).size ((perms r.id).foldl (fun cur π =>
      if π.size == base.size then
        let cand := π.map fun j => (base[j]?.join)
        if slotsLt cand cur then cand else cur
      else cur) base) := by
    apply Array.foldl_induction (motive := inv) ⟨hbaseSz, rfl⟩
    intro idx cur ⟨hcsz, hceq⟩
    have hπ := hPerm r.id (perms r.id)[idx] (Array.getElem_mem _)
    dsimp only
    split
    · split
      · refine ⟨Array.size_map.trans hπ.1, ?_⟩
        rw [hπ.2 (fun j => evalEdgeSlot env fresh (base[j]?.join))]
        apply hDep r.id
        intro j hj
        have hjπ : j < (perms r.id)[idx].size := by rw [hπ.1]; exact hj
        simp only [Array.getElem?_map, Array.getElem?_eq_getElem hjπ, Option.map_some, Option.join_some, Option.getD_some]
      · exact ⟨hcsz, hceq⟩
    · exact ⟨hcsz, hceq⟩
  exact hfold.2.trans hbaseEq

/-- Rebuilding a node preserves its meaning up to `shape`'s `used` slot projection. -/
theorem rebuildNode_meaning {V R : Type} (alg : Algebra V R)
    (arityOf : Nat → Nat) (val : Nat → (Nat → V) → R)
    (rep : Nat → Applied Nat) (perms : Nat → Array (Array Nat))
    (hDep : ∀ i, DependsOnly (arityOf i) (val i))
    (hRep : ∀ i, (rep i).slots.size = arityOf (rep i).id ∧
      ∀ env, val i env = val (rep i).id (fun j => env ((rep i).slots[j]?.getD 0)))
    (hPerm : ∀ c π, π ∈ perms c → π.size = arityOf c ∧
      ∀ env, val c env = val c (fun j => env (π[j]?.getD 0)))
    (n : Node) (env : Nat → V) :
    meaning alg val n env =
      meaning alg val (rebuildNode rep perms n).1
        (fun j => env ((rebuildNode rep perms n).2[j]?.getD 0)) := by
  unfold rebuildNode
  rw [← shape_meaning]
  cases n with
  | mk ar op ch =>
    cases op with
    | var => rfl
    | bind =>
      simp only [meaning, Array.map_map]
      congr 1
      apply Array.ext (by simp)
      intro i hi1 hi2
      have hi : i < ch.size := by simpa using hi1
      simp only [Array.getElem_map, Function.comp_apply]
      funext fresh
      exact (rebuildEdge_meaning arityOf val rep perms hDep hRep hPerm (ch[i]'hi) env fresh).symm
    | node tag =>
      simp only [meaning, Array.map_map]
      congr 1
      apply Array.ext (by simp)
      intro i hi1 hi2
      have hi : i < ch.size := by simpa using hi1
      simp only [Array.getElem_map, Function.comp_apply]
      funext fresh
      exact (rebuildEdge_meaning arityOf val rep perms hDep hRep hPerm (ch[i]'hi) env fresh).symm

private theorem idxOf?_some_getElem {xs : Array Nat} {x j : Nat} (h : xs.idxOf? x = some j) :
    ∃ hj : j < xs.size, xs[j]'hj = x := by
  have hl : xs.toList.idxOf? x = some j := by
    rw [← List.idxOf?_toArray, Array.toArray_toList]; exact h
  obtain ⟨hj, hget, _⟩ := List.idxOf?_eq_some_iff.mp hl
  exact ⟨by simpa using hj, by simpa [Array.getElem_toList] using hget⟩

private theorem idxOf?_of_nodup_getElem {xs : Array Nat} (hNd : xs.toList.Nodup)
    {j : Nat} (hj : j < xs.size) : xs.idxOf? (xs[j]'hj) = some j := by
  have hconv : ∀ (x : Nat), xs.idxOf? x = xs.toList.idxOf? x := fun x => by
    rw [← Array.toArray_toList (xs := xs), List.idxOf?_toArray]
  rw [hconv]
  have hjL : j < xs.toList.length := by simpa using hj
  refine List.idxOf?_eq_some_iff.mpr ⟨hjL, by simp, fun k hk heq => ?_⟩
  have hne := (List.pairwise_iff_getElem.mp hNd) k j (Nat.lt_trans hk hjL) hjL hk
  exact hne (by simpa [Array.getElem_toList] using heq)

private theorem evalApplied_appFromUsed {V R : Type} (alg : Algebra V R)
    (val : Nat → (Nat → V) → R) (id arity freshBase : Nat) (key : Node) (used : Array Nat)
    (hNd : used.toList.Nodup) (hSz : used.size = key.arity)
    (hBnd : usedInBounds arity used = true)
    (hNode : ∀ env, val id env = meaning alg val key (fun j => env (used[j]?.getD 0)))
    (hKeyDep : DependsOnly key.arity (meaning alg val key))
    (env : Nat → V) :
    evalApplied val (appFromUsed id arity used freshBase) env = meaning alg val key env := by
  unfold evalApplied appFromUsed
  dsimp only
  rw [hNode]
  apply hKeyDep
  intro j hj
  have hju : j < used.size := by omega
  have hkLt : used[j]'hju < arity :=
    of_decide_eq_true ((Array.all_eq_true_iff_forall_mem.mp hBnd) (used[j]'hju) (Array.getElem_mem hju))
  have hidx : used.idxOf? (used[j]'hju) = some j := idxOf?_of_nodup_getElem hNd hju
  simp [hju, hkLt, hidx]

private theorem meaning_shape_dependsOnly {V R : Type} (alg : Algebra V R)
    (val : Nat → (Nat → V) → R) (n : Node) :
    DependsOnly (shape n).1.arity (meaning alg val (shape n).1) := by
  have hs := shape_spec n
  by_cases hvar : n.op = .var
  · obtain ⟨hn', _⟩ := hs.2.2.1 hvar
    rw [hn']
    intro env₁ env₂ hAgree
    exact congrArg alg.variableValue (hAgree 0 (by decide))
  · obtain ⟨hop', hsz, hedge⟩ := hs.2.2.2 hvar
    intro env₁ env₂ hAgree
    rw [meaning_nonvar alg val (shape n).1 (hop' ▸ hvar),
      meaning_nonvar alg val (shape n).1 (hop' ▸ hvar)]
    congr 1
    apply Array.ext (by simp)
    intro i hi1 hi2
    have hi' : i < (shape n).1.children.size := by simpa using hi1
    have hi : i < n.children.size := by omega
    simp only [Array.getElem_map]
    funext fresh; congr 1; funext j
    have hm := hedge i (n.children[i]'hi) ((shape n).1.children[i]'hi')
      (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hi')
    by_cases hj' : j < ((shape n).1.children[i]'hi').slots.size
    · have hj : j < (n.children[i]'hi).slots.size := by rw [← hm.2.1]; exact hj'
      have hsm := hm.2.2 j ((n.children[i]'hi).slots[j]'hj) (((shape n).1.children[i]'hi').slots[j]'hj')
        (Array.getElem?_eq_getElem hj) (Array.getElem?_eq_getElem hj')
      rw [Array.getElem?_eq_getElem hj']
      simp only [Option.join]
      cases horig : (n.children[i]'hi).slots[j]'hj with
      | none => rw [hsm.1 horig]; rfl
      | some k =>
        obtain ⟨idx, hidx, hu⟩ := hsm.2 k horig
        rw [hidx]
        have hlt : idx < (shape n).2.size := by
          by_cases h : idx < (shape n).2.size; · exact h
          · rw [Array.getElem?_eq_none (by omega)] at hu; cases hu
        exact hAgree idx (by rw [← hs.1]; exact hlt)
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hj')]; rfl

/-- Every equation emitted by `slottedRebuild` (including redundant-slot shrinking and
symmetry-normalized congruences) holds in every sound interpretation. -/
theorem slottedRebuild_sound {V R : Type} (alg : Algebra V R)
    (arityOf : Nat → Nat) (val : Nat → (Nat → V) → R)
    (rep : Nat → Applied Nat) (perms : Nat → Array (Array Nat))
    (hDep : ∀ i, DependsOnly (arityOf i) (val i))
    (hRep : ∀ i, (rep i).slots.size = arityOf (rep i).id ∧
      ∀ env, val i env = val (rep i).id (fun j => env ((rep i).slots[j]?.getD 0)))
    (hPerm : ∀ c π, π ∈ perms c → π.size = arityOf c ∧
      ∀ env, val c env = val c (fun j => env (π[j]?.getD 0)))
    (entries : Array (Nat × Node))
    (consistent : ∀ e ∈ entries, val e.1 = meaning alg val e.2) :
    ∀ eq ∈ slottedRebuild arityOf rep perms entries,
      ∀ env : Nat → V, evalApplied val eq.1 env = evalApplied val eq.2 env := by
  let inv := fun s : Work =>
    (∀ (key : Node) (owner : Nat) (used : Array Nat), s.1[key]? = some (owner, used) →
      used.size = key.arity ∧ used.toList.Nodup ∧
      DependsOnly key.arity (meaning alg val key) ∧
      ∀ env, val owner env = meaning alg val key (fun j => env (used[j]?.getD 0))) ∧
    (∀ eq ∈ s.2, ∀ env, evalApplied val eq.1 env = evalApplied val eq.2 env)
  have h : inv (entries.foldl (rebuildStep arityOf rep perms) ({}, #[])) := by
    apply Array.foldl_induction (motive := fun _ => inv) (by simp [inv])
    intro idx s ⟨hSeen, hEqs⟩
    let subst : Node := match entries[idx].2.op with
      | .var => entries[idx].2
      | op => ⟨entries[idx].2.arity, op, entries[idx].2.children.map (rebuildEdge rep perms)⟩
    have hPair : rebuildNode rep perms entries[idx].2 = shape subst := rfl
    have hs := shape_spec subst
    have hKeyDep : DependsOnly (shape subst).1.arity (meaning alg val (shape subst).1) :=
      meaning_shape_dependsOnly alg val subst
    have hValItem : ∀ env, val entries[idx].1 env =
        meaning alg val (shape subst).1 (fun j => env ((shape subst).2[j]?.getD 0)) := by
      intro env
      rw [consistent entries[idx] (Array.getElem_mem _)]
      exact rebuildNode_meaning alg arityOf val rep perms hDep hRep hPerm entries[idx].2 env
    change inv (rebuildStep arityOf rep perms s entries[idx])
    unfold rebuildStep
    dsimp only
    rw [hPair]
    by_cases hBnd : usedInBounds (arityOf entries[idx].1) (shape subst).2 = true
    · simp only [hBnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hSelf : ∀ env,
          evalApplied val (appFromUsed entries[idx].1 (arityOf entries[idx].1) (shape subst).2 (shape subst).1.arity) env =
          meaning alg val (shape subst).1 env :=
        evalApplied_appFromUsed alg val entries[idx].1 (arityOf entries[idx].1) (shape subst).1.arity
          (shape subst).1 (shape subst).2 hs.2.1 hs.1 hBnd hValItem hKeyDep
      have hSelf2 : ∀ env,
          evalApplied val (appFromUsed entries[idx].1 (arityOf entries[idx].1) (shape subst).2
            ((shape subst).1.arity + arityOf entries[idx].1)) env =
          meaning alg val (shape subst).1 env :=
        evalApplied_appFromUsed alg val entries[idx].1 (arityOf entries[idx].1)
          ((shape subst).1.arity + arityOf entries[idx].1)
          (shape subst).1 (shape subst).2 hs.2.1 hs.1 hBnd hValItem hKeyDep
      let eqs1 := if (shape subst).2.size < arityOf entries[idx].1 then
          s.2.push (appFromUsed entries[idx].1 (arityOf entries[idx].1) (shape subst).2 (shape subst).1.arity,
            appFromUsed entries[idx].1 (arityOf entries[idx].1) (shape subst).2 ((shape subst).1.arity + arityOf entries[idx].1))
        else s.2
      have hEqs1 : ∀ eq ∈ eqs1, ∀ env, evalApplied val eq.1 env = evalApplied val eq.2 env := by
        intro eq hMem env
        by_cases hlt : (shape subst).2.size < arityOf entries[idx].1
        · simp only [eqs1, hlt, ↓reduceIte, Array.mem_push] at hMem
          rcases hMem with hOld | rfl
          · exact hEqs eq hOld env
          · exact (hSelf env).trans (hSelf2 env).symm
        · simp only [eqs1, hlt, ↓reduceIte] at hMem
          exact hEqs eq hMem env
      cases hLook : s.1[(shape subst).1]? with
      | none =>
        refine ⟨fun key owner used hl => ?_, hEqs1⟩
        by_cases hk : (shape subst).1 = key
        · subst hk
          simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          exact ⟨hs.1, hs.2.1, hKeyDep, hValItem⟩
        · rw [Std.HashMap.getElem?_insert, beq_false_of_ne hk] at hl
          exact hSeen key owner used hl
      | some earlierPair =>
        obtain ⟨earlier, earlierUsed⟩ := earlierPair
        by_cases hBndE : usedInBounds (arityOf earlier) earlierUsed = true
        · simp only [hBndE, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨heSz, heNd, heDep, heVal⟩ := hSeen _ earlier earlierUsed hLook
          refine ⟨hSeen, fun eq hMem env => ?_⟩
          rcases Array.mem_push.mp hMem with hOld | rfl
          · exact hEqs1 eq hOld env
          · exact (hSelf env).trans
              (evalApplied_appFromUsed alg val earlier (arityOf earlier)
                ((shape subst).1.arity + arityOf entries[idx].1)
                (shape subst).1 earlierUsed heNd heSz hBndE heVal heDep env).symm
        · simp only [hBndE, Bool.not_false, ↓reduceIte]
          exact ⟨hSeen, hEqs1⟩
    · simp only [hBnd, Bool.not_false, ↓reduceIte]
      exact ⟨hSeen, hEqs⟩
  exact h.2

/-! ## Union-Find Soundness & `Graph.close_sound` -/

private def UFSound {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure) : Prop :=
  cl.parent.size = cl.arity.size ∧
  cl.perms.size = cl.arity.size ∧
  (∀ i, DependsOnly (cl.arityOf i) (val i)) ∧
  (∀ i p, cl.parent[i]? = some p →
    ∃ hp : p.id < cl.arity.size, p.slots.size = cl.arity[p.id]'hp ∧
      ∀ env, val i env = val p.id (fun j => env (p.slots[j]?.getD 0))) ∧
  (∀ i π, π ∈ cl.perms[i]?.getD #[] →
    π.size = cl.arityOf i ∧
    ∀ env, val i env = val i (fun j => env (π[j]?.getD 0)))

private example :
    UFSound (V := Nat) (R := Nat) (fun _ _ => 0) ⟨#[], #[], #[]⟩ ∧
    arrayNodup #[0, 1] = true := by
  refine ⟨⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩, ?_⟩
  rw [arrayNodup, Array.all_eq_true_iff_forall_mem]
  intro i hi
  have hlt : i < (#[0, 1] : Array Nat).size := Array.mem_range.mp hi
  have hlt2 : i < 2 := by simpa using hlt
  match i, hlt2 with
  | 0, _ => simp; decide
  | 1, _ => simp; decide

private theorem walkUF_sound {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure)
    (hok : UFSound val cl) (fuel : Nat) (a : Applied Nat)
    (ha : a.id < cl.arity.size) (hsz : a.slots.size = cl.arity[a.id]'ha) :
    let r := walkUF cl.parent fuel a
    ∃ hr : r.id < cl.arity.size, r.slots.size = cl.arity[r.id]'hr ∧
      ∀ env, evalApplied val r env = evalApplied val a env := by
  induction fuel generalizing a with
  | zero => exact ⟨ha, hsz, fun _ => rfl⟩
  | succ n ih =>
    rw [walkUF]
    have hpLt : a.id < cl.parent.size := by rw [hok.1]; exact ha
    rw [Array.getElem?_eq_getElem hpLt]
    dsimp only
    by_cases hself : (cl.parent[a.id]'hpLt).id = a.id
    · have hbeq : ((cl.parent[a.id]'hpLt).id == a.id) = true := beq_iff_eq.mpr hself
      rw [ite_eq_left hbeq]
      exact ⟨ha, hsz, fun _ => rfl⟩
    · have hbeq : ((cl.parent[a.id]'hpLt).id == a.id) = false := beq_false_of_ne hself
      rw [ite_eq_right (by simp [hbeq])]
      obtain ⟨hpId, hpSz, hpVal⟩ := hok.2.2.2.1 a.id (cl.parent[a.id]'hpLt) (Array.getElem?_eq_getElem hpLt)
      let p := cl.parent[a.id]'hpLt
      let next : Applied Nat := ⟨p.id, p.slots.map fun j => a.slots[j]?.getD 0⟩
      have hnextSz : next.slots.size = cl.arity[next.id]'hpId := by simp [next, p, hpSz]
      obtain ⟨hr, hrsz, hreq⟩ := ih next hpId hnextSz
      refine ⟨hr, hrsz, fun env => (hreq env).trans ?_⟩
      unfold evalApplied
      rw [hpVal]
      have hdep := hok.2.2.1 p.id
      have hpId' : p.id < cl.arity.size := hpId
      simp only [Closure.arityOf, Array.getElem?_eq_getElem hpId', Option.getD_some] at hdep
      apply hdep
      intro j hj
      have hjp : j < p.slots.size := by rw [hpSz]; exact hj
      simp only [next, p, Array.getElem?_map, Array.getElem?_eq_getElem hjp, Option.map_some, Option.getD_some]

private theorem closure_repOf_sound {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure)
    (hok : UFSound val cl) (i : Nat) :
    (cl.repOf i).slots.size = cl.arityOf (cl.repOf i).id ∧
    ∀ env, val i env = val (cl.repOf i).id (fun j => env ((cl.repOf i).slots[j]?.getD 0)) := by
  by_cases hi : i < cl.arity.size
  · have hsz : (Array.range (cl.arity[i]?.getD 0)).size = cl.arity[i]'hi := by simp [hi]
    obtain ⟨hr, hrsz, hreq⟩ := walkUF_sound val cl hok cl.parent.size
      ⟨i, Array.range (cl.arity[i]?.getD 0)⟩ hi hsz
    refine ⟨by simp [Closure.repOf, Closure.find, Closure.arityOf, hr, hrsz], fun env => ?_⟩
    have h1 := (hreq env).symm
    have h2 : evalApplied val ⟨i, Array.range (cl.arity[i]?.getD 0)⟩ env = val i env := by
      unfold evalApplied
      have hdep := hok.2.2.1 i
      simp only [Closure.arityOf, Array.getElem?_eq_getElem hi, Option.getD_some] at hdep
      apply hdep
      intro j hj; simp [hi, hj]
    exact h2.symm.trans h1
  · have hge : cl.arity.size ≤ i := Nat.le_of_not_lt hi
    have hNone : cl.parent[i]? = none := Array.getElem?_eq_none (by rw [hok.1]; exact hge)
    have hwalk : ∀ fuel, walkUF cl.parent fuel ⟨i, Array.range (cl.arity[i]?.getD 0)⟩ =
        ⟨i, Array.range (cl.arity[i]?.getD 0)⟩ := by
      intro fuel; cases fuel with | zero => rfl | succ _ => simp [walkUF, hNone]
    have h0 : cl.arityOf i = 0 := by simp [Closure.arityOf, Array.getElem?_eq_none hge]
    have hRepId : (cl.repOf i).id = i := by simp [Closure.repOf, Closure.find, hwalk]
    have hRepSz : (cl.repOf i).slots.size = 0 := by
      unfold Closure.repOf Closure.find; rw [hwalk]; simp [Array.getElem?_eq_none hge]
    refine ⟨by rw [hRepId, hRepSz, h0], fun env => ?_⟩
    rw [hRepId]
    have hdep := hok.2.2.1 i
    rw [h0] at hdep
    exact hdep env _ (fun j hj => by omega)

private theorem closure_canonApplied_sound {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure)
    (hok : UFSound val cl) (a : Applied Nat)
    (ha : a.id < cl.arity.size) (hsz : a.slots.size = cl.arity[a.id]'ha) (env : Nat → V) :
    evalApplied val (cl.canonApplied a) env = evalApplied val a env := by
  unfold Closure.canonApplied
  dsimp only
  obtain ⟨hr, hrsz, hreq⟩ := walkUF_sound val cl hok cl.parent.size a ha hsz
  let r := cl.find a
  let ps := cl.perms[r.id]?.getD #[]
  let inv := fun (_ : Nat) (cur : Array Nat) =>
    cur.size = cl.arity[r.id]'hr ∧
    val r.id (fun j => env (cur[j]?.getD 0)) = evalApplied val r env
  have hfold : inv ps.size (ps.foldl (fun cur π =>
      if π.size == r.slots.size then
        let cand := π.map fun j => r.slots[j]?.getD 0
        if natArrayLt cand cur then cand else cur
      else cur) r.slots) := by
    apply Array.foldl_induction (motive := inv) ⟨hrsz, rfl⟩
    intro idx cur ⟨hcsz, hceq⟩
    have hπ := hok.2.2.2.2 r.id ps[idx] (Array.getElem_mem _)
    have hr' : r.id < cl.arity.size := hr
    have hArR : cl.arityOf r.id = cl.arity[r.id]'hr' := by
      unfold Closure.arityOf
      rw [Array.getElem?_eq_getElem hr']; rfl
    rw [hArR] at hπ
    dsimp only
    split
    · split
      · refine ⟨Array.size_map.trans hπ.1, ?_⟩
        unfold evalApplied
        rw [hπ.2 (fun j => env (r.slots[j]?.getD 0))]
        have hdep := hok.2.2.1 r.id
        rw [hArR] at hdep
        apply hdep
        intro j hj
        have hjπ : j < ps[idx].size := by rw [hπ.1]; exact hj
        simp only [Array.getElem?_map, Array.getElem?_eq_getElem hjπ, Option.map_some, Option.getD_some]
      · exact ⟨hcsz, hceq⟩
    · exact ⟨hcsz, hceq⟩
  exact hfold.2.trans (hreq env)

private theorem arrayNodup_idxOf {xs : Array Nat} (h : arrayNodup xs = true)
    {j : Nat} (hj : j < xs.size) : xs.idxOf? (xs[j]'hj) = some j := by
  have hall := Array.all_eq_true_iff_forall_mem.mp h j (Array.mem_range.mpr hj)
  simpa [hj] using hall

private theorem idxOf?_some_of_contains {xs : Array Nat} {x : Nat} (h : xs.contains x = true) :
    ∃ (j : Nat) (hj : j < xs.size), xs.idxOf? x = some j ∧ xs[j]'hj = x := by
  have hmem : x ∈ xs := Array.contains_iff_mem.mp h
  cases hi : xs.idxOf? x with
  | none => exact absurd hmem (Array.idxOf?_eq_none_iff.mp hi)
  | some j =>
    obtain ⟨hj, hx⟩ := idxOf?_some_getElem hi
    exact ⟨j, hj, rfl, hx⟩

private def envFromSlots {V : Type} (a : Array Nat) (env : Nat → V) (fallback : V) (x : Nat) : V :=
  match a.idxOf? x with
  | some j => env j
  | none => fallback

private theorem eval_of_subset {V R : Type} (val : Nat → (Nat → V) → R)
    {id1 id2 : Nat} {a1 a2 : Array Nat}
    (hDep1 : DependsOnly a1.size (val id1)) (hDep2 : DependsOnly a2.size (val id2))
    (hNd1 : arrayNodup a1 = true) (hSub : isSubsetSlots a2 a1 = true)
    (hEq : ∀ env : Nat → V, evalApplied val ⟨id1, a1⟩ env = evalApplied val ⟨id2, a2⟩ env) :
    ∀ env1 : Nat → V, val id1 env1 = val id2 (fun k => env1 ((projectIndices a1 a2)[k]?.getD 0)) := by
  intro env1
  let env : Nat → V := envFromSlots a1 env1 (env1 0)
  have hL : evalApplied val ⟨id1, a1⟩ env = val id1 env1 := by
    unfold evalApplied
    apply hDep1
    intro j hj
    simp [env, envFromSlots, hj, arrayNodup_idxOf hNd1 hj]
  have hR : evalApplied val ⟨id2, a2⟩ env = val id2 (fun k => env1 ((projectIndices a1 a2)[k]?.getD 0)) := by
    unfold evalApplied
    apply hDep2
    intro k hk
    have hmem : a1.contains (a2[k]'hk) = true :=
      Array.all_eq_true_iff_forall_mem.mp hSub (a2[k]'hk) (Array.getElem_mem hk)
    obtain ⟨idx, _, hIdx, _⟩ := idxOf?_some_of_contains hmem
    simp [env, envFromSlots, projectIndices, hk, hIdx]
  exact hL.symm.trans ((hEq env).trans hR)

private theorem composePerm_sound {V R : Type} {f : (Nat → V) → R} {ar : Nat} {p q : Array Nat}
    (hDep : DependsOnly ar f)
    (hp : p.size = ar ∧ ∀ env, f env = f (fun j => env (p[j]?.getD 0)))
    (hq : q.size = ar ∧ ∀ env, f env = f (fun j => env (q[j]?.getD 0))) :
    (composePerm p q).size = ar ∧ ∀ env, f env = f (fun j => env ((composePerm p q)[j]?.getD 0)) := by
  refine ⟨by simp [composePerm, hq.1], fun env => ?_⟩
  rw [hp.2 env, hq.2 (fun j => env (p[j]?.getD 0))]
  apply hDep
  intro j hj
  have hjq : j < q.size := by rw [hq.1]; exact hj
  simp [composePerm, hjq]

private theorem addPerm_sound {V R : Type} {f : (Nat → V) → R} {ar : Nat}
    {ps : Array (Array Nat)} {π : Array Nat}
    (hDep : DependsOnly ar f)
    (hps : ∀ ρ ∈ ps, ρ.size = ar ∧ ∀ env, f env = f (fun j => env (ρ[j]?.getD 0)))
    (hπ : π.size = ar ∧ ∀ env, f env = f (fun j => env (π[j]?.getD 0))) :
    ∀ ρ ∈ (addPerm ps π).1, ρ.size = ar ∧ ∀ env, f env = f (fun j => env (ρ[j]?.getD 0)) := by
  unfold addPerm
  split
  · exact hps
  · let ps1 := ps.push π
    have hps1 : ∀ ρ ∈ ps1, ρ.size = ar ∧ ∀ env, f env = f (fun j => env (ρ[j]?.getD 0)) := by
      intro ρ hmem
      rcases Array.mem_push.mp hmem with hOld | rfl
      · exact hps ρ hOld
      · exact hπ
    apply Array.foldl_induction
      (motive := fun _ (acc : Array (Array Nat)) =>
        ∀ ρ ∈ acc, ρ.size = ar ∧ ∀ env, f env = f (fun j => env (ρ[j]?.getD 0)))
      hps1
    intro idx acc hacc
    have hρ := hps1 ps1[idx] (Array.getElem_mem _)
    have hc1 := composePerm_sound hDep hπ hρ
    have hc2 := composePerm_sound hDep hρ hπ
    dsimp only
    split
    · exact hacc
    · have hpush : ∀ (a : Array (Array Nat)) (c : Array Nat),
          (∀ x ∈ a, x.size = ar ∧ ∀ env, f env = f (fun j => env (x[j]?.getD 0))) →
          (c.size = ar ∧ ∀ env, f env = f (fun j => env (c[j]?.getD 0))) →
          ∀ x ∈ (if a.contains c || a.size ≥ 24 then a else a.push c),
            x.size = ar ∧ ∀ env, f env = f (fun j => env (x[j]?.getD 0)) := by
        intro a c ha hc
        split
        · exact ha
        · intro x hx; rcases Array.mem_push.mp hx with ho | rfl; exact ha x ho; exact hc
      exact hpush _ _ (hpush acc _ hacc hc1) hc2

private theorem intersection_sound {V R : Type} (val : Nat → (Nat → V) → R)
    {id1 id2 : Nat} {a1 a2 : Array Nat}
    (hDep1 : DependsOnly a1.size (val id1)) (hDep2 : DependsOnly a2.size (val id2))
    (hNd1 : arrayNodup a1 = true) (hNd2 : arrayNodup a2 = true)
    (hEq : ∀ env : Nat → V, evalApplied val ⟨id1, a1⟩ env = evalApplied val ⟨id2, a2⟩ env) :
    let common := a1.filter (a2.contains ·)
    let map1 := projectIndices a1 common
    let map2 := projectIndices a2 common
    let valNew : (Nat → V) → R := fun envC =>
      val id1 (fun j => match common.idxOf? (a1[j]?.getD 0) with
        | some c => envC c | none => envC 0)
    DependsOnly common.size valNew ∧
    (∀ env1, val id1 env1 = valNew (fun c => env1 (map1[c]?.getD 0))) ∧
    (∀ env2, val id2 env2 = valNew (fun c => env2 (map2[c]?.getD 0))) := by
  intro common map1 map2 valNew
  have hCommonMem : ∀ x, x ∈ common ↔ x ∈ a1 ∧ x ∈ a2 := fun x => by
    simp [common, Array.contains_iff_mem]
  have hCommonContains : ∀ x, common.contains x = true ↔ a1.contains x = true ∧ a2.contains x = true :=
    fun x => by simp [Array.contains_iff_mem, hCommonMem]
  have hCommonSub1 : ∀ {x c}, common.idxOf? x = some c →
      ∃ hc : c < common.size, common[c]'hc = x ∧
        ∃ idx, a1.idxOf? x = some idx ∧ map1[c]?.getD 0 = idx := by
    intro x c hcIdx
    obtain ⟨hc, hxEq⟩ := idxOf?_some_getElem hcIdx
    have hIn1 : a1.contains x = true := Array.contains_iff_mem.mpr ((hCommonMem x).mp (hxEq ▸ Array.getElem_mem hc)).1
    obtain ⟨idx, _, hIdx, _⟩ := idxOf?_some_of_contains hIn1
    exact ⟨hc, hxEq, idx, hIdx, by simp [map1, projectIndices, hc, hxEq, hIdx]⟩
  have hCommonSub2 : ∀ {x c}, common.idxOf? x = some c →
      ∃ hc : c < common.size, common[c]'hc = x ∧
        ∃ idx, a2.idxOf? x = some idx ∧ map2[c]?.getD 0 = idx := by
    intro x c hcIdx
    obtain ⟨hc, hxEq⟩ := idxOf?_some_getElem hcIdx
    have hIn2 : a2.contains x = true := Array.contains_iff_mem.mpr ((hCommonMem x).mp (hxEq ▸ Array.getElem_mem hc)).2
    obtain ⟨idx, _, hIdx, _⟩ := idxOf?_some_of_contains hIn2
    exact ⟨hc, hxEq, idx, hIdx, by simp [map2, projectIndices, hc, hxEq, hIdx]⟩
  have h1 : ∀ env1, val id1 env1 = valNew (fun c => env1 (map1[c]?.getD 0)) := by
    intro env1
    let d : V := env1 (map1[0]?.getD 0)
    let envX : Nat → V := envFromSlots a1 env1 d
    let envY : Nat → V := fun x => match common.idxOf? x with
      | some c => env1 (map1[c]?.getD 0) | none => d
    have hL : evalApplied val ⟨id1, a1⟩ envX = val id1 env1 := by
      unfold evalApplied; apply hDep1; intro j hj
      simp [envX, envFromSlots, hj, arrayNodup_idxOf hNd1 hj]
    have hR : evalApplied val ⟨id2, a2⟩ envX = evalApplied val ⟨id2, a2⟩ envY := by
      unfold evalApplied; apply hDep2; intro k hk
      simp only [Array.getElem?_eq_getElem hk, Option.getD_some]
      have hIn2 : a2[k]'hk ∈ a2 := Array.getElem_mem hk
      by_cases hIn1 : a1.contains (a2[k]'hk) = true
      · have hInC : common.contains (a2[k]'hk) = true :=
          (hCommonContains _).mpr ⟨hIn1, Array.contains_iff_mem.mpr hIn2⟩
        obtain ⟨c, _, hcIdx, _⟩ := idxOf?_some_of_contains hInC
        obtain ⟨_, _, idx, hIdx1, hMap1⟩ := hCommonSub1 hcIdx
        simp [envX, envFromSlots, envY, hIdx1, hcIdx, hMap1]
      · have hNotIn1 : a2[k]'hk ∉ a1 := fun hm => hIn1 (Array.contains_iff_mem.mpr hm)
        have hNone1 : a1.idxOf? (a2[k]'hk) = none := Array.idxOf?_eq_none_iff.mpr hNotIn1
        have hNoneC : common.idxOf? (a2[k]'hk) = none := Array.idxOf?_eq_none_iff.mpr fun hm => hNotIn1 ((hCommonMem _).mp hm).1
        simp [envX, envFromSlots, envY, hNone1, hNoneC]
    exact hL.symm.trans ((hEq envX).trans (hR.trans ((hEq envY).symm)))
  have h2 : ∀ env2, val id2 env2 = valNew (fun c => env2 (map2[c]?.getD 0)) := by
    intro env2
    let d : V := env2 (map2[0]?.getD 0)
    let envZ : Nat → V := envFromSlots a2 env2 d
    have hL : evalApplied val ⟨id2, a2⟩ envZ = val id2 env2 := by
      unfold evalApplied; apply hDep2; intro k hk
      simp [envZ, envFromSlots, hk, arrayNodup_idxOf hNd2 hk]
    have hR : evalApplied val ⟨id1, a1⟩ envZ = valNew (fun c => env2 (map2[c]?.getD 0)) := by
      unfold evalApplied valNew; apply hDep1; intro j hj
      simp only [Array.getElem?_eq_getElem hj, Option.getD_some]
      have hIn1 : a1[j]'hj ∈ a1 := Array.getElem_mem hj
      by_cases hIn2 : a2.contains (a1[j]'hj) = true
      · have hInC : common.contains (a1[j]'hj) = true :=
          (hCommonContains _).mpr ⟨Array.contains_iff_mem.mpr hIn1, hIn2⟩
        obtain ⟨c, _, hcIdx, _⟩ := idxOf?_some_of_contains hInC
        obtain ⟨_, _, idx, hIdx2, hMap2⟩ := hCommonSub2 hcIdx
        simp [envZ, envFromSlots, hIdx2, hcIdx, hMap2]
      · have hNotIn2 : a1[j]'hj ∉ a2 := fun hm => hIn2 (Array.contains_iff_mem.mpr hm)
        have hNone2 : a2.idxOf? (a1[j]'hj) = none := Array.idxOf?_eq_none_iff.mpr hNotIn2
        have hNoneC : common.idxOf? (a1[j]'hj) = none := Array.idxOf?_eq_none_iff.mpr fun hm => hNotIn2 ((hCommonMem _).mp hm).2
        simp [envZ, envFromSlots, d, hNone2, hNoneC]
    exact hL.symm.trans ((hEq envZ).symm.trans hR)
  refine ⟨?_, h1, h2⟩
  intro envC₁ envC₂ hAgree
  by_cases hPos : 0 < common.size
  · have h0 : envC₁ 0 = envC₂ 0 := hAgree 0 hPos
    unfold valNew; apply hDep1; intro j hj
    cases hc : common.idxOf? (a1[j]?.getD 0) with
    | none => exact h0
    | some c =>
      obtain ⟨hclt, _, _, _, _⟩ := hCommonSub1 hc
      exact hAgree c hclt
  · have hNone : ∀ x, common.idxOf? x = none := fun x => by
      cases hc : common.idxOf? x with
      | none => rfl
      | some c => obtain ⟨hclt, _, _, _, _⟩ := hCommonSub1 hc; omega
    have hDisj : ∀ x, a1.contains x = true → a2.contains x = false := fun x hx1 => by
      cases hx2 : a2.contains x with
      | false => rfl
      | true =>
        have hInC : x ∈ common := (hCommonMem x).mpr ⟨Array.contains_iff_mem.mp hx1, Array.contains_iff_mem.mp hx2⟩
        obtain ⟨c, hc, _⟩ := Array.mem_iff_getElem.mp hInC; omega
    let envBridge : Nat → V := fun x => if a1.contains x then envC₁ 0 else envC₂ 0
    have hb1 : evalApplied val ⟨id1, a1⟩ envBridge = valNew envC₁ := by
      unfold evalApplied valNew; apply hDep1; intro j hj
      have hin1 : a1[j]'hj ∈ a1 := Array.getElem_mem hj
      simp [envBridge, hj, hin1, hNone]
    have hb2 : evalApplied val ⟨id2, a2⟩ envBridge = evalApplied val ⟨id2, a2⟩ (fun _ => envC₂ 0) := by
      unfold evalApplied; apply hDep2; intro k hk
      have hc2 : a2.contains (a2[k]'hk) = true := Array.contains_iff_mem.mpr (Array.getElem_mem hk)
      have hnot1 : a2[k]'hk ∉ a1 := fun hm => by
        have := hDisj _ (Array.contains_iff_mem.mpr hm)
        rw [hc2] at this; cases this
      simp [envBridge, hk, hnot1]
    have hb3 : evalApplied val ⟨id1, a1⟩ (fun _ => envC₂ 0) = valNew envC₂ := by
      unfold evalApplied valNew; apply hDep1; intro j hj
      simp [hj, hNone]
    exact hb1.symm.trans ((hEq envBridge).trans (hb2.trans ((hEq (fun _ => envC₂ 0)).symm.trans hb3)))

private theorem pushShrunk_sound {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure)
    (hok : UFSound val cl) {id1 id2 : Nat} {map1 map2 : Array Nat} {arNew : Nat}
    {valNew : (Nat → V) → R}
    (hid1 : id1 < cl.arity.size) (hid2 : id2 < cl.arity.size)
    (hm1 : map1.size = arNew) (hm2 : map2.size = arNew)
    (hDepNew : DependsOnly arNew valNew)
    (hv1 : ∀ env, val id1 env = valNew (fun c => env (map1[c]?.getD 0)))
    (hv2 : ∀ env, val id2 env = valNew (fun c => env (map2[c]?.getD 0))) :
    let cl' := pushShrunk cl id1 id2 map1 map2 arNew
    cl.arity.size ≤ cl'.arity.size ∧
    ∃ val', (∀ i < cl.arity.size, val' i = val i) ∧ UFSound val' cl' := by
  let newId := cl.arity.size
  let idPerm := Array.range arNew
  let val' : Nat → (Nat → V) → R := fun i => if i = newId then valNew else val i
  have hValOld : ∀ i < cl.arity.size, val' i = val i := fun i hi => by
    simp [val', show i ≠ newId by omega]
  have hParSz : (pushShrunk cl id1 id2 map1 map2 arNew).parent.size = cl.arity.size + 1 := by
    unfold pushShrunk; dsimp only; split <;> simp [hok.1]
  have hArSz : (pushShrunk cl id1 id2 map1 map2 arNew).arity.size = cl.arity.size + 1 := by
    simp [pushShrunk]
  refine ⟨by simp [pushShrunk], val', hValOld, by rw [hParSz, hArSz], by simp [pushShrunk, hok.2.1], ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = newId
    · subst hi
      have hArNew : (pushShrunk cl id1 id2 map1 map2 arNew).arityOf newId = arNew := by
        simp [pushShrunk, Closure.arityOf, newId]
      rw [hArNew]; simp only [val', ↓reduceIte]; exact hDepNew
    · by_cases hlt : i < newId
      · have har : (pushShrunk cl id1 id2 map1 map2 arNew).arityOf i = cl.arityOf i := by
          simp [pushShrunk, Closure.arityOf, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
        rw [har, hValOld i hlt]; exact hok.2.2.1 i
      · have har : (pushShrunk cl id1 id2 map1 map2 arNew).arityOf i = cl.arityOf i := by
          unfold pushShrunk Closure.arityOf; dsimp only
          rw [Array.getElem?_eq_none (show (cl.arity.push arNew).size ≤ i by simp; omega),
            Array.getElem?_eq_none (show cl.arity.size ≤ i by omega)]
        rw [har]; simp [val', hi]; exact hok.2.2.1 i
  · intro i p hp
    unfold pushShrunk at hp ⊢; dsimp only at hp ⊢
    have hBase : ∀ (p0 : Applied Nat), (cl.parent.push ⟨newId, idPerm⟩)[i]? = some p0 →
        ∃ hp0 : p0.id < (cl.arity.push arNew).size, p0.slots.size = (cl.arity.push arNew)[p0.id]'hp0 ∧
          ∀ env, val' i env = val' p0.id (fun j => env (p0.slots[j]?.getD 0)) := by
      intro p0 hp0
      by_cases hinew : i = newId
      · subst hinew
        have hEqPush : (cl.parent.push ⟨newId, idPerm⟩)[newId]? = some ⟨newId, idPerm⟩ :=
          (congrArg (fun k => (cl.parent.push ⟨newId, idPerm⟩)[k]?) hok.1.symm).trans Array.getElem?_push_size
        rw [hEqPush] at hp0
        injection hp0 with hpEq; subst hpEq
        refine ⟨by simp [newId], by simp [idPerm, newId], fun env => ?_⟩
        simp only [val', ↓reduceIte]
        apply hDepNew; intro j hj; simp [idPerm, hj]
      · by_cases hlt : i < cl.parent.size
        · rw [Array.getElem?_push_lt hlt] at hp0
          have hp' : cl.parent[i]? = some p0 := by rw [Array.getElem?_eq_getElem hlt]; exact hp0
          obtain ⟨hpId, hpSz, hpVal⟩ := hok.2.2.2.1 i p0 hp'
          have hilt : i < cl.arity.size := by rw [← hok.1]; exact hlt
          refine ⟨by simp; omega, by simp [Array.getElem_push_lt hpId, hpSz], fun env => ?_⟩
          rw [hValOld i hilt, hValOld p0.id hpId]; exact hpVal env
        · have hge : (cl.parent.push ⟨newId, idPerm⟩).size ≤ i := by
            have := hok.1; simp only [Array.size_push]; omega
          rw [Array.getElem?_eq_none hge] at hp0; cases hp0
    have hSet1 : ∀ (p0 : Applied Nat), ((cl.parent.push ⟨newId, idPerm⟩).setIfInBounds id1 ⟨newId, map1⟩)[i]? = some p0 →
        ∃ hp0 : p0.id < (cl.arity.push arNew).size, p0.slots.size = (cl.arity.push arNew)[p0.id]'hp0 ∧
          ∀ env, val' i env = val' p0.id (fun j => env (p0.slots[j]?.getD 0)) := by
      intro p0 hp0
      by_cases hi1 : i = id1
      · subst i
        have hlt : id1 < (cl.parent.push ⟨newId, idPerm⟩).size := by simp [hok.1]; omega
        rw [Array.getElem?_setIfInBounds_self, ite_eq_left hlt] at hp0
        injection hp0 with hpEq; subst hpEq
        refine ⟨by simp [newId], by simp [hm1, newId], fun env => ?_⟩
        rw [hValOld id1 hid1]; simpa [val', newId] using hv1 env
      · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hi1)] at hp0
        exact hBase p0 hp0
    by_cases heq12 : (id1 == id2) = true
    · simp only [heq12, ↓reduceIte] at hp; exact hSet1 p hp
    · simp only [heq12, Bool.false_eq_true, ↓reduceIte] at hp
      by_cases hi2 : i = id2
      · subst i
        have hlt : id2 < ((cl.parent.push ⟨newId, idPerm⟩).setIfInBounds id1 ⟨newId, map1⟩).size := by
          simp [hok.1]; omega
        rw [Array.getElem?_setIfInBounds_self, ite_eq_left hlt] at hp
        injection hp with hpEq; subst hpEq
        refine ⟨by simp [newId], by simp [hm2, newId], fun env => ?_⟩
        rw [hValOld id2 hid2]; simpa [val', newId] using hv2 env
      · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hi2)] at hp
        exact hSet1 p hp
  · intro i ρ hρ
    unfold pushShrunk at hρ ⊢; dsimp only at hρ ⊢
    by_cases hinew : i = newId
    · subst hinew
      have hEqPush : (cl.perms.push #[idPerm])[newId]? = some #[idPerm] := by
        have : newId = cl.perms.size := hok.2.1.symm
        conv => lhs; rw [this]
        exact Array.getElem?_push_size
      rw [hEqPush] at hρ
      simp only [Option.getD_some, Array.mem_singleton] at hρ
      subst hρ
      refine ⟨by simp [idPerm, Closure.arityOf, newId], fun env => ?_⟩
      simp only [val', ↓reduceIte]
      apply hDepNew; intro j hj; simp [idPerm, hj]
    · by_cases hlt : i < cl.perms.size
      · rw [Array.getElem?_push_lt hlt] at hρ
        have hilt : i < cl.arity.size := by rw [← hok.2.1]; exact hlt
        have hρ' : ρ ∈ cl.perms[i]?.getD #[] := by simpa [Array.getElem?_eq_getElem hlt] using hρ
        obtain ⟨hszρ, hvρ⟩ := hok.2.2.2.2 i ρ hρ'
        refine ⟨by simpa [Closure.arityOf, Array.getElem?_push_lt hilt, Array.getElem?_eq_getElem hilt] using hszρ,
          fun env => ?_⟩
        rw [hValOld i hilt]; exact hvρ env
      · have hge : (cl.perms.push #[idPerm]).size ≤ i := by
          have := hok.2.1; simp only [Array.size_push]; omega
        rw [Array.getElem?_eq_none hge] at hρ
        simp at hρ

private theorem walkUF_sound_any {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure)
    (hok : UFSound val cl) :
    ∀ (fuel : Nat) (a : Applied Nat),
      (walkUF cl.parent fuel a).id < cl.arity.size →
      (walkUF cl.parent fuel a).slots.size = cl.arity[(walkUF cl.parent fuel a).id]?.getD 0 →
      ∀ env, evalApplied val (walkUF cl.parent fuel a) env = evalApplied val a env := by
  intro fuel
  induction fuel with
  | zero => intro a _ _ _; rfl
  | succ n ih =>
    intro a hrid hrsz env
    rw [walkUF] at hrid hrsz ⊢
    cases hp : cl.parent[a.id]? with
    | none => simp [hp]
    | some p =>
      simp only [hp] at hrid hrsz ⊢
      by_cases hself : (p.id == a.id) = true
      · simp [hself]
      · simp only [hself, Bool.false_eq_true, ↓reduceIte] at hrid hrsz ⊢
        obtain ⟨hpId, hpSz, hpVal⟩ := hok.2.2.2.1 a.id p hp
        have hStep := ih ⟨p.id, p.slots.map fun j => a.slots[j]?.getD 0⟩ hrid hrsz env
        refine hStep.trans ?_
        unfold evalApplied
        rw [hpVal]
        have hdep := hok.2.2.1 p.id
        simp only [Closure.arityOf, Array.getElem?_eq_getElem hpId, Option.getD_some] at hdep
        apply hdep
        intro j hj
        have hjp : j < p.slots.size := by rw [hpSz]; exact hj
        simp [hjp]

private theorem unionStep_sound {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure)
    (ch : Bool) (eqn : Equation) (hok : UFSound val cl)
    (he : ∀ env, evalApplied val eqn.1 env = evalApplied val eqn.2 env) :
    let cl' := (unionStep (cl, ch) eqn).1
    cl.arity.size ≤ cl'.arity.size ∧
    ∃ val', (∀ i < cl.arity.size, val' i = val i) ∧ UFSound val' cl' := by
  unfold unionStep
  dsimp only
  have keep : cl.arity.size ≤ cl.arity.size ∧ ∃ val', (∀ i < cl.arity.size, val' i = val i) ∧ UFSound val' cl :=
    ⟨Nat.le_refl _, val, fun _ _ => rfl, hok⟩
  by_cases hIn : (decide ((cl.find eqn.1).id < cl.arity.size) && decide ((cl.find eqn.2).id < cl.arity.size)) = true
  · rw [ite_eq_right (by simp [hIn])]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hIn
    obtain ⟨hr1, hr2⟩ := hIn
    by_cases hOk : (((cl.find eqn.1).slots.size == cl.arity[(cl.find eqn.1).id]?.getD 0) &&
        ((cl.find eqn.2).slots.size == cl.arity[(cl.find eqn.2).id]?.getD 0) &&
        arrayNodup (cl.find eqn.1).slots && arrayNodup (cl.find eqn.2).slots) = true
    · rw [ite_eq_right (by simp [hOk])]
      simp only [Bool.and_eq_true, beq_iff_eq] at hOk
      obtain ⟨⟨⟨hsz1, hsz2⟩, hnd1⟩, hnd2⟩ := hOk
      have hDep1 : DependsOnly (cl.find eqn.1).slots.size (val (cl.find eqn.1).id) := by
        rw [hsz1]; exact hok.2.2.1 (cl.find eqn.1).id
      have hDep2 : DependsOnly (cl.find eqn.2).slots.size (val (cl.find eqn.2).id) := by
        rw [hsz2]; exact hok.2.2.1 (cl.find eqn.2).id
      have hEqR : ∀ env, evalApplied val (cl.find eqn.1) env = evalApplied val (cl.find eqn.2) env := fun env =>
        (walkUF_sound_any val cl hok cl.parent.size eqn.1 hr1 hsz1 env).trans
          ((he env).trans (walkUF_sound_any val cl hok cl.parent.size eqn.2 hr2 hsz2 env).symm)
      by_cases hSameId : ((cl.find eqn.1).id == (cl.find eqn.2).id) = true
      · rw [ite_eq_left hSameId]
        have hIdEq : (cl.find eqn.1).id = (cl.find eqn.2).id := beq_iff_eq.mp hSameId
        by_cases hSameSlots : ((cl.find eqn.1).slots == (cl.find eqn.2).slots) = true
        · rw [ite_eq_left hSameSlots]; exact keep
        · rw [ite_eq_right hSameSlots]
          by_cases hSub : isSubsetSlots (cl.find eqn.2).slots (cl.find eqn.1).slots = true
          · rw [ite_eq_left hSub]
            let π := projectIndices (cl.find eqn.1).slots (cl.find eqn.2).slots
            have hπVal : ∀ env, val (cl.find eqn.1).id env = val (cl.find eqn.1).id (fun j => env (π[j]?.getD 0)) := by
              have h := eval_of_subset val hDep1 hDep2 hnd1 hSub hEqR
              simpa [← hIdEq] using h
            have hπSz : π.size = cl.arityOf (cl.find eqn.1).id := by
              simp [π, projectIndices, hsz2, ← hIdEq, Closure.arityOf]
            have hPermOk := addPerm_sound (hok.2.2.1 (cl.find eqn.1).id) (hok.2.2.2.2 (cl.find eqn.1).id) ⟨hπSz, hπVal⟩
            split
            · refine ⟨Nat.le_refl _, val, fun _ _ => rfl, hok.1, by simp [hok.2.1], hok.2.2.1, hok.2.2.2.1, ?_⟩
              intro i ρ hρ
              by_cases hi : i = (cl.find eqn.1).id
              · subst hi
                have hlt : (cl.find eqn.1).id < cl.perms.size := by rw [hok.2.1]; exact hr1
                rw [Array.getElem?_setIfInBounds_self, ite_eq_left hlt] at hρ
                exact hPermOk ρ hρ
              · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hi)] at hρ
                exact hok.2.2.2.2 i ρ hρ
            · exact keep
          · rw [ite_eq_right hSub]
            have hInt := intersection_sound val hDep1 hDep2 hnd1 hnd2 hEqR
            exact pushShrunk_sound val cl hok hr1 hr1 (by simp [projectIndices]) (by simp [projectIndices])
              hInt.1 hInt.2.1 hInt.2.1
      · rw [ite_eq_right hSameId]
        by_cases hSub2 : (isSubsetSlots (cl.find eqn.2).slots (cl.find eqn.1).slots &&
            (decide ((cl.find eqn.2).slots.size < (cl.find eqn.1).slots.size) ||
              ((cl.find eqn.2).slots.size == (cl.find eqn.1).slots.size && decide ((cl.find eqn.2).id < (cl.find eqn.1).id)))) = true
        · rw [ite_eq_left hSub2]
          have hSub : isSubsetSlots (cl.find eqn.2).slots (cl.find eqn.1).slots = true := (Bool.and_eq_true_iff.mp hSub2).1
          have hMapVal := eval_of_subset val hDep1 hDep2 hnd1 hSub hEqR
          have hsz2' : (cl.find eqn.2).slots.size = cl.arity[(cl.find eqn.2).id]'hr2 := by simpa [hr2] using hsz2
          refine ⟨Nat.le_refl _, val, fun _ _ => rfl, by simp [hok.1], hok.2.1, hok.2.2.1, ?_, hok.2.2.2.2⟩
          intro i p hp
          by_cases hi : i = (cl.find eqn.1).id
          · subst hi
            have hlt : (cl.find eqn.1).id < cl.parent.size := by rw [hok.1]; exact hr1
            rw [Array.getElem?_setIfInBounds_self, ite_eq_left hlt] at hp
            injection hp with hpEq; subst hpEq
            exact ⟨hr2, by simp [projectIndices, hsz2'], hMapVal⟩
          · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hi)] at hp
            exact hok.2.2.2.1 i p hp
        · rw [ite_eq_right hSub2]
          by_cases hSub1 : isSubsetSlots (cl.find eqn.1).slots (cl.find eqn.2).slots = true
          · rw [ite_eq_left hSub1]
            have hMapVal := eval_of_subset val hDep2 hDep1 hnd2 hSub1 (fun env => (hEqR env).symm)
            have hsz1' : (cl.find eqn.1).slots.size = cl.arity[(cl.find eqn.1).id]'hr1 := by simpa [hr1] using hsz1
            refine ⟨Nat.le_refl _, val, fun _ _ => rfl, by simp [hok.1], hok.2.1, hok.2.2.1, ?_, hok.2.2.2.2⟩
            intro i p hp
            by_cases hi : i = (cl.find eqn.2).id
            · subst hi
              have hlt : (cl.find eqn.2).id < cl.parent.size := by rw [hok.1]; exact hr2
              rw [Array.getElem?_setIfInBounds_self, ite_eq_left hlt] at hp
              injection hp with hpEq; subst hpEq
              exact ⟨hr1, by simp [projectIndices, hsz1'], hMapVal⟩
            · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hi)] at hp
              exact hok.2.2.2.1 i p hp
          · rw [ite_eq_right hSub1]
            have hInt := intersection_sound val hDep1 hDep2 hnd1 hnd2 hEqR
            exact pushShrunk_sound val cl hok hr1 hr2 (by simp [projectIndices]) (by simp [projectIndices])
              hInt.1 hInt.2.1 hInt.2.2
    · rw [ite_eq_left (by simp [hOk])]; exact keep
  · rw [ite_eq_left (by simp [hIn])]; exact keep

private theorem unionClasses_sound {V R : Type} (val : Nat → (Nat → V) → R) (cl : Closure)
    (eqs : Array Equation) (hok : UFSound val cl)
    (he : ∀ eq ∈ eqs, eq.1.id < cl.arity.size ∧ eq.2.id < cl.arity.size ∧
      ∀ env, evalApplied val eq.1 env = evalApplied val eq.2 env) :
    let cl' := (unionClasses cl eqs).1
    cl.arity.size ≤ cl'.arity.size ∧
    ∃ val', (∀ i < cl.arity.size, val' i = val i) ∧ UFSound val' cl' := by
  let inv := fun (_ : Nat) (s : Closure × Bool) =>
    cl.arity.size ≤ s.1.arity.size ∧
    ∃ val', (∀ i < cl.arity.size, val' i = val i) ∧ UFSound val' s.1
  apply Array.foldl_induction (motive := inv) ⟨Nat.le_refl _, val, fun _ _ => rfl, hok⟩
  intro idx s ⟨hle, valCur, hAgree, hSound⟩
  obtain ⟨h1, h2, heq⟩ := he eqs[idx] (Array.getElem_mem _)
  have heq' : ∀ env, evalApplied valCur eqs[idx].1 env = evalApplied valCur eqs[idx].2 env := by
    intro env; simp only [evalApplied, hAgree _ h1, hAgree _ h2]; exact heq env
  obtain ⟨hle2, valNext, hAgree2, hSound2⟩ := unionStep_sound valCur s.1 s.2 eqs[idx] hSound heq'
  exact ⟨Nat.le_trans hle hle2, valNext,
    fun i hi => (hAgree2 i (Nat.lt_of_lt_of_le hi hle)).trans (hAgree i hi), hSound2⟩

private theorem initClosure_sound {V R : Type} (g : Graph) (val : Nat → (Nat → V) → R)
    (hDep : ∀ i, DependsOnly ((g.initClosure).arityOf i) (val i)) :
    UFSound val g.initClosure := by
  refine ⟨by simp [Graph.initClosure], by simp [Graph.initClosure], hDep, ?_, ?_⟩
  · intro i p hp
    simp only [Graph.initClosure, Array.getElem?_map, Array.getElem?_range] at hp
    by_cases hi : i < g.nodes.size
    · simp only [hi, ↓reduceIte, Option.map_some, Option.some.injEq] at hp
      subst hp
      refine ⟨by simp [Graph.initClosure, hi], by simp [Graph.initClosure, hi], fun env => ?_⟩
      have hd := hDep i
      simp only [Closure.arityOf, Graph.initClosure, Array.getElem?_map, Array.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some] at hd
      apply hd; intro j hj; simp [hi, hj]
    · simp [hi] at hp
  · intro i π hπ
    simp only [Graph.initClosure, Array.getElem?_map] at hπ
    by_cases hi : i < g.nodes.size
    · simp only [Array.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, Array.mem_singleton] at hπ
      subst hπ
      refine ⟨by simp [Closure.arityOf, Graph.initClosure, hi], fun env => ?_⟩
      have hd := hDep i
      simp only [Closure.arityOf, Graph.initClosure, Array.getElem?_map, Array.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some] at hd
      apply hd; intro j hj; simp [hj]
    · have hge : g.nodes.size ≤ i := Nat.le_of_not_lt hi
      rw [Array.getElem?_eq_none hge] at hπ; simp at hπ

private theorem slottedRebuild_bounds (arityOf : Nat → Nat) (rep : Nat → Applied Nat)
    (perms : Nat → Array (Array Nat)) (entries : Array (Nat × Node)) (bound : Nat)
    (hb : ∀ e ∈ entries, e.1 < bound) :
    ∀ eq ∈ slottedRebuild arityOf rep perms entries, eq.1.id < bound ∧ eq.2.id < bound := by
  let inv := fun (_ : Nat) (s : Work) =>
    (∀ (key : Node) (owner : Nat) (used : Array Nat), s.1[key]? = some (owner, used) → owner < bound) ∧
    (∀ eq ∈ s.2, eq.1.id < bound ∧ eq.2.id < bound)
  have h : inv entries.size (entries.foldl (rebuildStep arityOf rep perms) ({}, #[])) := by
    apply Array.foldl_induction (motive := inv) ⟨fun _ _ _ h => by simp at h, fun _ h => by simp at h⟩
    intro idx s ⟨hSeen, hEqs⟩
    have hItem : entries[idx].1 < bound := hb entries[idx] (Array.getElem_mem _)
    unfold rebuildStep; dsimp only
    by_cases hBnd : usedInBounds (arityOf entries[idx].1) (rebuildNode rep perms entries[idx].2).2 = true
    · simp only [hBnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hEqs1 : ∀ eq ∈ (if (rebuildNode rep perms entries[idx].2).2.size < arityOf entries[idx].1 then
            s.2.push (appFromUsed entries[idx].1 (arityOf entries[idx].1) (rebuildNode rep perms entries[idx].2).2
              (rebuildNode rep perms entries[idx].2).1.arity,
              appFromUsed entries[idx].1 (arityOf entries[idx].1) (rebuildNode rep perms entries[idx].2).2
              ((rebuildNode rep perms entries[idx].2).1.arity + arityOf entries[idx].1))
          else s.2), eq.1.id < bound ∧ eq.2.id < bound := by
        intro eq hMem
        by_cases hlt : (rebuildNode rep perms entries[idx].2).2.size < arityOf entries[idx].1
        · simp only [hlt, ↓reduceIte, Array.mem_push] at hMem
          rcases hMem with ho | rfl; exact hEqs eq ho; exact ⟨hItem, hItem⟩
        · simp only [hlt, ↓reduceIte] at hMem; exact hEqs eq hMem
      cases hLook : s.1[(rebuildNode rep perms entries[idx].2).1]? with
      | none =>
        refine ⟨fun key owner used hl => ?_, hEqs1⟩
        by_cases hk : (rebuildNode rep perms entries[idx].2).1 = key
        · subst hk; simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, _⟩ := hl; exact hItem
        · rw [Std.HashMap.getElem?_insert, beq_false_of_ne hk] at hl; exact hSeen key owner used hl
      | some earlierPair =>
        obtain ⟨earlier, earlierUsed⟩ := earlierPair
        have hEarlier : earlier < bound := hSeen _ earlier earlierUsed hLook
        by_cases hBndE : usedInBounds (arityOf earlier) earlierUsed = true
        · simp only [hBndE, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          refine ⟨hSeen, fun eq hMem => ?_⟩
          rcases Array.mem_push.mp hMem with ho | rfl; exact hEqs1 eq ho; exact ⟨hItem, hEarlier⟩
        · simp only [hBndE, Bool.not_false, ↓reduceIte]; exact ⟨hSeen, hEqs1⟩
    · simp only [hBnd, Bool.not_false, ↓reduceIte]; exact ⟨hSeen, hEqs⟩
  exact h.2

private theorem unionStep_arity_extends (s : Closure × Bool) (eq : Equation) :
    ArrayExtends s.1.arity (unionStep s eq).1.arity := by
  unfold unionStep; dsimp only
  repeat (first
    | exact ArrayExtends.refl _
    | exact ArrayExtends.push _ _
    | (unfold pushShrunk; exact ArrayExtends.push _ _)
    | split)

private theorem unionClasses_arity_extends (cl : Closure) (qs : Array Equation) :
    ArrayExtends cl.arity (unionClasses cl qs).1.arity := by
  apply Array.foldl_induction (motive := fun _ (s : Closure × Bool) => ArrayExtends cl.arity s.1.arity)
    (ArrayExtends.refl _)
  intro idx s hs
  exact hs.trans (unionStep_arity_extends s qs[idx])

private theorem closeLoop_arity_extends (entries : Array (Nat × Node)) :
    ∀ (fuel : Nat) (cl : Closure), ArrayExtends cl.arity (closeLoop entries fuel cl).arity
  | 0, _ => ArrayExtends.refl _
  | fuel + 1, cl => by
    rw [closeLoop]; dsimp only
    let qs := slottedRebuild cl.arityOf cl.repOf (fun i => cl.perms[i]?.getD #[]) entries
    have h1 := unionClasses_arity_extends cl qs
    split
    · exact h1.trans (closeLoop_arity_extends entries fuel _)
    · exact ArrayExtends.refl _

/-- All rounds of slotted congruence closure, redundant-slot shrinking, and symmetry normalization
preserve every sound interpretation that validates the supplied equations. -/
theorem Graph.close_sound {V R : Type} (g : Graph) (eqs : Array Equation) (alg : Algebra V R)
    (val : Nat → (Nat → V) → R)
    (hDep : ∀ i, DependsOnly (g.initClosure.arityOf i) (val i))
    (hEqBounds : ∀ eq ∈ eqs, eq.1.id < g.nodes.size ∧ eq.2.id < g.nodes.size)
    (he : ∀ eq ∈ eqs, ∀ env, evalApplied val eq.1 env = evalApplied val eq.2 env)
    (hChildBounds : ∀ e ∈ (Array.range g.nodes.size).zip g.nodes, ∀ c ∈ e.2.children, c.id < g.nodes.size)
    (hc : ∀ e ∈ (Array.range g.nodes.size).zip g.nodes, val e.1 = meaning alg val e.2)
    {a b : Applied Nat}
    (ha : a.id < g.nodes.size) (hasz : a.slots.size = (g.nodes[a.id]'ha).arity)
    (hb : b.id < g.nodes.size) (hbsz : b.slots.size = (g.nodes[b.id]'hb).arity)
    (hequiv : (g.close eqs).equiv a b = true) (env : Nat → V) :
    evalApplied val a env = evalApplied val b env := by
  let entries := (Array.range g.nodes.size).zip g.nodes
  have hInit := initClosure_sound g val hDep
  have hInitSz : g.initClosure.arity.size = g.nodes.size := by simp [Graph.initClosure]
  have hEqs' : ∀ eq ∈ eqs, eq.1.id < g.initClosure.arity.size ∧ eq.2.id < g.initClosure.arity.size ∧
      ∀ env, evalApplied val eq.1 env = evalApplied val eq.2 env := fun eq hmem =>
    ⟨hInitSz ▸ (hEqBounds eq hmem).1, hInitSz ▸ (hEqBounds eq hmem).2, he eq hmem⟩
  obtain ⟨hle0, val0, hAg0, hOk0⟩ := unionClasses_sound val g.initClosure eqs hInit hEqs'
  have hEntBnd : ∀ e ∈ entries, e.1 < g.nodes.size := by
    intro e hmem
    obtain ⟨idx, hidx, rfl⟩ := Array.mem_iff_getElem.mp hmem
    simp [entries] at hidx ⊢; omega
  have hLoop : ∀ (fuel : Nat) (cl : Closure) (valC : Nat → (Nat → V) → R),
      g.nodes.size ≤ cl.arity.size →
      (∀ i < g.nodes.size, valC i = val i) →
      UFSound valC cl →
      g.nodes.size ≤ (closeLoop entries fuel cl).arity.size ∧
      ∃ valF, (∀ i < g.nodes.size, valF i = val i) ∧ UFSound valF (closeLoop entries fuel cl) := by
    intro fuel
    induction fuel with
    | zero => intro cl valC hle hAg hOk; exact ⟨hle, valC, hAg, hOk⟩
    | succ n ih =>
      intro cl valC hle hAg hOk
      rw [closeLoop]; dsimp only
      have hc' : ∀ e ∈ entries, valC e.1 = meaning alg valC e.2 := by
        intro e hmem
        have he1 : e.1 < g.nodes.size := hEntBnd e hmem
        rw [hAg e.1 he1, hc e hmem]
        by_cases hvar : e.2.op = .var
        · cases hn : e.2 with | mk ar op ch => simp only [hn] at hvar; subst hvar; rfl
        · funext env'
          rw [meaning_nonvar alg val e.2 hvar, meaning_nonvar alg valC e.2 hvar]
          congr 1; apply Array.ext (by simp)
          intro k hk1 hk2; have hk : k < e.2.children.size := by simpa using hk1
          simp only [Array.getElem_map]; funext fresh
          rw [hAg _ (hChildBounds e hmem (e.2.children[k]'hk) (Array.getElem_mem hk))]
      have hFoundEq := slottedRebuild_sound alg cl.arityOf valC cl.repOf
        (fun i => cl.perms[i]?.getD #[]) hOk.2.2.1
        (closure_repOf_sound valC cl hOk) hOk.2.2.2.2 entries hc'
      have hFoundBnd := slottedRebuild_bounds cl.arityOf cl.repOf
        (fun i => cl.perms[i]?.getD #[]) entries g.nodes.size hEntBnd
      have hFoundAll : ∀ eq ∈ slottedRebuild cl.arityOf cl.repOf (fun i => cl.perms[i]?.getD #[]) entries,
          eq.1.id < cl.arity.size ∧ eq.2.id < cl.arity.size ∧
          ∀ env, evalApplied valC eq.1 env = evalApplied valC eq.2 env := fun eq hmem =>
        ⟨Nat.lt_of_lt_of_le (hFoundBnd eq hmem).1 hle,
         Nat.lt_of_lt_of_le (hFoundBnd eq hmem).2 hle, hFoundEq eq hmem⟩
      obtain ⟨hle1, val1, hAg1, hOk1⟩ := unionClasses_sound valC cl _ hOk hFoundAll
      split
      · exact ih _ val1 (Nat.le_trans hle hle1)
          (fun i hi => (hAg1 i (Nat.lt_of_lt_of_le hi hle)).trans (hAg i hi)) hOk1
      · exact ⟨hle, valC, hAg, hOk⟩
  obtain ⟨hleF, valF, hAgF, hOkF⟩ := hLoop (g.nodes.size * 4 + 8)
    (unionClasses g.initClosure eqs).1 val0 (hInitSz ▸ hle0) (fun i hi => hAg0 i (hInitSz ▸ hi)) hOk0
  have hArExt : ArrayExtends g.initClosure.arity (g.close eqs).arity :=
    (unionClasses_arity_extends g.initClosure eqs).trans (closeLoop_arity_extends entries _ _)
  have hArFinal : ∀ i (hi : i < g.nodes.size),
      (g.close eqs).arity[i]'(Nat.lt_of_lt_of_le hi hleF) = (g.nodes[i]'hi).arity := by
    intro i hi
    have hget : (g.close eqs).arity[i]? = g.initClosure.arity[i]? := hArExt.2 i (hInitSz ▸ hi)
    have hget' : (g.close eqs).arity[i]? = some ((g.close eqs).arity[i]'(Nat.lt_of_lt_of_le hi hleF)) :=
      Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi hleF)
    have hinitGet : g.initClosure.arity[i]? = some (g.nodes[i]'hi).arity := by
      simp [Graph.initClosure, Array.getElem?_eq_getElem hi]
    exact Option.some.inj (hget'.symm.trans (hget.trans hinitGet))
  have haAr : a.slots.size = (g.close eqs).arity[a.id]'(Nat.lt_of_lt_of_le ha hleF) :=
    hasz.trans (hArFinal a.id ha).symm
  have hbAr : b.slots.size = (g.close eqs).arity[b.id]'(Nat.lt_of_lt_of_le hb hleF) :=
    hbsz.trans (hArFinal b.id hb).symm
  have hCanEq : (g.close eqs).canonApplied a = (g.close eqs).canonApplied b := beq_iff_eq.mp hequiv
  have haVal := closure_canonApplied_sound valF (g.close eqs) hOkF a (Nat.lt_of_lt_of_le ha hleF) haAr env
  have hbVal := closure_canonApplied_sound valF (g.close eqs) hOkF b (Nat.lt_of_lt_of_le hb hleF) hbAr env
  have hF : evalApplied valF a env = evalApplied valF b env := by rw [← haVal, ← hbVal, hCanEq]
  simpa only [evalApplied, hAgF a.id ha, hAgF b.id hb] using hF

/-! ## `Obend.Core.Term` Soundness of `insertCore` and End-to-End Core Congruence Closure -/

mutual
def evalShape {V R : Type} (alg : Algebra V R) :
    TermTraverse.Shape → (Nat → V) → R
  | .var i, env => alg.variableValue (env i)
  | .bind body, env => alg.apply .bind #[fun fresh =>
      evalShape alg body (fun i => match i with | 0 => fresh | j + 1 => env j)]
  | .node tag cs, env => alg.apply (.node tag) (evalShapes alg cs env).toArray
termination_by structural s => s

def evalShapes {V R : Type} (alg : Algebra V R) :
    List TermTraverse.Shape → (Nat → V) → List (V → R)
  | [], _ => []
  | c :: cs, env => (fun _ => evalShape alg c env) :: evalShapes alg cs env
termination_by structural cs => cs
end

def evalCore {V R : Type} (alg : Algebra V R) (t : Term) (env : Nat → V) : R :=
  evalShape alg (TermTraverse.encode t) env

def GraphWF (g : Graph) : Prop :=
  (∀ i (hi : i < g.nodes.size), (g.nodes[i]'hi).op = .var → (g.nodes[i]'hi).arity = 1) ∧
  (∀ i (hi : i < g.nodes.size), ∀ c ∈ (g.nodes[i]'hi).children,
    c.id < i ∧ ∀ s ∈ c.slots, ∀ k, s = some k → k < (g.nodes[i]'hi).arity) ∧
  (∀ (n : Node) (j : Nat), g.index[n]? = some j → g.nodes[j]? = some n)

theorem graphWF_empty : GraphWF {} :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ h => by simp at h⟩

private def evalNodesAt {V R : Type} (alg : Algebra V R) (nodes : Array Node) :
    Nat → Nat → (Nat → V) → R
  | 0, _, _ => alg.apply .var #[]
  | fuel + 1, id, env =>
    match nodes[id]? with
    | none => alg.apply .var #[]
    | some n => meaning alg (evalNodesAt alg nodes fuel) n env

def graphVal {V R : Type} (alg : Algebra V R) (g : Graph) (id : Nat) (env : Nat → V) : R :=
  evalNodesAt alg g.nodes (id + 1) id env

private theorem evalNodesAt_fuel_indep {V R : Type} (alg : Algebra V R) (nodes : Array Node)
    (hDag : ∀ i (hi : i < nodes.size), ∀ c ∈ (nodes[i]'hi).children, c.id < i) :
    ∀ (id f1 f2 : Nat), id < f1 → id < f2 →
      evalNodesAt alg nodes f1 id = evalNodesAt alg nodes f2 id := by
  intro id
  induction id using Nat.strongRecOn with
  | ind id ih =>
    intro f1 f2 hf1 hf2
    cases f1 with
    | zero => omega
    | succ k1 =>
      cases f2 with
      | zero => omega
      | succ k2 =>
        funext env
        simp only [evalNodesAt]
        cases hn : nodes[id]? with
        | none => rfl
        | some n =>
          simp only [hn]
          have hi : id < nodes.size := by
            by_cases h : id < nodes.size; · exact h
            · rw [Array.getElem?_eq_none (by omega)] at hn; cases hn
          have hneq : nodes[id]'hi = n := Option.some.inj ((Array.getElem?_eq_getElem hi).symm.trans hn)
          by_cases hvar : n.op = .var
          · cases n with | mk _ op _ => simp only at hvar; subst hvar; rfl
          · rw [meaning_nonvar alg _ n hvar, meaning_nonvar alg _ n hvar]
            congr 1; apply Array.ext (by simp)
            intro j hj1 hj2; have hj : j < n.children.size := by simpa using hj1
            simp only [Array.getElem_map]; funext fresh
            have hcLt : (n.children[j]'hj).id < id := hDag id hi (n.children[j]'hj) (hneq ▸ Array.getElem_mem hj)
            rw [ih _ hcLt k1 k2 (by omega) (by omega)]

theorem graphVal_consistent {V R : Type} (alg : Algebra V R) (g : Graph) (hwf : GraphWF g)
    {i : Nat} (hi : i < g.nodes.size) :
    graphVal alg g i = meaning alg (graphVal alg g) (g.nodes[i]'hi) := by
  funext env
  simp only [graphVal, evalNodesAt, Array.getElem?_eq_getElem hi]
  by_cases hvar : (g.nodes[i]'hi).op = .var
  · cases hn : g.nodes[i]'hi with | mk _ op _ => simp only [hn] at hvar; subst hvar; rfl
  · rw [meaning_nonvar alg _ _ hvar, meaning_nonvar alg _ _ hvar]
    congr 1; apply Array.ext (by simp)
    intro j hj1 hj2; have hj : j < (g.nodes[i]'hi).children.size := by simpa using hj1
    simp only [Array.getElem_map]; funext fresh
    have hcLt : ((g.nodes[i]'hi).children[j]'hj).id < i := (hwf.2.1 i hi _ (Array.getElem_mem hj)).1
    have hEq := evalNodesAt_fuel_indep alg g.nodes (fun m hm c hc => (hwf.2.1 m hm c hc).1)
      ((g.nodes[i]'hi).children[j]'hj).id i (((g.nodes[i]'hi).children[j]'hj).id + 1) hcLt (Nat.lt_succ_self _)
    exact congrFun hEq _

theorem graphVal_dependsOnly {V R : Type} (alg : Algebra V R) (g : Graph) (hwf : GraphWF g) (i : Nat) :
    DependsOnly (g.initClosure.arityOf i) (graphVal alg g i) := by
  by_cases hi : i < g.nodes.size
  · have har : g.initClosure.arityOf i = (g.nodes[i]'hi).arity := by
      simp [Closure.arityOf, Graph.initClosure, Array.getElem?_eq_getElem hi]
    rw [har, graphVal_consistent alg g hwf hi]
    intro env₁ env₂ hAgree
    by_cases hvar : (g.nodes[i]'hi).op = .var
    · have h1 := hwf.1 i hi hvar
      cases hn : g.nodes[i]'hi with | mk ar op ch =>
        simp only [hn] at hvar h1 hAgree; subst hvar
        exact congrArg alg.variableValue (hAgree 0 (by omega))
    · rw [meaning_nonvar alg _ _ hvar, meaning_nonvar alg _ _ hvar]
      congr 1; apply Array.ext (by simp)
      intro j hj1 hj2; have hj : j < (g.nodes[i]'hi).children.size := by simpa using hj1
      simp only [Array.getElem_map]; funext fresh; congr 1; funext k
      have hSlots := (hwf.2.1 i hi ((g.nodes[i]'hi).children[j]'hj) (Array.getElem_mem hj)).2
      by_cases hk : k < ((g.nodes[i]'hi).children[j]'hj).slots.size
      · rw [Array.getElem?_eq_getElem hk]; simp only [Option.join]
        cases hs : ((g.nodes[i]'hi).children[j]'hj).slots[k]'hk with
        | none => rfl
        | some s => exact hAgree s (hSlots (some s) (hs ▸ Array.getElem_mem hk) s rfl)
      · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hk)]; rfl
  · intro env₁ env₂ _
    simp [graphVal, evalNodesAt, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]

def GraphExtends (g g' : Graph) : Prop :=
  g.nodes.size ≤ g'.nodes.size ∧ ∀ (i : Nat), i < g.nodes.size → g'.nodes[i]? = g.nodes[i]?

private theorem GraphExtends.refl (g : Graph) : GraphExtends g g := ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem GraphExtends.trans {a b c : Graph} (h1 : GraphExtends a b) (h2 : GraphExtends b c) :
    GraphExtends a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun i hi => (h2.2 i (Nat.lt_of_lt_of_le hi h1.1)).trans (h1.2 i hi)⟩

private theorem GraphExtends.getElem_eq {g g' : Graph} (he : GraphExtends g g') {i : Nat}
    (hi : i < g.nodes.size) : g'.nodes[i]'(Nat.lt_of_lt_of_le hi he.1) = g.nodes[i]'hi := by
  have h := he.2 i hi
  rw [Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi he.1), Array.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

private theorem graphVal_extends {V R : Type} (alg : Algebra V R) {g g' : Graph}
    (hwf : GraphWF g) (hwf' : GraphWF g') (hext : GraphExtends g g')
    {i : Nat} (hi : i < g.nodes.size) :
    graphVal alg g' i = graphVal alg g i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [graphVal_consistent alg g' hwf' (Nat.lt_of_lt_of_le hi hext.1),
      graphVal_consistent alg g hwf hi, hext.getElem_eq hi]
    by_cases hvar : (g.nodes[i]'hi).op = .var
    · cases hn : g.nodes[i]'hi with | mk _ op _ => simp only [hn] at hvar; subst hvar; rfl
    · funext env
      rw [meaning_nonvar alg _ _ hvar, meaning_nonvar alg _ _ hvar]
      congr 1; apply Array.ext (by simp)
      intro j hj1 hj2; have hj : j < (g.nodes[i]'hi).children.size := by simpa using hj1
      simp only [Array.getElem_map]; funext fresh
      have hcid : ((g.nodes[i]'hi).children[j]'hj).id < i := (hwf.2.1 i hi _ (Array.getElem_mem hj)).1
      rw [ih _ hcid (Nat.lt_trans hcid hi)]

private theorem internGo_spec (n : Node) (g : Graph) (hwf : GraphWF g)
    (hVar : n.op = .var → n.arity = 1)
    (hCh : ∀ c ∈ n.children, c.id < g.nodes.size ∧ ∀ s ∈ c.slots, ∀ k, s = some k → k < n.arity) :
    let res := internGo n g
    GraphWF res.2 ∧ GraphExtends g res.2 ∧ ∃ hid : res.1 < res.2.nodes.size, res.2.nodes[res.1]'hid = n := by
  unfold internGo
  cases hLook : g.index[n]? with
  | some id =>
    simp only [hLook]
    have hg := hwf.2.2 n id hLook
    have hid : id < g.nodes.size := by
      by_cases h : id < g.nodes.size; · exact h
      · rw [Array.getElem?_eq_none (by omega)] at hg; cases hg
    exact ⟨hwf, GraphExtends.refl g, hid, Option.some.inj ((Array.getElem?_eq_getElem hid).symm.trans hg)⟩
  | none =>
    simp only [hLook]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨by simp, fun i hi => by rw [Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]⟩,
      ⟨by simp, by simp⟩⟩
    · intro i hi
      simp only [Array.size_push] at hi
      by_cases hlt : i < g.nodes.size
      · rw [Array.getElem_push_lt hlt]; exact hwf.1 i hlt
      · have heq : i = g.nodes.size := by omega
        subst heq; simp only [Array.getElem_push_eq]; exact hVar
    · intro i hi c hc
      simp only [Array.size_push] at hi
      by_cases hlt : i < g.nodes.size
      · rw [Array.getElem_push_lt hlt] at hc ⊢; exact hwf.2.1 i hlt c hc
      · have heq : i = g.nodes.size := by omega
        subst heq; simp only [Array.getElem_push_eq] at hc ⊢; exact hCh c hc
    · intro m j hm
      by_cases he : n = m
      · subst he; simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hm
        subst hm; exact Array.getElem?_push_size
      · rw [Std.HashMap.getElem?_insert, beq_false_of_ne he] at hm
        have hg := hwf.2.2 m j hm
        have hj : j < g.nodes.size := by
          by_cases h : j < g.nodes.size; · exact h
          · rw [Array.getElem?_eq_none (by omega)] at hg; cases hg
        rw [Array.getElem?_push_lt hj, ← Array.getElem?_eq_getElem hj]; exact hg

private def AddSlotMaps (binder : Option Nat) (names : Array Nat) (x : Nat) (s : Option Nat) : Prop :=
  (s = none → binder = some x) ∧
  (∀ k, s = some k → binder ≠ some x ∧ names[k]? = some x)

private theorem AddSlotMaps.mono {binder : Option Nat} {u1 u2 : Array Nat} {x : Nat} {s : Option Nat}
    (hm : AddSlotMaps binder u1 x s) (he : ArrayExtends u1 u2) : AddSlotMaps binder u2 x s :=
  ⟨hm.1, fun k hk => ⟨(hm.2 k hk).1, he.get_some (hm.2 k hk).2⟩⟩

private def AddEdgeMatchesOpt (binder : Option Nat) (child : Applied Nat)
    (edge : Applied (Option Nat)) (names : Array Nat) : Prop :=
  edge.id = child.id ∧ edge.slots.size = child.slots.size ∧
  ∀ (i : Nat) x s, child.slots[i]? = some x → edge.slots[i]? = some s → AddSlotMaps binder names x s

private theorem AddEdgeMatchesOpt.mono {binder : Option Nat} {child : Applied Nat}
    {edge : Applied (Option Nat)} {u1 u2 : Array Nat}
    (hm : AddEdgeMatchesOpt binder child edge u1) (he : ArrayExtends u1 u2) :
    AddEdgeMatchesOpt binder child edge u2 :=
  ⟨hm.1, hm.2.1, fun i x s h1 h2 => (hm.2.2 i x s h1 h2).mono he⟩

private theorem addSlot_spec (binder : Option Nat) (name : Nat)
    (st : Array Nat × Std.HashMap Nat Nat) (hwf : RenStateWF st.1 st.2) :
    let r := addSlot binder name st
    RenStateWF r.2.1 r.2.2 ∧ ArrayExtends st.1 r.2.1 ∧ AddSlotMaps binder r.2.1 name r.1 := by
  unfold addSlot
  by_cases hb : (binder == some name) = true
  · simp only [hb, ↓reduceIte]
    exact ⟨hwf, ArrayExtends.refl _, ⟨fun _ => beq_iff_eq.mp hb, fun _ h => by cases h⟩⟩
  · have hne : binder ≠ some name := fun h => by simp [h] at hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    cases h : st.2[name]? with
    | some i =>
      exact ⟨hwf, ArrayExtends.refl _, ⟨fun h' => (by cases h'), fun k hk => ⟨hne, (Option.some.inj hk) ▸ hwf.1 name i h⟩⟩⟩
    | none =>
      refine ⟨⟨?_, ?_⟩, ArrayExtends.push st.1 name, ⟨fun h' => (by cases h'), fun k hk => ?_⟩⟩
      · intro k' j' hk'
        by_cases he : name = k'
        · subst he; simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hk'
          subst hk'; exact Array.getElem?_push_size
        · rw [Std.HashMap.getElem?_insert, beq_false_of_ne he] at hk'
          exact (ArrayExtends.push st.1 name).get_some (hwf.1 k' j' hk')
      · intro j' k' hj'
        by_cases hlt : j' < st.1.size
        · rw [Array.getElem?_push_lt hlt] at hj'
          injection hj' with hk'; subst hk'
          have hne' : name ≠ st.1[j']'hlt := fun heq => by
            have := hwf.2 j' (st.1[j']'hlt) (Array.getElem?_eq_getElem hlt)
            rw [← heq, h] at this; cases this
          rw [Std.HashMap.getElem?_insert, beq_false_of_ne hne']
          exact hwf.2 j' (st.1[j']'hlt) (Array.getElem?_eq_getElem hlt)
        · by_cases heq : j' = st.1.size
          · subst heq; rw [Array.getElem?_push_size] at hj'
            injection hj' with hk'; subst hk'; simp
          · rw [Array.getElem?_eq_none (by simp; omega)] at hj'; cases hj'
      · injection hk with hkeq; subst hkeq; exact ⟨hne, Array.getElem?_push_size⟩

private theorem addChild_spec (binder : Option Nat) (child : Applied Nat)
    (st : Array Nat × Std.HashMap Nat Nat) (hwf : RenStateWF st.1 st.2) :
    let r := addChild binder child st
    RenStateWF r.2.1 r.2.2 ∧ ArrayExtends st.1 r.2.1 ∧ AddEdgeMatchesOpt binder child r.1 r.2.1 := by
  let inv := fun (idx : Nat) (p : Array (Option Nat) × (Array Nat × Std.HashMap Nat Nat)) =>
    RenStateWF p.2.1 p.2.2 ∧ ArrayExtends st.1 p.2.1 ∧ p.1.size = idx ∧
    ∀ (i : Nat) x s, i < idx → child.slots[i]? = some x → p.1[i]? = some s → AddSlotMaps binder p.2.1 x s
  have hfold : inv child.slots.size (child.slots.foldl (fun (acc, s) name =>
      let (slot, s') := addSlot binder name s; (acc.push slot, s')) (#[], st)) := by
    apply Array.foldl_induction (motive := inv)
    · exact ⟨hwf, ArrayExtends.refl _, rfl, fun _ _ _ h => by omega⟩
    · intro idx ⟨acc, s⟩ ⟨hsw, hext, hsz, hall⟩
      have hss := addSlot_spec binder child.slots[idx] s hsw
      refine ⟨hss.1, hext.trans hss.2.1, by simp [hsz], fun i x s' hi hx hs' => ?_⟩
      by_cases hilt : i < idx.val
      · have hiacc : i < acc.size := by rw [hsz]; exact hilt
        rw [Array.getElem?_push_lt hiacc, ← Array.getElem?_eq_getElem hiacc] at hs'
        exact (hall i x s' hilt hx hs').mono hss.2.1
      · have hiEq : i = idx.val := by omega
        subst hiEq
        have h1 : child.slots[idx.val]? = some child.slots[idx] := Array.getElem?_eq_getElem idx.isLt
        rw [h1] at hx; injection hx with hxeq; subst hxeq
        have h2 : (acc.push (addSlot binder child.slots[idx] s).1)[acc.size]? = some (addSlot binder child.slots[idx] s).1 :=
          Array.getElem?_push_size
        rw [hsz] at h2; rw [h2] at hs'; injection hs' with hseq; subst hseq
        exact hss.2.2
  refine ⟨hfold.1, hfold.2.1, rfl, hfold.2.2.1, fun i x s hx hs => ?_⟩
  have hi : i < child.slots.size := by
    by_cases hlt : i < child.slots.size; · exact hlt
    · rw [Array.getElem?_eq_none (by omega)] at hx; cases hx
  exact hfold.2.2.2 i x s hi hx hs

private theorem addNodeGo_spec (op : Op) (hNotVar : op ≠ .var) (binder : Option Nat)
    (children : Array (Applied Nat)) (g : Graph) (hwf : GraphWF g)
    (hCh : ∀ c ∈ children, c.id < g.nodes.size) :
    let res := addNodeGo op binder children g
    GraphWF res.2 ∧ GraphExtends g res.2 ∧
    (∃ hid : res.1.id < res.2.nodes.size,
      (res.2.nodes[res.1.id]'hid).op = op ∧
      (res.2.nodes[res.1.id]'hid).arity = res.1.slots.size ∧
      (res.2.nodes[res.1.id]'hid).children.size = children.size ∧
      ∀ (i : Nat) c e, children[i]? = some c → (res.2.nodes[res.1.id]'hid).children[i]? = some e →
        AddEdgeMatchesOpt binder c e res.1.slots) ∧
    res.1.slots.toList.Nodup := by
  let inv := fun (idx : Nat) (p : Array (Applied (Option Nat)) × (Array Nat × Std.HashMap Nat Nat)) =>
    RenStateWF p.2.1 p.2.2 ∧ p.1.size = idx ∧
    ∀ (i : Nat) c e, i < idx → children[i]? = some c → p.1[i]? = some e → AddEdgeMatchesOpt binder c e p.2.1
  have hinit : RenStateWF (#[] : Array Nat) ({} : Std.HashMap Nat Nat) :=
    ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩
  have hfold : inv children.size (children.foldl (fun (acc, s) child =>
      let (edge, s') := addChild binder child s; (acc.push edge, s')) (#[], (#[], {}))) := by
    apply Array.foldl_induction (motive := inv)
    · exact ⟨hinit, rfl, fun _ _ _ h => by omega⟩
    · intro idx ⟨acc, s⟩ ⟨hsw, hsz, hall⟩
      have hsc := addChild_spec binder children[idx] s hsw
      refine ⟨hsc.1, by simp [hsz], fun i c e hi hc he => ?_⟩
      by_cases hilt : i < idx.val
      · have hiacc : i < acc.size := by rw [hsz]; exact hilt
        rw [Array.getElem?_push_lt hiacc, ← Array.getElem?_eq_getElem hiacc] at he
        exact (hall i c e hilt hc he).mono hsc.2.1
      · have hiEq : i = idx.val := by omega
        subst hiEq
        have h1 : children[idx.val]? = some children[idx] := Array.getElem?_eq_getElem idx.isLt
        rw [h1] at hc; injection hc with hceq; subst hceq
        have h2 : (acc.push (addChild binder children[idx] s).1)[acc.size]? = some (addChild binder children[idx] s).1 :=
          Array.getElem?_push_size
        rw [hsz] at h2; rw [h2] at he; injection he with heeq; subst heeq
        exact hsc.2.2
  let edges := (children.foldl (fun (acc, s) child =>
    let (edge, s') := addChild binder child s; (acc.push edge, s')) (#[], (#[], {}))).1
  let names := (children.foldl (fun (acc, s) child =>
    let (edge, s') := addChild binder child s; (acc.push edge, s')) (#[], (#[], {}))).2.1
  have hEdgesBnd : ∀ c ∈ edges, c.id < g.nodes.size ∧ ∀ s ∈ c.slots, ∀ k, s = some k → k < names.size := by
    intro c hc
    obtain ⟨idx, hidx, rfl⟩ := Array.mem_iff_getElem.mp hc
    have hidx' : idx < children.size := by rw [← hfold.2.1]; exact hidx
    have hm := hfold.2.2 idx (children[idx]'hidx') (edges[idx]'hidx) hidx'
      (Array.getElem?_eq_getElem hidx') (Array.getElem?_eq_getElem hidx)
    refine ⟨hm.1 ▸ hCh (children[idx]'hidx') (Array.getElem_mem hidx'), fun s hs k hsk => ?_⟩
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hs
    have hjc : j < (children[idx]'hidx').slots.size := by rw [← hm.2.1]; exact hj
    have hslot := hm.2.2 j ((children[idx]'hidx').slots[j]'hjc) ((edges[idx]'hidx).slots[j]'hj)
      (Array.getElem?_eq_getElem hjc) (Array.getElem?_eq_getElem hj)
    have hget := (hslot.2 k hsk).2
    by_cases hlt : k < names.size
    · exact hlt
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hget; cases hget
  have hint := internGo_spec ⟨names.size, op, edges⟩ g hwf (fun h => absurd h hNotVar) hEdgesBnd
  unfold addNodeGo
  dsimp only
  obtain ⟨hwf', hext, hid, hget⟩ := hint
  refine ⟨hwf', hext, ⟨hid, by rw [hget], by rw [hget], by rw [hget]; exact hfold.2.1, fun i c e hc he => ?_⟩,
    renStateWF_nodup hfold.1⟩
  rw [hget] at he
  have hi : i < children.size := by
    by_cases hlt : i < children.size; · exact hlt
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hc; cases hc
  exact hfold.2.2 i c e hi hc he

private def depthEnv {V : Type} (depth : Nat) (freeName : Nat → Nat) (env : Nat → V) (i : Nat) : V :=
  if i < depth then env (2 * (depth - 1 - i) + 1) else env (2 * freeName (i - depth))

private theorem depthEnv_lift {V : Type} (depth : Nat) (freeName : Nat → Nat)
    (env : Nat → V) (fresh : V) (i : Nat) :
    depthEnv (depth + 1) freeName (fun k => if k = 2 * depth + 1 then fresh else env k) i =
      match i with | 0 => fresh | j + 1 => depthEnv depth freeName env j := by
  cases i with
  | zero => simp [depthEnv]
  | succ j =>
    simp only [depthEnv]
    by_cases hj : j < depth
    · have hj1 : j + 1 < depth + 1 := by omega
      have heq : depth + 1 - 1 - (j + 1) = depth - 1 - j := by omega
      simp only [hj, hj1, ↓reduceIte, heq]
      rw [ite_eq_right (by omega)]
    · have hj1 : ¬ (j + 1 < depth + 1) := by omega
      have heq : j + 1 - (depth + 1) = j - depth := by omega
      simp only [hj, hj1, ↓reduceIte, heq]
      rw [ite_eq_right (by omega)]

private theorem addEdge_eval {V : Type} {binder : Option Nat} {child : Applied Nat}
    {edge : Applied (Option Nat)} {names : Array Nat}
    (hm : AddEdgeMatchesOpt binder child edge names)
    (env : Nat → V) (fresh : V) (j : Nat) (hj : j < child.slots.size) :
    evalEdgeSlot (fun k => env (names[k]?.getD 0)) fresh (edge.slots[j]?.join) =
      (fun x => if binder = some x then fresh else env x) (child.slots[j]'hj) := by
  have hje : j < edge.slots.size := by rw [hm.2.1]; exact hj
  have hs := hm.2.2 j (child.slots[j]'hj) (edge.slots[j]'hje)
    (Array.getElem?_eq_getElem hj) (Array.getElem?_eq_getElem hje)
  rw [Array.getElem?_eq_getElem hje]
  simp only [Option.join]
  cases hsl : edge.slots[j]'hje with
  | none => simp [evalEdgeSlot, hs.1 hsl]
  | some k => obtain ⟨hne, hget⟩ := hs.2 k hsl; simp [evalEdgeSlot, hne, hget]

private theorem evalShapes_len {V R : Type} (alg : Algebra V R) (env : Nat → V) :
    ∀ cs : List TermTraverse.Shape, (evalShapes alg cs env).length = cs.length
  | [] => rfl
  | _ :: xs => by simp [evalShapes, evalShapes_len alg env xs]

private theorem evalShapes_getElem {V R : Type} (alg : Algebra V R) (env : Nat → V) (fresh : V) :
    ∀ (cs : List TermTraverse.Shape) (k : Nat) (hk : k < cs.length),
      ((evalShapes alg cs env)[k]'(by rw [evalShapes_len]; exact hk)) fresh =
        evalShape alg (cs[k]'hk) env
  | [], _, hk => by simp at hk
  | _ :: xs, 0, _ => rfl
  | _ :: xs, k + 1, hk => evalShapes_getElem alg env fresh xs k (by simpa using hk)

mutual
private theorem insertShapeGo_sound {V R : Type} (alg : Algebra V R)
    (depth : Nat) (freeName : Nat → Nat) :
    ∀ (t : TermTraverse.Shape) (g : Graph), GraphWF g →
    let res := insertShapeGo depth freeName t g
    GraphWF res.2 ∧ GraphExtends g res.2 ∧
    ∃ hid : res.1.id < res.2.nodes.size,
      res.1.slots.size = (res.2.nodes[res.1.id]'hid).arity ∧
      res.1.slots.toList.Nodup ∧
      ∀ env : Nat → V, evalApplied (graphVal alg res.2) res.1 env = evalShape alg t (depthEnv depth freeName env)
  | .var i, g, hwf => by
    let name := if i < depth then 2 * (depth - 1 - i) + 1 else 2 * freeName (i - depth)
    have hint := internGo_spec ⟨1, .var, #[]⟩ g hwf (fun _ => rfl) (fun _ h => by simp at h)
    unfold insertShapeGo; dsimp only
    obtain ⟨hwf', hext, hid, hget⟩ := hint
    refine ⟨hwf', hext, hid, by simp [hget], by simp, fun env => ?_⟩
    unfold evalApplied
    rw [graphVal_consistent alg _ hwf' hid, hget]
    by_cases h : i < depth <;> simp [meaning, evalShape, depthEnv, name, h]
  | .bind body, g, hwf => by
    unfold insertShapeGo; dsimp only
    let res1 := insertShapeGo (depth + 1) freeName body g
    obtain ⟨hwf1, hext1, hid1, hsz1, _, heval1⟩ := insertShapeGo_sound alg (depth + 1) freeName body g hwf
    have had := addNodeGo_spec .bind (by simp) (some (2 * depth + 1)) #[res1.1] res1.2 hwf1
      (fun c hc => by simp at hc; subst hc; exact hid1)
    obtain ⟨hwf2, hext2, ⟨hid2, hop2, har2, hchsz2, hedge2⟩, hnd2⟩ := had
    let res2 := addNodeGo .bind (some (2 * depth + 1)) #[res1.1] res1.2
    refine ⟨hwf2, hext1.trans hext2, hid2, har2.symm, hnd2, fun env => ?_⟩
    unfold evalApplied
    rw [graphVal_consistent alg res2.2 hwf2 hid2, meaning_nonvar alg _ _ (by rw [hop2]; simp), hop2]
    simp only [evalShape]
    congr 1
    apply Array.ext (by simp [res2, hchsz2])
    intro idx hi1 hi2
    have hidx0 : idx = 0 := by simp at hi2; omega
    subst hidx0
    have h0ch : 0 < (res2.2.nodes[res2.1.id]'hid2).children.size := by
      have h1 : (res2.2.nodes[res2.1.id]'hid2).children.size = 1 := by simpa [res2] using hchsz2
      omega
    simp only [Array.getElem_map, Array.getElem_singleton]
    funext fresh
    have hm := hedge2 0 res1.1 ((res2.2.nodes[res2.1.id]'hid2).children[0]'h0ch)
      (by simp) (Array.getElem?_eq_getElem h0ch)
    rw [hm.1, graphVal_extends alg hwf1 hwf2 hext2 hid1]
    let env' : Nat → V := fun k => if k = 2 * depth + 1 then fresh else env k
    have hStep : graphVal alg res1.2 res1.1.id
        (fun j => evalEdgeSlot (fun k => env (res2.1.slots[k]?.getD 0))
          fresh (((res2.2.nodes[res2.1.id]'hid2).children[0]'h0ch).slots[j]?.join)) =
        evalApplied (graphVal alg res1.2) res1.1 env' := by
      unfold evalApplied
      have hdep := graphVal_dependsOnly alg res1.2 hwf1 res1.1.id
      have har1 : res1.2.initClosure.arityOf res1.1.id = res1.1.slots.size := by
        unfold Closure.arityOf Graph.initClosure
        simp only [res1, Array.getElem?_map, Array.getElem?_eq_getElem hid1, Option.map_some, Option.getD_some, hsz1]
      rw [har1] at hdep
      apply hdep
      intro j hj
      rw [addEdge_eval hm env fresh j hj, Array.getElem?_eq_getElem hj, Option.getD_some]
      simp only [env', Option.some.injEq]
      by_cases h : 2 * depth + 1 = res1.1.slots[j]'hj <;> simp [h, eq_comm]
    rw [hStep, heval1 env']
    congr 1; funext i
    exact depthEnv_lift depth freeName env fresh i
  | .node tag cs, g, hwf => by
    unfold insertShapeGo; dsimp only
    let res1 := insertShapesGo depth freeName cs g
    obtain ⟨hwf1, hext1, hlen1, hall1⟩ := insertShapesGo_sound alg depth freeName cs g hwf
    have hChBnd : ∀ c ∈ res1.1.toArray, c.id < res1.2.nodes.size := by
      intro c hc
      obtain ⟨idx, hidx, rfl⟩ := Array.mem_iff_getElem.mp hc
      have hiL : idx < res1.1.length := by simpa using hidx
      exact (hall1 idx hiL (by rw [← hlen1]; exact hiL)).1
    have had := addNodeGo_spec (.node tag) (by simp) none res1.1.toArray res1.2 hwf1 hChBnd
    obtain ⟨hwf2, hext2, ⟨hid2, hop2, har2, hchsz2, hedge2⟩, hnd2⟩ := had
    let res2 := addNodeGo (.node tag) none res1.1.toArray res1.2
    refine ⟨hwf2, hext1.trans hext2, hid2, har2.symm, hnd2, fun env => ?_⟩
    unfold evalApplied
    rw [graphVal_consistent alg res2.2 hwf2 hid2, meaning_nonvar alg _ _ (by rw [hop2]; simp), hop2]
    simp only [evalShape]
    congr 1
    apply Array.ext (by simp [res2, hchsz2, res1, hlen1, evalShapes_len])
    intro idx hi1 hi2
    have hidxCh : idx < (res2.2.nodes[res2.1.id]'hid2).children.size := by simpa using hi1
    have hidxC : idx < res1.1.toArray.size := by
      have hszEq : (res2.2.nodes[res2.1.id]'hid2).children.size = res1.1.toArray.size := hchsz2
      omega
    have hidxL : idx < res1.1.length := by simpa using hidxC
    have hidxS : idx < cs.length := by rw [← hlen1]; exact hidxL
    simp only [Array.getElem_map]
    funext fresh
    have hm := hedge2 idx (res1.1[idx]'hidxL) ((res2.2.nodes[res2.1.id]'hid2).children[idx]'hidxCh)
      (Array.getElem?_eq_getElem hidxC) (Array.getElem?_eq_getElem hidxCh)
    obtain ⟨hcid, hcsz, hceval⟩ := hall1 idx hidxL hidxS
    rw [hm.1, graphVal_extends alg hwf1 hwf2 hext2 hcid]
    have hStep : graphVal alg res1.2 (res1.1[idx]'hidxL).id
        (fun j => evalEdgeSlot (fun k => env (res2.1.slots[k]?.getD 0))
          fresh (((res2.2.nodes[res2.1.id]'hid2).children[idx]'hidxCh).slots[j]?.join)) =
        evalApplied (graphVal alg res1.2) (res1.1[idx]'hidxL) env := by
      unfold evalApplied
      have hdep := graphVal_dependsOnly alg res1.2 hwf1 (res1.1[idx]'hidxL).id
      have har1 : res1.2.initClosure.arityOf (res1.1[idx]'hidxL).id = (res1.1[idx]'hidxL).slots.size := by
        unfold Closure.arityOf Graph.initClosure
        simp only [res1, Array.getElem?_map, Array.getElem?_eq_getElem hcid, Option.map_some, Option.getD_some, hcsz]
      rw [har1] at hdep
      apply hdep
      intro j hj
      rw [addEdge_eval hm env fresh j hj, Array.getElem?_eq_getElem hj, Option.getD_some]
      simp
    rw [hStep, hceval env]
    exact (evalShapes_getElem alg (depthEnv depth freeName env) fresh cs idx hidxS).symm
termination_by structural t => t

private theorem insertShapesGo_sound {V R : Type} (alg : Algebra V R)
    (depth : Nat) (freeName : Nat → Nat) :
    ∀ (ts : List TermTraverse.Shape) (g : Graph), GraphWF g →
    let res := insertShapesGo depth freeName ts g
    GraphWF res.2 ∧ GraphExtends g res.2 ∧ res.1.length = ts.length ∧
    ∀ (i : Nat) (hi : i < res.1.length) (hit : i < ts.length),
      ∃ (hid : (res.1[i]'hi).id < res.2.nodes.size),
        (res.1[i]'hi).slots.size = (res.2.nodes[(res.1[i]'hi).id]'hid).arity ∧
        ∀ env : Nat → V, evalApplied (graphVal alg res.2) (res.1[i]'hi) env =
          evalShape alg (ts[i]'hit) (depthEnv depth freeName env)
  | [], g, hwf => ⟨hwf, GraphExtends.refl g, rfl, fun _ hi => by unfold insertShapesGo at hi; simp at hi⟩
  | x :: xs, g, hwf => by
    unfold insertShapesGo; dsimp only
    let r1 := insertShapeGo depth freeName x g
    obtain ⟨hwf1, hext1, hid1, hsz1, _, heval1⟩ := insertShapeGo_sound alg depth freeName x g hwf
    obtain ⟨hwf2, hext2, hlen2, hall2⟩ := insertShapesGo_sound alg depth freeName xs r1.2 hwf1
    refine ⟨hwf2, hext1.trans hext2, by simpa [r1] using hlen2, fun i hi hit => ?_⟩
    cases i with
    | zero =>
      refine ⟨Nat.lt_of_lt_of_le hid1 hext2.1, ?_, fun env => ?_⟩
      · have hEq := hext2.getElem_eq hid1
        simpa only [List.getElem_cons_zero] using hsz1.trans (congrArg Node.arity hEq.symm)
      · simp only [List.getElem_cons_zero]
        unfold evalApplied
        rw [graphVal_extends alg hwf1 hwf2 hext2 hid1]
        exact heval1 env
    | succ i' =>
      exact hall2 i' (by simpa using hi) (by simpa using hit)
termination_by structural ts => ts
end

/-- `insertCore` preserves graph well-formedness and evaluates any `Obend.Core.Term.Term`
faithfully in EVERY binder algebra `alg`. -/
theorem insertCore_eval {V R : Type} (alg : Algebra V R) (t : Term) (freeName : Nat → Nat)
    (g : Graph) (hwf : GraphWF g) :
    let res := (insertCore t freeName).run g
    GraphWF res.2 ∧ GraphExtends g res.2 ∧
    ∃ hid : res.1.id < res.2.nodes.size,
      res.1.slots.size = (res.2.nodes[res.1.id]'hid).arity ∧
      res.1.slots.toList.Nodup ∧
      ∀ env : Nat → V, evalApplied (graphVal alg res.2) res.1 env = evalCore alg t (fun i => env (2 * freeName i)) := by
  have h := insertShapeGo_sound alg 0 freeName (TermTraverse.encode t) g hwf
  have hEnv : ∀ env : Nat → V, depthEnv 0 freeName env = fun i => env (2 * freeName i) := by
    intro env; funext i; simp [depthEnv]
  simpa only [insertCore, evalCore, StateT.run, hEnv] using h

private def shapeAlgApply :
    Op → Array ((Nat → TermTraverse.Shape) → Nat → TermTraverse.Shape) → Nat → TermTraverse.Shape
  | .var, _ => fun _ => .var 0
  | .bind, cs => fun d =>
      let body := match cs[0]? with
        | some f => f (fun d' => .var (d' - 1 - d)) (d + 1)
        | none => .var 0
      .bind body
  | .node tag, cs => fun d =>
      .node tag (cs.toList.map fun child => child (fun _ => .var 0) d)

/-- Exact syntactic `TermTraverse.Shape` reconstruction algebra (de Bruijn level semantics). -/
def shapeAlg : Algebra (Nat → TermTraverse.Shape) (Nat → TermTraverse.Shape) where
  variableValue v := v
  apply := shapeAlgApply

private def coreFreeEnv (d0 : Nat) (i : Nat) : Nat → TermTraverse.Shape :=
  if i < d0 then fun d => .var (d - 1 - (d0 - 1 - i)) else fun d => .var ((i - d0) + d)

private theorem evalShape_shapeAlg (t : TermTraverse.Shape) :
    ∀ (d : Nat), evalShape shapeAlg t (coreFreeEnv d) d = t := by
  induction t using Obend.Core.Traverse.Tree.inductionOn with
  | var i =>
    intro d
    simp only [evalShape, shapeAlg, coreFreeEnv]
    by_cases h : i < d
    · simp only [h, ↓reduceIte]; congr 1; omega
    · simp only [h, ↓reduceIte]; congr 1; omega
  | bind body ih =>
    intro d
    simp only [evalShape, shapeAlg, shapeAlgApply]
    change Obend.Core.Traverse.Tree.bind (evalShape shapeAlg body _ (d + 1)) = _
    congr 1
    have hLift : (fun i => match i with | 0 => (fun d' => .var (d' - 1 - d)) | j + 1 => coreFreeEnv d j) =
        coreFreeEnv (d + 1) := by
      funext i; cases i with
      | zero => simp [coreFreeEnv]
      | succ j =>
        funext d'
        simp only [coreFreeEnv]
        by_cases hj : j < d
        · have hj1 : j + 1 < d + 1 := by omega
          simp only [hj, hj1, ↓reduceIte]; congr 1; omega
        · have hj1 : ¬ (j + 1 < d + 1) := by omega
          simp only [hj, hj1, ↓reduceIte]; congr 1; omega
    rw [hLift, ih (d + 1)]
  | node tag cs ih =>
    intro d
    simp only [evalShape, shapeAlg, shapeAlgApply]
    congr 1
    have hMap : ∀ xs : List TermTraverse.Shape,
        (∀ c ∈ xs, evalShape shapeAlg c (coreFreeEnv d) d = c) →
        (evalShapes shapeAlg xs (coreFreeEnv d)).map (fun child => child (fun _ => .var 0) d) = xs := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons x rest ihr =>
        simp only [evalShapes, List.map_cons, hxs x (.head _), ihr (fun c hc => hxs c (.tail _ hc))]
    exact hMap cs (fun c hc => ih c hc d)

/-- External-name assignment mapping even name `2 * k` to free de Bruijn variable `k`. -/
def coreNameEnv (name : Nat) : Nat → TermTraverse.Shape :=
  fun d => .var (name / 2 + d)

/-- **Exact `Obend.Core.Term` Reconstruction Soundness**: inserting any `t : Obend.Core.Term.Term`
into any well-formed graph and decoding in `shapeAlg` recovers `t` identically. -/
theorem insertCore_decode_sound (t : Term) (g : Graph) (hwf : GraphWF g) :
    let res := (insertCore t).run g
    TermTraverse.decode (evalApplied (graphVal shapeAlg res.2) res.1 coreNameEnv 0) = t := by
  dsimp only
  obtain ⟨_, _, _, _, _, heval⟩ := insertCore_eval shapeAlg t id g hwf
  have h := heval coreNameEnv
  simp only [id_eq] at h
  have hEnv : (fun i => coreNameEnv (2 * i)) = coreFreeEnv 0 := by
    funext i d; simp [coreNameEnv, coreFreeEnv]
  rw [h, hEnv, evalCore, evalShape_shapeAlg (TermTraverse.encode t) 0, TermTraverse.decode_encode]

/-- **End-to-End `Core.Term` Slotted Congruence Closure Soundness**: when `t₁` and `t₂` are
inserted alongside equations validated by `alg`, equivalence in `Graph.close` implies
semantic equality `evalCore alg t₁ env = evalCore alg t₂ env` for every `env`. -/
theorem coreClose_sound {V R : Type} (alg : Algebra V R) (g : Graph) (hwf : GraphWF g)
    (eqs : Array Equation)
    (hEqBounds : ∀ eq ∈ eqs, eq.1.id < g.nodes.size ∧ eq.2.id < g.nodes.size)
    (he : ∀ eq ∈ eqs, ∀ env, evalApplied (graphVal alg g) eq.1 env = evalApplied (graphVal alg g) eq.2 env)
    {t₁ t₂ : Term} {a₁ a₂ : Applied Nat}
    (ha₁ : a₁.id < g.nodes.size) (ha₁sz : a₁.slots.size = (g.nodes[a₁.id]'ha₁).arity)
    (ha₂ : a₂.id < g.nodes.size) (ha₂sz : a₂.slots.size = (g.nodes[a₂.id]'ha₂).arity)
    (ht₁ : ∀ env, evalApplied (graphVal alg g) a₁ env = evalCore alg t₁ (fun i => env (2 * i)))
    (ht₂ : ∀ env, evalApplied (graphVal alg g) a₂ env = evalCore alg t₂ (fun i => env (2 * i)))
    (hequiv : (g.close eqs).equiv a₁ a₂ = true) (env : Nat → V) :
    evalCore alg t₁ env = evalCore alg t₂ env := by
  have hCh : ∀ e ∈ (Array.range g.nodes.size).zip g.nodes, ∀ c ∈ e.2.children, c.id < g.nodes.size := by
    intro e hmem c hc
    obtain ⟨idx, hidx, rfl⟩ := Array.mem_iff_getElem.mp hmem
    have hlt : idx < g.nodes.size := by simp at hidx; omega
    have he1 : ((Array.range g.nodes.size).zip g.nodes)[idx] = (idx, g.nodes[idx]'hlt) := by simp [hlt]
    rw [he1] at hc
    exact Nat.lt_trans (hwf.2.1 idx hlt c hc).1 hlt
  have hCons : ∀ e ∈ (Array.range g.nodes.size).zip g.nodes,
      graphVal alg g e.1 = meaning alg (graphVal alg g) e.2 := by
    intro e hmem
    obtain ⟨idx, hidx, rfl⟩ := Array.mem_iff_getElem.mp hmem
    have hlt : idx < g.nodes.size := by simp at hidx; omega
    have he1 : ((Array.range g.nodes.size).zip g.nodes)[idx] = (idx, g.nodes[idx]'hlt) := by simp [hlt]
    rw [he1]
    exact graphVal_consistent alg g hwf hlt
  let extEnv : Nat → V := fun k => env (k / 2)
  have hEq := Graph.close_sound g eqs alg (graphVal alg g)
    (graphVal_dependsOnly alg g hwf) hEqBounds he hCh hCons ha₁ ha₁sz ha₂ ha₂sz hequiv extEnv
  have hDiv : (fun i => extEnv (2 * i)) = env := by funext i; simp [extEnv]
  rw [ht₁ extEnv, ht₂ extEnv, hDiv] at hEq
  exact hEq

end Obend.SemanticKG.Slotted
