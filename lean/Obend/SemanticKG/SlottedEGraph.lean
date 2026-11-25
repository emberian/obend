module
public import Obend.Core.TermTraverse
public import Std.Data.HashMap
import all Obend.Core.TermTraverse
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
At an e-node edge, none names the enclosing binder. -/
structure Applied (Name : Type) where
  id : Nat
  slots : Array Name
  deriving DecidableEq, Hashable

structure Node where
  arity : Nat
  op : Op
  children : Array (Applied (Option Nat))
  deriving DecidableEq, Hashable

structure Graph where
  nodes : Array Node := #[]
  index : Std.HashMap Node Nat := {}

private def intern (n : Node) : StateM Graph Nat := do
  let g ← get
  if let some id := g.index[n]? then return id
  let id := g.nodes.size
  set (⟨g.nodes.push n, g.index.insert n id⟩ : Graph)
  return id

/-- Slots are numbered by first use. A repeated free name therefore denotes the same parameter,
and permuting the surrounding names changes only the application at the root. -/
private def addNode (op : Op) (binder : Option Nat) (children : Array (Applied Nat)) :
    StateM Graph (Applied Nat) := do
  let mut names := #[]
  let mut formals : Std.HashMap Nat Nat := {}
  let mut edges := #[]
  for child in children do
    let mut slots := #[]
    for name in child.slots do
      if binder == some name then slots := slots.push none
      else
        match formals[name]? with
        | some i => slots := slots.push (some i)
        | none =>
          let i := names.size
          formals := formals.insert name i
          names := names.push name
          slots := slots.push (some i)
    edges := edges.push ⟨child.id, slots⟩
  return ⟨← intern ⟨names.size, op, edges⟩, names⟩

mutual
/-- External names are even. Binder depths inhabit the disjoint odd namespace. Every binder edge
comes from the Core traversal, including case arms and the successor arm of ifZero. -/
private def insertShape (depth : Nat) (freeName : Nat → Nat) :
    TermTraverse.Shape → StateM Graph (Applied Nat)
  | .var i => do
    let name := if i < depth then 2 * (depth - 1 - i) + 1 else 2 * freeName (i - depth)
    return ⟨← intern ⟨1, .var, #[]⟩, #[name]⟩
  | .bind body => do
    let child ← insertShape (depth+1) freeName body
    addNode .bind (some (2*depth+1)) #[child]
  | .node tag cs => do
    let children ← insertShapes depth freeName cs
    addNode (.node tag) none children.toArray
termination_by structural t => t

private def insertShapes (depth : Nat) (freeName : Nat → Nat) :
    List TermTraverse.Shape → StateM Graph (List (Applied Nat))
  | [] => pure []
  | x :: xs => do
    let child ← insertShape depth freeName x
    return child :: (← insertShapes depth freeName xs)
termination_by structural ts => ts
end

def insertCore (term : Term) (freeName : Nat → Nat := id) : StateM Graph (Applied Nat) :=
  insertShape 0 freeName (TermTraverse.encode term)

/-- Replace child classes by the current representatives. Their slot interfaces have the same
formal order. The edge retains its partial bijection, including the locally bound parameter. -/
def rebuildNode (rep : Nat → Nat) (n : Node) : Node :=
  { n with children := n.children.map (fun e => { e with id := rep e.id }) }

/-- A rebuild pass emits class identifications. Owners may already denote unions of several
e-nodes. Running another pass with the new representatives propagates parent congruences. -/
private abbrev Work := Std.HashMap Node Nat × Array (Nat × Nat)

private def rebuildStep (rep : Nat → Nat) (s : Work) (item : Nat × Node) : Work :=
  let key := rebuildNode rep item.2
  match s.1[key]? with
  | some earlier => (s.1, s.2.push (item.1, earlier))
  | none => (s.1.insert key item.1, s.2)

def slottedRebuild (rep : Nat → Nat) (entries : Array (Nat × Node)) : Array (Nat × Nat) :=
  (entries.foldl (rebuildStep rep) ({}, #[])).2

private def walk (parent : Array Nat) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => match parent[i]? with
    | some j => if j < i then walk parent n j else i
    | none => i

private def representative (parent : Array Nat) := walk parent parent.size

private def unionStep (nodes : Array Node) (state : Array Nat × Bool) (eqn : Nat × Nat) :
    Array Nat × Bool :=
  let x := representative state.1 eqn.1
  let y := representative state.1 eqn.2
  if x == y then state else
    match nodes[x]?, nodes[y]? with
    | some l, some r =>
      if l.arity == r.arity then (state.1.setIfInBounds (max x y) (min x y), true) else state
    | _, _ => state

private def unionClasses (nodes : Array Node) (parent : Array Nat) (eqs : Array (Nat × Nat)) :=
  eqs.foldl (unionStep nodes) (parent, false)

private def closeLoop (nodes : Array Node) (entries : Array (Nat × Node)) : Nat → Array Nat → Array Nat
  | 0, parents => parents
  | fuel + 1, parents =>
    let found := slottedRebuild (representative parents) entries
    let (next, changed) := unionClasses nodes parents found
    if changed then closeLoop nodes entries fuel next else parents

/-- Congruence closure after caller-supplied equations between equally parameterized classes.
Every successful round strictly decreases the number of distinct representatives. -/
def Graph.close (g : Graph) (equations : Array (Nat × Nat)) : Array Nat :=
  let ids := Array.range g.nodes.size
  let entries := ids.zip g.nodes
  let (initial, _) := unionClasses g.nodes ids equations
  let final := closeLoop g.nodes entries ids.size initial
  ids.map (representative final)

/-- The binder algebra supplies a fresh value to a child. Free parameters are interpreted through
the edge's slot map, so a captured or permuted argument can change the denotation. -/
structure Algebra (V R : Type) where
  variableValue : V → R
  apply : Op → Array (V → R) → R

def meaning {V R : Type} (alg : Algebra V R) (interpret : Nat → (Nat → V) → R)
    (n : Node) (env : Nat → V) : R :=
  match n.op with
  | .var => alg.variableValue (env 0)
  | op => alg.apply op (n.children.map fun e fresh =>
      interpret e.id (fun j => match e.slots[j]?.join with
        | none => fresh | some k => env k))

private theorem rebuildNode_meaning {V R : Type} (alg : Algebra V R)
    (val : Nat → (Nat → V) → R) (rep : Nat → Nat) (valid : ∀ i, val (rep i) = val i)
    (n : Node) : meaning alg val (rebuildNode rep n) = meaning alg val n := by
  cases n with
  | mk ar op children =>
    cases op <;> funext env <;> simp [meaning, rebuildNode, Function.comp_def, valid]

theorem slottedRebuild_sound {V R : Type} (alg : Algebra V R)
    (val : Nat → (Nat → V) → R) (rep : Nat → Nat) (valid : ∀ i, val (rep i) = val i)
    (entries : Array (Nat × Node))
    (consistent : ∀ e ∈ entries, val e.1 = meaning alg val e.2) :
    ∀ pair ∈ slottedRebuild rep entries, val pair.1 = val pair.2 := by
  let inv := fun s : Work =>
    (∀ key owner, s.1[key]? = some owner → val owner = meaning alg val key) ∧
    (∀ p ∈ s.2, val p.1 = val p.2)
  have h : inv (entries.foldl (rebuildStep rep) ({}, #[])) := by
    apply Array.foldl_induction (motive := fun _ => inv) (by simp [inv])
    intro i s hs
    let e := entries[i]
    have he : val e.1 = meaning alg val (rebuildNode rep e.2) :=
      (consistent e (Array.getElem_mem _)).trans (rebuildNode_meaning alg val rep valid _).symm
    change inv (rebuildStep rep s e)
    obtain ⟨seen, pairs⟩ := hs
    unfold rebuildStep
    dsimp only
    cases hkey : s.1[rebuildNode rep e.2]? with
    | some owner =>
      refine ⟨seen, fun p hp => ?_⟩
      rcases Array.mem_push.mp hp with hp | rfl
      · exact pairs p hp
      · exact he.trans (seen _ _ hkey).symm
    | none =>
      refine ⟨fun key owner hl => ?_, pairs⟩
      by_cases eq : rebuildNode rep e.2 = key
      · subst key
        simp at hl
        exact hl ▸ he
      · exact seen key owner (by simpa [Std.HashMap.getElem?_insert, eq] using hl)
  exact h.2

private def ParentSound {D : Type} (val : Nat → D) (parents : Array Nat) : Prop :=
  ∀ i j, parents[i]? = some j → val j = val i

private theorem ParentSound_inhabited {D : Type} (val : Nat → D) (n : Nat) :
    ParentSound val (Array.range n) := by
  intro i j hij
  by_cases hi : i < n
  · simpa [Array.getElem?_eq_getElem, hi] using congrArg (Option.map val) hij.symm
  · simp [hi] at hij

private theorem walk_sound {D : Type} (val : Nat → D) (pa : Array Nat) (ok : ParentSound val pa)
    (fuel i : Nat) : val (walk pa fuel i) = val i := by
  induction fuel generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [walk]
    cases h : pa[i]? with
    | none => rfl
    | some j =>
      change val (if j < i then walk pa n j else i) = val i
      split <;> first | rfl | exact (ih j).trans (ok i j h)

private theorem union_sound {D : Type} (val : Nat → D) (nodes : Array Node) (pa : Array Nat)
    (eqs : Array (Nat × Nat)) (ok : ParentSound val pa)
    (he : ∀ e ∈ eqs, val e.1 = val e.2) : ParentSound val (unionClasses nodes pa eqs).1 := by
  apply Array.foldl_induction (motive := fun _ (s : Array Nat × Bool) => ParentSound val s.1) ok
  intro i s hs
  let x := representative s.1 eqs[i].1
  let y := representative s.1 eqs[i].2
  have hv : val x = val y := (walk_sound val s.1 hs _ _).trans
    ((he eqs[i] (Array.getElem_mem _)).trans (walk_sound val s.1 hs _ _).symm)
  have hmin : val (min x y) = val (max x y) := by
    by_cases h : x ≤ y
    · simpa [Nat.min_eq_left h, Nat.max_eq_right h] using hv
    · have h' := Nat.le_of_lt (Nat.lt_of_not_ge h)
      simpa [Nat.min_eq_right h', Nat.max_eq_left h'] using hv.symm
  have hup : ParentSound val (s.1.setIfInBounds (max x y) (min x y)) := by
    intro j target h
    rw [Array.getElem?_setIfInBounds] at h
    split at h
    · rename_i hj; subst j
      split at h <;> first | cases h; exact hmin | contradiction
    · exact hs j target h
  unfold unionStep
  dsimp only
  split <;> try exact hs
  split <;> try exact hs
  split <;> first | exact hup | exact hs

/-- All rounds of congruence closure, including transitive unions and final representative lookup,
preserve every slot-dependent interpretation which validates the supplied equations. -/
theorem Graph.close_sound {V R : Type} (g : Graph) (eqs : Array (Nat × Nat)) (alg : Algebra V R)
    (val : Nat → (Nat → V) → R) (he : ∀ e ∈ eqs, val e.1 = val e.2)
    (hc : ∀ e ∈ (Array.range g.nodes.size).zip g.nodes, val e.1 = meaning alg val e.2)
    {i j : Nat} (h : (g.close eqs)[i]? = some j) : val j = val i := by
  let ids := Array.range g.nodes.size
  let entries := ids.zip g.nodes
  have initial : ParentSound val ids := ParentSound_inhabited val _
  have loop (n : Nat) (pa : Array Nat) (ok : ParentSound val pa) :
      ParentSound val (closeLoop g.nodes entries n pa) := by
    induction n generalizing pa with
    | zero => exact ok
    | succ n ih =>
      rw [closeLoop]
      dsimp only
      split
      · apply ih
        exact union_sound val _ pa _ ok
          (slottedRebuild_sound alg val _ (walk_sound val _ ok _) entries hc)
      · exact ok
  let base := (unionClasses g.nodes ids eqs).1
  let final := closeLoop g.nodes entries ids.size base
  have finalOk : ParentSound val final := loop _ _ (union_sound val _ _ _ initial he)
  change (ids.map (representative final))[i]? = some j at h
  rw [Array.getElem?_map] at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (walk_sound val final finalOk _ _).trans (initial i k hk)

end Obend.SemanticKG.Slotted
