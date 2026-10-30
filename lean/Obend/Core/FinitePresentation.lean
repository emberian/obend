module
/- A finite closed support presents a global deterministic graph exactly.
Indexing requires a membership proof; no missing node acquires a fallback. -/
public import Obend.Core.FiniteBisimulation
@[expose] public section
namespace Obend.Core.FinitePresentation
set_option autoImplicit false
open Obend.Core.FiniteBisimulation (Children children_mono children_refl children_symm children_comp)
namespace FB
export Obend.Core.FiniteBisimulation (Graph Bisimilar visitedSame visitedSame_iff)
end FB

structure Graph (α Label : Type) where
  label : α → Label
  successors : α → List α

def Bisimulation {α Label : Type} (g : Graph α Label) (R : α → α → Prop) : Prop :=
  ∀ x y, R x y → g.label x = g.label y ∧ Children R (g.successors x) (g.successors y)

def Bisimilar {α Label : Type} (g : Graph α Label) (x y : α) : Prop :=
  ∃ R, Bisimulation g R ∧ R x y

theorem bisimilar_refl {α Label : Type} (g : Graph α Label) (x : α) : Bisimilar g x x := by
  refine ⟨Eq,?_,rfl⟩
  intro a b h
  subst b
  exact ⟨rfl,children_refl _⟩

theorem bisimilar_symm {α Label : Type} {g : Graph α Label} {x y : α}
    (h : Bisimilar g x y) : Bisimilar g y x := by
  obtain ⟨R,closed,related⟩ := h
  refine ⟨fun a b => R b a,?_,related⟩
  intro a b h
  obtain ⟨labels,children⟩ := closed b a h
  exact ⟨labels.symm,children_symm children⟩

theorem bisimilar_trans {α Label : Type} {g : Graph α Label} {x y z : α}
    (one : Bisimilar g x y) (two : Bisimilar g y z) : Bisimilar g x z := by
  obtain ⟨R,rc,hr⟩ := one
  obtain ⟨S,sc,hs⟩ := two
  refine ⟨fun a c => ∃ b, R a b ∧ S b c,?_,⟨y,hr,hs⟩⟩
  intro a c h
  obtain ⟨b,hab,hbc⟩ := h
  obtain ⟨lab,cab⟩ := rc a b hab
  obtain ⟨lbc,cbc⟩ := sc b c hbc
  exact ⟨lab.trans lbc,children_comp cab cbc⟩

theorem bisimilar_equivalence {α Label : Type} (g : Graph α Label) :
    Equivalence (Bisimilar g) := ⟨bisimilar_refl g,bisimilar_symm,bisimilar_trans⟩

theorem children_map_iff {α β : Type} (f : β → α) (R : α → α → Prop)
    (xs ys : List β) :
    Children R (xs.map f) (ys.map f) ↔ Children (fun x y => R (f x) (f y)) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [Children]
  | cons x xs ih => cases ys <;> simp [Children,ih]

theorem children_map_image {α β : Type} (f : β → α) {R : β → β → Prop}
    {xs ys : List β} (h : Children R xs ys) :
    Children (fun x y => ∃ i j, f i = x ∧ f j = y ∧ R i j) (xs.map f) (ys.map f) := by
  apply (children_map_iff f _ xs ys).mpr
  exact children_mono (fun i j related => ⟨i,j,rfl,rfl,related⟩) h

/-- Duplicates and unreachable extra nodes are permitted. Only closure matters. -/
structure ClosedSupport {α Label : Type} (g : Graph α Label) where
  nodes : List α
  closed : ∀ x ∈ nodes, ∀ child ∈ g.successors x, child ∈ nodes

namespace ClosedSupport
variable {α Label : Type} [DecidableEq α] {g : Graph α Label}

def index (P : ClosedSupport g) (x : α) (member : x ∈ P.nodes) : Fin P.nodes.length :=
  ⟨P.nodes.idxOf x,List.idxOf_lt_length_of_mem member⟩

def decode (P : ClosedSupport g) (i : Fin P.nodes.length) : α := P.nodes[i.val]

theorem decode_mem (P : ClosedSupport g) (i : Fin P.nodes.length) : P.decode i ∈ P.nodes :=
  List.getElem_mem i.isLt

@[simp] theorem decode_index (P : ClosedSupport g) (x : α) (member : x ∈ P.nodes) :
    P.decode (P.index x member) = x := by
  change P.nodes[P.nodes.idxOf x]'(List.idxOf_lt_length_of_mem member) = x
  apply eq_of_beq
  exact List.findIdx_getElem (xs := P.nodes) (p := fun a => a == x)
    (w := by simpa only [List.idxOf] using List.idxOf_lt_length_of_mem member)

def finiteGraph (P : ClosedSupport g) : FB.Graph Label P.nodes.length where
  label := fun i => g.label (P.decode i)
  successors := fun i => (g.successors (P.decode i)).attach.map
    (fun child => P.index child.val (P.closed _ (P.decode_mem i) child.val child.property))

@[simp] theorem finite_label (P : ClosedSupport g) (i : Fin P.nodes.length) :
    P.finiteGraph.label i = g.label (P.decode i) := rfl

theorem decode_successors (P : ClosedSupport g) (i : Fin P.nodes.length) :
    (P.finiteGraph.successors i).map P.decode = g.successors (P.decode i) := by
  change ((g.successors (P.decode i)).attach.map
    (fun child => P.index child.val (P.closed _ (P.decode_mem i) child.val child.property))).map P.decode = _
  rw [List.map_map]
  calc
    _ = (g.successors (P.decode i)).attach.map Subtype.val := by
      apply List.map_congr_left
      intro child _
      exact P.decode_index child.val _
    _ = _ := List.attach_map_subtype_val _

/-- A finite relation pushes forward to a global relation supported on these
nodes. A global relation pulls back without requiring any support restriction. -/
theorem finite_iff (P : ClosedSupport g) (i j : Fin P.nodes.length) :
    FB.Bisimilar P.finiteGraph i j ↔ Bisimilar g (P.decode i) (P.decode j) := by
  constructor
  · rintro ⟨R,closed,related⟩
    refine ⟨fun x y => ∃ a b, P.decode a = x ∧ P.decode b = y ∧ R a b,?_,
      ⟨i,j,rfl,rfl,related⟩⟩
    intro x y h
    obtain ⟨a,b,rfl,rfl,hab⟩ := h
    obtain ⟨labels,children⟩ := closed a b hab
    refine ⟨labels,?_⟩
    have image := children_map_image P.decode children
    simpa only [P.decode_successors] using image
  · rintro ⟨R,closed,related⟩
    refine ⟨fun a b => R (P.decode a) (P.decode b),?_,related⟩
    intro a b hab
    obtain ⟨labels,children⟩ := closed _ _ hab
    refine ⟨labels,(children_map_iff P.decode R _ _).mp ?_⟩
    simpa only [P.decode_successors] using children

def agreement [DecidableEq Label] (P : ClosedSupport g) (x y : α)
    (hx : x ∈ P.nodes) (hy : y ∈ P.nodes) : Bool :=
  FB.visitedSame P.finiteGraph (P.index x hx) (P.index y hy)

theorem global_iff [DecidableEq Label] (P : ClosedSupport g) (x y : α)
    (hx : x ∈ P.nodes) (hy : y ∈ P.nodes) :
    P.agreement x y hx hy = true ↔ Bisimilar g x y := by
  rw [agreement,FB.visitedSame_iff,P.finite_iff]
  simp only [decode_index]

/-- Presentation size, ordering, duplicates and additional query roots do not
change the answer, provided both finite supports are successor-closed. -/
theorem support_independent [DecidableEq Label] (P Q : ClosedSupport g) (x y : α)
    (px : x ∈ P.nodes) (py : y ∈ P.nodes) (qx : x ∈ Q.nodes) (qy : y ∈ Q.nodes) :
    P.agreement x y px py = Q.agreement x y qx qy := by
  cases hp : P.agreement x y px py <;> cases hq : Q.agreement x y qx qy
  · rfl
  · exact False.elim (Bool.false_ne_true (hp.symm.trans
      ((P.global_iff x y px py).mpr ((Q.global_iff x y qx qy).mp hq))))
  · exact False.elim (Bool.false_ne_true (hq.symm.trans
      ((Q.global_iff x y qx qy).mpr ((P.global_iff x y px py).mp hp))))
  · rfl

end ClosedSupport

#assert_axioms bisimilar_equivalence ClosedSupport.decode_index ClosedSupport.decode_successors
  ClosedSupport.finite_iff ClosedSupport.global_iff ClosedSupport.support_independent

/-- The union of all bisimulations is itself closed. -/
theorem bisimilar_closed {α Label : Type} (g : Graph α Label) :
    Bisimulation g (Bisimilar g) := by
  intro x y related
  obtain ⟨R,closed,root⟩ := related
  obtain ⟨labels,children⟩ := closed x y root
  exact ⟨labels,children_mono (fun a b h => ⟨R,closed,h⟩) children⟩

/-- Fuse matching observations whose corresponding children are already
bisimilar. The new root pair closes together with the existing greatest relation. -/
theorem bisimilar_of_children {α Label : Type} {g : Graph α Label} {x y : α}
    (labels : g.label x = g.label y)
    (children : Children (Bisimilar g) (g.successors x) (g.successors y)) :
    Bisimilar g x y := by
  let R : α → α → Prop := fun a b => Bisimilar g a b ∨ (a = x ∧ b = y)
  refine ⟨R,?_,Or.inr ⟨rfl,rfl⟩⟩
  intro a b related
  rcases related with prior | ⟨rfl,rfl⟩
  · obtain ⟨equal,nested⟩ := bisimilar_closed g a b prior
    exact ⟨equal,children_mono (fun _ _ h => Or.inl h) nested⟩
  · exact ⟨labels,children_mono (fun _ _ h => Or.inl h) children⟩

#assert_axioms bisimilar_closed bisimilar_of_children

end Obend.Core.FinitePresentation
