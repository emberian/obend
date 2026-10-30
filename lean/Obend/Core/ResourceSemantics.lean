module
/- Greatest safety predicates, decided by the existing shared visited worklist.
The mirror construction compares actual local safety labels with an all-good
copy of the same graph. This module is independent of RecursiveRows. -/
public import Obend.Core.AliasExposure
public import Obend.Core.FinitePresentation
@[expose] public section
namespace Obend.Core.FiniteSafety
open Obend.Core.FiniteBisimulation (Children children_mono)
open Obend.Core.FinitePresentation (Graph Bisimulation Bisimilar ClosedSupport)
set_option autoImplicit false

def Closed {α : Type} (g : Graph α Bool) (P : α → Prop) : Prop :=
  ∀ x, P x → g.label x = true ∧ ∀ child ∈ g.successors x, P child

def Safe {α : Type} (g : Graph α Bool) (x : α) : Prop :=
  ∃ P, Closed g P ∧ P x

theorem safe_closed {α : Type} (g : Graph α Bool) : Closed g (Safe g) := by
  intro x h
  obtain ⟨P,closed,root⟩ := h
  obtain ⟨good,children⟩ := closed x root
  exact ⟨good,fun child member => ⟨P,closed,children child member⟩⟩

theorem safe_of_children {α : Type} {g : Graph α Bool} {x : α}
    (good : g.label x = true) (children : ∀ child ∈ g.successors x, Safe g child) : Safe g x := by
  refine ⟨fun y => Safe g y ∨ y = x,?_,Or.inr rfl⟩
  intro y hy
  rcases hy with prior | rfl
  · obtain ⟨localGood,nested⟩ := safe_closed g y prior
    exact ⟨localGood,fun child member => Or.inl (nested child member)⟩
  · exact ⟨good,fun child member => Or.inl (children child member)⟩

theorem safe_iff {α : Type} (g : Graph α Bool) (x : α) :
    Safe g x ↔ g.label x = true ∧ ∀ child ∈ g.successors x, Safe g child :=
  ⟨safe_closed g x,fun h => safe_of_children h.1 h.2⟩

theorem children_same_map {α β : Type} (R : β → β → Prop) (f h : α → β) (xs : List α) :
    Children R (xs.map f) (xs.map h) ↔ ∀ x ∈ xs, R (f x) (h x) := by
  induction xs with
  | nil => simp [Children]
  | cons x xs ih => simp [Children,ih]

def mirror {α : Type} (g : Graph α Bool) : Graph (α × Bool) Bool where
  label := fun node => if node.2 then true else g.label node.1
  successors := fun node => (g.successors node.1).map (fun child => (child,node.2))

theorem mirror_iff {α : Type} (g : Graph α Bool) (x : α) :
    Bisimilar (mirror g) (x,false) (x,true) ↔ Safe g x := by
  constructor
  · intro root
    refine ⟨fun y => Bisimilar (mirror g) (y,false) (y,true),?_,root⟩
    intro y related
    obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (mirror g) (y,false) (y,true) related
    refine ⟨by simpa [mirror] using labels,?_⟩
    exact (children_same_map _ _ _ _).mp children
  · rintro ⟨P,closed,root⟩
    refine ⟨fun a b => a.1 = b.1 ∧ P a.1,?_,⟨rfl,root⟩⟩
    intro a b related
    rcases a with ⟨a,modeA⟩
    rcases b with ⟨b,modeB⟩
    obtain ⟨equal,ha⟩ := related
    change a = b at equal
    subst b
    obtain ⟨good,children⟩ := closed a ha
    refine ⟨by simp [mirror,good],?_⟩
    apply (children_same_map _ _ _ _).mpr
    intro child member
    exact ⟨rfl,children child member⟩

def mirrorNodes {α : Type} (nodes : List α) : List (α × Bool) :=
  nodes.flatMap (fun x => [(x,false),(x,true)])

theorem mem_mirrorNodes {α : Type} (nodes : List α) (x : α) (mode : Bool) :
    (x,mode) ∈ mirrorNodes nodes ↔ x ∈ nodes := by
  cases mode <;> simp [mirrorNodes,List.mem_flatMap]

def mirrorSupport {α : Type} {g : Graph α Bool} (P : ClosedSupport g) : ClosedSupport (mirror g) where
  nodes := mirrorNodes P.nodes
  closed := by
    intro node member child found
    rcases node with ⟨x,mode⟩
    have present := (mem_mirrorNodes P.nodes x mode).mp member
    obtain ⟨y,inside,rfl⟩ := List.mem_map.mp found
    exact (mem_mirrorNodes P.nodes y mode).mpr (P.closed x present y inside)

/-- The implementation is the existing finite visited-pair worklist. Both
copies share each original successor graph, so siblings share visited pairs. -/
def decision {α : Type} [DecidableEq α] {g : Graph α Bool}
    (P : ClosedSupport g) (x : α) (member : x ∈ P.nodes) : Bool :=
  (mirrorSupport P).agreement (x,false) (x,true)
    ((mem_mirrorNodes _ _ _).mpr member) ((mem_mirrorNodes _ _ _).mpr member)

theorem decision_iff {α : Type} [DecidableEq α] {g : Graph α Bool}
    (P : ClosedSupport g) (x : α) (member : x ∈ P.nodes) :
    decision P x member = true ↔ Safe g x :=
  ((mirrorSupport P).global_iff _ _ _ _).trans (mirror_iff g x)

theorem decision_support_independent {α : Type} [DecidableEq α] {g : Graph α Bool}
    (P Q : ClosedSupport g) (x : α) (hp : x ∈ P.nodes) (hq : x ∈ Q.nodes) :
    decision P x hp = decision Q x hq := by
  cases one : decision P x hp <;> cases two : decision Q x hq
  · rfl
  · exact False.elim (Bool.false_ne_true (one.symm.trans
      ((decision_iff P x hp).mpr ((decision_iff Q x hq).mp two))))
  · exact False.elim (Bool.false_ne_true (two.symm.trans
      ((decision_iff Q x hq).mpr ((decision_iff P x hp).mp one))))
  · rfl

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

#assert_axioms safe_closed safe_of_children safe_iff mirror_iff decision_iff decision_support_independent
end Obend.Core.FiniteSafety

namespace Obend.Core.ResourceSemantics
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

def head (assumptions : Assumptions) (t : Ty) : Bool × List Ty :=
  match expose assumptions t with
  | .nominal index => (assumptions.shareableVariables.contains index,[])
  | .unproductive _ => (true,[])
  | .constructor observation =>
    match observation.tag with
    | .natural | .label | .boolean | .emptyRow => (true,[])
    | .arrow reuse _ => (reuse == .reusable,[])
    | .custody _ | .computation => (false,[])
    | .field _ | .specification | .prototype | .variant => (true,observation.children)

def graph (assumptions : Assumptions) : Obend.Core.FinitePresentation.Graph Ty Bool where
  label := fun t => (head assumptions t).1
  successors := fun t => (head assumptions t).2

theorem dependencies_support {assumptions : Assumptions} {left right t : Ty}
    (present : t ∈ support assumptions left right) :
    ∀ child ∈ (head assumptions t).2, child ∈ support assumptions left right := by
  intro child inside
  cases exposed : expose assumptions t with
  | nominal index => simp [head,exposed] at inside
  | unproductive index => simp [head,exposed] at inside
  | constructor observation =>
    have closed := expose_children_support present exposed
    cases tag : observation.tag <;> simp [head,exposed,tag] at inside
    all_goals exact closed child inside

def presentation (assumptions : Assumptions) (t : Ty) :
    Obend.Core.FinitePresentation.ClosedSupport (graph assumptions) where
  nodes := support assumptions t t
  closed := by
    intro node present child inside
    exact dependencies_support present child inside

/-- Replacement candidate for RecursiveRows.shareable, with a universal
greatest-safe-predicate characterization and no user-supplied fuel. -/
def shareable (assumptions : Assumptions) (t : Ty) : Bool :=
  Obend.Core.FiniteSafety.decision (presentation assumptions t) t (left_mem_support _ _ _)

theorem shareable_iff (assumptions : Assumptions) (t : Ty) :
    shareable assumptions t = true ↔ Obend.Core.FiniteSafety.Safe (graph assumptions) t :=
  Obend.Core.FiniteSafety.decision_iff _ _ _

theorem shareable_unfold (assumptions : Assumptions) (t : Ty) :
    shareable assumptions t = true ↔ (head assumptions t).1 = true ∧
      ∀ child ∈ (head assumptions t).2, shareable assumptions child = true := by
  rw [shareable_iff,Obend.Core.FiniteSafety.safe_iff]
  simp only [graph,shareable_iff]

theorem head_eq_of_expose_eq {assumptions : Assumptions} {left right : Ty}
    (same : expose assumptions left = expose assumptions right) :
    head assumptions left = head assumptions right := by
  unfold head
  rw [same]

theorem shareable_eq_of_expose_eq {assumptions : Assumptions} {left right : Ty}
    (same : expose assumptions left = expose assumptions right) :
    shareable assumptions left = shareable assumptions right := by
  apply Obend.Core.FiniteSafety.bool_ext
  have leftRule := shareable_unfold assumptions left
  have rightRule := shareable_unfold assumptions right
  simp only [head_eq_of_expose_eq same] at leftRule
  exact leftRule.trans rightRule.symm

theorem head_field (assumptions : Assumptions) (name : String) (member tail : Ty) :
    head assumptions (.field name member tail) = (true,[member,tail]) := by
  simp [head,expose,exposeWalk,constructorHead]

theorem head_specification (assumptions : Assumptions) (metadata extension : Ty) :
    head assumptions (.specification metadata extension) = (true,[metadata,extension]) := by
  simp [head,expose,exposeWalk,constructorHead]

theorem head_prototype (assumptions : Assumptions) (spec target : Ty) :
    head assumptions (.prototype spec target) = (true,[spec,target]) := by
  simp [head,expose,exposeWalk,constructorHead]

theorem head_variant (assumptions : Assumptions) (row : Ty) :
    head assumptions (.variant row) = (true,[row]) := by
  simp [head,expose,exposeWalk,constructorHead]

theorem shareable_field (assumptions : Assumptions) (name : String) (member tail : Ty) :
    shareable assumptions (.field name member tail) =
      (shareable assumptions member && shareable assumptions tail) := by
  apply Obend.Core.FiniteSafety.bool_ext
  rw [shareable_unfold]
  simp [head_field,Bool.and_eq_true]

theorem shareable_specification (assumptions : Assumptions) (metadata extension : Ty) :
    shareable assumptions (.specification metadata extension) =
      (shareable assumptions metadata && shareable assumptions extension) := by
  apply Obend.Core.FiniteSafety.bool_ext
  rw [shareable_unfold]
  simp [head_specification,Bool.and_eq_true]

theorem shareable_prototype (assumptions : Assumptions) (spec target : Ty) :
    shareable assumptions (.prototype spec target) =
      (shareable assumptions spec && shareable assumptions target) := by
  apply Obend.Core.FiniteSafety.bool_ext
  rw [shareable_unfold]
  simp [head_prototype,Bool.and_eq_true]

theorem shareable_variant (assumptions : Assumptions) (row : Ty) :
    shareable assumptions (.variant row) = shareable assumptions row := by
  apply Obend.Core.FiniteSafety.bool_ext
  rw [shareable_unfold]
  simp [head_variant]

#assert_axioms dependencies_support shareable_iff shareable_unfold shareable_eq_of_expose_eq
  shareable_field shareable_specification shareable_prototype shareable_variant
end Obend.Core.ResourceSemantics
