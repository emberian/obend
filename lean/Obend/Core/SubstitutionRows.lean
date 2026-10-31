module
public import Obend.Core.SubstitutionBisimulation
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
open Obend.Core.FiniteBisimulation (Children children_mono children_refl children_symm children_comp)
set_option autoImplicit false

theorem instantiation_children_trans {σ : Nat → Ty} {a b : Assumptions} {xs ys zs : List Node}
    (one : Children (InstantiationRelated σ a b) xs ys)
    (two : Children (InstantiationRelated σ a b) ys zs) :
    Children (InstantiationRelated σ a b) xs zs :=
  children_mono (fun _ _ ⟨_,h,k⟩ => InstantiationRelated.trans h k) (children_comp one two)

theorem residual_existing_children {b : Assumptions} {left right : RR.Tail}
    (related : Obend.Core.RecursiveRows.ResidualRelated b left right) :
    Children (FP.Bisimilar (graph b)) (tailChildren left) (tailChildren right) := by
  cases related with
  | nonRow h => exact ⟨h,True.intro⟩
  | _ => trivial

theorem mapped_residual_interface (σ : Nat → Ty) (a b : Assumptions)
    (left right : RR.Tail) (kinds : tailKind left = tailKind right)
    (children : Children (FP.Bisimilar (graph a)) (tailChildren left) (tailChildren right)) :
    tailKind (Obend.Core.RecursiveRows.instantiateResidual σ b left) =
      tailKind (Obend.Core.RecursiveRows.instantiateResidual σ b right) ∧
    Children (InstantiationRelated σ a b)
      (tailChildren (Obend.Core.RecursiveRows.instantiateResidual σ b left))
      (tailChildren (Obend.Core.RecursiveRows.instantiateResidual σ b right)) := by
  cases left with
  | closed => cases right <;> simp_all [tailKind,Obend.Core.RecursiveRows.instantiateResidual,tailChildren,Children]
  | productiveCycle => cases right <;> simp_all [tailKind,Obend.Core.RecursiveRows.instantiateResidual,tailChildren,Children]
  | unproductive index => cases right <;> simp_all [tailKind,Obend.Core.RecursiveRows.instantiateResidual,tailChildren,Children]
  | nominal index =>
    cases right with
    | nominal other =>
      have same : index = other := TailKind.nominal.inj kinds
      subst other
      exact ⟨rfl,children_mono (fun x y equal => by
        subst y
        exact InstantiationRelated.existing ((FP.bisimilar_equivalence (graph b)).refl x)) (children_refl _)⟩
    | _ => simp [tailKind] at kinds
  | nonRow left =>
    cases right with
    | nonRow right => exact ⟨rfl,InstantiationRelated.types children.1,True.intro⟩
    | _ => simp [tailKind] at kinds

theorem Discharges.row_residual_interface
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) {left right : Ty} (view : RowInterface a left right) :
    tailKind (RR.residual b (left.instantiate σ)) = tailKind (RR.residual b (right.instantiate σ)) ∧
    Children (InstantiationRelated σ a b)
      (tailChildren (RR.residual b (left.instantiate σ)))
      (tailChildren (RR.residual b (right.instantiate σ))) := by
  have one := Obend.Core.RecursiveRows.discharge_residual_instantiate D left
  have two := Obend.Core.RecursiveRows.discharge_residual_instantiate D right
  have middle := mapped_residual_interface σ a b (RR.residual a left) (RR.residual a right)
    view.residualKind view.residualChildren
  refine ⟨one.tailKind.trans (middle.1.trans two.tailKind.symm),?_⟩
  have front := children_mono (fun _ _ h => InstantiationRelated.existing (σ := σ) (a := a) h)
    (residual_existing_children one)
  have back := children_mono (fun _ _ h => InstantiationRelated.existing (σ := σ) (a := a)
    ((FP.bisimilar_equivalence (graph b)).symm h)) (children_symm (residual_existing_children two))
  exact instantiation_children_trans front (instantiation_children_trans middle.2 back)

theorem Discharges.row_alphabet_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {left right : Ty} (view : RowInterface a left right) :
    RR.labels b (left.instantiate σ) = RR.labels b (right.instantiate σ) := by
  apply Obend.Core.RecursiveRows.sorted_ext _ _
    (Obend.Core.RecursiveRows.scanLabels_sorted b _ (left.instantiate σ))
    (Obend.Core.RecursiveRows.scanLabels_sorted b _ (right.instantiate σ))
  intro label
  change label ∈ RR.labels b (left.instantiate σ) ↔ label ∈ RR.labels b (right.instantiate σ)
  rw [Obend.Core.RecursiveRows.labels_iff_true_emits,Obend.Core.RecursiveRows.labels_iff_true_emits]
  have related : FilteredRelated a label (.source left true) (.source right true) :=
    .source (view.streams label) view.residualKind
  constructor
  · rintro ⟨member,tail,emitted⟩
    obtain ⟨member',tail',found,_⟩ := D.related_stream_emits valid related emitted
    exact ⟨member',tail',found⟩
  · rintro ⟨member,tail,emitted⟩
    obtain ⟨member',tail',found,_⟩ := D.related_stream_emits valid related.symm emitted
    exact ⟨member',tail',found⟩

theorem instantiation_type_children (σ : Nat → Ty) (a b : Assumptions) (xs ys : List Ty)
    (children : Children (FP.Bisimilar (graph a)) (xs.map Node.type) (ys.map Node.type)) :
    Children (InstantiationRelated σ a b)
      (xs.map (fun t => Node.type (t.instantiate σ))) (ys.map (fun t => Node.type (t.instantiate σ))) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [Children]
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys => exact ⟨.types children.1,ih ys children.2⟩

end Obend.Core.Proofs.Templates
