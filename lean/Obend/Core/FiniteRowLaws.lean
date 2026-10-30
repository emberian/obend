module
public import Obend.Core.RowExposureInvariance
public import Obend.Core.TypeGraphResource
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

private theorem stream_of_observe_eq (a : Assumptions) {x y : Node}
    (same : observe a x = observe a y) : FP.Bisimilar (graph a) x y := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · exact congrArg Prod.fst same
  · change Children _ (observe a x).2 (observe a y).2
    rw [same]
    exact Obend.Core.FiniteBisimulation.children_mono
      (fun x y h => by subst y; exact (FP.bisimilar_equivalence (graph a)).refl x)
      (Obend.Core.FiniteBisimulation.children_refl _)

private theorem field_step (a : Assumptions) (name label : String)
    (first : Bool) (member tail : Ty) :
    RowHit.step a label first (.field name member tail) =
      if name == label && (first || !RR.shareable a member) then
        .emit (member, tail) else .skip tail := by
  simp [RowHit.step, expose, exposeWalk, constructorHead]

theorem field_stream_skip (a : Assumptions) (name label : String)
    (first : Bool) (member tail : Ty)
    (skip : (name == label && (first || !RR.shareable a member)) = false) :
    FP.Bisimilar (graph a) (.stream (.field name member tail) label first)
      (.stream tail label first) := by
  apply stream_of_observe_eq
  apply RowHit.stream_skip_observe_eq
  simp only [field_step, skip, Bool.false_eq_true, ↓reduceIte]

theorem field_stream_emit (a : Assumptions) (name label : String)
    (first : Bool) (member tail : Ty)
    (emit : (name == label && (first || !RR.shareable a member)) = true) :
    observe a (.stream (.field name member tail) label first) =
      (.streamEmit, [.type member, .stream tail label false]) := by
  apply RowHit.stream_emit_observe_eq
  simp only [field_step, emit, ↓reduceIte]

private theorem emit_fusion (a : Assumptions) {x y : Node} {member tail tail' : Ty}
    {label : String}
    (left : observe a x = (.streamEmit,[.type member,.stream tail label false]))
    (right : observe a y = (.streamEmit,[.type member,.stream tail' label false]))
    (tails : FP.Bisimilar (graph a) (.stream tail label false) (.stream tail' label false)) :
    FP.Bisimilar (graph a) x y := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe a x).1 = (observe a y).1
    rw [left,right]
  · change Children _ (observe a x).2 (observe a y).2
    rw [left,right]
    exact ⟨(FP.bisimilar_equivalence (graph a)).refl _,tails,True.intro⟩

theorem stream_commute (a : Assumptions) (name prior label : String)
    (first : Bool) (member old tail : Ty) (different : name ≠ prior) :
    FP.Bisimilar (graph a)
      (.stream (.field name member (.field prior old tail)) label first)
      (.stream (.field prior old (.field name member tail)) label first) := by
  let eqv := FP.bisimilar_equivalence (graph a)
  cases hm : (name == label && (first || !RR.shareable a member)) with
  | false =>
    have leftSkip := field_stream_skip a name label first member (.field prior old tail) hm
    cases ho : (prior == label && (first || !RR.shareable a old)) with
    | false =>
      exact eqv.trans leftSkip (eqv.trans (field_stream_skip a prior label first old tail ho)
        (eqv.symm (eqv.trans (field_stream_skip a prior label first old (.field name member tail) ho)
          (field_stream_skip a name label first member tail hm))))
    | true =>
      have nameOther : name ≠ label := by
        have priorSame : prior = label := by simpa using (Bool.and_eq_true_iff.mp ho).1
        exact fun same => different (same.trans priorSame.symm)
      have hidden : (name == label && (false || !RR.shareable a member)) = false := by simp [nameOther]
      exact eqv.trans leftSkip (emit_fusion a
        (field_stream_emit a prior label first old tail ho)
        (field_stream_emit a prior label first old (.field name member tail) ho)
        (eqv.symm (field_stream_skip a name label false member tail hidden)))
  | true =>
    have priorOther : prior ≠ label := by
      have nameSame : name = label := by simpa using (Bool.and_eq_true_iff.mp hm).1
      exact fun same => different (nameSame.trans same.symm)
    have ho : (prior == label && (first || !RR.shareable a old)) = false := by simp [priorOther]
    have hidden : (prior == label && (false || !RR.shareable a old)) = false := by simp [priorOther]
    exact eqv.trans (emit_fusion a
      (field_stream_emit a name label first member (.field prior old tail) hm)
      (field_stream_emit a name label first member tail hm)
      (field_stream_skip a prior label false old tail hidden))
      (eqv.symm (field_stream_skip a prior label first old (.field name member tail) ho))

theorem stream_shadow (a : Assumptions) (name label : String) (first : Bool)
    (member old tail : Ty) (share : RR.shareable a old = true) :
    FP.Bisimilar (graph a)
      (.stream (.field name member (.field name old tail)) label first)
      (.stream (.field name member tail) label first) := by
  let eqv := FP.bisimilar_equivalence (graph a)
  have hidden : (name == label && (false || !RR.shareable a old)) = false := by simp [share]
  cases hm : (name == label && (first || !RR.shareable a member)) with
  | true =>
    exact emit_fusion a
      (field_stream_emit a name label first member (.field name old tail) hm)
      (field_stream_emit a name label first member tail hm)
      (field_stream_skip a name label false old tail hidden)
  | false =>
    have oldSkip : (name == label && (first || !RR.shareable a old)) = false := by
      cases first <;> simp_all
    exact eqv.trans (field_stream_skip a name label first member (.field name old tail) hm)
      (eqv.trans (field_stream_skip a name label first old tail oldSkip)
        (eqv.symm (field_stream_skip a name label first member tail hm)))

/-- Syntactic shareability never contains a rigid variable, so no assumptions
about aliases or quantified shareability variables are required here. -/
theorem semantic_shareable_of_syntactic (a : Assumptions) (type : Ty)
    (share : type.shareable = true) : RR.shareable a type = true := by
  induction type with
  | field name member tail im it =>
    simp only [Ty.shareable, Bool.and_eq_true] at share
    simp [Obend.Core.RecursiveRows.shareable_field, im share.1, it share.2]
  | specification m e im ie =>
    simp only [Ty.shareable, Bool.and_eq_true] at share
    simp [Obend.Core.RecursiveRows.shareable_specification, im share.1, ie share.2]
  | prototype s t is it =>
    simp only [Ty.shareable, Bool.and_eq_true] at share
    simp [Obend.Core.RecursiveRows.shareable_prototype, is share.1, it share.2]
  | variant row ih => exact (Obend.Core.RecursiveRows.shareable_variant a row).trans (ih share)
  | «variable» | custody | computation => simp [Ty.shareable] at share
  | arrow reuse quantity domain codomain _ _ =>
    simpa only [Ty.shareable,Obend.Core.RecursiveRows.shareable_arrow] using share
  | natural | label | boolean | emptyRow => simp

private theorem fields_equivalent (a : Assumptions) (n n' : String) (m t m' t' : Ty)
    (labels : RR.labels a (.field n m t) = RR.labels a (.field n' m' t'))
    (residual : RR.residual a (.field n m t) = RR.residual a (.field n' m' t'))
    (share : RR.shareable a (.field n m t) = RR.shareable a (.field n' m' t'))
    (streams : ∀ label, FP.Bisimilar (graph a)
      (.stream (.field n m t) label true) (.stream (.field n' m' t') label true)) :
    Equivalent a (.field n m t) (.field n' m' t') := by
  have obs (name : String) (member tail : Ty) :
      observe a (.type (.field name member tail)) = rowObservation a (.field name member tail) := by
    simp [observe, expose, exposeWalk, constructorHead, rowTag]
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe a (.type (.field n m t))).1 = (observe a (.type (.field n' m' t'))).1
    simp only [obs, rowObservation, labels, residual, share]
  · change Children _ (observe a (.type (.field n m t))).2 (observe a (.type (.field n' m' t'))).2
    simp only [obs, rowObservation, rowChildren, ← labels, ← residual]
    have mapped (names : List String) : Children (FP.Bisimilar (graph a))
        (names.map (fun label => .stream (.field n m t) label true) ++ tailChildren (RR.residual a (.field n m t)))
        (names.map (fun label => .stream (.field n' m' t') label true) ++ tailChildren (RR.residual a (.field n m t))) := by
      induction names with
      | nil =>
        simp only [List.map_nil,List.nil_append]
        exact Obend.Core.FiniteBisimulation.children_mono
          (fun x y h => by subst y; exact (FP.bisimilar_equivalence (graph a)).refl x)
          (Obend.Core.FiniteBisimulation.children_refl _)
      | cons label names ih => exact ⟨streams label,ih⟩
    exact mapped _

theorem finite_field_commute (a : Assumptions) (name prior : String)
    (member old tail : Ty) (different : name ≠ prior) :
    Equivalent a (.field name member (.field prior old tail))
      (.field prior old (.field name member tail)) := by
  apply fields_equivalent
  · simp only [Obend.Core.RecursiveRows.labels_field]
    apply Obend.Core.RecursiveRows.sorted_ext
    · apply Obend.Core.RecursiveRows.insertLabel_sorted
      apply Obend.Core.RecursiveRows.insertLabel_sorted
      exact Obend.Core.RecursiveRows.scanLabels_sorted a _ tail
    · apply Obend.Core.RecursiveRows.insertLabel_sorted
      apply Obend.Core.RecursiveRows.insertLabel_sorted
      exact Obend.Core.RecursiveRows.scanLabels_sorted a _ tail
    · intro label
      simp only [Obend.Core.RecursiveRows.mem_insertLabel]
      simp only [or_assoc,or_left_comm,or_comm]
  · simp only [Obend.Core.RecursiveRows.residual_field]
  · simp only [Obend.Core.RecursiveRows.shareable_field]
    cases RR.shareable a member <;> cases RR.shareable a old <;> cases RR.shareable a tail <;> rfl
  · intro label
    exact stream_commute a name prior label true member old tail different

theorem semantic_field_shadow (a : Assumptions) (name : String) (member old tail : Ty)
    (share : RR.shareable a old = true) :
    Equivalent a (.field name member (.field name old tail)) (.field name member tail) := by
  apply fields_equivalent
  · simp only [Obend.Core.RecursiveRows.labels_field]
    apply Obend.Core.RecursiveRows.sorted_ext
    · apply Obend.Core.RecursiveRows.insertLabel_sorted
      apply Obend.Core.RecursiveRows.insertLabel_sorted
      exact Obend.Core.RecursiveRows.scanLabels_sorted a _ tail
    · apply Obend.Core.RecursiveRows.insertLabel_sorted
      exact Obend.Core.RecursiveRows.scanLabels_sorted a _ tail
    · intro label
      simp only [Obend.Core.RecursiveRows.mem_insertLabel]
      simp only [← or_assoc,or_self]
  · simp only [Obend.Core.RecursiveRows.residual_field]
  · simp only [Obend.Core.RecursiveRows.shareable_field,share,Bool.true_and]
  · intro label
    exact stream_shadow a name label true member old tail share

theorem finite_field_shadow (a : Assumptions) (name : String) (member old tail : Ty)
    (oldShare : old.shareable = true) :
    Equivalent a (.field name member (.field name old tail)) (.field name member tail) :=
  semantic_field_shadow a name member old tail (semantic_shareable_of_syntactic a old oldShare)

#assert_axioms field_stream_skip field_stream_emit stream_commute stream_shadow
  semantic_shareable_of_syntactic finite_field_commute semantic_field_shadow finite_field_shadow
end Obend.Core.TypeGraph
