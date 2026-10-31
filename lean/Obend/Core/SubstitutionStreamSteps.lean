module
public import Obend.Core.ResourceSubstitution
public import Obend.Core.RowHit
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
namespace Search
export Obend.Core.RowSearch (Step Hit SkipPath)
end Search
set_option autoImplicit false

/-- Every source epsilon field remains an epsilon field. The only resource
premise needed is preservation of source-true shareability. -/
theorem Discharges.stream_step_skip_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row tail : Ty} {label : String} {first : Bool}
    (skipped : RowHit.step a label first row = .skip tail) :
    RowHit.step b label first (row.instantiate σ) = .skip (tail.instantiate σ) := by
  rw [RowHit.step] at skipped
  split at skipped
  · rename_i observation exposed
    split at skipped
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name,[member,fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at skipped
      · contradiction
      · rename_i notmatched
        have sameTail : fieldTail = tail := Obend.Core.RowSearch.Step.skip.inj skipped
        subst tail
        have targetSkip : (name == label && (first || !RR.shareable b (member.instantiate σ))) = false := by
          cases named : (name == label) with
          | false => simp [named]
          | true =>
            have invisible : first = false := by cases first <;> simp_all
            have sourceSafe : RR.shareable a member = true := by
              cases resource : RR.shareable a member <;> simp_all
            have imageSafe : RR.shareable b (member.instantiate σ) = true :=
              D.semantic_shareable_instantiate valid sourceSafe
            simp [invisible,imageSafe]
        have mapped := D.expose_instantiate_constructor exposed
        simp [RowHit.step,mapped,targetSkip]
    · contradiction
  · contradiction

/-- A source emission determines the exact mapped field observation, before
choosing whether the instantiated hidden member is emitted or skipped. -/
theorem Discharges.stream_step_emit_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) {row member tail : Ty} {label : String} {first : Bool}
    (emitted : RowHit.step a label first row = .emit (member,tail)) :
    RowHit.step b label first (row.instantiate σ) =
      if first || !RR.shareable b (member.instantiate σ) then
        .emit (member.instantiate σ,tail.instantiate σ) else .skip (tail.instantiate σ) := by
  rw [RowHit.step] at emitted
  split at emitted
  · rename_i observation exposed
    split at emitted
    · rename_i name fieldMember fieldTail tag children
      have shape : observation = ⟨.field name,[fieldMember,fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at emitted
      · rename_i matched
        have named : (name == label) = true := (Bool.and_eq_true_iff.mp matched).1
        have same := Obend.Core.RowSearch.Step.emit.inj emitted
        have memberSame : fieldMember = member := congrArg Prod.fst same
        have tailSame : fieldTail = tail := congrArg Prod.snd same
        subst fieldMember
        subst fieldTail
        have mapped := D.expose_instantiate_constructor exposed
        simp [RowHit.step,mapped,named]
      · contradiction
    · contradiction
  · contradiction

theorem Discharges.stream_path_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row tail : Ty} {label : String} {first : Bool}
    (path : Search.SkipPath (RowHit.step a label first) row tail) :
    Search.SkipPath (RowHit.step b label first) (row.instantiate σ) (tail.instantiate σ) := by
  induction path with
  | refl row => exact .refl _
  | cons row next tail observed nested ih =>
    exact .cons _ _ _ (D.stream_step_skip_instantiate valid observed) ih

theorem Discharges.stream_hit_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row : Ty} {payload : Ty × Ty} {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step a label first) row payload n)
    (retained : (first || !RR.shareable b (payload.1.instantiate σ)) = true) :
    Search.Hit (RowHit.step b label first) (row.instantiate σ)
      (payload.1.instantiate σ,payload.2.instantiate σ) n := by
  revert retained
  induction hit with
  | emit row payload observed =>
    intro retained
    cases payload with
    | mk member tail =>
      apply Obend.Core.RowSearch.Hit.emit
      simpa only [retained,↓reduceIte] using D.stream_step_emit_instantiate observed
  | skip row next payload n observed nested ih =>
    intro retained
    exact .skip _ _ _ n (D.stream_step_skip_instantiate valid observed) (ih retained)

/-- A newly safe source emission becomes one more target epsilon step, after
all already invisible fields in its finite source hit path. -/
theorem Discharges.stream_hit_hidden_path
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row : Ty} {payload : Ty × Ty} {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step a label first) row payload n)
    (hidden : (first || !RR.shareable b (payload.1.instantiate σ)) = false) :
    Search.SkipPath (RowHit.step b label first) (row.instantiate σ) (payload.2.instantiate σ) := by
  revert hidden
  induction hit with
  | emit row payload observed =>
    intro hidden
    cases payload with
    | mk member tail =>
      apply Obend.Core.RowSearch.SkipPath.cons _ _ _ _ (.refl _)
      simpa only [hidden,Bool.false_eq_true,↓reduceIte] using D.stream_step_emit_instantiate observed
  | skip row next payload n observed nested ih =>
    intro hidden
    exact .cons _ _ _ (D.stream_step_skip_instantiate valid observed) (ih hidden)

end Obend.Core.Proofs.Templates
