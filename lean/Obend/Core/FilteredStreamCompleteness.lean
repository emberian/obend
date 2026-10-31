module
public import Obend.Core.FilteredStreamSteps
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

private theorem stream_stop_after_constructor_map
    {a b : Assumptions} {σ : Nat → Ty} {row : Ty} {c : Constructor}
    {label : String} {first : Bool}
    (source : expose a row = .constructor c)
    (target : expose b (row.instantiate σ) = .constructor ⟨c.tag,c.children.map (Ty.instantiate σ)⟩)
    (stopped : RowHit.step a label first row = .stop) :
    RowHit.step b label first (row.instantiate σ) = .stop := by
  cases tag : c.tag <;> try simp [RowHit.step,target,tag]
  case field name =>
    cases children : c.children with
    | nil => simp [RowHit.step,target,tag,children]
    | cons member rest =>
      cases rest with
      | nil => simp [RowHit.step,target,tag,children]
      | cons tail rest =>
        cases rest with
        | cons x xs => simp [RowHit.step,target,tag,children]
        | nil =>
          simp only [RowHit.step,source,tag,children] at stopped
          split at stopped <;> contradiction

/-- Every finite actual emission has a finite path in the filtered source
machine. The induction consumes actual epsilon steps; old source epsilons
are compressed, and newly safe emissions become explicit filtered skips. -/
theorem Discharges.image_hit_filtered
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {source member tail : Ty} {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step b label first) (source.instantiate σ) (member,tail) n) :
    ∃ next k, Search.Hit (filteredStep σ a b label) (.source source first) (member,next) k ∧
      filteredRow σ next = tail ∧ filteredFirst next = false := by
  cases sourceStep : RowHit.step a label first source with
  | skip sourceTail =>
    have targetStep := D.stream_step_skip_instantiate valid sourceStep
    cases hit with
    | emit _ _ observed => rw [targetStep] at observed; contradiction
    | skip _ actualTail _ count observed nested =>
      have same : actualTail = sourceTail.instantiate σ := by
        exact Obend.Core.RowSearch.Step.skip.inj (observed.symm.trans targetStep)
      subst actualTail
      obtain ⟨next,k,filtered,row,mode⟩ := D.image_hit_filtered valid nested
      have compressed := filteredStep_source_skip σ a b sourceStep
      exact ⟨next,k,Obend.Core.RowSearch.hit_of_step_eq compressed.symm filtered,row,mode⟩
  | emit payload =>
    cases payload with
    | mk sourceMember sourceTail =>
      have targetStep := D.stream_step_emit_instantiate sourceStep
      have macroStep := filteredStep_source_emit σ a b sourceStep
      cases retained : (first || !RR.shareable b (sourceMember.instantiate σ)) with
      | true =>
        simp only [retained,↓reduceIte] at targetStep macroStep
        cases hit with
        | skip _ actualTail _ count observed nested => rw [targetStep] at observed; contradiction
        | emit _ _ observed =>
          have same := Obend.Core.RowSearch.Step.emit.inj (targetStep.symm.trans observed)
          have sameMember : sourceMember.instantiate σ = member := congrArg Prod.fst same
          have sameTail : sourceTail.instantiate σ = tail := congrArg Prod.snd same
          subst member
          subst tail
          exact ⟨.source sourceTail false,0,.emit _ _ macroStep,rfl,rfl⟩
      | false =>
        have hidden : first = false := by cases first <;> simp_all
        subst first
        simp only [retained,Bool.false_eq_true,↓reduceIte] at targetStep macroStep
        cases hit with
        | emit _ _ observed => rw [targetStep] at observed; contradiction
        | skip _ actualTail _ count observed nested =>
          have same : actualTail = sourceTail.instantiate σ :=
            Obend.Core.RowSearch.Step.skip.inj (observed.symm.trans targetStep)
          subst actualTail
          obtain ⟨next,k,filtered,row,mode⟩ := D.image_hit_filtered valid nested
          exact ⟨next,k + 1,.skip _ _ _ k macroStep filtered,row,mode⟩
  | stop =>
    cases sourceHead : expose a source with
    | nominal index =>
      have mapped := D.expose_instantiate_nominal sourceHead
      have same : RowHit.step b label first (source.instantiate σ) = RowHit.step b label first (σ index) := by
        unfold RowHit.step
        rw [mapped]
      have imageHit := Obend.Core.RowSearch.hit_of_step_eq same hit
      have expanded := expanded_hit σ a b imageHit
      have macroStep := filteredStep_source_nominal σ a b (label := label) (first := first) sourceHead
      exact ⟨.expanded tail false,n + 1,.skip _ _ _ n macroStep expanded,rfl,rfl⟩
    | unproductive representative =>
      have mapped := D.expose_instantiate_unproductive sourceHead
      have stopped : RowHit.step b label first (source.instantiate σ) = .stop := by
        simp [RowHit.step,mapped]
      cases hit with
      | emit _ _ observed => rw [stopped] at observed; contradiction
      | skip _ _ _ _ observed _ => rw [stopped] at observed; contradiction
    | constructor c =>
      have stopped := stream_stop_after_constructor_map sourceHead
        (D.expose_instantiate_constructor sourceHead) sourceStep
      cases hit with
      | emit _ _ observed => rw [stopped] at observed; contradiction
      | skip _ _ _ _ observed _ => rw [stopped] at observed; contradiction
termination_by n
decreasing_by
  all_goals
    have current : n = count + 1 := by assumption
    omega

end Obend.Core.Proofs.Templates
