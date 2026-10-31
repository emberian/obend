module
/- The independent source semantics: determinism, derivations, costs. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.Defs
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 public theorem sourceSteps_trans {a b c : Term} (first : Steps a b) (second : Steps b c) : Steps a c := by
  induction first with
  | refl => exact second
  | next step _ ih => exact .next step (ih second)

 theorem source_value_noStep {term next : Term} (value : Value term) (step : Step term next) : False := by
  cases value <;> cases step

set_option maxHeartbeats 600000 in
/-- The independent reference semantics is deterministic for every partial
constructor. This includes fixed-point unfolding and field shadowing. -/
 theorem sourceStep_deterministic {term first second : Term}
    (left : Step term first) (right : Step term second) : first = second := by
  induction left generalizing second <;> cases right
  all_goals first
    | exact False.elim (source_value_noStep (Value.function _) (by assumption))
    | exact False.elim (source_value_noStep (Value.natural _) (by assumption))
    | exact False.elim (source_value_noStep (Value.record _) (by assumption))
    | exact False.elim (source_value_noStep (Value.specification _ _) (by assumption))
    | exact False.elim (source_value_noStep (Value.prototype _ _) (by assumption))
    | exact False.elim (source_value_noStep (Value.inject _ _) (by assumption))
    | exact False.elim (source_value_noStep (Value.boolean _) (by assumption))
    | grind [source_value_noStep]

 theorem source_value_steps_identity {term next : Term} (value : Value term) (steps : Steps term next) : term = next := by
  cases steps with
  | refl => rfl
  | next step _ => exact False.elim (source_value_noStep value step)

 public theorem source_evaluates_unique {source first second : Term}
    (left : Evaluates source first) (right : Evaluates source second) : first = second := by
  obtain ⟨steps,value⟩ := left
  obtain ⟨otherSteps,otherValue⟩ := right
  induction steps generalizing second with
  | refl => exact source_value_steps_identity value otherSteps
  | next step rest ih =>
      cases otherSteps with
      | refl => exact False.elim (source_value_noStep otherValue step)
      | next otherStep otherRest =>
          have aligned := sourceStep_deterministic step otherStep
          cases aligned
          exact ih value otherRest otherValue

/-- A genuine source reduction cannot discard a terminating derivation.
Determinism aligns its first reduction with the independent evaluation trace. -/
 theorem sourceStep_evaluates_tail {source next value : Term}
    (step : Step source next) (evaluates : Evaluates source value) : Evaluates next value := by
  obtain ⟨steps,isValue⟩ := evaluates
  cases steps with
  | refl => exact False.elim (source_value_noStep isValue step)
  | next first rest =>
      have aligned := sourceStep_deterministic step first
      cases aligned
      exact ⟨rest,isValue⟩

 public theorem sourceSteps_evaluates_tail {source next value : Term}
    (steps : Steps source next) (evaluates : Evaluates source value) : Evaluates next value := by
  induction steps with
  | refl => exact evaluates
  | next first rest ih => exact ih (sourceStep_evaluates_tail first evaluates)

public theorem sourceDerivation_hole_false {n : Nat} {payload : List Term} {v : Term} {cost : Nat}
    (d : SourceDerivation (.hole n payload) v cost) : False := by
  obend_cases d with []
  case value h => obend_cases h with []

 theorem sourceSteps_lift (context : Term → Term)
    (compatible : ∀ {first second}, Step first second → Step (context first) (context second))
    {first second : Term} (steps : Steps first second) : Steps (context first) (context second) := by
  induction steps with
  | refl => exact .refl _
  | next first rest ih => exact .next (compatible first) ih

 theorem primitiveResult_value {primitive : Primitive} {left right result : Term}
    (found : primitiveResult primitive left right = some result) : Value result := by
  unfold primitiveResult at found
  split at found <;> cases found
  all_goals first | exact .natural _ | exact .boolean _

/-- Every cost derivation is a genuine evaluation in the independent source
small-step semantics. The value/thunk rules do not force latent fields. -/
 public theorem sourceDerivation_evaluates {source result : Term} {cost : Nat}
    (derivation : SourceDerivation source result cost) : Evaluates source result := by
  induction derivation with
  | value value => exact ⟨.refl _,value⟩
  | applicationLambda first second ihf ihb =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun f => .app f _) (fun step => Step.application _ step) ihf.1)
        (.next (Step.beta _ _) ihb.1),ihb.2⟩
  | applicationSpecification first second ihf ihb =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun f => .app f _) (fun step => Step.application _ step) ihf.1)
        (.next (Step.applySpecification _ _ _) ihb.1),ihb.2⟩
  | mix first ih => exact ⟨.next (Step.mix _ _) ih.1,ih.2⟩
  | fix first ih => exact ⟨.next (Step.fix _ _) ih.1,ih.2⟩
  | reflect first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift Term.reflect Step.reflectStep iht.1)
        (.next (Step.reflectPrototype _ _) ihr.1),ihr.2⟩
  | metadata first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift Term.metadata Step.metadataStep iht.1)
        (.next (Step.metadataSpecification _ _) ihr.1),ihr.2⟩
  | project first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift Term.project Step.projectStep iht.1)
        (.next (Step.projectPrototype _ _) ihr.1),ihr.2⟩
  | field first found second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun t => .get t _) (fun step => Step.target _ step) iht.1)
        (.next (Step.field _ _ _ found) ihr.1),ihr.2⟩
  | extend first iht =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun t => .extend t _) (fun step => Step.extendTarget _ step) iht.1)
        (.next (Step.extendRecord _ _) (.refl _)),Value.record _⟩
  | binary first second found ihl ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun l => .binary _ l _) (fun step => Step.binaryLeft _ _ step) ihl.1)
        (sourceSteps_trans (sourceSteps_lift (fun r => .binary _ _ r) (fun step => Step.binaryRight _ _ ihl.2 step) ihr.1)
          (.next (Step.primitive _ _ _ _ ihl.2 ihr.2 found) (.refl _))),primitiveResult_value found⟩
  | zero first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifZero c _ _) (fun step => Step.condition _ _ step) iht.1)
        (.next (Step.zero _ _) ihr.1),ihr.2⟩
  | successor first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifZero c _ _) (fun step => Step.condition _ _ step) iht.1)
        (.next (Step.successor _ _ _) ihr.1),ihr.2⟩
  | case first found second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun t => .case t _) (fun step => Step.caseTarget _ step) iht.1)
        (.next (Step.caseInject _ _ _ _ found) ihr.1),ihr.2⟩
  | ifTrue first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifBool c _ _) (fun step => Step.ifCondition _ _ step) iht.1)
        (.next (Step.ifTrue _ _) ihr.1),ihr.2⟩
  | ifFalse first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifBool c _ _) (fun step => Step.ifCondition _ _ step) iht.1)
        (.next (Step.ifFalse _ _) ihr.1),ihr.2⟩
  | done first ih => exact ⟨.next (Step.done _) ih.1,ih.2⟩

 public theorem sourceDerivation_cost_positive {source result : Term} {cost : Nat}
    (derivation : SourceDerivation source result cost) : 0 < cost := by
  cases derivation <;> omega

 public theorem sourceDerivation_value_inv {source result : Term} {cost : Nat}
    (value : Value source) (derivation : SourceDerivation source result cost) : result = source ∧ cost = 1 := by
  cases derivation <;> cases value <;> exact ⟨rfl,rfl⟩

/-- Pulling a cost derivation backwards through one real source reduction
strictly increases demand cost. Context reductions retain the latent terms. -/
 theorem sourceStep_derivation_prepend {source next result : Term} {cost : Nat}
    (step : Step source next) (derivation : SourceDerivation next result cost) :
    ∃ larger, SourceDerivation source result larger ∧ cost < larger := by
  induction step generalizing result cost with
  | beta body argument =>
      exact ⟨_,.applicationLambda (.value (.function body)) derivation,by omega⟩
  | mix lower upper => exact ⟨_,.mix derivation,by omega⟩
  | fix spec inherited => exact ⟨_,.fix derivation,by omega⟩
  | applySpecification descriptor extension argument =>
      exact ⟨_,.applicationSpecification (.value (.specification descriptor extension)) derivation,by omega⟩
  | reflectPrototype spec inherited =>
      exact ⟨_,.reflect (.value (.prototype spec inherited)) derivation,by omega⟩
  | metadataSpecification descriptor extension =>
      exact ⟨_,.metadata (.value (.specification descriptor extension)) derivation,by omega⟩
  | projectPrototype spec inherited =>
      exact ⟨_,.project (.value (.prototype spec inherited)) derivation,by omega⟩
  | field fields name body found =>
      exact ⟨_,.field (.value (.record fields)) found derivation,by omega⟩
  | extendRecord inherited fields =>
      obtain ⟨rfl,rfl⟩ := sourceDerivation_value_inv (.record _) derivation
      exact ⟨_,.extend (.value (.record inherited)),by omega⟩
  | primitive primitive left right result lv rv found =>
      obtain ⟨rfl,rfl⟩ := sourceDerivation_value_inv (primitiveResult_value found) derivation
      exact ⟨_,.binary (.value lv) (.value rv) found,by omega⟩
  | zero zero body => exact ⟨_,.zero (.value (.natural 0)) derivation,by omega⟩
  | successor number zero body => exact ⟨_,.successor (.value (.natural _)) derivation,by omega⟩
  | caseInject tag payload arms body found =>
      exact ⟨_,.case (.value (.inject tag payload)) found derivation,by omega⟩
  | ifTrue whenTrue whenFalse => exact ⟨_,.ifTrue (.value (.boolean true)) derivation,by omega⟩
  | ifFalse whenTrue whenFalse => exact ⟨_,.ifFalse (.value (.boolean false)) derivation,by omega⟩
  | done value => exact ⟨_,.done derivation,by omega⟩
  | caseTarget arms step ih =>
      cases derivation with
      | value value => cases value
      | case first found second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.case first' found second,by omega⟩
  | ifCondition whenTrue whenFalse step ih =>
      cases derivation with
      | value value => cases value
      | ifTrue first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.ifTrue first' second,by omega⟩
      | ifFalse first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.ifFalse first' second,by omega⟩
  | application argument step ih =>
      cases derivation with
      | value value => cases value
      | applicationLambda first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.applicationLambda first' second,by omega⟩
      | applicationSpecification first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.applicationSpecification first' second,by omega⟩
  | reflectStep step ih =>
      cases derivation with
      | value value => cases value
      | reflect first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.reflect first' second,by omega⟩
  | metadataStep step ih =>
      cases derivation with
      | value value => cases value
      | metadata first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.metadata first' second,by omega⟩
  | projectStep step ih =>
      cases derivation with
      | value value => cases value
      | project first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.project first' second,by omega⟩
  | target name step ih =>
      cases derivation with
      | value value => cases value
      | field first found second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.field first' found second,by omega⟩
  | extendTarget fields step ih =>
      cases derivation with
      | value value => cases value
      | extend first =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.extend first',by omega⟩
  | binaryLeft primitive right step ih =>
      cases derivation with
      | value value => cases value
      | binary first second found =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.binary first' second found,by omega⟩
  | binaryRight primitive left value step ih =>
      cases derivation with
      | value value => cases value
      | binary first second found =>
          obtain ⟨larger,second',greater⟩ := ih second
          exact ⟨_,.binary first second' found,by omega⟩
  | condition zero body step ih =>
      cases derivation with
      | value value => cases value
      | zero first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.zero first' second,by omega⟩
      | successor first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.successor first' second,by omega⟩

/-- Cost derivations characterize the given independent source semantics;
their existence does not restrict the partial source domain. -/
 public theorem source_evaluates_derivation {source result : Term} (evaluates : Evaluates source result) :
    ∃ cost, SourceDerivation source result cost := by
  obtain ⟨steps,value⟩ := evaluates
  induction steps with
  | refl => exact ⟨1,.value value⟩
  | next first rest ih =>
      obtain ⟨cost,derivation⟩ := ih value
      obtain ⟨larger,previous,_⟩ := sourceStep_derivation_prepend first derivation
      exact ⟨larger,previous⟩

 theorem source_evaluates_iff_derivation {source result : Term} :
    Evaluates source result ↔ ∃ cost, SourceDerivation source result cost := by
  exact ⟨source_evaluates_derivation,fun ⟨_,derivation⟩ => sourceDerivation_evaluates derivation⟩

 theorem sourceDerivation_result_unique {source first second : Term} {firstCost secondCost : Nat}
    (left : SourceDerivation source first firstCost) (right : SourceDerivation source second secondCost) :
    first = second :=
  source_evaluates_unique (sourceDerivation_evaluates left) (sourceDerivation_evaluates right)

set_option maxHeartbeats 600000 in
/-- Demand cost is determined by the partial source computation, even when
there are multiple proofs of its evaluation. -/
 public theorem sourceDerivation_cost_unique {source first second : Term} {firstCost secondCost : Nat}
    (left : SourceDerivation source first firstCost) (right : SourceDerivation source second secondCost) :
    firstCost = secondCost := by
  induction left generalizing second secondCost <;> cases right
  all_goals try rfl
  all_goals try (cases ‹Value _›)
  all_goals grind [sourceDerivation_result_unique]

/-- Every real source reduction consumes a positive part of the unique finite
demand budget. This is the semantic component of the lazy graph progress rank. -/
 public theorem sourceStep_derivation_tail {source next result : Term} {cost : Nat}
    (step : Step source next) (derivation : SourceDerivation source result cost) :
    ∃ smaller, SourceDerivation next result smaller ∧ smaller < cost := by
  obtain ⟨smaller,tail⟩ := source_evaluates_derivation
    (sourceStep_evaluates_tail step (sourceDerivation_evaluates derivation))
  obtain ⟨larger,previous,greater⟩ := sourceStep_derivation_prepend step tail
  have aligned := sourceDerivation_cost_unique previous derivation
  exact ⟨smaller,tail,aligned ▸ greater⟩

 public theorem sourceSteps_derivation_tail {source next result : Term} {cost : Nat}
    (steps : Steps source next) (derivation : SourceDerivation source result cost) :
    ∃ smaller, SourceDerivation next result smaller ∧ smaller ≤ cost := by
  induction steps generalizing cost with
  | refl => exact ⟨cost,derivation,Nat.le_refl _⟩
  | next first rest ih =>
      obtain ⟨middle,tail,less⟩ := sourceStep_derivation_tail first derivation
      obtain ⟨smaller,last,le⟩ := ih tail
      exact ⟨smaller,last,Nat.le_trans le (Nat.le_of_lt less)⟩

 public theorem sourceSteps_derivation_strict {source next result : Term} {cost : Nat}
    (steps : Steps source next) (different : source ≠ next)
    (derivation : SourceDerivation source result cost) :
    ∃ smaller, SourceDerivation next result smaller ∧ smaller < cost := by
  cases steps with
  | refl => exact False.elim (different rfl)
  | next first rest =>
      obtain ⟨middle,tail,less⟩ := sourceStep_derivation_tail first derivation
      obtain ⟨smaller,last,le⟩ := sourceSteps_derivation_tail rest tail
      exact ⟨smaller,last,Nat.lt_of_le_of_lt le less⟩

end Obend.Core.Proofs.Adequacy
