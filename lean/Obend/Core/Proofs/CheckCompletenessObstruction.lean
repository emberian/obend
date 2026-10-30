module
/-
Counterexamples to completeness of `check` for its certificate type `Checked`.
Fuel bounds procedure, but annotations and the algorithmic fragment are independent
obstructions. This leaf changes no checker or calculus interface.
-/
public import Obend.Core.Check
public import Obend.AxiomPin

namespace Obend.Core.Proofs.CheckCompletenessObstruction
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
set_option autoImplicit false

@[expose] public def naturalAnnotation : LambdaAnnotation :=
  ⟨.natural, .natural, .unrestricted, .reusable⟩

@[expose] public def unannotatedConstant : AnnotatedTerm :=
  ⟨.lam (.nat 0), fun _ => none, {}⟩

/-- This is an actual certificate, including all top-level validity premises. -/
@[expose] public def unannotatedConstantChecked : Checked unannotatedConstant [] where
  type := .arrow .reusable .unrestricted .natural .natural
  uses := []
  derivation := .lambda (annotation := naturalAnnotation) (.natural _ _)
    (by simp [naturalAnnotation, safeUses, zeroUses, safeQuantity])
    (by simp [naturalAnnotation, validContext, Ty.shareableUnder, Ty.shareable])
    (by simp [naturalAnnotation, reusableAllowed, reusableCaptures, zeroUses])
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

theorem unannotatedConstant_refused (fuel : Nat) :
    check unannotatedConstant [] fuel = none := by
  cases fuel <;> simp [check, infer, unannotatedConstant]

/-- A closed, semantically typed lambda with no annotations is refused at EVERY
fuel. Existence of `Checked` is strictly weaker than eventual checker success. -/
public theorem checked_lambda_without_annotations_never_checks :
    ∃ source : AnnotatedTerm,
      source.term = .lam (.nat 0) ∧
      source.annotations = (fun _ => none) ∧
      (∃ certificate : Checked source [],
        certificate.type = .arrow .reusable .unrestricted .natural .natural) ∧
      ∀ fuel, check source [] fuel = none :=
  ⟨unannotatedConstant, rfl, rfl, ⟨unannotatedConstantChecked, rfl⟩,
    unannotatedConstant_refused⟩

public theorem checked_does_not_imply_eventual_success :
    ¬ (∀ (source : AnnotatedTerm) (context : Context),
      Nonempty (Checked source context) → ∃ fuel, (check source context fuel).isSome = true) := by
  intro complete
  obtain ⟨fuel, accepted⟩ := complete unannotatedConstant [] ⟨unannotatedConstantChecked⟩
  simp [unannotatedConstant_refused] at accepted

/-- Repairing the missing annotation makes this particular fixture check. -/
@[expose] public def annotatedConstant : AnnotatedTerm :=
  { unannotatedConstant with annotations := fun _ => some naturalAnnotation }

theorem annotatedConstant_accepted :
    (check annotatedConstant [] 2).isSome = true := by
  simp [check, infer, annotatedConstant, unannotatedConstant, naturalAnnotation,
    agree, sameType, Ty.canonical, Ty.shareable,
    safeUses, zeroUses, safeQuantity, validContext, reusableAllowed,
    reusableCaptures, Assumptions.valid]

/-! Correct annotations used not to suffice: a branch could use a declarative
conversion that the algorithm's exact branch-type comparison refused. The join now
converts (`agree`), and the example checks. -/

@[expose] public def naturalAliasAssumptions : Assumptions :=
  ⟨[(0, .natural)], [0], []⟩

@[expose] public def aliasBranchAnnotation : LambdaAnnotation :=
  ⟨.variable 0, .natural, .unrestricted, .reusable⟩

@[expose] public def aliasBranch : AnnotatedTerm :=
  ⟨.lam (.ifBool (.boolean true) (.bound 0) (.nat 0)),
    fun _ => some aliasBranchAnnotation, naturalAliasAssumptions⟩

@[expose] public def aliasBranchChecked : Checked aliasBranch [] where
  type := .arrow .reusable .unrestricted (.variable 0) .natural
  uses := []
  derivation := .lambda (annotation := aliasBranchAnnotation)
    (.ifBool (.boolean _ _)
      (.conversion (.bound (binding := ⟨.variable 0, .unrestricted⟩) (index := 0) (by rfl))
        (by decide))
      (.natural _ _))
    (by simp [aliasBranchAnnotation, safeUses, zeroUses, variableUses,
      addUses, safeQuantity])
    (by simp [aliasBranch, aliasBranchAnnotation, naturalAliasAssumptions, validContext,
      Ty.shareableUnder])
    (by simp [aliasBranchAnnotation, reusableAllowed, reusableCaptures,
      zeroUses, variableUses, addUses])
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

/-- Since the branch join converts through `agree` (2026-10-30), the correctly annotated
lambda checks, at the type the exhibited derivation has. -/
theorem aliasBranch_accepted :
    (check aliasBranch [] 4).map (fun checked => checked.type) = some aliasBranchChecked.type := by decide

/-- The former counterexample `correct_lambda_annotation_still_incomplete`, negated: a
correct annotation now suffices for this lambda. -/
public theorem correct_lambda_annotation_now_checks :
    (∀ position, aliasBranch.annotations position = some aliasBranchAnnotation) ∧
    ¬ ∀ fuel, check aliasBranch [] fuel = none := by
  refine ⟨fun _ => rfl, fun refused => ?_⟩
  have := aliasBranch_accepted
  rw [refused 4] at this
  cases this

/-! Empty variants have a semantic eliminator at any result type. The
algorithm refuses empty arm lists because there is no result type to infer. -/

@[expose] public def emptyCaseAnnotation : LambdaAnnotation :=
  ⟨.variant .emptyRow, .natural, .unrestricted, .reusable⟩

@[expose] public def emptyCase : AnnotatedTerm :=
  ⟨.lam (.case (.bound 0) []), fun _ => some emptyCaseAnnotation, {}⟩

@[expose] public def emptyCaseChecked : Checked emptyCase [] where
  type := .arrow .reusable .unrestricted (.variant .emptyRow) .natural
  uses := []
  derivation := .lambda (annotation := emptyCaseAnnotation)
    (.case (.bound (binding := ⟨.variant .emptyRow, .unrestricted⟩) (index := 0) (by rfl))
      (.nil _ _) rfl)
    (by simp [emptyCaseAnnotation, safeUses, variableUses, zeroUses, addUses, safeQuantity])
    (by simp [emptyCaseAnnotation, validContext, Ty.shareableUnder, Ty.shareable])
    (by simp [emptyCaseAnnotation, reusableAllowed, reusableCaptures,
      variableUses, zeroUses, addUses])
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

theorem emptyCase_refused (fuel : Nat) : check emptyCase [] fuel = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel <;>
        simp [check, infer, inferArms, variantRow, emptyCase, emptyCaseAnnotation]

public theorem annotated_empty_eliminator_still_incomplete :
    Nonempty (Checked emptyCase []) ∧
    (∀ position, emptyCase.annotations position = some emptyCaseAnnotation) ∧
    ∀ fuel, check emptyCase [] fuel = none :=
  ⟨⟨emptyCaseChecked⟩, fun _ => rfl, emptyCase_refused⟩

/-! A later duplicate arm is unreachable under first-match execution. The relation used
to check it at its own row entry, whose payload no scrutinee determines; since
2026-10-30 both judgments refuse a case whose arms repeat a label (`labelsDistinct`),
so this obstruction is retired by the relation, not by the checker. -/

@[expose] public def duplicateRow : Ty :=
  .field "a" .natural (.field "a" .boolean .emptyRow)

@[expose] public def duplicateInjectionAnnotation : LambdaAnnotation :=
  ⟨.natural, .variant duplicateRow, .unrestricted, .reusable⟩

@[expose] public def unreachableBooleanArm : Term :=
  .ifBool (.bound 0) (.nat 0) (.nat 0)

@[expose] public def duplicateCase : AnnotatedTerm :=
  ⟨.case (.inject "a" (.nat 0)) [("a", .nat 0), ("a", unreachableBooleanArm)],
    fun _ => some duplicateInjectionAnnotation, {}⟩

/-- Every derivation of a case, through any number of conversions, has distinct labels. -/
public theorem case_labels_distinct {assumptions : Assumptions} {context : Context}
    {scrutinee : Term} {arms : List (String × Term)} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context (.case scrutinee arms) type uses) :
    labelsDistinct arms = true := by
  refine (PartialTyping.rec
    (motive_1 := fun _ term _ _ _ => ∀ s a, term = Term.case s a → labelsDistinct a = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed) _ _ rfl
  all_goals intros
  all_goals first | trivial | simp_all

/-- The duplicate-arm program has no certificate at all, so no checker is incomplete on it. -/
public theorem duplicate_arms_have_no_derivation : ¬ Nonempty (Checked duplicateCase []) := by
  rintro ⟨checked⟩
  have := case_labels_distinct checked.derivation
  simp [duplicateCase, AnnotatedTerm.erase, labelsDistinct] at this

theorem duplicateCase_refused (fuel : Nat) : check duplicateCase [] fuel = none := by
  cases h : check duplicateCase [] fuel with
  | none => rfl
  | some checked => exact (duplicate_arms_have_no_derivation ⟨checked⟩).elim

#assert_axioms checked_lambda_without_annotations_never_checks
  checked_does_not_imply_eventual_success unannotatedConstant_refused
  annotatedConstant_accepted aliasBranch_accepted correct_lambda_annotation_now_checks
  emptyCase_refused annotated_empty_eliminator_still_incomplete
  case_labels_distinct duplicate_arms_have_no_derivation duplicateCase_refused

end Obend.Core.Proofs.CheckCompletenessObstruction
