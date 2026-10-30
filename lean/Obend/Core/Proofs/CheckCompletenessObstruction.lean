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

/-! Correct annotations still do not suffice: a branch can use a declarative
conversion that the inference algorithm's exact branch-type comparison refuses. -/

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
        (by simp [sameType, aliasBranch, aliasBranchAnnotation,
          naturalAliasAssumptions, Assumptions.alias,
          Ty.canonical, Ty.isComputation]))
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

theorem aliasBranch_refused (fuel : Nat) : check aliasBranch [] fuel = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel <;>
        simp [check, infer, aliasBranch, aliasBranchAnnotation]

/-- Every annotation lookup succeeds, the sole lambda annotation agrees exactly
with the exhibited derivation, and nevertheless no fuel suffices. -/
public theorem correct_lambda_annotation_still_incomplete :
    (∀ position, aliasBranch.annotations position = some aliasBranchAnnotation) ∧
    aliasBranchChecked.type = .arrow aliasBranchAnnotation.reuse aliasBranchAnnotation.parameter
      aliasBranchAnnotation.domain aliasBranchAnnotation.codomain ∧
    ∀ fuel, check aliasBranch [] fuel = none :=
  ⟨fun _ => rfl, rfl, aliasBranch_refused⟩

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
      (.nil _ _))
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

/-! A later duplicate arm is unreachable under first-match execution. The
relation checks it at its own row entry, whereas the algorithm uses the FIRST
entry for every occurrence of that label. This is a different obstruction from
empty cases and does not involve a missing or false annotation. -/

@[expose] public def duplicateRow : Ty :=
  .field "a" .natural (.field "a" .boolean .emptyRow)

@[expose] public def duplicateInjectionAnnotation : LambdaAnnotation :=
  ⟨.natural, .variant duplicateRow, .unrestricted, .reusable⟩

@[expose] public def unreachableBooleanArm : Term :=
  .ifBool (.bound 0) (.nat 0) (.nat 0)

@[expose] public def duplicateCase : AnnotatedTerm :=
  ⟨.case (.inject "a" (.nat 0)) [("a", .nat 0), ("a", unreachableBooleanArm)],
    fun _ => some duplicateInjectionAnnotation, {}⟩

@[expose] public def duplicateCaseChecked : Checked duplicateCase [] where
  type := .natural
  uses := []
  derivation := .case
    (.inject (fuel := 1) (.natural _ _) (by rfl) rfl)
    (.cons (payload := .natural) (.natural _ _)
      (by simp [safeUses, zeroUses, safeQuantity]) rfl
      (.cons (payload := .boolean)
        (.ifBool (.bound (binding := ⟨.boolean, .unrestricted⟩) (index := 0) (by rfl))
          (.natural _ _) (.natural _ _))
        (by simp [safeUses, variableUses, zeroUses, addUses, safeQuantity])
        rfl (.nil _ _)))
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

theorem booleanArm_at_natural_refused (annotations : Annotations) (position : List Nat)
    (fuel : Nat) :
    infer {} annotations [⟨.natural, .unrestricted⟩] position fuel unreachableBooleanArm = none := by
  cases fuel with
  | zero => rfl
  | succ fuel => cases fuel <;> simp [infer, unreachableBooleanArm]

theorem duplicateArms_refused (position : List Nat) (index : Nat) (expected : Option Ty)
    (fuel : Nat) :
    inferArms {} duplicateCase.annotations [] position index duplicateRow expected fuel
      [("a", .nat 0), ("a", unreachableBooleanArm)] = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel <;>
        simp [inferArms, infer, duplicateRow, Ty.lookup,
          Ty.shareable, safeUses, zeroUses, safeQuantity,
          booleanArm_at_natural_refused]

theorem duplicateCase_refused (fuel : Nat) : check duplicateCase [] fuel = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        have refused := duplicateArms_refused [1] 0 none (fuel + 2)
        simp only [duplicateCase, duplicateInjectionAnnotation, duplicateRow] at refused
        simp [check, infer, duplicateCase, duplicateInjectionAnnotation,
          duplicateRow, Ty.lookup, agree, sameType, Ty.canonical,
          Ty.shareableUnder, Ty.shareable, Ty.isComputation, variantRow, refused]

public theorem annotated_unreachable_arm_still_incomplete :
    Nonempty (Checked duplicateCase []) ∧
    (∀ position, duplicateCase.annotations position = some duplicateInjectionAnnotation) ∧
    ∀ fuel, check duplicateCase [] fuel = none :=
  ⟨⟨duplicateCaseChecked⟩, fun _ => rfl, duplicateCase_refused⟩

#assert_axioms checked_lambda_without_annotations_never_checks
  checked_does_not_imply_eventual_success unannotatedConstant_refused
  annotatedConstant_accepted aliasBranch_refused correct_lambda_annotation_still_incomplete
  emptyCase_refused annotated_empty_eliminator_still_incomplete
  booleanArm_at_natural_refused duplicateArms_refused duplicateCase_refused
  annotated_unreachable_arm_still_incomplete

end Obend.Core.Proofs.CheckCompletenessObstruction
