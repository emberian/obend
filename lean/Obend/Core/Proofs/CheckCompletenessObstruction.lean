module
/-
Counterexamples to completeness of `check` for its certificate type `Checked`.
Fuel bounds procedure, but annotations and the algorithmic fragment are independent
obstructions. This leaf changes no checker or calculus interface.
-/
public import Obend.Core.Check
public import Obend.Core.Bidirectional

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
    (by simp [naturalAnnotation, safeUses, zeroUses, safeQuantity, Quantity.fits, linearFree])
    (by simp [naturalAnnotation, validContext, Ty.shareableUnder, Ty.shareable])
    (by simp [naturalAnnotation, reusableAllowed, reusableCaptures, zeroUses])
    rfl
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
    agree, sameType_refl, Ty.canonical, Ty.shareable,
    safeUses, zeroUses, safeQuantity, Quantity.fits, linearFree, validContext, reusableAllowed,
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

/-- The concrete alias equation uses the certified extension of the old checker,
not reduction of the finite graph decision. -/
@[simp] public theorem naturalAlias_agrees :
    sameType (⟨[(0, .natural)], [0], []⟩ : Assumptions) (.variable 0) .natural = true :=
  sameType_extends (by decide)

@[simp] public theorem naturalAlias_agrees_reverse :
    sameType (⟨[(0, .natural)], [0], []⟩ : Assumptions) .natural (.variable 0) = true :=
  sameType_symm naturalAlias_agrees

@[expose] public def aliasBranchChecked : Checked aliasBranch [] where
  type := .arrow .reusable .unrestricted (.variable 0) .natural
  uses := []
  derivation := .lambda (annotation := aliasBranchAnnotation)
    (.ifBool (.boolean _ _)
      (.conversion (.bound (binding := ⟨.variable 0, .unrestricted⟩) (index := 0) (by rfl))
        (naturalAlias_agrees))
      (.natural _ _))
    (by simp [aliasBranchAnnotation, safeUses, zeroUses, variableUses,
      addUses, safeQuantity, Quantity.fits, linearFree])
    (by simp [aliasBranch, aliasBranchAnnotation, naturalAliasAssumptions, validContext,
      Ty.shareableUnder])
    (by simp [aliasBranchAnnotation, reusableAllowed, reusableCaptures,
      zeroUses, variableUses, addUses])
    rfl
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

/-- Since the branch join converts through `agree` (2026-10-30), the correctly annotated
lambda checks, at the type the exhibited derivation has. -/
theorem aliasBranch_accepted :
    (check aliasBranch [] 4).map (fun checked => checked.type) = some aliasBranchChecked.type := by
  simp [check, infer, aliasBranch, aliasBranchAnnotation, aliasBranchChecked,
    agree, sameType_refl, naturalAlias_agrees, naturalAlias_agrees_reverse,
    safeUses, zeroUses, variableUses, addUses, safeQuantity, Quantity.fits, linearFree, validContext,
    Ty.shareableUnder, Ty.shareable, Ty.isComputation, reusableAllowed, reusableCaptures,
    naturalAliasAssumptions, Assumptions.valid]

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
    (by simp [emptyCaseAnnotation, safeUses, variableUses, zeroUses, addUses, safeQuantity, Quantity.fits, linearFree])
    (by simp [emptyCaseAnnotation, validContext, Ty.shareableUnder, Ty.shareable])
    (by simp [emptyCaseAnnotation, reusableAllowed, reusableCaptures,
      variableUses, zeroUses, addUses])
    rfl
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
  -- A constructor other than `case` or a conversion meets `term = .case s a` as a constructor
  -- clash: `cases` closes it at once (`trivial`'s `contradiction` took 150 ms a goal here).
  all_goals first | exact True.intro | (rename_i h; cases h; done) | simp_all

/-- The duplicate-arm program has no certificate at all, so no checker is incomplete on it. -/
public theorem duplicate_arms_have_no_derivation : ¬ Nonempty (Checked duplicateCase []) := by
  rintro ⟨checked⟩
  have := case_labels_distinct checked.derivation
  simp [duplicateCase, AnnotatedTerm.erase, labelsDistinct] at this

theorem duplicateCase_refused (fuel : Nat) : check duplicateCase [] fuel = none := by
  cases h : check duplicateCase [] fuel with
  | none => rfl
  | some checked => exact (duplicate_arms_have_no_derivation ⟨checked⟩).elim

/-! ## Expected checking and local representative annotations

The historical `check` fixtures above retain their original annotation maps.
The bidirectional checker reads representatives at every relevant position, so a
lambda annotation must not accidentally become an operand annotation below it.
The following maps put representatives only where that rule consumes them. -/

@[expose] public def aliasBranchBidirectional : AnnotatedTerm :=
  { aliasBranch with annotations := fun path =>
      if path = [] then some aliasBranchAnnotation else none }

@[expose] public def emptyCaseBidirectional : AnnotatedTerm :=
  { emptyCase with annotations := fun path =>
      if path = [] ∨ path = [0] then some emptyCaseAnnotation else none }

@[expose] public def duplicateCaseBidirectional : AnnotatedTerm :=
  { duplicateCase with annotations := fun path =>
      if path = [0] then some duplicateInjectionAnnotation else none }

-- Simplify the checker algebra and established agreement laws; the graph
-- decision itself is deliberately opaque in these regression proofs.
local macro "obstruction_check" : tactic => `(tactic|
  simp [bind, Except.bind, Functor.map, Except.map, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw, Except.toOption, List.getElem?_cons_zero, Bidirectional.checkAgainst, Bidirectional.infer,
    Bidirectional.checkAt, Bidirectional.synthAt, Bidirectional.elaborate,
    Bidirectional.checkArms, Bidirectional.introduce, Bidirectional.finish,
    Bidirectional.ascribe, Bidirectional.checkedSynth, Bidirectional.need,
    Bidirectional.representativeHead, Bidirectional.injectionHead, Bidirectional.whnf,
    Assumptions.chase, Assumptions.unfoldHead, sameType_refl,
    naturalAlias_agrees, naturalAlias_agrees_reverse,
    unannotatedConstant, unannotatedConstantChecked, naturalAnnotation,
    aliasBranchBidirectional, aliasBranch, aliasBranchChecked, aliasBranchAnnotation,
    emptyCaseBidirectional, emptyCase, emptyCaseChecked, emptyCaseAnnotation,
    duplicateCaseBidirectional, duplicateCase, duplicateInjectionAnnotation, duplicateRow,
    lookupV, lookupW, unvisited, walkRow, Ty.isComputation, Ty.canonical,
    safeUses, safeQuantity, Quantity.fits, linearFree, validContext, reusableAllowed, reusableCaptures,
    zeroUses, variableUses, addUses, Ty.shareableUnder, Ty.shareable,
    Assumptions.valid, naturalAliasAssumptions, labelsDistinct])

/-- An absent annotation permits expected-directed checking. -/
theorem unannotatedConstant_checks :
    (Bidirectional.checkAgainst unannotatedConstant [] unannotatedConstantChecked.type).toOption.map (·.type) =
      some unannotatedConstantChecked.type := by obstruction_check

/-- Synthesis still names the missing lambda annotation. -/
theorem unannotatedConstant_synthesis_names_annotation :
    (match Bidirectional.infer unannotatedConstant [] with
      | .error refusal => some refusal
      | .ok _ => none) = some (.missingLambdaAnnotation []) := by obstruction_check

theorem aliasBranch_checks :
    (Bidirectional.checkAgainst aliasBranchBidirectional [] aliasBranchChecked.type).toOption.isSome = true := by
  obstruction_check

/-- The empty case has its operand representative and result hint at its own path. -/
theorem emptyCase_checks :
    (Bidirectional.checkAgainst emptyCaseBidirectional [] emptyCaseChecked.type).toOption.isSome = true := by
  obstruction_check

theorem duplicateCase_names_duplicate_labels :
    (match Bidirectional.checkAgainst duplicateCaseBidirectional [] .natural with
      | .error refusal => some refusal
      | .ok _ => none) = some (.duplicateLabels []) := by obstruction_check

@[expose] public def wrongConstantAnnotation : LambdaAnnotation :=
  ⟨.natural, .computation .natural .natural .natural, .unrestricted, .reusable⟩

/-- Expected checking does not erase an explicitly wrong representative. -/
@[expose] public def wrongAnnotationConstant : AnnotatedTerm :=
  { unannotatedConstant with annotations := fun path =>
      if path = [] then (Option.some wrongConstantAnnotation) else Option.none }

theorem wrong_annotation_residue :
    (match Bidirectional.checkAgainst wrongAnnotationConstant [] unannotatedConstantChecked.type with
      | .error refusal => some refusal
      | .ok _ => none) =
      some (.typeMismatch [0] (.computation .natural .natural .natural) .natural) := by
  have mismatch : sameType ({} : Assumptions) .natural
      (.computation .natural .natural .natural) = false := by
    cases equation : sameType ({} : Assumptions) .natural (.computation .natural .natural .natural)
    · rfl
    · have activity := sameType_isComputation equation
      cases activity
  simp [bind, Except.bind, Functor.map, Except.map, pure, Except.pure,
    throw, Except.toOption, wrongAnnotationConstant, wrongConstantAnnotation, mismatch,
    Bidirectional.checkAgainst, Bidirectional.checkAt, Bidirectional.elaborate,
    Bidirectional.finish, unannotatedConstant, unannotatedConstantChecked]

end Obend.Core.Proofs.CheckCompletenessObstruction
