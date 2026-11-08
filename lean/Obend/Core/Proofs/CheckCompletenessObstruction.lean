module
/-
Where the checker meets its certificate type `Checked`: fixtures that once refuted the completeness
of the retired annotation-directed checker (`Check.check`, retired 2026-11-01), with what the
bidirectional checker does on each. Synthesis on a fixed source is still incomplete (an unannotated
lambda); checking at the certificate's type accepts it, and the alias-branch and empty-eliminator
obstructions are gone. Full completeness under prepared annotations is
`BidirectionalCompleteness.full_annotated`. This leaf changes no checker or calculus interface.
-/
public import Obend.Core.Check
public import Obend.Core.Bidirectional
import all Obend.Core.Check

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
    (by simp [naturalAnnotation, safeUses, zeroUses, safeQuantity, Quantity.fits, linearFree, joinUses, branchesAgree, Quantity.agrees])
    (by simp [naturalAnnotation, validContext, Ty.shareableUnder, Ty.shareable])
    (by simp [naturalAnnotation, reusableAllowed, reusableCaptures, zeroUses])
    rfl
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

/-- Repairing the missing annotation makes this particular fixture check. -/
@[expose] public def annotatedConstant : AnnotatedTerm :=
  { unannotatedConstant with annotations := fun _ => some naturalAnnotation }

@[expose] public def naturalAliasAssumptions : Assumptions :=
  ⟨[(0, .natural)], [0], [], []⟩

@[expose] public def aliasBranchAnnotation : LambdaAnnotation :=
  ⟨.variable 0, .natural, .unrestricted, .reusable⟩

@[expose] public def aliasBranch : AnnotatedTerm :=
  ⟨.lam (.ifBool (.boolean true) (.bound 0) (.nat 0)),
    fun _ => some aliasBranchAnnotation, naturalAliasAssumptions⟩

/-- The concrete alias equation, by the certified extension rule, not reduction of the finite
graph decision. -/
@[simp] public theorem naturalAlias_agrees :
    sameType (⟨[(0, .natural)], [0], [], []⟩ : Assumptions) (.variable 0) .natural = true :=
  sameType_extends (by decide)

@[simp] public theorem naturalAlias_agrees_reverse :
    sameType (⟨[(0, .natural)], [0], [], []⟩ : Assumptions) .natural (.variable 0) = true :=
  sameType_symm naturalAlias_agrees

@[expose] public def aliasBranchChecked : Checked aliasBranch [] where
  type := .arrow .reusable .unrestricted (.variable 0) .natural
  uses := []
  derivation := .lambda (annotation := aliasBranchAnnotation)
    (.ifBool (.boolean _ _)
      (.conversion (.bound (binding := ⟨.variable 0, .unrestricted⟩) (index := 0) (by rfl))
        (naturalAlias_agrees))
      (.natural _ _) rfl)
    (by simp [aliasBranchAnnotation, safeUses, zeroUses, variableUses,
      addUses, safeQuantity, Quantity.fits, linearFree, joinUses, branchesAgree, Quantity.agrees])
    (by simp [aliasBranch, aliasBranchAnnotation, naturalAliasAssumptions, validContext,
      Ty.shareableUnder])
    (by simp [aliasBranchAnnotation, reusableAllowed, reusableCaptures,
      zeroUses, variableUses, addUses])
    rfl
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

/-! Empty variants have a semantic eliminator at any result type. Synthesis has no result type
to infer for an empty arm list; checking has one (`emptyCase_checks`). -/

@[expose] public def emptyCaseAnnotation : LambdaAnnotation :=
  ⟨.variant .emptyRow, .natural, .unrestricted, .reusable⟩

@[expose] public def emptyCase : AnnotatedTerm :=
  ⟨.lam (.case (.bound 0) []), fun _ => some emptyCaseAnnotation, {}⟩

@[expose] public def emptyCaseChecked : Checked emptyCase [] where
  type := .arrow .reusable .unrestricted (.variant .emptyRow) .natural
  uses := []
  derivation := .lambda (annotation := emptyCaseAnnotation)
    (.case (.bound (binding := ⟨.variant .emptyRow, .unrestricted⟩) (index := 0) (by rfl))
      (.nil _ .unrestricted _) rfl (by simp [emptyCaseAnnotation, caseAllowed, linearFree, reusableCaptures, variableUses, Ty.shareableUnder, Ty.shareable]))
    (by simp [emptyCaseAnnotation, safeUses, variableUses, zeroUses, addUses, safeQuantity, Quantity.fits, linearFree, joinUses, branchesAgree, Quantity.agrees])
    (by simp [emptyCaseAnnotation, validContext, Ty.shareableUnder, Ty.shareable])
    (by simp [emptyCaseAnnotation, reusableAllowed, reusableCaptures,
      variableUses, zeroUses, addUses])
    rfl
  safe := by simp [safeUses]
  contextValid := rfl
  assumptionsValid := rfl

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
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed) _ _ rfl
  all_goals intros
  -- A constructor other than `case` or a conversion meets `term = .case s a` as a constructor
  -- clash: `cases` closes it at once (`trivial`'s `contradiction` took 150 ms a goal here).
  all_goals first | exact True.intro | (rename_i h; cases h; done) | simp_all

/-- The duplicate-arm program has no certificate at all, so the checker is not incomplete on it. -/
public theorem duplicate_arms_have_no_derivation : ¬ Nonempty (Checked duplicateCase []) := by
  rintro ⟨checked⟩
  have := case_labels_distinct checked.derivation
  simp [duplicateCase, AnnotatedTerm.erase, labelsDistinct] at this

/-! ## Expected checking and local representative annotations

The fixtures above keep their original annotation maps (a lambda annotation at every path).
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
    safeUses, safeQuantity, Quantity.fits, linearFree, joinUses, branchesAgree, Quantity.agrees, validContext, reusableAllowed, reusableCaptures,
    zeroUses, variableUses, addUses, Ty.shareableUnder, Ty.shareable,
    Assumptions.valid, naturalAliasAssumptions, labelsDistinct, caseAllowed, Bidirectional.caseQuantityAt,
    caseQuantity, Bidirectional.armsShareable])

/-- An absent annotation permits expected-directed checking. -/
theorem unannotatedConstant_checks :
    (Bidirectional.checkAgainst unannotatedConstant [] unannotatedConstantChecked.type).toOption.map (·.type) =
      some unannotatedConstantChecked.type := by obstruction_check

/-- Synthesis still names the missing lambda annotation. -/
theorem unannotatedConstant_synthesis_names_annotation :
    (match Bidirectional.infer unannotatedConstant [] with
      | .error refusal => some refusal
      | .ok _ => none) = some (.missingLambdaAnnotation []) := by obstruction_check

/-- A closed, semantically typed lambda with no annotations: synthesis refuses it, naming the
missing annotation, and checking at its certificate's type accepts it. -/
public theorem checked_lambda_without_annotations_synthesis_refused :
    ∃ source : AnnotatedTerm,
      source.term = .lam (.nat 0) ∧
      source.annotations = (fun _ => none) ∧
      (∃ certificate : Checked source [],
        certificate.type = .arrow .reusable .unrestricted .natural .natural) ∧
      (Bidirectional.infer source []).toBool = false ∧
      (Bidirectional.checkAgainst source [] (.arrow .reusable .unrestricted .natural .natural)).toBool = true := by
  refine ⟨unannotatedConstant, rfl, rfl, ⟨unannotatedConstantChecked, rfl⟩, ?_, ?_⟩
  · have named := unannotatedConstant_synthesis_names_annotation
    cases h : Bidirectional.infer unannotatedConstant [] with
    | error e => rfl
    | ok c => rw [h] at named; cases named
  · have accepted := unannotatedConstant_checks
    cases h : Bidirectional.checkAgainst unannotatedConstant [] (.arrow .reusable .unrestricted .natural .natural) with
    | error e => simp only [unannotatedConstantChecked] at accepted; rw [h] at accepted; cases accepted
    | ok c => rfl

/-- Existence of `Checked` does not imply synthesis on the same source succeeds. -/
public theorem checked_does_not_imply_synthesis :
    ¬ (∀ (source : AnnotatedTerm) (context : Context),
      Nonempty (Checked source context) → (Bidirectional.infer source context).toBool = true) := by
  intro complete
  have accepted := complete unannotatedConstant [] ⟨unannotatedConstantChecked⟩
  have named := unannotatedConstant_synthesis_names_annotation
  cases e : Bidirectional.infer unannotatedConstant [] with
  | error _ => rw [e] at accepted; cases accepted
  | ok _ => rw [e] at named; cases named

/-- Repairing the missing annotation makes synthesis accept this fixture. -/
-- fixture kept (2026-11-04): cheap closed check of `Bidirectional.infer` on literal data
example : (Bidirectional.infer annotatedConstant []).toBool = true := by
  decide +kernel

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
