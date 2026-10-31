module
/- The single judge is the bidirectional checker, bounded by the checker's work
(`Obend.Elab.Work.checkWork`: one per node plus the annotations it reads).
Full completeness prepares annotations while preserving the erased program and
assumptions. Arbitrary fixed annotations need not be accepted. -/
public import Obend.Core.Term
public import Obend.Core.TermTraverse
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.DecisionReduction
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Invariant
public import Obend.Core.Proofs.Substitution.Mono
public import Obend.Core.Proofs.TypedSubstitution
public import Obend.Slot.Calculus
public import Obend.Tactic.Fuel
public import Obend.Tactic.Tooth
public import Obend.Tactic.MonadicReduction
public import Obend.Elab.Work

@[expose] public section
namespace Obend.Slot.Core4

open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty Context Binding)
open Obend.Core.Check (AnnotatedTerm Annotations Checked)
open Obend.Core.Ty (LambdaAnnotation)
open Obend.Core.Invariant (Scoped)
open Obend.Core.Proofs.Substitution (fillingAt annotationsAt fillTerm msubst fillTerm_zero)
set_option autoImplicit false

/-- Does hypothesis `x` (a free de Bruijn index, counted at the root) occur in `t`? Each binder
shifts the index sought by one: `lam`, the successor arm of `ifZero`, every `case` arm. -/
def freeIn (x : Nat) (t : Term) : Bool :=
  Obend.Core.Traverse.Tree.uses x (Obend.Core.TermTraverse.encode t)

/-- Hypothesis `x` as a term: a bare `bound x`, no annotations. -/
def var (x : Nat) : AnnotatedTerm := ⟨.bound x, fun _ => none, {}⟩

/-- Rename hypothesis indices from `x` on down by one (the hypothesis `x` itself must be unused). -/
def lowerFrom (x : Nat) (index : Nat) : Nat := if x < index then index - 1 else index

/-- Rename hypothesis indices from `x` on up by one, making room at `x`. -/
def liftFrom (x : Nat) (index : Nat) : Nat := if x ≤ index then index + 1 else index

instance : Obend.Slot.Calculus AnnotatedTerm where
  Ty := Ty
  Ctx := Context
  msubst := msubst
  Typed Ψ t A := ∃ c : Checked t Ψ, c.type = A
  uses t x := freeIn x t.term
  drop Ψ x := Ψ.eraseIdx x
  strengthen x t := { t with term := t.term.rename (lowerFrom x) }
  weaken x t := { t with term := t.term.rename (liftFrom x) }
  var := var
  lookup Ψ x := (Ψ[x]?).map (·.type)

/-- What a grant prices: the work the bidirectional checker does on the annotated term. -/
abbrev checkWork (t : AnnotatedTerm) : Nat := Obend.Elab.Work.checkWork t

/-- Only annotations may change during preparation. -/
def Reannotates (source target : AnnotatedTerm) : Prop :=
  source.term = target.term ∧ source.assumptions = target.assumptions

/-- Full syntactic coverage: every constructor is eligible for annotation preparation.
Typing remains an independent premise of completeness, so this includes ill-typed syntax. -/
def Covered (_ : Context) (_ : AnnotatedTerm) (_ : Ty) : Prop := True

/-- One route: a work grant and the equi-recursive bidirectional checker. -/
def judge (grant : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) : Bool :=
  decide (checkWork t ≤ grant) && (Obend.Core.Bidirectional.checkAgainst t Ψ A).toBool

theorem judge_iff (grant : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    judge grant Ψ t A = true ↔ checkWork t ≤ grant ∧
      ∃ c, Obend.Core.Bidirectional.checkAgainst t Ψ A = .ok c := by
  unfold judge
  cases h : Obend.Core.Bidirectional.checkAgainst t Ψ A with
  | error e => simp [Except.toBool]
  | ok c => simp [Except.toBool]

theorem reannotates_typed {Ψ : Context} {t u : AnnotatedTerm} {A : Ty}
    (h : Reannotates t u) (typed : Calculus.Typed Ψ t A) : Calculus.Typed Ψ u A := by
  obtain ⟨c, same⟩ := typed
  obtain ⟨termSame, assumptionsSame⟩ := h
  refine ⟨⟨c.type, c.uses, ?_, c.safe, ?_, ?_⟩, same⟩
  · simpa only [AnnotatedTerm.erase, ← termSame, ← assumptionsSame] using c.derivation
  · simpa only [← assumptionsSame] using c.contextValid
  · simpa only [← assumptionsSame] using c.assumptionsValid

instance : Decides Nat AnnotatedTerm where
  check := judge
  Covered := Covered
  Prepares := Reannotates
  prepare_sound := reannotates_typed
  check_sound := by
    intro r Ψ t A h
    obtain ⟨_, c, accepted⟩ := (judge_iff r Ψ t A).1 h
    exact ⟨c, (Obend.Core.Bidirectional.checkAgainst_sound accepted).1⟩
  check_mono := by
    intro r s Ψ t A h le
    obtain ⟨within, accepted⟩ := (judge_iff r Ψ t A).1 h
    exact (judge_iff s Ψ t A).2 ⟨Nat.le_trans within le, accepted⟩
  check_complete := by
    intro Ψ t A typed _
    obtain ⟨c, same⟩ := typed
    obtain ⟨annotations, checked, accepted⟩ :=
      Obend.Core.Proofs.BidirectionalCompleteness.full_annotated c
    refine ⟨{ t with annotations := annotations }, checkWork { t with annotations := annotations }, ⟨rfl, rfl⟩, ?_⟩
    exact (judge_iff _ _ _ _).2 ⟨Nat.le_refl _, checked, same ▸ accepted⟩
  check_covered := by intros; trivial

/-- Exact-work completeness for the erased program: annotations can be prepared, and no
grant larger than the prepared term's own work is needed. -/
theorem typed_iff_preparable_within_work (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    Calculus.Typed Ψ t A ↔ ∃ annotations,
      judge (checkWork { t with annotations := annotations }) Ψ { t with annotations := annotations } A = true := by
  constructor
  · rintro ⟨certificate, same⟩
    obtain ⟨annotations, checked, accepted⟩ :=
      Obend.Core.Proofs.BidirectionalCompleteness.full_annotated certificate
    refine ⟨annotations, (judge_iff _ _ _ _).2 ?_⟩
    exact ⟨Nat.le_refl _, checked, same ▸ accepted⟩
  · rintro ⟨annotations, accepted⟩
    have preparedTyped : Calculus.Typed Ψ { t with annotations := annotations } A :=
      Decides.check_sound (R := Nat) accepted
    exact reannotates_typed (t := { t with annotations := annotations }) (u := t)
      ⟨rfl, rfl⟩ preparedTyped

section JudgeFixtures
attribute [local congr] Obend.Tactic.MonadicReduction.except_bind_source_congr
  Obend.Tactic.MonadicReduction.option_bind_source_congr
attribute [local simp ↓] Option.bind_eq_bind

-- Constructor equations preserve the source-first boundary; global unfolding
-- would expose speculative success branches before reducing their sources.
attribute [local simp ↓] Obend.Tactic.MonadicReduction.except_monad_bind
  Obend.Tactic.MonadicReduction.except_functor_map
attribute [local simp] Obend.Tactic.MonadicReduction.except_bind_ok
  Obend.Tactic.MonadicReduction.except_bind_error
  Obend.Tactic.MonadicReduction.except_map_ok
  Obend.Tactic.MonadicReduction.except_map_error
attribute [local congr] Obend.Tactic.MonadicReduction.except_map_source_congr

-- Keep routine checker simplification at the Boolean agreement API boundary.
-- Closed mismatches are reduced explicitly by `equirec_reduce` below.
attribute [local irreducible] Obend.Core.Check.sameType
  Obend.Core.EquiRecursiveAgreement.agrees Obend.Core.TypeGraph.candidate

/-- Object extension is admitted by the single checker. -/
def extendFilling : AnnotatedTerm := ⟨.extend (.record [("a", .nat 1)]) [("b", .nat 2)], fun _ => none, {}⟩
def extendType : Ty := .field "b" .natural (.field "a" .natural .emptyRow)

theorem extend_filling_admitted : judge 4 [] extendFilling extendType = true := by
  simp [judge, extendFilling, extendType, checkWork, Obend.Elab.Work.checkWork,
    Obend.Elab.Work.termWork, Obend.Elab.Work.fieldsWork, Obend.Elab.Work.annotationWork,
    Obend.Core.Bidirectional.checkAgainst,
    Obend.Core.Bidirectional.checkAt,
    Obend.Core.Bidirectional.elaborate,
    Obend.Core.Bidirectional.introduce,
    Obend.Core.Bidirectional.finish,
    Obend.Core.Bidirectional.ascribe,
    Obend.Core.Bidirectional.checkedSynth,
    Obend.Core.Bidirectional.synthFields,
    Obend.Core.Bidirectional.checkFields,
    Obend.Core.Bidirectional.checkFieldsByLabel,
    Obend.Core.Bidirectional.need,
    Obend.Core.Bidirectional.representativeHead,
    Obend.Core.Bidirectional.whnf,
    Obend.Core.Bidirectional.rowMember,
    Obend.Core.Check.sameType_refl, Obend.Core.Check.labelsDistinct,
    Obend.Core.Check.overlay, Obend.Core.Check.isRowV, Obend.Core.Check.isRowW,
    Obend.Core.Check.unvisited, Obend.Core.Check.walkRow,
    Obend.Core.Check.Assumptions.chase,
    Obend.Core.Check.Assumptions.valid, Obend.Core.Check.argumentAllowed,
    Obend.Core.Check.reusableAllowed, Obend.Core.Ty.Ty.canonical,
    Obend.Core.Ty.safeUses, Obend.Core.Ty.variableUses, Obend.Core.Ty.zeroUses,
    Obend.Core.Ty.addUses, Obend.Core.Ty.safeQuantity, Obend.Core.Ty.Quantity.fits,
    Obend.Core.Ty.linearFree, Obend.Core.Ty.validContext,
    Obend.Core.Ty.reusableCaptures, Obend.Core.Ty.Ty.shareableUnder,
    Obend.Core.Ty.Ty.shareable, Obend.Core.Ty.Ty.isComputation,
    List.range_succ, List.zipWith,
    Except.toBool, bind, Except.bind, pure, Except.pure]
  <;> equirec_reduce

theorem extend_filling_decided : Decides.check (R := Nat) 4 ([] : Context) extendFilling extendType = true :=
  extend_filling_admitted

/-- The exact same filling is refused below its work. -/
theorem extend_filling_budget_refused : judge 3 [] extendFilling extendType = false := by
  simp [judge, extendFilling, checkWork, Obend.Elab.Work.checkWork, Obend.Elab.Work.termWork,
    Obend.Elab.Work.fieldsWork, Obend.Elab.Work.annotationWork]

/-- A record of 1,000 literal fields: the retired structural depth said 3; the work is 1,001. -/
def wideRecord : AnnotatedTerm := ⟨.record (List.replicate 1000 ("a", .nat 0)), fun _ => none, {}⟩

theorem wide_record_work : Obend.Elab.Work.nestingDepth wideRecord.term = 3 ∧ checkWork wideRecord = 1001 := by
  constructor <;> decide +kernel

/-- The grant now refuses the wide record where a depth of 3 would have admitted it. -/
theorem wide_record_refused_at_depth_grant (A : Ty) : judge 3 [] wideRecord A = false := by
  have : checkWork wideRecord = 1001 := wide_record_work.2
  simp [judge, this]

#tooth extend_filling_admitted by mutation judge := fun _ _ _ _ => false
#tooth extend_filling_budget_refused by mutation judge := fun _ Ψ t A =>
  (Obend.Core.Bidirectional.checkAgainst t Ψ A).toBool

/-- Supplied annotations can still disagree with a typed erased program. -/
def wronglyAnnotated : AnnotatedTerm :=
  ⟨.app (.lam (.bound 0)) (.nat 1), fun _ => some ⟨.boolean, .boolean, .unrestricted, .reusable⟩, {}⟩

def wronglyAnnotatedChecked : Checked wronglyAnnotated [] :=
  ⟨.natural, [], .application (functionType := .arrow .reusable .unrestricted .natural .natural)
    (.lambda (annotation := ⟨.natural, .natural, .unrestricted, .reusable⟩) (.bound (binding := ⟨.natural, .unrestricted⟩) rfl)
      (by decide) (by decide) (by decide) (by decide))
    (.natural _ _) rfl rfl (by decide), rfl, rfl, rfl⟩

theorem wronglyAnnotated_judge_refused (grant : Nat) :
    judge grant [] wronglyAnnotated .natural = false := by
  have arrowNotBoolean : Obend.Core.Check.sameType {}
      (.arrow .reusable .unrestricted .boolean .boolean) .boolean = false := by
    equirec_reduce
  have refused : (Obend.Core.Bidirectional.checkAgainst wronglyAnnotated [] .natural).toBool = false := by
    simp [wronglyAnnotated, arrowNotBoolean,
      Obend.Core.Bidirectional.checkAgainst,
    Obend.Core.Bidirectional.checkAt,
    Obend.Core.Bidirectional.elaborate,
    Obend.Core.Bidirectional.introduce,
    Obend.Core.Bidirectional.finish,
    Obend.Core.Bidirectional.ascribe,
    Obend.Core.Bidirectional.checkedSynth,
    Obend.Core.Bidirectional.synthFields,
    Obend.Core.Bidirectional.checkFields,
    Obend.Core.Bidirectional.checkFieldsByLabel,
    Obend.Core.Bidirectional.need,
    Obend.Core.Bidirectional.representativeHead,
    Obend.Core.Bidirectional.whnf,
    Obend.Core.Bidirectional.rowMember,
    Obend.Core.Check.sameType_refl, Obend.Core.Check.labelsDistinct,
    Obend.Core.Check.overlay, Obend.Core.Check.isRowV, Obend.Core.Check.isRowW,
    Obend.Core.Check.unvisited, Obend.Core.Check.walkRow,
    Obend.Core.Check.Assumptions.chase,
    Obend.Core.Check.Assumptions.valid, Obend.Core.Check.argumentAllowed,
    Obend.Core.Check.reusableAllowed, Obend.Core.Ty.Ty.canonical,
    Obend.Core.Ty.safeUses, Obend.Core.Ty.variableUses, Obend.Core.Ty.zeroUses,
    Obend.Core.Ty.addUses, Obend.Core.Ty.safeQuantity, Obend.Core.Ty.Quantity.fits,
    Obend.Core.Ty.linearFree, Obend.Core.Ty.validContext,
    Obend.Core.Ty.reusableCaptures, Obend.Core.Ty.Ty.shareableUnder,
    Obend.Core.Ty.Ty.shareable, Obend.Core.Ty.Ty.isComputation,
    List.range_succ, List.zipWith, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Except.toBool, pure, Except.pure]

  simp only [judge, refused, Bool.and_false]

/-- Coverage is full syntax; it deliberately does not assert that supplied annotations
are correct. Completeness permits replacing them and preserves the program. -/
theorem annotation_presence_not_coverage :
    (∀ position, (wronglyAnnotated.annotations position).isSome = true) ∧
    Calculus.Typed ([] : Context) wronglyAnnotated Ty.natural ∧
    Covered [] wronglyAnnotated .natural ∧
    ∀ grant, judge grant [] wronglyAnnotated .natural = false :=
  ⟨fun _ => rfl, ⟨wronglyAnnotatedChecked, rfl⟩, trivial, wronglyAnnotated_judge_refused⟩

end JudgeFixtures

/-- The substitution law is about meaning, including derivations the checker
cannot recognize. Closedness and shared assumptions remain essential. -/
theorem calculus_typed_msubst (Ψ : Context) (t : AnnotatedTerm) (A : Ty)
    (σ : Nat → Option AnnotatedTerm) (ht : Calculus.Typed Ψ t A)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ b : Binding, Ψ[x]? = some b ∧ Calculus.Typed Ψ f b.type) :
    Calculus.Typed Ψ (msubst σ t) A := by
  obtain ⟨c, same⟩ := ht
  obtain ⟨c', same', _⟩ := Obend.Core.Proofs.TypedSubstitution.checked_msubst c σ hσ
  exact ⟨c', same'.trans same⟩

/-- At the root (depth 0, empty path), a filled hypothesis answers with the filling's own annotations. -/
theorem annotationsAt_root (σ : Nat → Option AnnotatedTerm) (ann : Annotations) (x : Nat)
    (f : AnnotatedTerm) (h : σ x = some f) (rest : List Nat) :
    annotationsAt σ ann 0 [] (.bound x) rest = f.annotations rest := by
  simp [annotationsAt, fillingAt, h]

/-- Filling a hypothesis that `σ` names gives the filling. -/
theorem msubst_var_filled (σ : Nat → Option AnnotatedTerm) (x : Nat) (f : AnnotatedTerm)
    (h : σ x = some f) : msubst σ (var x) = { f with assumptions := {} } := by
  unfold msubst var
  simp only [Obend.Core.Term.Term.substitute, fillTerm_zero, h]
  congr 1
  funext rest
  exact annotationsAt_root σ (fun _ => none) x f h rest

/-- A hypothesis `σ` does not name is left open. -/
theorem msubst_var_open (σ : Nat → Option AnnotatedTerm) (x : Nat) (h : σ x = none) :
    msubst σ (var x) = var x := by
  unfold msubst var
  simp only [Obend.Core.Term.Term.substitute, fillTerm_zero, h]
  congr 1
  funext rest
  simp [annotationsAt, fillingAt, h]

/-- A hypothesis occurs in itself. -/
theorem uses_var (x : Nat) : Obend.Slot.Calculus.uses (var x) x = true := by
  simp [Obend.Slot.Calculus.uses, var, freeIn, Obend.Core.Traverse.Tree.uses, Obend.Core.Traverse.Tree.all, Obend.Core.TermTraverse.encode]

end Obend.Slot.Core4
end
