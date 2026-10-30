module
/- Core4's fuel-free meaning is existence of Checked evidence. Its semantic
substitution law is independent of annotation coverage. The judge is the
bidirectional checker on its syntactic fragment (`checkCovered`): sound by its
certificate, complete there by `checkAgainst_complete`, and the fragment is decided
from the term alone, not by running the checker. -/
public import Obend.Core.Term
public import Obend.Core.TermTraverse
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Invariant
public import Obend.Core.Proofs.Substitution
public import Obend.Core.Proofs.TypedSubstitution
public import Obend.Slot.Calculus
public import Obend.Tactic.Fuel
public import Obend.Tactic.Tooth

@[expose] public section
namespace Obend.Slot.Core4

open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty Context Binding)
open Obend.Core.Check (AnnotatedTerm Annotations Checked check)
open Obend.Core.Ty (LambdaAnnotation)
open Obend.Core.Invariant (Scoped)
open Obend.Core.Proofs.Substitution (fillingAt annotationsAt fillTerm msubst fillTerm_zero check_msubst check_mono)
set_option autoImplicit false

/-- Does hypothesis `x` (a free de Bruijn index, counted at the root) occur in `t`? Each binder
shifts the index sought by one: `lam`, the successor arm of `ifZero`, every `case` arm. -/
def freeIn (x : Nat) (t : Term) : Bool :=
  Obend.Core.Traverse.Tree.uses x (Obend.Core.TermTraverse.encode t)

/-- The front end's type fuel (`Obend.Core.Check`'s preview wire caps `typeFuel` at 16384). -/
def checkFuel : Nat := 16384

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

/-- Exact-result recognition at a supplied grade. -/
def gradedCheck (fuel : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) : Bool :=
  match check t Ψ fuel with
  | some c => decide (c.type = A)
  | none => false

theorem gradedCheck_iff (fuel : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    gradedCheck fuel Ψ t A = true ↔ ∃ c : Checked t Ψ, check t Ψ fuel = some c ∧ c.type = A := by
  unfold gradedCheck
  cases h : check t Ψ fuel with
  | none => simp
  | some c =>
    simp only [decide_eq_true_eq]
    constructor
    · intro hc; exact ⟨c, rfl, hc⟩
    · rintro ⟨c', hc', hA⟩; cases hc'; exact hA

mutual
/-- The checker's recursion depth on a term: what a grant prices. -/
def termDepth : Term → Nat
  | .hole _ _ | .bound _ | .nat _ | .boolean _ | .label _ => 1
  | .lam t | .reflect t | .metadata t | .project t | .inject _ t | .perform t | .done t | .get t _ => termDepth t + 1
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b => max (termDepth a) (termDepth b) + 1
  | .ifZero a b c | .ifBool a b c => max (termDepth a) (max (termDepth b) (termDepth c)) + 1
  | .extend t fields => max (termDepth t) (fieldsDepth fields) + 1
  | .record fields => fieldsDepth fields + 1
  | .case t arms => max (termDepth t) (fieldsDepth arms) + 1
def fieldsDepth : List (String × Term) → Nat
  | [] => 0
  | (_, t) :: rest => max (termDepth t + 1) (fieldsDepth rest)
end

/-- The fragment route at a grant: the term is in the bidirectional checker's syntactic
fragment, its depth is within the grant, and the checker accepts it at `A`. -/
def fragmentJudge (grant : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) : Bool :=
  Obend.Core.Proofs.BidirectionalCompleteness.checkCovered t.term && decide (termDepth t.term ≤ grant) &&
    (Obend.Core.Bidirectional.checkAgainst t Ψ A).toBool

theorem fragmentJudge_iff (grant : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    fragmentJudge grant Ψ t A = true ↔ Obend.Core.Proofs.BidirectionalCompleteness.checkCovered t.term = true ∧
      termDepth t.term ≤ grant ∧ ∃ c, Obend.Core.Bidirectional.checkAgainst t Ψ A = .ok c := by
  unfold fragmentJudge
  cases h : Obend.Core.Bidirectional.checkAgainst t Ψ A with
  | error e => simp [Except.toBool]
  | ok c => simp [Except.toBool, and_assoc]

/-- The annotation route at a grant: the annotation-directed checker `Check.check`, the grant
its fuel, accepts the term at exactly `A`. -/
def annotatedJudge (grant : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) : Bool :=
  gradedCheck grant Ψ t A

/-- The judge: either route. -/
def judge (grant : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) : Bool :=
  fragmentJudge grant Ψ t A || annotatedJudge grant Ψ t A

/-- The annotation route's coverage: the annotation-directed checker accepts the term at `A`
at some fuel. It is not syntactic, and cannot be (`annotation_presence_not_coverage`): `Typed`
reads the erased term, so a term carrying every annotation the checker reads, but wrong
ones, is typed and refused. -/
def AnnotationDirected (Ψ : Context) (t : AnnotatedTerm) (A : Ty) : Prop :=
  ∃ fuel, gradedCheck fuel Ψ t A = true

/-- Both routes certify the same thing: a certificate is determined by its type. -/
theorem routes_agree {Ψ : Context} {t : AnnotatedTerm} {A : Ty} {fuel : Nat}
    {c d : Checked t Ψ} (fragment : Obend.Core.Bidirectional.checkAgainst t Ψ A = .ok c)
    (annotated : check t Ψ fuel = some d) (typed : d.type = A) : c = d :=
  Obend.Core.Proofs.BidirectionalCompleteness.Checked.eq_of_type c d
    ((Obend.Core.Bidirectional.checkAgainst_sound fragment).1.trans typed.symm)

instance : Decides Nat AnnotatedTerm where
  check := judge
  Covered Ψ t A := Obend.Core.Proofs.BidirectionalCompleteness.checkCovered t.term = true ∨ AnnotationDirected Ψ t A
  check_sound := by
    intro r Ψ t A h
    simp only [judge, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨-, -, c, hc⟩ := (fragmentJudge_iff r Ψ t A).1 h
      exact ⟨c, (Obend.Core.Bidirectional.checkAgainst_sound hc).1⟩
    · obtain ⟨c, _, same⟩ := (gradedCheck_iff r Ψ t A).1 h
      exact ⟨c, same⟩
  check_mono := by
    intro r s Ψ t A h le
    simp only [judge, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · obtain ⟨covered, within, accepted⟩ := (fragmentJudge_iff r Ψ t A).1 h
      exact .inl ((fragmentJudge_iff s Ψ t A).2 ⟨covered, Nat.le_trans within le, accepted⟩)
    · obtain ⟨c, hc, same⟩ := (gradedCheck_iff r Ψ t A).1 h
      exact .inr ((gradedCheck_iff s Ψ t A).2 ⟨c, check_mono hc le, same⟩)
  check_complete := by
    intro Ψ t A typed covered
    rcases covered with covered | ⟨fuel, accepted⟩
    · obtain ⟨c, same⟩ := typed
      obtain ⟨checked, accepted⟩ := Obend.Core.Proofs.BidirectionalCompleteness.checked_covered_accepted c covered
      refine ⟨termDepth t.term, ?_⟩
      simp only [judge, Bool.or_eq_true]
      exact .inl ((fragmentJudge_iff _ Ψ t A).2 ⟨covered, Nat.le_refl _, checked, same ▸ accepted⟩)
    · exact ⟨fuel, by simp [judge, annotatedJudge, accepted]⟩
  check_covered := by
    intro r Ψ t A h
    simp only [judge, Bool.or_eq_true] at h
    rcases h with h | h
    · exact .inl ((fragmentJudge_iff r Ψ t A).1 h).1
    · exact .inr ⟨r, h⟩

/-- An object filling built with `extend`: outside the fragment, so the fragment route (the
step-5 judge) refuses it at every grant; the annotation route admits it. -/
def extendFilling : AnnotatedTerm := ⟨.extend (.record [("a", .nat 1)]) [("b", .nat 2)], fun _ => none, {}⟩

def extendType : Ty := .field "b" .natural (.field "a" .natural .emptyRow)

theorem extend_filling_fragment_refused (grant : Nat) : fragmentJudge grant [] extendFilling extendType = false := by
  simp [fragmentJudge, extendFilling, Obend.Core.Proofs.BidirectionalCompleteness.checkCovered]

theorem extend_filling_admitted : judge 4 [] extendFilling extendType = true := by decide

theorem extend_filling_decided : Decides.check (R := Nat) 4 ([] : Context) extendFilling extendType = true :=
  extend_filling_admitted

/- The admission of the `extend` filling is the annotation route's: the stored proof is
rejected when that route is removed. -/
#tooth extend_filling_admitted by mutation annotatedJudge := fun _ _ _ _ => false

/-- A term carrying an annotation at every position, typed (at `Nat`), refused by both routes at
every grant: no condition on which positions are annotated can be the annotation route's
coverage. -/
def wronglyAnnotated : AnnotatedTerm :=
  ⟨.app (.lam (.bound 0)) (.nat 1), fun _ => some ⟨.boolean, .boolean, .unrestricted, .reusable⟩, {}⟩

def wronglyAnnotatedChecked : Checked wronglyAnnotated [] :=
  ⟨.natural, [], .application (functionType := .arrow .reusable .unrestricted .natural .natural)
    (.lambda (annotation := ⟨.natural, .natural, .unrestricted, .reusable⟩) (.bound (binding := ⟨.natural, .unrestricted⟩) rfl)
      (by decide) (by decide) (by decide))
    (.natural _ _) rfl rfl (by decide), rfl, rfl, rfl⟩

theorem wronglyAnnotated_check_refused (fuel : Nat) : check wronglyAnnotated [] fuel = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel => cases fuel <;> simp [check, Obend.Core.Check.infer, wronglyAnnotated, Obend.Core.Check.agree,
      Obend.Core.Check.sameType, Obend.Core.Ty.Ty.canonical, Obend.Core.Check.Assumptions.orbit,
      Obend.Core.Check.Assumptions.unfoldHead, Obend.Core.Ty.safeUses, Obend.Core.Ty.variableUses,
      Obend.Core.Ty.validContext, Obend.Core.Check.reusableAllowed, Obend.Core.Ty.reusableCaptures,
      Obend.Core.Ty.Ty.shareableUnder, Obend.Core.Ty.Ty.shareable, Obend.Core.Ty.safeQuantity,
      Obend.Core.Check.callable, Obend.Core.Ty.zeroUses, Obend.Core.Ty.addUses]

theorem annotation_presence_not_coverage :
    (∀ position, (wronglyAnnotated.annotations position).isSome = true) ∧
    wronglyAnnotatedChecked.type = .natural ∧
    ∀ grant, judge grant [] wronglyAnnotated .natural = false := by
  refine ⟨fun _ => rfl, rfl, fun grant => ?_⟩
  have fragment : fragmentJudge grant [] wronglyAnnotated .natural = false := by
    simp [fragmentJudge, wronglyAnnotated, Obend.Core.Proofs.BidirectionalCompleteness.checkCovered,
      Obend.Core.Proofs.BidirectionalCompleteness.synthCovered]
  simp [judge, fragment, annotatedJudge, gradedCheck, wronglyAnnotated_check_refused]

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

/-- The judge of this calculus: `check` at the fixed fuel, then the type compared exactly. -/
theorem calculus_check_iff (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    gradedCheck checkFuel Ψ t A = true ↔ ∃ c : Checked t Ψ, check t Ψ checkFuel = some c ∧ c.type = A := by
  show (match check t Ψ checkFuel with
    | some checked => decide (checked.type = A)
    | none => false) = true ↔ _
  cases h : check t Ψ checkFuel with
  | none => simp
  | some c =>
    simp only [decide_eq_true_eq]
    constructor
    · intro hc; exact ⟨c, rfl, hc⟩
    · rintro ⟨c', hc', hA⟩; cases hc'; exact hA

/-- **The law of the calculus at Core4.** A template passing the judge at `A`, with every filling
closed, sharing the template's assumptions, and passing the judge at the type `Ψ` declares for its
hypothesis, gives a filled term that `check` accepts at `A` with twice the judge's fuel (the
template's budget plus a filling's: `fuel_tooth` is why the fuel adds). -/
theorem calculus_check_msubst (Ψ : Context) (t : AnnotatedTerm) (A : Ty) (σ : Nat → Option AnnotatedTerm)
    (ht : gradedCheck checkFuel Ψ t A = true)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ b : Binding, Ψ[x]? = some b ∧ gradedCheck checkFuel Ψ f b.type = true) :
    ∃ c : Checked (msubst σ t) Ψ, check (msubst σ t) Ψ (2 * checkFuel) = some c ∧ c.type = A := by
  obtain ⟨c, hc, hA⟩ := (calculus_check_iff Ψ t A).1 ht
  obtain ⟨c', hc', hty, -⟩ := check_msubst σ hc (fun x f hx => by
    obtain ⟨closed, hfa, b, hb, hf⟩ := hσ x f hx
    obtain ⟨d, hd, hdt⟩ := (calculus_check_iff Ψ f b.type).1 hf
    have e : { f with assumptions := t.assumptions } = f := by rw [← hfa]
    refine ⟨closed, b, ?_⟩
    rw [e]
    exact ⟨d, hb, hd, hdt⟩)
  refine ⟨c', ?_, hty.trans hA⟩
  fuel_lift hc' using check_mono

/-- The law at the judge's own fuel: when the template checks at fuel `n` and every filling at fuel
`m` with `n + m ≤ checkFuel`, the filled term passes the judge. Fuel is the one corner where the law
is conditional; the premise is the budget. -/
theorem calculus_check_msubst_within (Ψ : Context) (t : AnnotatedTerm) (A : Ty) (σ : Nat → Option AnnotatedTerm)
    (n m : Nat) (budget : n + m ≤ checkFuel) (c : Checked t Ψ) (ht : check t Ψ n = some c) (hA : c.type = A)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ (b : Binding) (d : Checked f Ψ), Ψ[x]? = some b ∧ check f Ψ m = some d ∧ d.type = b.type) :
    gradedCheck checkFuel Ψ (msubst σ t) A = true := by
  obtain ⟨c', hc', hty, -⟩ := check_msubst σ ht (fun x f hx => by
    obtain ⟨closed, hfa, b, d, hb, hd, hdt⟩ := hσ x f hx
    have e : { f with assumptions := t.assumptions } = f := by rw [← hfa]
    refine ⟨closed, b, ?_⟩
    rw [e]
    exact ⟨d, hb, hd, hdt⟩)
  refine (calculus_check_iff Ψ _ A).2 ⟨c', ?_, hty.trans hA⟩
  fuel_lift hc' using check_mono

#assert_axioms gradedCheck_iff fragmentJudge_iff routes_agree extend_filling_fragment_refused extend_filling_admitted
  extend_filling_decided wronglyAnnotated_check_refused annotation_presence_not_coverage calculus_typed_msubst annotationsAt_root msubst_var_filled msubst_var_open uses_var calculus_check_iff
  calculus_check_msubst calculus_check_msubst_within

end Obend.Slot.Core4
end
