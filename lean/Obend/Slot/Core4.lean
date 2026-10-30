module
/- Core4's fuel-free meaning is existence of Checked evidence. Its semantic
substitution law is independent of annotation coverage. The checker is a graded
sound procedure, complete only on its explicitly recognized fragment. -/
public import Obend.Core.Term
public import Obend.Core.TermTraverse
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Core.Proofs.Substitution
public import Obend.Core.Proofs.TypedSubstitution
public import Obend.Slot.Calculus
public import Obend.Tactic.Fuel

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

/-- Recognition is explicit evidence about the algorithm, not another spelling
of semantic typing. No decision procedure for this predicate is claimed. -/
def Recognized (Ψ : Context) (t : AnnotatedTerm) (A : Ty) : Prop :=
  ∃ fuel, ∃ c : Checked t Ψ, check t Ψ fuel = some c ∧ c.type = A

instance : Decides Nat AnnotatedTerm where
  check := gradedCheck
  Covered := Recognized
  check_sound := by
    intro r Ψ t A h
    obtain ⟨c, _, same⟩ := (gradedCheck_iff r Ψ t A).1 h
    exact ⟨c, same⟩
  check_mono := by
    intro r s Ψ t A h le
    obtain ⟨c, hc, same⟩ := (gradedCheck_iff r Ψ t A).1 h
    apply (gradedCheck_iff s Ψ t A).2
    refine ⟨c, ?_, same⟩
    fuel_lift hc using check_mono
  check_complete := by
    intro Ψ t A _ covered
    obtain ⟨r, c, hc, same⟩ := covered
    exact ⟨r, (gradedCheck_iff r Ψ t A).2 ⟨c, hc, same⟩⟩
  check_covered := by
    intro r Ψ t A h
    exact ⟨r, (gradedCheck_iff r Ψ t A).1 h⟩

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

#assert_axioms gradedCheck_iff calculus_typed_msubst annotationsAt_root msubst_var_filled msubst_var_open uses_var calculus_check_iff
  calculus_check_msubst calculus_check_msubst_within

end Obend.Slot.Core4
end
