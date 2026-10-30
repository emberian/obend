module
/- Meaning, procedure, and the budget granted to a procedure are separate.
`Covered` is an explicit algorithmic-fragment premise, not a claim that every
semantic derivation is recognized. Core4's counterexamples forbid that claim. -/
public import Obend.Slot
public import Obend.Core.Graded

@[expose] public section
namespace Obend.Slot

class Calculus (Tm : Type) where
  Ty : Type
  Ctx : Type
  Typed : Ctx → Tm → Ty → Prop
  msubst : (Nat → Option Tm) → Tm → Tm
  uses : Tm → Nat → Bool
  drop : Ctx → Nat → Ctx
  strengthen : Nat → Tm → Tm
  weaken : Nat → Tm → Tm
  var : Nat → Tm
  lookup : Ctx → Nat → Option Ty

/-- A sound monotone procedure for a calculus. Completeness is conditional on
membership in its recognized fragment. The Core4 semantic substitution law is
proved on `Typed`, independently of this class and its coverage premise. -/
class Decides (R Tm : Type) [Obend.Core.Graded R] [Calculus Tm] where
  check : R → Calculus.Ctx Tm → Tm → Calculus.Ty Tm → Bool
  Covered : Calculus.Ctx Tm → Tm → Calculus.Ty Tm → Prop
  check_sound : ∀ {r Ψ t A}, check r Ψ t A = true → Calculus.Typed Ψ t A
  check_mono : ∀ {r s Ψ t A}, check r Ψ t A = true → r ≤ s → check s Ψ t A = true
  check_complete : ∀ {Ψ t A}, Calculus.Typed Ψ t A → Covered Ψ t A → ∃ r, check r Ψ t A = true
  check_covered : ∀ {r Ψ t A}, check r Ψ t A = true → Covered Ψ t A

/-- The declared grant for this invocation, independent of semantic typing. -/
structure Budget (R : Type) where
  grade : R

/-- The procedure did not establish coverage within the declared grant. This
names a refusal, not a diagnosis that the term is ill-typed or that fuel alone
would repair it. -/
inductive BudgetRefusal (R : Type) where
  | uncovered (budget : R)
  deriving DecidableEq, Repr

namespace Calculus
variable {Tm R : Type} [Calculus Tm] [Obend.Core.Graded R] [Decides R Tm] {Fact : Type}

def slotOf (budget : Budget R) (Ψ : Ctx Tm) (A : Ty Tm)
    (supports : Tm → List Fact) : Slot Fact Tm :=
  ⟨supports, fun t => Decides.check budget.grade Ψ t A⟩

/-- Admission exposes the named budget refusal; the generic slot retains its
existing `rejected` reading for a failed judge. -/
def admit (budget : Budget R) (Ψ : Ctx Tm) (A : Ty Tm) (t : Tm) : Except (BudgetRefusal R) Tm :=
  if Decides.check budget.grade Ψ t A then .ok t else .error (.uncovered budget.grade)

theorem slotOf_usable (budget : Budget R) (Ψ : Ctx Tm) (A : Ty Tm)
    (supports : Tm → List Fact) (holds : Fact → Bool) (t : Tm)
    (h : (slotOf budget Ψ A supports).usable holds t = true) :
    Typed Ψ t A ∧ ∀ f ∈ supports t, holds f = true := by
  obtain ⟨checked, live⟩ := (usable_iff (slotOf budget Ψ A supports) holds t).1 h
  exact ⟨Decides.check_sound checked, live⟩

theorem resolve_checks {Ix : Type} {S : Protocol.Sig Ix} {Hole : Ix → Type} {A' : Ix → Type}
    (budget : Budget R) (Ψ : Ctx Tm) (A : Ty Tm) (supports : Tm → List Fact)
    (holds : Fact → Bool) {i : Ix} (body : Tm → Protocol.Prot S Hole A' i)
    (order : List Tm) {f : Protocol.Prot S Hole A' i}
    (h : (slotOf budget Ψ A supports).resolve holds body order = .ok f) :
    ∃ t ∈ order, Typed Ψ t A ∧ f = body t := by
  obtain ⟨t, _, _, hmem, hu, rfl⟩ := resolve_ok h
  exact ⟨t, hmem, (slotOf_usable budget Ψ A supports holds t hu).1, rfl⟩

#assert_axioms slotOf_usable resolve_checks
end Calculus
end Obend.Slot
