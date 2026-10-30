module
/-
# Obend.Slot.Core4 — Core4 as a contextual calculus, on its closed-hole fragment

The instance the slot theory needs, at the language this library is about. A HOLE is a free de Bruijn
hypothesis of an open Core4 term (`Term.bound x` with `x` beyond the binders above it); a FILLING is
a closed annotated term; `msubst` (`Obend.Core.Proofs.Substitution.msubst`) substitutes fillings for
the hypotheses they name and merges the fillings' lambda annotations at the positions where they land,
so the filled term is again an `AnnotatedTerm` the checker reads.

What fragment this is, said as LANG-68 said it of nano: a hole here has the EMPTY local context. CMTT's
`u :: [Ψ ⊢ A]` with `Ψ ≠ []` and occurrences `u[σ]` carrying a substitution are not expressible: Core4
has no hole former, and a free variable cannot carry a context. So `Calculus.check Ψ t A` judges a
filling in the context `Ψ` of the HOLE'S SURROUNDINGS, and the filling may use those hypotheses, but a
filling is itself never open in further holes (depth one). The checker is Core4's own `check` at the
front end's type fuel; `strengthen`/`weaken` rename hypotheses with `Term.rename`.

The law of the calculus (nano's `CalculusLaws.msubst_lemma`) is PROVED here, from the substitution
lemma of `Obend.Core.Check` (`check_msubst`): a template that passes the judge at `A`, with every
filling closed, under the template's assumptions, and passing the judge at the type `Ψ` declares for
its hypothesis, gives a filled term that checks at `A` (`calculus_check_msubst`), with no more uses of
any hypothesis than the template had. Three corners, each with a tooth in `Substitution`:
- FUEL. The judge runs `check` at the fixed `checkFuel`; the filled term needs the template's fuel
  plus a filling's, so the law at the fixed fuel holds within that budget
  (`calculus_check_msubst_within`), and in general at `2 * checkFuel` (`calculus_check_msubst`).
  `fuel_tooth` exhibits template and filling at fuel 2 whose filling is refused at 2.
- CLOSED FILLINGS. An open filling that shares a linear hypothesis with its surroundings is refused
  after substitution (`open_filling_tooth`); `Scoped 0` on fillings is load-bearing.
- ASSUMPTIONS. `msubst` keeps the template's assumptions; a filling that passes the judge only under
  its own is refused (`assumptions_tooth`); the law asks `f.assumptions = t.assumptions`.
Also proved: the equations a slot reader relies on (`msubst_var_filled`, `msubst_var_open`,
`uses_var`) and `annotationsAt_root`.
-/
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Core.Proofs.Substitution
public import Obend.Slot.Calculus

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
def freeIn (x : Nat) : Term → Bool
  | .bound index => index == x
  | .lam body => freeIn (x + 1) body
  | .app function argument => freeIn x function || freeIn x argument
  | .mix lower upper => freeIn x lower || freeIn x upper
  | .fix spec inherited => freeIn x spec || freeIn x inherited
  | .specification metadata extension => freeIn x metadata || freeIn x extension
  | .prototype spec target => freeIn x spec || freeIn x target
  | .reflect target => freeIn x target
  | .metadata spec => freeIn x spec
  | .project target => freeIn x target
  | .nat _ => false
  | .boolean _ => false
  | .label _ => false
  | .binary _ left right => freeIn x left || freeIn x right
  | .extend inherited fields => freeIn x inherited || (fields.map fun field => freeIn x field.2).any id
  | .record fields => (fields.map fun field => freeIn x field.2).any id
  | .get target _ => freeIn x target
  | .ifZero value zero successorBody => freeIn x value || freeIn x zero || freeIn (x + 1) successorBody
  | .inject _ payload => freeIn x payload
  | .case scrutinee arms => freeIn x scrutinee || (arms.map fun arm => freeIn (x + 1) arm.2).any id
  | .ifBool condition whenTrue whenFalse => freeIn x condition || freeIn x whenTrue || freeIn x whenFalse
  | .perform plan => freeIn x plan
  | .done value => freeIn x value
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf field.snd < sizeOf field := by
         cases field
         simp +arith
       omega)
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf arm.snd < sizeOf arm := by
         cases arm
         simp +arith
       omega)

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
  check Ψ t A :=
    match check t Ψ checkFuel with
    | some checked => decide (checked.type = A)
    | none => false
  uses t x := freeIn x t.term
  drop Ψ x := Ψ.eraseIdx x
  strengthen x t := { t with term := t.term.rename (lowerFrom x) }
  weaken x t := { t with term := t.term.rename (liftFrom x) }
  var := var
  lookup Ψ x := (Ψ[x]?).map (·.type)

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
  simp [Obend.Slot.Calculus.uses, var, freeIn]

/-- The judge of this calculus: `check` at the fixed fuel, then the type compared exactly. -/
theorem calculus_check_iff (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    Obend.Slot.Calculus.check Ψ t A = true ↔ ∃ c : Checked t Ψ, check t Ψ checkFuel = some c ∧ c.type = A := by
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
    (ht : Obend.Slot.Calculus.check Ψ t A = true)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ b : Binding, Ψ[x]? = some b ∧ Obend.Slot.Calculus.check Ψ f b.type = true) :
    ∃ c : Checked (msubst σ t) Ψ, check (msubst σ t) Ψ (2 * checkFuel) = some c ∧ c.type = A := by
  obtain ⟨c, hc, hA⟩ := (calculus_check_iff Ψ t A).1 ht
  obtain ⟨c', hc', hty, -⟩ := check_msubst σ hc (fun x f hx => by
    obtain ⟨closed, hfa, b, hb, hf⟩ := hσ x f hx
    obtain ⟨d, hd, hdt⟩ := (calculus_check_iff Ψ f b.type).1 hf
    have e : { f with assumptions := t.assumptions } = f := by rw [← hfa]
    refine ⟨closed, b, ?_⟩
    rw [e]
    exact ⟨d, hb, hd, hdt⟩)
  rw [Nat.two_mul]
  exact ⟨c', hc', hty.trans hA⟩

/-- The law at the judge's own fuel: when the template checks at fuel `n` and every filling at fuel
`m` with `n + m ≤ checkFuel`, the filled term passes the judge. Fuel is the one corner where the law
is conditional; the premise is the budget. -/
theorem calculus_check_msubst_within (Ψ : Context) (t : AnnotatedTerm) (A : Ty) (σ : Nat → Option AnnotatedTerm)
    (n m : Nat) (budget : n + m ≤ checkFuel) (c : Checked t Ψ) (ht : check t Ψ n = some c) (hA : c.type = A)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ (b : Binding) (d : Checked f Ψ), Ψ[x]? = some b ∧ check f Ψ m = some d ∧ d.type = b.type) :
    Obend.Slot.Calculus.check Ψ (msubst σ t) A = true := by
  obtain ⟨c', hc', hty, -⟩ := check_msubst σ ht (fun x f hx => by
    obtain ⟨closed, hfa, b, d, hb, hd, hdt⟩ := hσ x f hx
    have e : { f with assumptions := t.assumptions } = f := by rw [← hfa]
    refine ⟨closed, b, ?_⟩
    rw [e]
    exact ⟨d, hb, hd, hdt⟩)
  exact (calculus_check_iff Ψ _ A).2 ⟨c', check_mono hc' budget, hty.trans hA⟩

#assert_axioms annotationsAt_root msubst_var_filled msubst_var_open uses_var calculus_check_iff
  calculus_check_msubst calculus_check_msubst_within

end Obend.Slot.Core4
end
