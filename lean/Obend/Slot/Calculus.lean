module
/-
# Obend.Slot.Calculus — a contextual calculus, as the slot judges fillings

nano's `CalculusData` (deleted there with the toy closure, LANG-74; its laws were `CalculusLaws`) as
a typeclass: a term language with hypotheses (holes), a checker, meta-substitution of closed fillings
for holes, and the context operations a strengthening needs. The class carries NO laws (Ember's rule,
2026-10-29): what is true of an instance is stated of that instance (`Obend.Slot.Core4`). What the
class buys is one consumer in this package: `Calculus.slotOf` turns a hole `[Ψ ⊢ A]` into a `Slot`
whose judge is the calculus's checker, so `slot_repair`, `resolve_ok` and `resolve_error` speak about
fillings that are TERMS of the calculus, checked at the hole's context and type.
-/
public import Obend.Slot

@[expose] public section
namespace Obend.Slot

/-- A contextual calculus over terms `Tm`. Hole occurrences are the free hypotheses of an open term,
numbered; a filling is a term. `msubst σ t` fills every hypothesis `σ` names and leaves the others
(partial filling); `check Ψ t A` is the authority a filling acquires; `uses t x` says whether
hypothesis `x` occurs in `t`; `drop`, `strengthen`, `weaken` are the context operations of a
strengthening `t ≡ t₀[π]`; `var x` is hypothesis `x` as a term; `lookup Ψ x` its declared type. -/
class Calculus (Tm : Type) where
  Ty : Type
  Ctx : Type
  msubst : (Nat → Option Tm) → Tm → Tm
  check : Ctx → Tm → Ty → Bool
  uses : Tm → Nat → Bool
  drop : Ctx → Nat → Ctx
  strengthen : Nat → Tm → Tm
  weaken : Nat → Tm → Tm
  var : Nat → Tm
  lookup : Ctx → Nat → Option Ty

namespace Calculus

variable {Tm : Type} [Calculus Tm] {Fact : Type}

/-- The slot a hole `[Ψ ⊢ A]` gives: candidates are terms, each citing the supports `supports`
assigns it, and the judge is the checker at the hole's context and type. -/
def slotOf (Ψ : Ctx Tm) (A : Ty Tm) (supports : Tm → List Fact) : Slot Fact Tm :=
  ⟨supports, fun t => check Ψ t A⟩

/-- A usable candidate of a hole's slot checks at the hole, and every support it cites holds. -/
theorem slotOf_usable (Ψ : Ctx Tm) (A : Ty Tm) (supports : Tm → List Fact) (holds : Fact → Bool)
    (t : Tm) (h : (slotOf Ψ A supports).usable holds t = true) :
    check Ψ t A = true ∧ ∀ f ∈ supports t, holds f = true := by
  have := (usable_iff (slotOf Ψ A supports) holds t).1 h
  exact this

/-- A filling a hole's slot resolves to checks at the hole: `Slot.resolve` took it from the usable
candidates, whose judge is the checker. -/
theorem resolve_checks {Ix : Type} {S : Protocol.Sig Ix} {Hole : Ix → Type} {A' : Ix → Type}
    (Ψ : Ctx Tm) (A : Ty Tm) (supports : Tm → List Fact) (holds : Fact → Bool) {i : Ix}
    (body : Tm → Protocol.Prot S Hole A' i) (order : List Tm) {f : Protocol.Prot S Hole A' i}
    (h : (slotOf Ψ A supports).resolve holds body order = .ok f) :
    ∃ t ∈ order, check Ψ t A = true ∧ f = body t := by
  obtain ⟨t, _, _, hmem, hu, rfl⟩ := resolve_ok h
  exact ⟨t, hmem, (slotOf_usable Ψ A supports holds t hu).1, rfl⟩

end Calculus
end Obend.Slot
end
