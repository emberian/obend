module
/- Teeth of T7 (`Obend.Core.Proofs.Splice.contextual_msubst_uses`, lane C2, 2026-11-01).

The laundering program is `open_filling_tooth`'s (`SubstitutionTeeth`): in `h₀ : unrestricted ℕ,
h₁ : linear ℕ`, the template `h₀ + h₁` uses `h₁` once; filling `h₀` with the open code `h₁` gives
`h₁ + h₁`, which spends the once-resource twice. The composition counts it: `spliceUses` puts `2` at
`h₁`, so `spliceSafe` refuses, and `spliceAllowed` refuses too (an `unrestricted` hole takes no
filling that uses a `linear` hypothesis). Without the premises the theorem's conclusion is false
(`splice_without_premises_false`), and each premise is load-bearing in the stored proof (`#tooth`).
The control fills a `linear` hole with another `linear` hypothesis, used once: accepted. -/
public import Obend.Core.Proofs.Splice
public import Obend.Core.Proofs.Substitution.Defs
public import Obend.Tactic.Tooth
import all Obend.Core.Proofs.Splice
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Check
import all Obend.Core.Ty

namespace Obend.Core.Proofs.Splice
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
open Obend.Core.Proofs.Substitution (linearTemplate linearFilling linearContext)
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences uses_determined)
set_option autoImplicit false

theorem laundered_term : splice 0 linearTemplate.term linearFilling.term = .binary .add (.bound 1) (.bound 1) := by
  simp [splice, fillAt, linearTemplate, linearFilling, Term.substitute]

/-- The composed uses put `2` at the `linear` hypothesis, and both premises refuse the splice. -/
theorem open_filling_composed :
    spliceUses (occurrences 2 linearTemplate.term) 0 (occurrences 2 linearFilling.term) 1 = 2 ∧
    spliceSafe linearContext (occurrences 2 linearTemplate.term) 0 (occurrences 2 linearFilling.term) = false ∧
    spliceAllowed {} .unrestricted linearContext (occurrences 2 linearFilling.term) = false := by
  decide

theorem template_typed : PartialTyping {} linearContext linearTemplate.term .natural
    (addUses (variableUses linearContext 0) (variableUses linearContext 1)) :=
  .binary (input := .natural) rfl (.bound (binding := ⟨.natural, .unrestricted⟩) rfl)
    (.bound (index := 1) (binding := ⟨.natural, .linear⟩) rfl)

theorem filling_typed : PartialTyping {} linearContext linearFilling.term .natural (variableUses linearContext 1) :=
  .bound (index := 1) (binding := ⟨.natural, .linear⟩) rfl

/-- **The premises are what refuse laundering.** Dropping them, the conclusion fails on the
laundering program: no derivation of `h₁ + h₁` is within `h₁`'s quantity. -/
theorem splice_without_premises_false :
    ¬ (∀ (t f : Term) (T : Ty) (u uf : Uses) (x : Nat) (b : Binding),
        PartialTyping {} linearContext t T u → linearContext[x]? = some b →
        PartialTyping {} linearContext f b.type uf →
        ∃ u', PartialTyping {} linearContext (splice x t f) T u' ∧ safeUses linearContext u' = true) := by
  intro claim
  obtain ⟨u', h, safe⟩ := claim _ _ _ _ _ 0 ⟨.natural, .unrestricted⟩ template_typed rfl filling_typed
  rw [laundered_term] at h
  rw [uses_determined h] at safe
  exact absurd safe (by decide)

/-- Control: a `linear` hole filled by another `linear` hypothesis, used once, splices. -/
theorem linear_into_linear :
    ∃ u', PartialTyping {} [⟨.natural, .linear⟩, ⟨.natural, .linear⟩] (splice 0 (.bound 0) (.bound 1)) .natural u' ∧
      safeUses [⟨.natural, .linear⟩, ⟨.natural, .linear⟩] u' = true := by
  obtain ⟨u', h, s, _, _⟩ := splice_typed (a := {}) (Ψ := [⟨.natural, .linear⟩, ⟨.natural, .linear⟩]) (x := 0) (b := ⟨.natural, .linear⟩)
    (.bound (index := 0) (binding := ⟨.natural, .linear⟩) rfl) (by decide) rfl
    (.bound (index := 1) (binding := ⟨.natural, .linear⟩) rfl) (by decide) (by decide)
  exact ⟨u', h, s⟩

#tooth contextual_msubst_uses by mutation spliceSafe := fun _ _ _ _ => true
#tooth contextual_msubst_uses by mutation spliceAllowed := fun _ _ _ _ => true

end Obend.Core.Proofs.Splice
