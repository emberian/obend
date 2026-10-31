module
/- The three corners of the substitution lemma (`Obend.Core.Proofs.CheckerTransport.checkAgainst_msubst`,
over `TypedSubstitution.checked_msubst`), each with a tooth: fillings must be closed, fillings check
under the template's assumptions, and a work grant that admits the template does not admit the
filled term (the grant is procedural; semantic substitution has none). -/
public import Obend.Tactic.Tooth
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Bidirectional
public import Obend.Core.Invariant
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Substitution.Defs
public import Obend.Slot.Core4
import all Obend.Core.Ty
import all Obend.Core.Check
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant Obend.Core.Bidirectional
set_option autoImplicit false

/-! ## Teeth: the three corners, each a refusal the kernel computes -/

/-- `λ(x : Nat). h`, with `h : Nat → Nat` the hole at hypothesis `0`. -/
abbrev fuelTemplateType : Ty := .arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural)

theorem fuel_template_checks : (checkAgainst fuelTemplate fuelContext fuelTemplateType).toBool = true := by
  decide +kernel
theorem fuel_filling_checks :
    (checkAgainst fuelFilling fuelContext (.arrow .reusable .unrestricted .natural .natural)).toBool = true := by
  decide +kernel
theorem msubst_fuel : msubst (fillZero fuelFilling) fuelTemplate =
    ⟨.lam (.lam (.bound 0)), annotationsAt (fillZero fuelFilling) fuelTemplate.annotations 0 [] fuelTemplate.term, {}⟩ := by
  have e : (msubst (fillZero fuelFilling) fuelTemplate).term = .lam (.lam (.bound 0)) := by
    simp [msubst, Term.substitute, liftSubstitution, fillTerm, fillingAt, fillZero, fuelTemplate, fuelFilling, Term.rename,
      liftRename]
  rw [← e]; rfl
/-- TOOTH (the grant is procedural). The template is admitted by the slot's judge at its own work;
the filled term, accepted by the checker with the filling's annotation carried in, needs more work
and is refused at that grant. A grant limits procedural admission, not semantic substitution
(`Obend.Slot.Core4.calculus_typed_msubst`); `checkAgainst_msubst` has no grant. -/
theorem fuel_tooth :
    Obend.Slot.Core4.judge (Obend.Slot.Core4.checkWork fuelTemplate) fuelContext fuelTemplate fuelTemplateType = true ∧
    Obend.Slot.Core4.judge (Obend.Slot.Core4.checkWork fuelTemplate) fuelContext
      (msubst (fillZero fuelFilling) fuelTemplate) fuelTemplateType = false ∧
    (checkAgainst (msubst (fillZero fuelFilling) fuelTemplate) fuelContext fuelTemplateType).toBool = true := by
  rw [msubst_fuel]
  -- Only these two annotation addresses are consumed; kernel reduction at concrete paths.
  have outer : annotationsAt (fillZero fuelFilling) fuelTemplate.annotations 0 []
      fuelTemplate.term [] =
      some ⟨.natural, .arrow .reusable .unrestricted .natural .natural, .unrestricted, .reusable⟩ := rfl
  have inner : annotationsAt (fillZero fuelFilling) fuelTemplate.annotations 0 []
      fuelTemplate.term [0] =
      some ⟨.natural, .natural, .unrestricted, .reusable⟩ := rfl
  decide +kernel

#tooth fuel_tooth by mutation fuelFilling := ⟨.nat 0, fun _ => none, {}⟩

theorem linear_template_checks : (checkAgainst linearTemplate linearContext .natural).toBool = true := by
  decide +kernel
theorem linear_filling_checks : (checkAgainst linearFilling linearContext .natural).toBool = true := by
  decide +kernel
theorem linear_filling_open : ¬ Scoped 0 linearFilling.term := by
  intro h; have := (scoped_bound_iff _ _).1 h; omega
theorem msubst_linear : msubst (fillZero linearFilling) linearTemplate =
    ⟨.binary .add (.bound 1) (.bound 1), annotationsAt (fillZero linearFilling) linearTemplate.annotations 0 []
      linearTemplate.term, {}⟩ := by
  have e : (msubst (fillZero linearFilling) linearTemplate).term = .binary .add (.bound 1) (.bound 1) := by
    simp [msubst, Term.substitute, fillTerm, fillingAt, fillZero, linearTemplate, linearFilling]
  rw [← e]; rfl
/-- TOOTH (fillings are closed). An OPEN filling (`bound 1`, the linear hypothesis) checks at the type
of hypothesis `0`, and the template checks; the filled term uses the linear hypothesis twice and is
refused. `Scoped 0` on the fillings is load-bearing. -/
theorem open_filling_tooth :
    (checkAgainst (msubst (fillZero linearFilling) linearTemplate) linearContext .natural).toBool = false := by
  rw [msubst_linear]; decide +kernel

#tooth open_filling_tooth by mutation linearFilling := ⟨.nat 0, fun _ => none, {}⟩

theorem alias_filling_checks : (checkAgainst aliasFilling aliasContext (.variable 0)).toBool = true := by
  decide +kernel
theorem alias_template_checks : (checkAgainst aliasTemplate aliasContext (.variable 0)).toBool = true := by
  decide +kernel
theorem alias_filling_closed : Scoped 0 aliasFilling.term := .inject (.natural _)
theorem msubst_alias : msubst (fillZero aliasFilling) aliasTemplate =
    ⟨.inject "l" (.nat 1), annotationsAt (fillZero aliasFilling) aliasTemplate.annotations 0 [] aliasTemplate.term, {}⟩ := by
  have e : (msubst (fillZero aliasFilling) aliasTemplate).term = .inject "l" (.nat 1) := by
    simp [msubst, Term.substitute, fillTerm, fillingAt, fillZero, aliasTemplate, aliasFilling]
  rw [← e]; rfl
/-- TOOTH (fillings check under the template's assumptions). The filling checks under ITS assumptions
(a bound for type variable `0`, so its injection converts to the declared sum) at the hypothesis's
type; `msubst` keeps the template's assumptions, which have no bound, and the filled term is refused.
This is why `checkAgainst_msubst` asks `f.assumptions = t.assumptions` of every filling. -/
theorem assumptions_tooth :
    (checkAgainst (msubst (fillZero aliasFilling) aliasTemplate) aliasContext (.variable 0)).toBool = false := by
  rw [msubst_alias]; decide +kernel

#tooth assumptions_tooth by mutation aliasFilling := aliasTemplate

end Obend.Core.Proofs.Substitution
