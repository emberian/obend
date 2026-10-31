module
/- `infer_mono`, `check_mono`: `infer` is monotone in its fuel. -/
public import Obend.Tactic.Tooth
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Substitution.Transport
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
set_option autoImplicit false

/-- More fuel never loses a result of `infer`, and the result is the same. -/
public theorem infer_mono {asm : Assumptions} {ann : Annotations} {Γ : Context} {pos : List Nat}
    {fuel fuel' : Nat} {term : Term} {result : Inferred asm Γ term}
    (h : infer asm ann Γ pos fuel term = some result) (le : fuel ≤ fuel') :
    infer asm ann Γ pos fuel' term = some result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  have e : Γ ++ [] = Γ := List.append_nil Γ
  revert result h
  rw [← e]
  intro result h
  have hs : Scoped Γ.length term := by simpa using typed_scoped result.derivation
  obtain ⟨a, _, hu, result', h', ht, hu'⟩ :=
    (infer_transport asm [] [] rfl extra fuel).1 ann ann Γ pos pos term result hs h (fun _ => rfl)
  cases result with
  | mk ty us d =>
    cases result' with
    | mk ty' us' d' =>
      simp only at ht hu hu'
      subst ht
      have : us' = us := hu'.trans hu.symm
      subst this
      exact h'

/-- More fuel never loses a result of `check`, and the result is the same. -/
public theorem check_mono {source : AnnotatedTerm} {Γ : Context} {fuel fuel' : Nat} {c : Checked source Γ}
    (h : check source Γ fuel = some c) (le : fuel ≤ fuel') : check source Γ fuel' = some c := by
  unfold check at h ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨result, typed, h⟩ := h
  exact ⟨result, infer_mono typed le, h⟩


end Obend.Core.Proofs.Substitution
