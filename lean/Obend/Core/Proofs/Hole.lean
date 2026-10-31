module
/- Inert holes are traversable syntax, and are refused when demanded (the checker refuses one in any
mode: `Bidirectional.elaborate_refuses_hole`). -/
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Tactic.Cases

namespace Obend.Core.Proofs.Hole
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant Obend.Core.Machine
set_option autoImplicit false

public theorem demanded_hole_refused (heap : Array Cell) (env : Environment)
    (stack : List Frame) (n : Nat) (σ : List Term) :
    stepRaw ⟨heap, .evaluate (.hole n σ) env, stack⟩ =
      ⟨heap, .refused .unresolvedHole, stack⟩ := by
  rfl

/-- Weak-head evaluation does not demand an unused argument. -/
public theorem ignored_hole_evaluates (n : Nat) (σ : List Term) :
    Evaluates (.app (.lam (.nat 7)) (.hole n σ)) (.nat 7) := by
  refine ⟨.next (.beta _ _) ?_, .natural 7⟩
  simpa [instantiate, Term.substitute] using (Steps.refl (.nat 7))

public theorem rename_hole_payload :
    (Term.hole 9 [.bound 0, .lam (.bound 1)]).rename Nat.succ =
      .hole 9 [.bound 1, .lam (.bound 2)] := by
  simp [Term.rename, liftRename]

public theorem substitute_hole_payload :
    (Term.hole 9 [.bound 0, .lam (.bound 1)]).substitute (fun _ => .nat 7) =
      .hole 9 [.nat 7, .lam (.nat 7)] := by
  simp [Term.substitute, liftSubstitution, Term.rename]

public theorem scoped_hole_payload (depth n : Nat) (σ : List Term) :
    Scoped depth (.hole n σ) ↔ ∀ t ∈ σ, Scoped depth t := by
  constructor
  · intro h
    obend_cases h with []
  · intro h
    exact .hole h

end Obend.Core.Proofs.Hole
