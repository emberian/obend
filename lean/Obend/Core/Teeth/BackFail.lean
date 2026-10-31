/-
# Obend.Core.Teeth.BackFail — tick suspension is a resource failure, executed (legacy leaf)

Not a `module`, for the reason `Obend.Core.Teeth.Collect` gives: `suspendedCheck_true` evaluates
`yieldedPlan` by `decide +kernel`, through `Array` functions whose bodies Lean v4.30.0's `Init` does not
expose to `module` files; `suspended_is_resource` consumes it and moves with it.
-/
import Obend.Core.Proofs.Forcing.BackFail

namespace Obend.Core.Proofs.Forcing
open Obend.Core.Term Obend.Core.Machine Obend.Core.Collect Obend.Core.Data

theorem suspendedCheck_true : suspendedCheck = true := by decide +kernel

/-- **Tick suspension does not transfer: it is a resource failure.** One yield, one heap and stack
room, the same output nodes and bytes: with no extraction ticks its Plan extraction fails
`tickExhausted`, with 16 it succeeds. (So the backward theorems above exclude it, and a kernel
fault "plan extraction: tickExhausted" is a statement about the envelope, not the program.) -/
theorem suspended_is_resource :
    ∃ st r, Obend.Core.Data.yieldedPlan ⟨8, 8⟩ ⟨8, 0, 64⟩ suspendedYield = .error (.tickExhausted, st) ∧
      Obend.Core.Data.yieldedPlan ⟨8, 8⟩ ⟨8, 16, 64⟩ suspendedYield = .ok r := by
  have checked := suspendedCheck_true
  unfold suspendedCheck at checked
  rw [Bool.and_eq_true] at checked
  obtain ⟨one, two⟩ := checked
  split at one
  · rename_i st found
    split at two
    · rename_i r ok
      exact ⟨st, r, found, ok⟩
    · cases two
  · cases one

end Obend.Core.Proofs.Forcing
