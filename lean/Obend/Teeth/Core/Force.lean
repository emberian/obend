/-
# Obend.Core.Teeth.Force — the executed tooth over `largerYield` (legacy leaf)

Not a `module`, for the reason `Obend.Core.Teeth.Collect` gives: `decide +kernel` runs `yieldedPlan` and
`checkpoint` on a concrete state, through `Array` functions whose bodies Lean v4.30.0's `Init` does not
expose to `module` files.
-/
import Obend.Core.Proofs.Force

namespace Obend.Core.Collect
open Obend.Core.Term Obend.Core.Machine Obend.Core.Data

theorem largerYield_checkpoint_grows :
    (collect largerYield).heap.size = 2 ∧
      ((yieldedPlan largerLimits largerBudget largerYield).toOption.map
        fun r => (checkpoint r.state).heap.size) = some 5 := by
  decide +kernel

end Obend.Core.Collect
