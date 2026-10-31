/-
# Obend.Core.Teeth.CollectTyping — the evaluation tooth over `garbageTyped` (legacy leaf)

Not a `module`, for the reason `Obend.Core.Teeth.Collect` gives: `decide +kernel` evaluates `collect`,
which runs `Array` functions whose bodies Lean v4.30.0's `Init` does not expose to `module` files.
-/
import Obend.Core.Proofs.Collect

namespace Obend.Core.Collect
open Obend.Core.Term Obend.Core.Machine Obend.Core.Data Obend.Core.Ty Obend.Core.Check

/-- The collected typed state drops the garbage cell and keeps its typing. -/
public theorem garbageTyped_collected : garbageTyped.heap.size = 1 ∧ (collect garbageTyped).heap.size = 0 := by
  decide +kernel

end Obend.Core.Collect
