/-
# Obend.Core.Teeth.CollectYield — the executed teeth over `exampleYield` (legacy leaf)

Not a `module`, for the reason `Obend.Core.Teeth.Collect` gives: these theorems run the demand machine
(`runBounded`, `yieldedPlan`) and `collect` on a concrete term by `rfl`/`decide +kernel`, through `Array`
functions whose bodies Lean v4.30.0's `Init` does not expose to `module` files.
-/
import Obend.Core.Proofs.Collect
import Obend.AxiomPin

namespace Obend.Core.Collect
open Obend.Core.Term Obend.Core.Machine Obend.Core.Data

theorem yieldingTerm_yields : runBounded exampleLimits 32 (initial yieldingTerm) = .yielded 1 exampleYield := by
  rfl

/-- The yield leaves one garbage cell of two; collection drops it. -/
theorem exampleYield_collected : exampleYield.heap.size = 2 ∧ (collect exampleYield).heap.size = 1 := by
  decide +kernel

/-- Both Plans extract, to the same encoded Data. -/
theorem exampleYield_plan_agrees :
    ((yieldedPlan exampleLimits exampleBudget exampleYield).toOption.map fun r => encoded 4 r.value) =
      some (some [0, 53, 0]) ∧
    ((yieldedPlan exampleLimits exampleBudget (collect exampleYield)).toOption.map fun r => encoded 4 r.value) =
      some (some [0, 53, 0]) := by
  decide +kernel

theorem exampleYield_plan_extracts : ∃ r, yieldedPlan exampleLimits exampleBudget exampleYield = .ok r := by
  have agrees := exampleYield_plan_agrees.1
  cases extracted : yieldedPlan exampleLimits exampleBudget exampleYield with
  | ok r => exact ⟨r, rfl⟩
  | error e => rw [extracted] at agrees; simp [Except.toOption] at agrees

/-- The segment premises are inhabited: the original yields and its Plan extracts. -/
theorem exampleYield_segment_premises :
    ∃ plan y r, runBounded exampleLimits 32 (initial yieldingTerm) = .yielded plan y ∧
      yieldedPlan exampleLimits exampleBudget y = .ok r := by
  obtain ⟨r, extracted⟩ := exampleYield_plan_extracts
  exact ⟨1, exampleYield, r, yieldingTerm_yields, extracted⟩

#assert_axioms yieldingTerm_yields
#assert_axioms exampleYield_collected
#assert_axioms exampleYield_plan_agrees
#assert_axioms exampleYield_plan_extracts
#assert_axioms exampleYield_segment_premises

end Obend.Core.Collect
