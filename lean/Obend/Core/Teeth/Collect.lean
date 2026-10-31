/-
# Obend.Core.Teeth.Collect — evaluation teeth for garbage collection (legacy leaf)

Not a `module`: `decide`/`decide +kernel` here evaluate `collect` on a concrete heap, which runs
`Array.map`, `Array.zip` and `Array.filterMap`; under the module system (Lean v4.30.0) the kernel does
not see `Init`'s bodies for `Array.map`/`Array.zip`, so the evaluation is only possible in a legacy file.
A legacy file may import `module` files (the converse is refused), so teeth are leaves: nothing imports
this module, and the theorems keep their statements.
-/
import Obend.Core.Collect

namespace Obend.Core.Collect

/-- Two of five cells are garbage: the collected heap has three. -/
theorem collect_garbageExample_heap_size : (collect garbageExample).heap.size = 3 := by decide +kernel

/-- The yielded Plan cell moved from 2 to 1, and the frame's capture from 4 to 2. -/
theorem collect_garbageExample_roots :
    (match (collect garbageExample).control with | .yielded plan => plan | _ => 99) = 1 ∧
    (collect garbageExample).stack.flatMap frameAddresses = [2] := by decide

end Obend.Core.Collect
