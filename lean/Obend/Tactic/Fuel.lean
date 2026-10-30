module
public import Obend.Core.Graded

public section
open Lean Elab Tactic

/-- Raise a judgment using its monotonicity theorem. Common summed grades are
handled by the resource laws; an explicitly declared covering budget is reused
from the context. Arithmetic is only a fallback for concrete Nat grades. -/
macro "fuel_lift " h:term " using " mono:term : tactic =>
  `(tactic| exact Obend.Core.Graded.lift $mono $h (by
    first
    | assumption
    | exact Obend.Core.Graded.le_refl _
    | exact Obend.Core.Graded.le_add_right _ _
    | exact Obend.Core.Graded.le_add_left _ _
    | omega))
