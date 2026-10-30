module
public import Obend.Core.Ty
@[expose] public section
namespace Obend.Core.Check
open Obend.Core.Ty
set_option autoImplicit false

structure Assumptions where
  bounds : Bounds := []
  shareableVariables : List Nat := []
  /-- Rigid variables (OB-LTUO LT2 D2): a template's `Self`, checked once against its
  declared bound. A rigid variable's bound is a LOWER bound: members are looked up
  through it (`Ty.lookup`, `Ty.isRow`), but it is never an alias, so no conversion
  equates the variable with its bound row. Emitted programs have `rigid = []`, where
  `alias` is `bounds.lookup` and the checker is the alias checker. -/
  rigid : List Nat := []

/-- The declared head a variable unfolds to in a conversion: its bound unless it is rigid. -/
def Assumptions.alias (assumptions : Assumptions) (index : Nat) : Option Ty :=
  if assumptions.rigid.contains index then none else assumptions.bounds.lookup index

theorem Assumptions.alias_bound {assumptions : Assumptions} {index : Nat} {bound : Ty}
    (found : assumptions.alias index = some bound) : assumptions.bounds.lookup index = some bound := by
  unfold Assumptions.alias at found
  split at found
  · cases found
  · exact found

theorem Assumptions.alias_of_rigid_nil {assumptions : Assumptions} (open_ : assumptions.rigid = [])
    (index : Nat) : assumptions.alias index = assumptions.bounds.lookup index := by
  simp [Assumptions.alias, open_]

theorem Assumptions.alias_rigid {assumptions : Assumptions} {index : Nat}
    (rigid : assumptions.rigid.contains index = true) : assumptions.alias index = none := by
  unfold Assumptions.alias; rw [if_pos rigid]

end Obend.Core.Check
