module
/-
# Obend.Teeth.Core.NominalTeeth — the higher-order Kilo-to-Mile crossing, refused by name

The checker at work on `Obend.Core.Nominal`'s fixtures: `λf. f` annotated over `Kilo → Nat` is
refused at `(Kilo → Nat) → (Mile → Nat)` and the refusal names Mile expected and Kilo given; the
same term is accepted within the kind. (Evaluated here, in an importer: the kernel reduces the
checker on these fixtures from the imported, exposed bodies.)
-/
public import Obend.Core.Nominal
import all Obend.Core.Nominal
import all Obend.Core.Check
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.FiniteBisimulation
import all Obend.Core.RecursiveAgreement
import all Obend.Core.EquiRecursiveAgreement
@[expose] public section
namespace Obend.Core.Nominal
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

/-- What a checker run refused, if it refused. -/
@[expose] def refusalOf {α : Type} : Except Obend.Core.Bidirectional.CheckRefusal α → Option Obend.Core.Bidirectional.CheckRefusal
  | .error e => some e
  | .ok _ => none

/-- **The tooth**: the checker refuses the higher-order crossing, and the refusal names the two kinds
at the root, Mile expected and Kilo given. -/
theorem crossing_refused_by_name :
    ((refusalOf (Obend.Core.Bidirectional.checkAgainst crossing [] crossingType)).bind crossedKinds).map
      (·.2) = some ("Units.Mile", "Units.Kilo") := by
  decide +kernel

/-- The same term at `(Kilo → Nat) → (Kilo → Nat)` is accepted. -/
theorem crossing_within_kind :
    (Obend.Core.Bidirectional.checkAgainst crossing []
      (.arrow .reusable .unrestricted (.arrow .reusable .unrestricted kilo .natural)
        (.arrow .reusable .unrestricted kilo .natural))).toBool = true := by
  decide +kernel

/-- An anonymous record of the same layout is neither kind: structural records stay structural. -/
theorem anonymous_is_neither :
    sameType {} mile distance = false ∧ sameType {} kilo distance = false ∧ sameType {} mile kilo = false ∧
      sameType {} mile mile = true := by
  decide +kernel

/-- An extension constructing an instance of another kind overwrites the brand: `{#kind: Kilo}`
under `{#kind: Mile, n}` is a Kilo (the first field of a name is the one a row shows). -/
theorem rebranded_is_the_new_kind :
    sameType {} (.field brandLabel (kindTy "Units.Kilo") mile) kilo = true ∧
      sameType {} (.field brandLabel (kindTy "Units.Kilo") mile) mile = false := by
  decide +kernel

end Obend.Core.Nominal

end
