module
/-
# Obend.Teeth.Core.NominalTeeth — the higher-order Kilo-to-Mile crossing, refused by name

The checker at work on `Obend.Core.Nominal`'s fixtures: a function over Kilos used where a function
over Miles is expected is refused, and the refusal names Mile expected and Kilo given; `λf. f` over
Kilo functions is accepted within the kind; anonymous records are neither kind; an extension that
writes another kind's brand is that kind. (The general statements are `Obend.Core.Nominal`'s
`kinded_refuses`, `kinds_never_agree` and `kinded_domain_refuses`.) (Evaluated here, in an importer: the kernel reduces the
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
def refusalOf {α : Type} : Except Obend.Core.Bidirectional.CheckRefusal α → Option Obend.Core.Bidirectional.CheckRefusal
  | .error e => some e
  | .ok _ => none

/-- A function over Kilos held as a hypothesis, `f : Kilo → Nat`. -/
def kiloFunction : Context := [⟨.arrow .reusable .unrestricted kilo .natural, .unrestricted⟩]

/-- **The tooth**: `f : Kilo → Nat` used where a `Mile → Nat` is expected, the higher-order
Kilo-to-Mile crossing, is refused by the checker, and the refusal names the two kinds, Mile expected
and Kilo given. (The two kinds' layouts are equal.) -/
example :
    ((refusalOf (Obend.Core.Bidirectional.checkAgainst ⟨.bound 0, fun _ => none, {}⟩ kiloFunction
      (.arrow .reusable .unrestricted mile .natural))).bind crossedKinds).map (·.2) =
      some ("Units.Mile", "Units.Kilo") := by
  decide +kernel

/-- The same term at `(Kilo → Nat) → (Kilo → Nat)` is accepted. -/
example :
    (Obend.Core.Bidirectional.checkAgainst crossing []
      (.arrow .reusable .unrestricted (.arrow .reusable .unrestricted kilo .natural)
        (.arrow .reusable .unrestricted kilo .natural))).toBool = true := by
  decide +kernel

/-- An anonymous record of the same layout is neither kind: structural records stay structural. -/
example :
    sameType {} mile distance = false ∧ sameType {} kilo distance = false ∧ sameType {} mile kilo = false ∧
      sameType {} mile mile = true := by
  decide +kernel

/-- An extension constructing an instance of another kind overwrites the brand: `{#kind: Kilo}`
under `{#kind: Mile, n}` is a Kilo (the first field of a name is the one a row shows). -/
example :
    sameType {} (.field brandLabel (kindTy "Units.Kilo") mile) kilo = true ∧
      sameType {} (.field brandLabel (kindTy "Units.Kilo") mile) mile = false := by
  decide +kernel

end Obend.Core.Nominal

end
