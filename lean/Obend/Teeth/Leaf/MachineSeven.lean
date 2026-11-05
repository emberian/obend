/-
# Obend.Teeth.Leaf.MachineSeven — `twiceOfThree` on the demand machine, from the book and the object

Not a `module`, for the reason `Obend.Teeth.Core.Force` gives: `decide +kernel` runs the demand
machine (`Obend.Core.Machine.runBounded`) through `Array` functions whose bodies `Init` does not
expose to `module` files. The book of `compose(Base, Twice, Augmented)` and the object
`fix (compose …) {seed}` both finish at `7` on the machine; with `Override` composed last the object
finishes at `3`.
-/
import Obend.Teeth.Leaf.ReviewTeeth
import Obend.Core.Machine

namespace Obend.Teeth.Leaf.Review
open Obend.Core.Machine

/-- The natural the demand machine finishes with. -/
def machineNat (t : Obend.Core.Term.Term) : Option Nat :=
  match runBounded ⟨100000, 100000⟩ 5000 (initial t) with
  | .finished (.natural n) _ => some n
  | _ => none

example : machineNat (bookTwiceOfThree (comp 1)) = some 7 := by decide +kernel

example : machineNat (objectTwiceOfThree (comp 1)) = some 7 := by decide +kernel

example : machineNat (objectTwiceOfThree overridden) = some 3 := by decide +kernel

end Obend.Teeth.Leaf.Review
