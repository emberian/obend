module

@[expose] public section
namespace Obend.Core

/-- Nonnegative resource grades: an ordered commutative additive monoid.
The least element is zero, so combining budgets covers either component.
No total order, subtraction, or cancellation is required. -/
class Graded (R : Type) extends Lean.Grind.AddCommMonoid R, LE R where
  le_refl : ∀ r : R, r ≤ r
  le_trans : ∀ {r s t : R}, r ≤ s → s ≤ t → r ≤ t
  le_antisymm : ∀ {r s : R}, r ≤ s → s ≤ r → r = s
  zero_le : ∀ r : R, 0 ≤ r
  add_mono : ∀ {r s t u : R}, r ≤ s → t ≤ u → r + t ≤ s + u

namespace Graded
variable {R : Type} [Graded R]

instance : Std.IsPartialOrder R where
  le_refl := Graded.le_refl
  le_trans := fun _ _ _ => Graded.le_trans
  le_antisymm := fun _ _ => Graded.le_antisymm

theorem le_add_right (r s : R) : r ≤ r + s := by
  have h := add_mono (le_refl r) (zero_le s)
  simpa only [Lean.Grind.AddCommMonoid.add_zero] using h

theorem le_add_left (r s : R) : s ≤ r + s := by
  rw [Lean.Grind.AddCommMonoid.add_comm]
  exact le_add_right s r

/-- A monotone judgment can use a joint budget without changing its meaning. -/
theorem lift {P : R → Prop} (mono : ∀ {r s}, P r → r ≤ s → P s)
    {r s : R} (h : P r) (covered : r ≤ s) : P s := mono h covered

instance : Graded Nat where
  le := Nat.le
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
  le_antisymm := Nat.le_antisymm
  zero_le := Nat.zero_le
  add_mono := Nat.add_le_add

end Graded
end Obend.Core
