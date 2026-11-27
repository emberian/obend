module
import all Obend.Category.Projection
import Obend.Tactic.Tooth

/-! A mixed fiber, a missing fiber and a surjective comparison with two distinct lifts.
These examples fix the polarity of the quantifiers and exhibit why uniqueness is unnecessary
in the predicate-level Beck–Chevalley theorem. -/
public section
namespace Obend.Teeth.Projection
open Obend.Category.Projection

example : existsAlong (fun _ : Bool => false) (· = true) false ∧
    ¬ forallAlong (fun _ : Bool => false) (· = true) false :=
  ⟨⟨true, rfl, rfl⟩, fun all => Bool.noConfusion (all false rfl)⟩

example : ¬ existsAlong (fun _ : Bool => false) (fun _ => True) true ∧
    forallAlong (fun _ : Bool => false) (fun _ => False) true :=
  ⟨fun ⟨_, h, _⟩ => Bool.noConfusion h, fun _ h => Bool.noConfusion h⟩

example : FiberwiseSurjective (id : Unit → Unit) (fun _ : Bool => ())
    (fun _ : Bool => ()) id ∧
    ∃ x y : Bool, x ≠ y ∧ (fun _ : Bool => ()) x = (fun _ : Bool => ()) y := by
  constructor
  · rintro ⟨⟩ ⟨⟩ _
    exact ⟨false, rfl, rfl⟩
  · exact ⟨false, true, by decide, rfl⟩

#tooth Obend.Category.Projection.exists_adj by
  mutation Obend.Category.Projection.existsAlong := fun {E B} (_ : E → B) _ _ => False

#tooth Obend.Category.Projection.forall_adj by
  mutation Obend.Category.Projection.forallAlong := fun {E B} (_ : E → B) _ _ => True

#tooth Obend.Category.Projection.exists_baseChange_iff by
  mutation Obend.Category.Projection.FiberwiseSurjective := fun {E B E' B'}
    (_ : E → B) (_ : E' → B') _ _ => True

#tooth Obend.Category.Projection.forall_baseChange_iff by
  mutation Obend.Category.Projection.FiberwiseSurjective := fun {E B E' B'}
    (_ : E → B) (_ : E' → B') _ _ => True

end Obend.Teeth.Projection
end
