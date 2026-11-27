module
import all Obend.Category.ObservationDescent
import Obend.Tactic.Tooth

public section
namespace Obend.Teeth.ObservationDescent
open Obend.Category.ObservationDescent

/-- Giving both copies the same visible name hides their distinct internal bit. -/
example : ¬ Descends (fun _ : Bool => ()) (· = true) := by
  intro h
  exact Bool.noConfusion (((descends_iff_invariant _ _).mp h true false rfl).mp rfl)

/-- Querying a bit carried in the view is possible for both bit values. -/
example : Descends (id : Bool → Bool) (· = true) :=
  ⟨(· = true), fun _ => Iff.rfl⟩

#tooth Obend.Category.ObservationDescent.descends_iff_invariant by
  mutation Obend.Category.ObservationDescent.Descends := fun {World View} (_ : World → View) _ => True

#tooth Obend.Category.ObservationDescent.descends_insert_copy_iff by
  mutation Obend.Category.ObservationDescent.Descends := fun {World View} (_ : World → View) _ => True

end Obend.Teeth.ObservationDescent
end
