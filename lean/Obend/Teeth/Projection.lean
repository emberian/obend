module
import all Obend.Category.Projection
import all Obend.Category.FiberGrowth
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

/- Both worlds realize every Boolean value somewhere and have a point over each name.
Swapping the values between names nevertheless changes which value is visible at `false`.
The two mutations drop precisely the name guard or the value guard. -/
example : (∀ v : Bool, ∃ e : Bool, !e = v) ∧
    (∃ e : Bool, id e = false) ∧
    Obend.Category.FiberGrowth.observes id id false false ∧
    ¬ Obend.Category.FiberGrowth.observes id Bool.not false false := by
  refine ⟨?_, ⟨false, rfl⟩, ⟨false, rfl, rfl⟩, ?_⟩
  · intro v
    cases v
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  · rintro ⟨e, he, hv⟩
    change e = false at he
    subst e
    exact Bool.noConfusion hv

#tooth Obend.Category.FiberGrowth.exists_observations_iff by
  mutation Obend.Category.FiberGrowth.observes :=
    fun {E B V} (_ : E → B) (h : E → V) _ v => ∃ e, h e = v

#tooth Obend.Category.FiberGrowth.forall_observations_iff by
  mutation Obend.Category.FiberGrowth.observes :=
    fun {E B V} (p : E → B) (_ : E → V) b _ => ∃ e, p e = b

end Obend.Teeth.Projection
end
