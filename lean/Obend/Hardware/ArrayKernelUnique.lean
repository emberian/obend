module
public import Std.Data.HashSet.Lemmas
@[expose] public section

/-! Hash-set-backed uniqueness checking for the array source's scatter addresses. -/
namespace Obend.Hardware.ArrayKernel.Unique
set_option autoImplicit false

abbrev Address := Nat × Nat

/-- Linear expected-time duplicate detection. The set is threaded through the recursion and can
be updated in place by the evaluator; no pairwise event relation is constructed. -/
def insertUnique (seen : Std.HashSet Address) : List Address → Bool
  | [] => true
  | a :: rest => !(seen.contains a) && insertUnique (seen.insert a) rest

def checkUnique (addresses : List Address) : Bool := insertUnique ∅ addresses

theorem insertUnique_sound (addresses : List Address) (seen : Std.HashSet Address)
    (h : insertUnique seen addresses = true) :
    addresses.Nodup ∧ ∀ a ∈ addresses, seen.contains a = false := by
  induction addresses generalizing seen with
  | nil => simp
  | cons a rest ih =>
    simp only [insertUnique, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hr := ih (seen.insert a) h.2
    refine ⟨List.nodup_cons.mpr ⟨?_, hr.1⟩, ?_⟩
    · intro ha
      have := hr.2 a ha
      simpa using this
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h.1
      · have hb' := hr.2 b hb
        simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at hb'
        exact hb'.2

/-- Successful admission establishes mathematical uniqueness of every scatter address. -/
theorem checkUnique_sound (addresses : List Address) (h : checkUnique addresses = true) :
    addresses.Nodup := (insertUnique_sound addresses ∅ h).1

end Obend.Hardware.ArrayKernel.Unique
