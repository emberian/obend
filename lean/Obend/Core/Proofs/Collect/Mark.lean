module
/- Marking is sound: the marks contain the roots and are closed. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

theorem pending_nil {marks : Array Bool} {work : List Nat} (drained : pending marks work = []) :
    ∀ x ∈ work, marks[x]? ≠ some false := by
  induction work with
  | nil => intro x member; cases member
  | cons head rest ih =>
    intro x member
    simp only [pending] at drained
    split at drained
    · cases drained
    · rename_i notFalse
      rcases List.mem_cons.mp member with rfl | member
      · exact notFalse
      · exact ih drained x member

theorem pending_cons {marks : Array Bool} {work rest : List Nat} {address : Nat}
    (next : pending marks work = address :: rest) :
    marks[address]? = some false ∧ ∀ x ∈ work, marks[x]? ≠ some false ∨ x ∈ address :: rest := by
  induction work with
  | nil => simp [pending] at next
  | cons head tail ih =>
    simp only [pending] at next
    split at next
    · rename_i isFalse
      cases next
      exact ⟨isFalse, fun x member => .inr member⟩
    · rename_i notFalse
      obtain ⟨first, others⟩ := ih next
      refine ⟨first, fun x member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact .inl notFalse
      · exact others x member

public theorem bound_of_some {α : Type} {xs : Array α} {i : Nat} {v : α} (found : xs[i]? = some v) :
    i < xs.size := (Array.getElem?_eq_some_iff.mp found).1

theorem count_false_set {marks : Array Bool} {address : Nat}
    (unmarked : marks[address]? = some false) :
    (marks.set! address true).count false + 1 = marks.count false := by
  have bound : address < marks.size := bound_of_some unmarked
  have entry : marks[address] = false := by simpa [Array.getElem?_eq_getElem bound] using unmarked
  have positive : 0 < marks.count false := by
    have member : false ∈ marks := Array.mem_of_getElem? unmarked
    exact Nat.pos_of_ne_zero (fun h => (Array.count_eq_zero.mp h) member)
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, bound, dite_true]
  rw [Array.count_set bound]
  simp [entry]
  omega

theorem all_marked {marks : Array Bool} (none : marks.count false = 0) (address : Nat) :
    marks[address]? ≠ some false := by
  intro isFalse
  have member : false ∈ marks := Array.mem_of_getElem? isFalse
  exact (Array.count_eq_zero.mp none) member

/-- The marking invariant: every unmarked child of a marked cell is still to be traced. -/
@[expose] public def Traced (heap : Array Cell) (marks : Array Bool) (work : List Nat) : Prop :=
  ∀ a x : Nat, marks[a]? = some true → x ∈ children heap a → marks[x]? = some false → x ∈ work

public theorem markFrom_spec (heap : Array Cell) :
    ∀ (fuel : Nat) (marks : Array Bool) (work : List Nat),
      marks.size = heap.size → marks.count false ≤ fuel → Traced heap marks work →
      (markFrom heap fuel marks work).size = heap.size ∧
      (∀ a : Nat, marks[a]? = some true → (markFrom heap fuel marks work)[a]? = some true) ∧
      (∀ x ∈ work, (markFrom heap fuel marks work)[x]? ≠ some false) ∧
      (∀ a x : Nat, (markFrom heap fuel marks work)[a]? = some true → x ∈ children heap a →
        (markFrom heap fuel marks work)[x]? ≠ some false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro marks work size count _
    have none : marks.count false = 0 := by omega
    simp only [markFrom]
    exact ⟨size, fun _ h => h, fun x _ => all_marked none x, fun _ x _ _ => all_marked none x⟩
  | succ fuel ih =>
    intro marks work size count traced
    simp only [markFrom]
    split
    · rename_i drained
      have done := pending_nil drained
      refine ⟨size, fun _ h => h, done, ?_⟩
      intro a x marked child isFalse
      exact done x (traced a x marked child isFalse) isFalse
    · rename_i address rest next
      obtain ⟨unmarked, covered⟩ := pending_cons next
      have bound : address < marks.size := bound_of_some unmarked
      have setAt : ∀ b, (marks.set! address true)[b]? = if address = b then some true else marks[b]? := by
        intro b; simp [Array.getElem?_setIfInBounds, bound]
      have size' : (marks.set! address true).size = heap.size := by simpa using size
      have count' : (marks.set! address true).count false ≤ fuel := by
        have := count_false_set unmarked; omega
      have traced' : Traced heap (marks.set! address true) (children heap address ++ rest) := by
        intro b x marked child isFalse
        rw [setAt] at marked isFalse
        by_cases same : address = b
        · subst same; exact List.mem_append_left _ child
        · rw [if_neg same] at marked
          by_cases sameX : address = x
          · rw [if_pos sameX] at isFalse; cases isFalse
          · rw [if_neg sameX] at isFalse
            have inWork := traced b x marked child isFalse
            rcases covered x inWork with notFalse | member
            · exact absurd isFalse notFalse
            · rcases List.mem_cons.mp member with rfl | member
              · exact absurd rfl sameX
              · exact List.mem_append_right _ member
      obtain ⟨outSize, monotone, drains, closed⟩ := ih _ _ size' count' traced'
      refine ⟨outSize, ?_, ?_, closed⟩
      · intro a marked
        apply monotone
        rw [setAt]; split
        · rfl
        · exact marked
      · intro x member
        rcases covered x member with notFalse | member
        · intro isFalse
          by_cases sameX : address = x
          · subst sameX
            have := monotone address (by rw [setAt]; simp)
            rw [this] at isFalse; cases isFalse
          · cases hx : marks[x]? with
            | none =>
              have : x ≥ marks.size := Array.getElem?_eq_none_iff.mp hx
              have : (markFrom heap fuel (marks.set! address true) (children heap address ++ rest))[x]? = none :=
                Array.getElem?_eq_none (by rw [outSize, ← size]; exact this)
              rw [this] at isFalse; cases isFalse
            | some value =>
              cases value with
              | false => exact notFalse hx
              | true =>
                have := monotone x (by rw [setAt, if_neg sameX]; exact hx)
                rw [this] at isFalse; cases isFalse
        · rcases List.mem_cons.mp member with same | member
          · have := monotone address (by rw [setAt]; simp)
            rw [same, this]; simp
          · exact drains x (List.mem_append_right _ member)

/-- **Marking soundness.** The live marks cover the heap, contain every root in the
heap, and are closed: a marked cell's in-heap children are marked. -/
public theorem liveMarks_spec (state : State) :
    (liveMarks state).size = state.heap.size ∧
    (∀ x ∈ rootAddresses state, (liveMarks state)[x]? ≠ some false) ∧
    (∀ a x : Nat, (liveMarks state)[a]? = some true → x ∈ children state.heap a →
      (liveMarks state)[x]? ≠ some false) := by
  have initial := markFrom_spec state.heap state.heap.size (Array.replicate state.heap.size false)
    (rootAddresses state) (by simp) (by simp)
    (by intro a x marked; simp [Array.getElem?_replicate] at marked)
  exact ⟨initial.1, initial.2.2.1, initial.2.2.2⟩

end Obend.Core.Collect
