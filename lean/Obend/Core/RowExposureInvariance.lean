module
public import Obend.Core.RowHit
public import Obend.AxiomPin

namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
namespace Search
export Obend.Core.RowSearch (Step Hit find find_step_eq)
end Search
set_option autoImplicit false

def labelStep (a : Assumptions) (wanted : String) (row : Ty) : Search.Step Ty Unit :=
  match expose a row with
  | .constructor observation =>
    match observation.tag, observation.children with
    | .field name, [_, tail] => if name = wanted then .emit () else .skip tail
    | _, _ => .stop
  | _ => .stop

theorem labelStep_skip_support (a : Assumptions) (left right row tail : Ty) (wanted : String)
    (present : row ∈ support a left right) (skipped : labelStep a wanted row = .skip tail) :
    tail ∈ support a left right := by
  rw [labelStep] at skipped
  split at skipped
  · rename_i observation exposed
    split at skipped
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at skipped
      · contradiction
      · cases skipped
        exact expose_children_support present exposed tail (by simp)
    · contradiction
  · contradiction

theorem labels_find_projection (a : Assumptions) (remaining : List Ty) (row : Ty) (wanted : String) :
    wanted ∈ scanLabels a remaining row ↔ Search.find (labelStep a wanted) remaining row = some () := by
  rw [scanLabels]
  split
  · rename_i observation exposed
    split
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      rw [Search.find, labelStep, exposed]
      by_cases present : row ∈ remaining
      · by_cases same : name = wanted
        · subst name
          simp [present, mem_insertLabel]
        · simpa [present, same, Ne.symm same, mem_insertLabel] using
            labels_find_projection a (remaining.erase row) tail wanted
      · by_cases same : name = wanted <;> simp [present, same]
    · rw [Search.find, labelStep, exposed]
      simp_all
  · rw [Search.find, labelStep]
    split <;> simp_all
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

public theorem insertLabel_sorted (name : String) (xs : List String)
    (sorted : xs.Pairwise (· < ·)) : (insertLabel name xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [insertLabel]
  | cons prior rest ih =>
    obtain ⟨before, tailSorted⟩ := List.pairwise_cons.mp sorted
    rw [insertLabel]
    split
    · exact sorted
    · rename_i different
      split
      · rename_i earlier
        apply List.pairwise_cons.mpr
        refine ⟨?_, sorted⟩
        intro item present
        rcases List.mem_cons.mp present with same | nested
        · simpa only [same] using earlier
        · exact String.lt_trans earlier (before item nested)
      · rename_i later
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih tailSorted⟩
        intro item present
        rcases (mem_insertLabel name item rest).mp present with same | nested
        · subst item
          exact Std.lt_of_le_of_ne (String.not_lt.mp later) (Ne.symm different)
        · exact before item nested

public theorem scanLabels_sorted (a : Assumptions) (remaining : List Ty) (row : Ty) :
    (scanLabels a remaining row).Pairwise (· < ·) := by
  rw [scanLabels]
  split
  · split
    · split
      · rename_i present
        apply insertLabel_sorted
        exact scanLabels_sorted a (remaining.erase row) _
      · simp
    · simp
  · simp
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

public theorem sorted_ext (xs ys : List String) (one : xs.Pairwise (· < ·))
    (two : ys.Pairwise (· < ·)) (same : ∀ name, name ∈ xs ↔ name ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons name rest => have impossible := (same name).mpr (by simp); simp at impossible
  | cons first rest ih =>
    cases ys with
    | nil => have impossible := (same first).mp (by simp); simp at impossible
    | cons other tail =>
      obtain ⟨beforeOne, sortedOne⟩ := List.pairwise_cons.mp one
      obtain ⟨beforeTwo, sortedTwo⟩ := List.pairwise_cons.mp two
      have firstOccurs := (same first).mp (show first ∈ first :: rest from by simp)
      have otherOccurs := (same other).mpr (show other ∈ other :: tail from by simp)
      have heads : first = other := by
        rcases List.mem_cons.mp firstOccurs with equal | nested
        · exact equal
        · rcases List.mem_cons.mp otherOccurs with equal | nested'
          · exact equal.symm
          · exact False.elim (String.lt_asymm (beforeOne other nested') (beforeTwo first nested))
      subst other
      have tails : ∀ name, name ∈ rest ↔ name ∈ tail := by
        intro name
        constructor
        · intro nested
          rcases List.mem_cons.mp ((same name).mp (List.mem_cons_of_mem _ nested)) with equal | inside
          · subst name
            exact False.elim (String.lt_irrefl first (beforeOne first nested))
          · exact inside
        · intro nested
          rcases List.mem_cons.mp ((same name).mpr (List.mem_cons_of_mem _ nested)) with equal | inside
          · subst name
            exact False.elim (String.lt_irrefl first (beforeTwo first nested))
          · exact inside
      exact congrArg (List.cons first) (ih tail sortedOne sortedTwo tails)

public theorem labels_expose_eq (a : Assumptions) (left right : Ty)
    (heads : expose a left = expose a right) : labels a left = labels a right := by
  apply sorted_ext _ _ (scanLabels_sorted a _ left) (scanLabels_sorted a _ right)
  intro wanted
  have initial : labelStep a wanted left = labelStep a wanted right := by
    simp only [labelStep, heads]
  have same := Search.find_step_eq (support a left left) (support a right right)
    (fun x y present skipped => labelStep_skip_support a left left x y wanted present skipped)
    (fun x y present skipped => labelStep_skip_support a right right x y wanted present skipped)
    (left_mem_support a left left) (left_mem_support a right right) initial
  change wanted ∈ scanLabels a (support a left left) left ↔
    wanted ∈ scanLabels a (support a right right) right
  rw [labels_find_projection, labels_find_projection, same]

/-- Residual terminal search retains raw non-row types. Consequently its heads
are exposure-invariant only on row constructors, not on arbitrary scalar aliases. -/
def residualStep (a : Assumptions) (row : Ty) : Search.Step Ty Tail :=
  match expose a row with
  | .nominal index => .emit (.nominal index)
  | .unproductive index => .emit (.unproductive index)
  | .constructor observation =>
    match observation.tag, observation.children with
    | .emptyRow, _ => .emit .closed
    | .field _, [_, tail] => .skip tail
    | _, _ => .emit (.nonRow row)

theorem residualStep_skip_support (a : Assumptions) (left right row tail : Ty)
    (present : row ∈ support a left right) (skipped : residualStep a row = .skip tail) :
    tail ∈ support a left right := by
  rw [residualStep] at skipped
  split at skipped
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at skipped
    · contradiction
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      cases skipped
      exact expose_children_support present exposed tail (by simp)
    · contradiction

theorem residual_find_projection (a : Assumptions) (left right : Ty)
    (remaining : List Ty) (row : Ty)
    (present : row ∈ support a left right)
    (coversTerminals : ∀ x payload, x ∈ support a left right →
      residualStep a x = .emit payload → x ∈ remaining) :
    scanResidual a remaining row =
      (Search.find (residualStep a) remaining row).getD .productiveCycle := by
  rw [scanResidual]
  split
  · rename_i index exposed
    have covered := coversTerminals row (.nominal index) present (by simp [residualStep, exposed])
    rw [Search.find, residualStep, exposed]
    simp [covered]
  · rename_i index exposed
    have covered := coversTerminals row (.unproductive index) present (by simp [residualStep, exposed])
    rw [Search.find, residualStep, exposed]
    simp [covered]
  · rename_i observation exposed
    split
    · have emitted : residualStep a row = .emit .closed := by
        simp_all [residualStep]
      have covered := coversTerminals row .closed present emitted
      rw [Search.find, emitted]
      simp [covered]
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have skipped : residualStep a row = .skip tail := by simp [residualStep, exposed]
      rw [Search.find, skipped]
      split
      · rename_i available
        simp only [available, ↓reduceDIte]
        apply residual_find_projection a left right (remaining.erase row) tail
          (expose_children_support present exposed tail (by simp))
        intro x payload inside emitted
        have different : x ≠ row := by
          intro same
          subst x
          rw [skipped] at emitted
          contradiction
        exact (List.mem_erase_of_ne different).mpr (coversTerminals x payload inside emitted)
      · rename_i unavailable
        simp [unavailable]
    · have emitted : residualStep a row = .emit (.nonRow row) := by
        simp_all [residualStep]
      have covered := coversTerminals row (.nonRow row) present emitted
      rw [Search.find, emitted]
      simp [covered]
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

theorem residual_projection (a : Assumptions) (row : Ty) :
    residual a row = (Search.find (residualStep a) (support a row row) row).getD .productiveCycle :=
  residual_find_projection a row row _ row (left_mem_support a row row)
    (fun _ _ present _ => present)

public theorem residual_expose_eq (a : Assumptions) (left right : Ty) (observation : Constructor)
    (one : expose a left = .constructor observation) (heads : expose a left = expose a right)
    (rowHead : Obend.Core.TypeGraph.rowTag observation.tag = true) :
    residual a left = residual a right := by
  have initial : residualStep a left = residualStep a right := by
    obtain ⟨source, _, raw⟩ := expose_origin (left_mem_support a left right) one
    have other : expose a right = .constructor observation := heads.symm.trans one
    cases source <;> simp only [constructorHead, Head.constructor.injEq] at raw
    all_goals try contradiction
    all_goals subst observation
    all_goals simp_all [Obend.Core.TypeGraph.rowTag, residualStep]
  rw [residual_projection, residual_projection]
  congr 1
  exact Search.find_step_eq (support a left left) (support a right right)
    (fun x y present skipped => residualStep_skip_support a left left x y present skipped)
    (fun x y present skipped => residualStep_skip_support a right right x y present skipped)
    (left_mem_support a left left) (left_mem_support a right right) initial

/-- Resetting the finite scan after one field does not change its terminal
residual. Productive-cycle markers and nominal tails remain exact. -/
public theorem residual_field (a : Assumptions) (name : String) (member tail : Ty) :
    residual a (.field name member tail) = residual a tail := by
  have skipped : residualStep a (.field name member tail) = .skip tail := by
    simp [residualStep, raw_field_observation]
  have same := Obend.Core.RowSearch.find_path_eq
    (support a (.field name member tail) (.field name member tail)) (support a tail tail)
    (fun x y present step => residualStep_skip_support a _ _ x y present step)
    (fun x y present step => residualStep_skip_support a tail tail x y present step)
    (left_mem_support a _ _) (left_mem_support a tail tail)
    (Obend.Core.RowSearch.SkipPath.cons _ tail tail skipped (.refl tail))
  rw [residual_projection, residual_projection, same]

/-- A field contributes exactly its label to the local sorted alphabet,
independently of the fresh finite-support budget used for its tail. -/
public theorem labels_field (a : Assumptions) (name : String) (member tail : Ty) :
    labels a (.field name member tail) = insertLabel name (labels a tail) := by
  apply sorted_ext _ _ (scanLabels_sorted a _ _)
    (insertLabel_sorted name _ (scanLabels_sorted a _ tail))
  intro wanted
  change wanted ∈ scanLabels a
      (support a (.field name member tail) (.field name member tail)) (.field name member tail) ↔ _
  rw [labels_find_projection, mem_insertLabel]
  by_cases sameName : wanted = name
  · subst wanted
    rw [Search.find, labelStep, raw_field_observation]
    simp [left_mem_support]
  · have skipped : labelStep a wanted (.field name member tail) = .skip tail := by
      simp [labelStep, raw_field_observation, Ne.symm sameName]
    have same := Obend.Core.RowSearch.find_path_eq
      (support a (.field name member tail) (.field name member tail)) (support a tail tail)
      (fun x y present step => labelStep_skip_support a _ _ x y wanted present step)
      (fun x y present step => labelStep_skip_support a tail tail x y wanted present step)
      (left_mem_support a _ _) (left_mem_support a tail tail)
      (Obend.Core.RowSearch.SkipPath.cons _ tail tail skipped (.refl tail))
    rw [same]
    simpa only [sameName, false_or, labels] using
      (labels_find_projection a (support a tail tail) tail wanted).symm

#assert_axioms labels_find_projection insertLabel_sorted scanLabels_sorted sorted_ext labels_expose_eq
  residual_find_projection residual_projection residual_expose_eq
  residual_field labels_field

end Obend.Core.RecursiveRows
