module
public import Obend.Core.FieldCongruence
@[expose] public section
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Every label collected by the finite alphabet scanner has a visible first
emission, using exactly the same finite visitation budget. -/
public theorem scanLabels_mem_true_emits (a : Assumptions) (remaining : List Ty)
    (row : Ty) (label : String) (presentLabel : label ∈ scanLabels a remaining row) :
    ∃ member tail, scanStream a remaining label true row = .emit member tail := by
  rw [scanLabels] at presentLabel
  split at presentLabel
  · rename_i observation exposed
    split at presentLabel
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at presentLabel
      · rename_i present
        rcases (mem_insertLabel name label _).mp presentLabel with same | nested
        · subst label
          refine ⟨member, tail, ?_⟩
          rw [scanStream, exposed]
          simp [present]
        · by_cases same : name = label
          · subst label
            refine ⟨member, tail, ?_⟩
            rw [scanStream, exposed]
            simp [present]
          · obtain ⟨found, rest, emitted⟩ :=
              scanLabels_mem_true_emits a (remaining.erase row) tail label nested
            refine ⟨found, rest, ?_⟩
            rw [scanStream, exposed]
            simpa [present, same] using emitted
      · simp_all
    · simp_all
  · simp_all
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

/-- The row alphabet is precisely the set of labels with a visible emission. -/
public theorem labels_iff_true_emits (a : Assumptions) (row : Ty) (label : String) :
    label ∈ labels a row ↔ ∃ member tail, streamStep a row label true = .emit member tail := by
  constructor
  · exact scanLabels_mem_true_emits a (support a row row) row label
  · rintro ⟨member, tail, emitted⟩
    exact Obend.Core.TypeGraph.scan_emission_label a (support a row row) label true
      row member tail emitted

end Obend.Core.RecursiveRows
