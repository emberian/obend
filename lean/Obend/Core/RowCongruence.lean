module
/- The coalgebraic part of row congruence. Scanner normalization is isolated
from coinduction: no traversal of an unbounded emitted stream is needed. -/
public import Obend.Core.RowHit
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

abbrev StreamEquivalent (a : Assumptions) (r s : Ty) (name : String)
    (first : Bool) : Prop :=
  FP.Bisimilar (graph a) (.stream r name first) (.stream s name first)

/-- The useful end law (kept separate to avoid any dependence on end payloads). -/
def HideEndLaw (a : Assumptions) : Prop :=
  ∀ r name ending, RR.streamStep a r name true = .end ending →
    FP.Bisimilar (graph a) (.stream r name false) (.stream r name true)

/-- A true-mode scan ending has encountered no matching field, so false mode
follows exactly the same finite epsilon path, including the same cycle cutoff. -/
theorem scanStream_hide_end (a : Assumptions) (remaining : List Ty)
    (name : String) (row : Ty) (ending : RR.Tail)
    (ended : Obend.Core.RecursiveRows.scanStream a remaining name true row = .end ending) :
    Obend.Core.RecursiveRows.scanStream a remaining name false row = .end ending := by
  rw [Obend.Core.RecursiveRows.scanStream] at ended
  split at ended
  · rename_i index exposed
    rw [Obend.Core.RecursiveRows.scanStream, exposed]
    exact ended
  · rename_i index exposed
    rw [Obend.Core.RecursiveRows.scanStream, exposed]
    exact ended
  · rename_i observation exposed
    split at ended
    · rw [Obend.Core.RecursiveRows.scanStream, exposed]
      simp_all
    · rename_i fieldName member tail tag children
      have shape : observation = ⟨.field fieldName, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      rw [Obend.Core.RecursiveRows.scanStream, exposed]
      split at ended
      · rename_i available
        simp only [available, ↓reduceDIte]
        split at ended
        · contradiction
        · rename_i skipped
          have different : (fieldName == name) = false := by simpa using skipped
          simp only [different, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact scanStream_hide_end a (remaining.erase row) name tail ending ended
      · rename_i absent
        simpa only [absent, ↓reduceDIte] using ended
    · rw [Obend.Core.RecursiveRows.scanStream, exposed]
      simp_all
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

/-- Resourceful visible entries are already present in the hidden stream.
This is exact scan equality even before choosing a complete support. -/
theorem scanStream_hide_resourceful (a : Assumptions) (remaining : List Ty)
    (name : String) (row member tail : Ty)
    (resourceful : RR.shareable a member = false)
    (emitted : Obend.Core.RecursiveRows.scanStream a remaining name true row = .emit member tail) :
    Obend.Core.RecursiveRows.scanStream a remaining name false row = .emit member tail := by
  rw [Obend.Core.RecursiveRows.scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at emitted
    · contradiction
    · rename_i fieldName fieldMember fieldTail tag children
      have shape : observation = ⟨.field fieldName, [fieldMember, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      rw [Obend.Core.RecursiveRows.scanStream, exposed]
      split at emitted
      · rename_i available
        simp only [available, ↓reduceDIte]
        split at emitted
        · rename_i matched
          have matching : (fieldName == name) = true := by simpa using matched
          cases emitted
          simp only [matching, resourceful, Bool.not_false, Bool.false_or,
            Bool.true_and, ↓reduceIte]
        · rename_i skipped
          have different : (fieldName == name) = false := by simpa using skipped
          simp only [different, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact scanStream_hide_resourceful a (remaining.erase row) name fieldTail
            member tail resourceful emitted
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

/-- The resourceful branch of hide-emit normalization is fully discharged. -/
theorem hide_emit_resourceful (a : Assumptions) (row member tail : Ty) (name : String)
    (resourceful : RR.shareable a member = false)
    (emitted : RR.streamStep a row name true = .emit member tail) :
    FP.Bisimilar (graph a) (.stream row name false) (.stream row name true) := by
  have hidden : RR.streamStep a row name false = .emit member tail :=
    scanStream_hide_resourceful a _ name row member tail resourceful emitted
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe a (.stream row name false)).1 =
      (observe a (.stream row name true)).1
    simp only [observe, hidden, emitted]
  · change Obend.Core.FiniteBisimulation.Children _
      (observe a (.stream row name false)).2 (observe a (.stream row name true)).2
    simp only [observe, hidden, emitted, Obend.Core.FiniteBisimulation.Children]
    have eqv := FP.bisimilar_equivalence (graph a)
    exact ⟨eqv.refl _, eqv.refl _, True.intro⟩

/-- Fully discharged end normalization; no support or resource premise. -/
theorem hide_end (a : Assumptions) : HideEndLaw a := by
  intro row name ending ended
  have hidden : RR.streamStep a row name false = .end ending :=
    scanStream_hide_end a _ name row ending ended
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe a (.stream row name false)).1 =
      (observe a (.stream row name true)).1
    simp only [observe, hidden, ended]
  · change Obend.Core.FiniteBisimulation.Children _
      (observe a (.stream row name false)).2 (observe a (.stream row name true)).2
    simp only [observe, hidden, ended, Obend.Core.FiniteBisimulation.Children]

/-- Equality of visible streams transports hiding. Shareability is read from
member type observations; this proof consumes only one graph step. -/
theorem hide_visible_congruence {a : Assumptions}
    (shareInvariant : ∀ {x y}, Equivalent a x y → RR.shareable a x = RR.shareable a y)
    {r s : Ty} {name : String} (h : StreamEquivalent a r s name true) :
    StreamEquivalent a r s name false := by
  have hideEmit (r : Ty) (name : String) (member tail : Ty)
      (emitted : RR.streamStep a r name true = .emit member tail) :
      FP.Bisimilar (graph a) (.stream r name false)
        (if RR.shareable a member then .stream tail name false else .stream r name true) := by
    cases resource : RR.shareable a member with
    | false =>
      simpa only [resource, Bool.false_eq_true, ↓reduceIte] using
        hide_emit_resourceful a r member tail name resource emitted
    | true =>
      simpa only [resource, ↓reduceIte] using
        RowHit.hide_emit_shareable a name r member tail emitted resource
  have eqv := FP.bisimilar_equivalence (graph a)
  obtain ⟨labels, children⟩ :=
    Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ h
  cases left : RR.streamStep a r name true with
  | «end» ending =>
    cases right : RR.streamStep a s name true with
    | «end» ending' =>
      exact eqv.trans (hide_end a r name ending left)
        (eqv.trans h (eqv.symm (hide_end a s name ending' right)))
    | emit member tail => simp [graph, observe, left, right] at labels
  | emit member tail =>
    cases right : RR.streamStep a s name true with
    | «end» ending => simp [graph, observe, left, right] at labels
    | emit member' tail' =>
      have nested : Equivalent a member member' ∧ StreamEquivalent a tail tail' name false := by
        simpa [graph, observe, left, right,
          Obend.Core.FiniteBisimulation.Children, Equivalent, StreamEquivalent] using children
      have share := shareInvariant nested.1
      have middle : FP.Bisimilar (graph a)
          (if RR.shareable a member then .stream tail name false else .stream r name true)
          (if RR.shareable a member' then .stream tail' name false else .stream s name true) := by
        rw [← share]
        cases RR.shareable a member <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact h
        · exact nested.2
      exact eqv.trans (hideEmit r name member tail left)
        (eqv.trans middle (eqv.symm (hideEmit s name member' tail' right)))

#assert_axioms scanStream_hide_end scanStream_hide_resourceful hide_end
  hide_emit_resourceful hide_visible_congruence

#assert_axioms scanStream_hide_end scanStream_hide_resourceful hide_emit_resourceful
  hide_end hide_visible_congruence

end Obend.Core.TypeGraph
