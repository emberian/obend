module
public import Obend.Core.RowCongruence
public import Obend.Core.RowExposureInvariance
public import Obend.Core.TypeGraphResource
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.FiniteBisimulation (Children)
namespace Rows
export Obend.Core.RecursiveRows (scanStream scanLabels scanResidual labels residual streamStep
  labels_field residual_field shareable_field mem_insertLabel)
end Rows
set_option autoImplicit false

/-- Reading the row interface from graph labels works for every type, including
nominal, opaque-cycle, and ordinary non-row tails. -/
def labelAlphabet : Label → List String
  | .row names _ _ => names
  | _ => []

def labelResidual : Label → TailKind
  | .nominal index => .nominal index
  | .unproductive index => .unproductive index
  | .row _ ending _ => ending
  | _ => .nonRow

def isRowLabel : Label → Bool
  | .row _ _ _ => true
  | _ => false

def isOrdinaryLabel : Label → Bool
  | .ordinary _ _ => true
  | _ => false

 theorem nonrow_scans (a : Assumptions) (t : Ty) (observation : Constructor)
    (head : expose a t = .constructor observation) (nonrow : rowTag observation.tag ≠ true) :
    RR.labels a t = [] ∧ RR.residual a t = .nonRow t := by
  cases observation with
  | mk tag children =>
    cases tag <;> simp_all [rowTag, RR.labels, Rows.scanLabels, RR.residual, Rows.scanResidual]

 theorem observed_alphabet (a : Assumptions) (t : Ty) :
    labelAlphabet ((graph a).label (.type t)) = RR.labels a t := by
  cases head : expose a t with
  | nominal index => simp [graph, observe, head, labelAlphabet, RR.labels, Rows.scanLabels]
  | unproductive index => simp [graph, observe, head, labelAlphabet, RR.labels, Rows.scanLabels]
  | constructor observation =>
    by_cases row : rowTag observation.tag = true
    · simp [graph, observe, head, row, rowObservation, labelAlphabet]
    · rw [(nonrow_scans a t observation head row).1]
      simp [graph, observe, head, row, labelAlphabet]

 theorem observed_residual (a : Assumptions) (t : Ty) :
    labelResidual ((graph a).label (.type t)) = tailKind (RR.residual a t) := by
  cases head : expose a t with
  | nominal index => simp [graph, observe, head, labelResidual, RR.residual, Rows.scanResidual, tailKind]
  | unproductive index => simp [graph, observe, head, labelResidual, RR.residual, Rows.scanResidual, tailKind]
  | constructor observation =>
    by_cases row : rowTag observation.tag = true
    · simp [graph, observe, head, row, rowObservation, labelResidual]
    · rw [(nonrow_scans a t observation head row).2]
      simp [graph, observe, head, row, labelResidual, tailKind]

 theorem observed_row_children (a : Assumptions) (t : Ty)
    (row : isRowLabel ((graph a).label (.type t)) = true) :
    (graph a).successors (.type t) =
      (RR.labels a t).map (fun name => Node.stream t name true) ++ tailChildren (RR.residual a t) := by
  cases head : expose a t with
  | nominal index => simp [graph, observe, head, isRowLabel] at row
  | unproductive index => simp [graph, observe, head, isRowLabel] at row
  | constructor observation =>
    by_cases actual : rowTag observation.tag = true
    · simp [graph, observe, head, actual, rowObservation, rowChildren]
    · simp [graph, observe, head, actual, isRowLabel] at row

 theorem observed_nonrow_children (a : Assumptions) (t : Ty)
    (nonrow : isRowLabel ((graph a).label (.type t)) ≠ true) :
    RR.labels a t = [] ∧ tailChildren (RR.residual a t) =
      (if isOrdinaryLabel ((graph a).label (.type t)) then [Node.type t] else []) := by
  cases head : expose a t with
  | nominal index =>
    simp [graph, observe, head, RR.labels, Rows.scanLabels, RR.residual, Rows.scanResidual,
      tailChildren, isOrdinaryLabel]
  | unproductive index =>
    simp [graph, observe, head, RR.labels, Rows.scanLabels, RR.residual, Rows.scanResidual,
      tailChildren, isOrdinaryLabel]
  | constructor observation =>
    by_cases actual : rowTag observation.tag = true
    · simp [graph, observe, head, actual, rowObservation, isRowLabel] at nonrow
    · obtain ⟨names, ending⟩ := nonrow_scans a t observation head actual
      simp [names, ending, graph, observe, head, actual, tailChildren, isOrdinaryLabel]

 theorem scan_emission_label (a : Assumptions) (remaining : List Ty) (name : String)
    (first : Bool) (row member tail : Ty)
    (emitted : Rows.scanStream a remaining name first row = .emit member tail) :
    name ∈ Rows.scanLabels a remaining row := by
  rw [Rows.scanStream] at emitted
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
      rw [Rows.scanLabels, exposed]
      split at emitted
      · rename_i present
        simp only [present, ↓reduceDIte]
        split at emitted
        · rename_i matched
          have same : fieldName = name := by
            have left : (fieldName == name) = true := (Bool.and_eq_true_iff.mp matched).1
            exact eq_of_beq left
          exact (Rows.mem_insertLabel fieldName name _).mpr (.inl same.symm)
        · exact (Rows.mem_insertLabel fieldName name _).mpr
            (.inr (scan_emission_label a (remaining.erase row) name first fieldTail member tail emitted))
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

 theorem absent_stream (a : Assumptions) (row : Ty) (name : String) (first : Bool)
    (absent : name ∉ RR.labels a row) : observe a (.stream row name first) = (.streamEnd, []) := by
  cases returned : RR.streamStep a row name first with
  | «end» ending => simp [observe, returned]
  | emit member tail =>
    exact False.elim (absent (scan_emission_label a _ name first row member tail returned))

 theorem children_map_append_split {α β : Type} (R : β → β → Prop) (f g : α → β)
    (names : List α) (left right : List β)
    (related : Children R (names.map f ++ left) (names.map g ++ right)) :
    (∀ name ∈ names, R (f name) (g name)) ∧ Children R left right := by
  induction names with
  | nil => exact ⟨fun _ absent => False.elim (by simpa using absent), related⟩
  | cons name rest ih =>
    obtain ⟨head, nested⟩ := related
    obtain ⟨members, tails⟩ := ih nested
    refine ⟨?_, tails⟩
    intro item inside
    rcases List.mem_cons.mp inside with same | later
    · subst item; exact head
    · exact members item later

structure RowInterface (a : Assumptions) (left right : Ty) : Prop where
  alphabet : RR.labels a left = RR.labels a right
  residualKind : tailKind (RR.residual a left) = tailKind (RR.residual a right)
  residualChildren : Children (FP.Bisimilar (graph a))
    (tailChildren (RR.residual a left)) (tailChildren (RR.residual a right))
  streams : ∀ name, StreamEquivalent a left right name true

 theorem equivalent_row_interface {a : Assumptions} {left right : Ty}
    (related : Equivalent a left right) : RowInterface a left right := by
  obtain ⟨labels, children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ related
  have alphabet : RR.labels a left = RR.labels a right := by
    simpa only [observed_alphabet] using congrArg labelAlphabet labels
  have residualKind : tailKind (RR.residual a left) = tailKind (RR.residual a right) := by
    simpa only [observed_residual] using congrArg labelResidual labels
  have ordinary := congrArg isOrdinaryLabel labels
  have rowFlag := congrArg isRowLabel labels
  have rowParts : (∀ name ∈ RR.labels a left, StreamEquivalent a left right name true) ∧
      Children (FP.Bisimilar (graph a)) (tailChildren (RR.residual a left))
        (tailChildren (RR.residual a right)) := by
    by_cases row : isRowLabel ((graph a).label (.type left)) = true
    · have row' : isRowLabel ((graph a).label (.type right)) = true := rowFlag.symm.trans row
      rw [observed_row_children a left row, observed_row_children a right row', ← alphabet] at children
      exact children_map_append_split _ _ _ _ _ _ children
    · have row' : isRowLabel ((graph a).label (.type right)) ≠ true := by
        intro actual; exact row (rowFlag.trans actual)
      obtain ⟨empty, ending⟩ := observed_nonrow_children a left row
      obtain ⟨_, ending'⟩ := observed_nonrow_children a right row'
      refine ⟨?_, ?_⟩
      · intro name present; simp [empty] at present
      · rw [ending, ending', ← ordinary]
        cases isOrdinaryLabel ((graph a).label (.type left)) <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Children]
        exact ⟨related, True.intro⟩
  refine ⟨alphabet, residualKind, rowParts.2, ?_⟩
  intro name
  by_cases present : name ∈ RR.labels a left
  · exact rowParts.1 name present
  · have absent' : name ∉ RR.labels a right := by simpa only [← alphabet] using present
    apply Obend.Core.FinitePresentation.bisimilar_of_children
    · change (observe a (.stream left name true)).1 = (observe a (.stream right name true)).1
      rw [absent_stream a left name true present, absent_stream a right name true absent']
    · change Children _ (observe a (.stream left name true)).2 (observe a (.stream right name true)).2
      rw [absent_stream a left name true present, absent_stream a right name true absent']
      trivial

 theorem stream_field_prefix_congruence {a : Assumptions} {name label : String}
    {member tail member' tail' : Ty}
    (members : Equivalent a member member') (tails : StreamEquivalent a tail tail' label true) :
    StreamEquivalent a (.field name member tail) (.field name member' tail') label true := by
  by_cases same : name = label
  · subst label
    have leftStep : RowHit.step a name true (.field name member tail) = .emit (member, tail) := by
      simp [RowHit.step, raw_field_observation]
    have rightStep : RowHit.step a name true (.field name member' tail') = .emit (member', tail') := by
      simp [RowHit.step, raw_field_observation]
    apply Obend.Core.FinitePresentation.bisimilar_of_children
    · change (observe a (.stream (.field name member tail) name true)).1 =
        (observe a (.stream (.field name member' tail') name true)).1
      rw [RowHit.stream_emit_observe_eq a name true _ _ _ leftStep,
        RowHit.stream_emit_observe_eq a name true _ _ _ rightStep]
    · change Children _ (observe a (.stream (.field name member tail) name true)).2
        (observe a (.stream (.field name member' tail') name true)).2
      rw [RowHit.stream_emit_observe_eq a name true _ _ _ leftStep,
        RowHit.stream_emit_observe_eq a name true _ _ _ rightStep]
      exact ⟨members, hide_visible_congruence (fun h => equivalent_shareable h) tails, True.intro⟩
  · have leftStep : RowHit.step a label true (.field name member tail) = .skip tail := by
      simp [RowHit.step, raw_field_observation, same, Bool.beq_eq_decide_eq]
    have rightStep : RowHit.step a label true (.field name member' tail') = .skip tail' := by
      simp [RowHit.step, raw_field_observation, same, Bool.beq_eq_decide_eq]
    obtain ⟨equal, nested⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ tails
    apply Obend.Core.FinitePresentation.bisimilar_of_children
    · change (observe a (.stream (.field name member tail) label true)).1 =
        (observe a (.stream (.field name member' tail') label true)).1
      rw [RowHit.stream_skip_observe_eq a label true _ _ leftStep,
        RowHit.stream_skip_observe_eq a label true _ _ rightStep]
      exact equal
    · change Children _ (observe a (.stream (.field name member tail) label true)).2
        (observe a (.stream (.field name member' tail') label true)).2
      rw [RowHit.stream_skip_observe_eq a label true _ _ leftStep,
        RowHit.stream_skip_observe_eq a label true _ _ rightStep]
      exact nested

 theorem children_mapped {α β : Type} (R : β → β → Prop) (f g : α → β)
    (names : List α) (related : ∀ name ∈ names, R (f name) (g name)) :
    Children R (names.map f) (names.map g) := by
  induction names with
  | nil => trivial
  | cons name rest ih => exact ⟨related name (by simp), ih (fun item h => related item (by simp [h]))⟩

 theorem children_append {α : Type} (R : α → α → Prop) {xs ys us vs : List α}
    (one : Children R xs ys) (two : Children R us vs) : Children R (xs ++ us) (ys ++ vs) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [Children]
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys => exact ⟨one.1, ih one.2⟩

/-- Arbitrary field congruence includes aliases, productive row cycles, hidden
resourceful repetitions, and ordinary non-row tails. -/
theorem field_congruence {a : Assumptions} {name : String} {member tail member' tail' : Ty}
    (members : Equivalent a member member') (tails : Equivalent a tail tail') :
    Equivalent a (.field name member tail) (.field name member' tail') := by
  have view := equivalent_row_interface tails
  have alphabet : RR.labels a (.field name member tail) = RR.labels a (.field name member' tail') := by
    rw [Rows.labels_field, Rows.labels_field, view.alphabet]
  have residualKind : tailKind (RR.residual a (.field name member tail)) =
      tailKind (RR.residual a (.field name member' tail')) := by
    rw [Rows.residual_field, Rows.residual_field]
    exact view.residualKind
  have observeField (m t : Ty) : observe a (.type (.field name m t)) = rowObservation a (.field name m t) := by
    simp [observe, raw_field_observation, rowTag]
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe a (.type (.field name member tail))).1 =
      (observe a (.type (.field name member' tail'))).1
    rw [observeField, observeField]
    simp only [rowObservation]
    rw [alphabet, residualKind, Rows.shareable_field, Rows.shareable_field,
      equivalent_shareable members, equivalent_shareable tails]
  · change Children _ (observe a (.type (.field name member tail))).2
      (observe a (.type (.field name member' tail'))).2
    rw [observeField, observeField]
    simp only [rowObservation, rowChildren]
    rw [← alphabet]
    apply children_append
    · apply children_mapped
      intro label _
      exact stream_field_prefix_congruence members (view.streams label)
    · rw [Rows.residual_field, Rows.residual_field]
      exact view.residualChildren

#assert_axioms nonrow_scans observed_alphabet observed_residual observed_row_children
  observed_nonrow_children scan_emission_label absent_stream equivalent_row_interface
  stream_field_prefix_congruence field_congruence

end Obend.Core.TypeGraph
