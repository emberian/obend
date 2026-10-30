module
public import Obend.Core.RowResourceSafety
public import Obend.Core.FieldCongruence
public import Obend.Core.FiniteRowLaws
public import Obend.Core.TypeGraphAlias
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

abbrev WeightedSafe (a : Assumptions) (nominal : Nat → Bool) (node : Node) : Prop :=
  Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) node

theorem weighted_safe_of_related (a : Assumptions) (nominal : Nat → Bool)
    {x y : Node} (related : FP.Bisimilar (graph a) x y) :
    WeightedSafe a nominal x ↔ WeightedSafe a nominal y :=
  Obend.Core.FiniteSafety.safe_bisimilar_iff _ (weightedResource_bisimilar a nominal related)

theorem weighted_end_safe (a : Assumptions) (nominal : Nat → Bool) {node : Node}
    (observed : observe a node = (.streamEnd,[])) : WeightedSafe a nominal node := by
  apply Obend.Core.FiniteSafety.safe_of_children
  · simp [weightedResourceGraph,graph,observed,weightedResourceLabel]
  · simp [weightedResourceGraph,graph,observed,weightedResourceDependencies]

theorem weighted_emit_safe (a : Assumptions) (nominal : Nat → Bool)
    {node : Node} {member tail : Ty} {label : String}
    (observed : observe a node = (.streamEmit,[.type member,.stream tail label false])) :
    WeightedSafe a nominal node ↔
      WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.stream tail label false) := by
  simp only [WeightedSafe]
  rw [Obend.Core.FiniteSafety.safe_iff]
  have labelEq : (weightedResourceGraph a nominal).label node = true := by
    simp [weightedResourceGraph,graph,observed,weightedResourceLabel]
  have childrenEq : (weightedResourceGraph a nominal).successors node =
      [.type member,.stream tail label false] := by
    simp [weightedResourceGraph,graph,observed,weightedResourceDependencies]
  rw [labelEq,childrenEq]
  simp

theorem weighted_hide_safe (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    (row : Ty) (label : String) :
    WeightedSafe a nominal (.stream row label true) ↔
      WeightedSafe a nominal (.stream row label false) := by
  cases emitted : RR.streamStep a row label true with
  | «end» ending =>
    exact (weighted_safe_of_related a nominal (hide_end a row label ending emitted)).symm
  | emit member tail =>
    cases resource : RR.shareable a member with
    | false =>
      exact (weighted_safe_of_related a nominal
        (hide_emit_resourceful a row member tail label resource emitted)).symm
    | true =>
      have hidden := weighted_safe_of_related a nominal
        (RowHit.hide_emit_shareable a label row member tail emitted resource)
      have visible := weighted_emit_safe a nominal
        (show observe a (.stream row label true) =
          (.streamEmit,[.type member,.stream tail label false]) by simp [observe,emitted])
      have goodMember := weighted_safe_of_shareable a nominal raised resource
      rw [visible]
      exact ⟨fun h => hidden.mpr h.2,fun h => ⟨goodMember,hidden.mp h⟩⟩

theorem weighted_field_stream_safe (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    (name label : String) (member tail : Ty) :
    WeightedSafe a nominal (.stream (.field name member tail) label true) ↔
      if name = label then
        WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.stream tail label true)
      else WeightedSafe a nominal (.stream tail label true) := by
  by_cases same : name = label
  · rw [if_pos same]
    have observed := field_stream_emit a name label true member tail (by simp [same])
    exact (weighted_emit_safe a nominal observed).trans
      (and_congr_right (fun _ => (weighted_hide_safe a nominal raised tail label).symm))
  · rw [if_neg same]
    exact weighted_safe_of_related a nominal
      (field_stream_skip a name label true member tail (by simp [same]))

def weightedTailLabel (nominal : Nat → Bool) : RR.Tail → Bool
  | .nominal index => nominal index
  | _ => true

def WeightedInterfaceSafe (a : Assumptions) (nominal : Nat → Bool) (row : Ty) : Prop :=
  weightedTailLabel nominal (RR.residual a row) = true ∧
    (∀ label, WeightedSafe a nominal (.stream row label true)) ∧
    ∀ child ∈ tailChildren (RR.residual a row), WeightedSafe a nominal child

private theorem weighted_row_label (nominal : Nat → Bool) (names : List String)
    (ending : RR.Tail) (share : Bool) :
    weightedResourceLabel nominal (.row names (tailKind ending) share) = weightedTailLabel nominal ending := by
  cases ending <;> rfl

theorem weighted_absent_stream_safe (a : Assumptions) (nominal : Nat → Bool)
    (row : Ty) (label : String) (absent : label ∉ RR.labels a row) :
    WeightedSafe a nominal (.stream row label true) :=
  weighted_end_safe a nominal (absent_stream a row label true absent)

/-- This interface characterization also covers nominal and ordinary non-row
tails. For the latter the residual retains the whole original type state. -/
theorem weighted_interface_safe (a : Assumptions) (nominal : Nat → Bool) (row : Ty) :
    WeightedSafe a nominal (.type row) ↔ WeightedInterfaceSafe a nominal row := by
  cases exposed : expose a row with
  | nominal index =>
    rw [WeightedSafe,Obend.Core.FiniteSafety.safe_iff]
    have streams (label : String) : WeightedSafe a nominal (.stream row label true) := by
      apply weighted_end_safe
      simp [observe,RR.streamStep,Rows.scanStream,exposed]
    simp [WeightedInterfaceSafe,weightedResourceGraph,graph,observe,exposed,
      weightedResourceLabel,weightedResourceDependencies,RR.labels,Rows.scanLabels,
      RR.residual,Rows.scanResidual,weightedTailLabel,tailChildren,streams]
  | unproductive representative =>
    rw [WeightedSafe,Obend.Core.FiniteSafety.safe_iff]
    have streams (label : String) : WeightedSafe a nominal (.stream row label true) := by
      apply weighted_end_safe
      simp [observe,RR.streamStep,Rows.scanStream,exposed]
    simp [WeightedInterfaceSafe,weightedResourceGraph,graph,observe,exposed,
      weightedResourceLabel,weightedResourceDependencies,RR.labels,Rows.scanLabels,
      RR.residual,Rows.scanResidual,weightedTailLabel,tailChildren,streams]
  | constructor observation =>
    by_cases isRow : rowTag observation.tag = true
    · have finite : WeightedSafe a nominal (.type row) ↔
          weightedTailLabel nominal (RR.residual a row) = true ∧
          (∀ label ∈ RR.labels a row, WeightedSafe a nominal (.stream row label true)) ∧
          ∀ child ∈ tailChildren (RR.residual a row), WeightedSafe a nominal child := by
        simp only [WeightedSafe]
        rw [Obend.Core.FiniteSafety.safe_iff]
        have labelEq : (weightedResourceGraph a nominal).label (.type row) =
            weightedTailLabel nominal (RR.residual a row) := by
          simp [weightedResourceGraph,graph,observe,exposed,isRow,rowObservation,weighted_row_label]
        have childrenEq : (weightedResourceGraph a nominal).successors (.type row) =
            (RR.labels a row).map (fun label => Node.stream row label true) ++
              tailChildren (RR.residual a row) := by
          simp [weightedResourceGraph,graph,observe,exposed,isRow,rowObservation,rowChildren,
            weightedResourceDependencies]
        rw [labelEq,childrenEq,List.forall_mem_append,List.forall_mem_map]
      constructor
      · intro safe
        obtain ⟨tail,streams,children⟩ := finite.mp safe
        refine ⟨tail,?_,children⟩
        intro label
        by_cases present : label ∈ RR.labels a row
        · exact streams label present
        · exact weighted_absent_stream_safe a nominal row label present
      · intro safe
        exact finite.mpr ⟨safe.1,fun label _ => safe.2.1 label,safe.2.2⟩
    · obtain ⟨labels,residual⟩ := nonrow_scans a row observation exposed isRow
      have streams (label : String) : WeightedSafe a nominal (.stream row label true) :=
        weighted_absent_stream_safe a nominal row label (by simp [labels])
      simp [WeightedInterfaceSafe,residual,weightedTailLabel,tailChildren,streams]

/-- Weighted row safety recovers the ordinary resource constructor equation.
The source scanner may omit entries only when their weighted safety is known. -/
theorem weighted_field_safe (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    (name : String) (member tail : Ty) :
    WeightedSafe a nominal (.type (.field name member tail)) ↔
      WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.type tail) := by
  have residual : RR.residual a (.field name member tail) = RR.residual a tail := Rows.residual_field a name member tail
  constructor
  · intro safe
    have field := (weighted_interface_safe a nominal _).mp safe
    have named := (weighted_field_stream_safe a nominal raised name name member tail).mp (field.2.1 name)
    simp only [if_pos rfl] at named
    refine ⟨named.1,(weighted_interface_safe a nominal tail).mpr ?_⟩
    refine ⟨by simpa only [residual] using field.1,?_,by simpa only [residual] using field.2.2⟩
    intro label
    have stream := (weighted_field_stream_safe a nominal raised name label member tail).mp (field.2.1 label)
    by_cases same : name = label
    · have both : WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.stream tail label true) := by
        simpa only [if_pos same] using stream
      exact both.2
    · simpa only [if_neg same] using stream
  · rintro ⟨memberSafe,tailSafe⟩
    have tail := (weighted_interface_safe a nominal _).mp tailSafe
    apply (weighted_interface_safe a nominal _).mpr
    refine ⟨by simpa only [residual] using tail.1,?_,by simpa only [residual] using tail.2.2⟩
    intro label
    apply (weighted_field_stream_safe a nominal raised name label member _).mpr
    by_cases same : name = label
    · simpa only [if_pos same] using And.intro memberSafe (tail.2.1 label)
    · simpa only [if_neg same] using tail.2.1 label

#assert_axioms weighted_safe_of_related weighted_end_safe weighted_emit_safe weighted_hide_safe
  weighted_field_stream_safe weighted_absent_stream_safe weighted_interface_safe weighted_field_safe
end Obend.Core.TypeGraph
