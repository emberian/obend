module
public import Obend.Core.FilteredStreamCompleteness
public import Obend.Core.FilteredStreamSoundness
public import Obend.Core.SubstitutionResidualTransport
public import Obend.Core.RowAlphabet
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

/-- Coinductive substitution seeds, closed under actual target equivalence
and composition. Composition absorbs raw alias wrappers in residual payloads. -/
inductive InstantiationRelated (σ : Nat → Ty) (a b : Assumptions) : Node → Node → Prop where
  | existing {x y} : FP.Bisimilar (graph b) x y → InstantiationRelated σ a b x y
  | types {left right} : Equivalent a left right →
      InstantiationRelated σ a b (.type (left.instantiate σ)) (.type (right.instantiate σ))
  | streams {left right label} : FilteredRelated a label left right →
      InstantiationRelated σ a b
        (.stream (filteredRow σ left) label (filteredFirst left))
        (.stream (filteredRow σ right) label (filteredFirst right))
  | trans {x y z} : InstantiationRelated σ a b x y → InstantiationRelated σ a b y z →
      InstantiationRelated σ a b x z

theorem streamStep_of_hit (b : Assumptions) {row member tail : Ty}
    {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step b label first) row (member,tail) n) :
    RR.streamStep b row label first = .emit member tail := by
  have found := (Obend.Core.RowSearch.find_iff_hit (RowHit.step b label first) (support b row row)
    (fun x y present skipped => RowHit.step_skip_support b row row x y label first present skipped)
    (left_mem_support b row row)).mpr ⟨n,hit⟩
  have projected : RowHit.emission (RR.streamStep b row label first) = some (member,tail) := by
    simpa only [RR.streamStep,RowHit.scan_projection] using found
  cases emitted : RR.streamStep b row label first with
  | «end» ending => simp [emitted,RowHit.emission] at projected
  | emit m t =>
    have same : m = member ∧ t = tail := by simpa [emitted,RowHit.emission] using projected
    simp only [same.1,same.2]

theorem Discharges.realized_hit_filtered
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {state : FilteredState} {member tail : Ty} {label : String} {n : Nat}
    (hit : Search.Hit (RowHit.step b label (filteredFirst state)) (filteredRow σ state) (member,tail) n) :
    ∃ next k, Search.Hit (filteredStep σ a b label) state (member,next) k ∧
      filteredRow σ next = tail ∧ filteredFirst next = false := by
  cases state with
  | source row first => exact D.image_hit_filtered valid hit
  | expanded row first => exact ⟨.expanded tail false,n,expanded_hit σ a b hit,rfl,rfl⟩

theorem filtered_payload_nodes {σ : Nat → Ty} {a b : Assumptions} {label : String}
    {left right : Ty × FilteredState}
    (related : FilteredPayloadRelated σ a label left right)
    (leftMode : filteredFirst left.2 = false) (rightMode : filteredFirst right.2 = false) :
    InstantiationRelated σ a b (.type left.1) (.type right.1) ∧
      InstantiationRelated σ a b (.stream (filteredRow σ left.2) label false)
        (.stream (filteredRow σ right.2) label false) := by
  rcases related with equal | ⟨l,r,types,leftMember,rightMember,tails⟩
  · subst right
    exact ⟨.existing ((FP.bisimilar_equivalence (graph b)).refl _),
      .existing ((FP.bisimilar_equivalence (graph b)).refl _)⟩
  · constructor
    · rw [leftMember,rightMember]
      exact .types types
    · simpa only [leftMode,rightMode] using
        (InstantiationRelated.streams (σ := σ) (b := b) tails)

/-- Finite actual emissions transport through the filtered source bisimulation;
their member and continuation pairs are seeds of the final type coinduction. -/
theorem Discharges.related_stream_emits
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {left right : FilteredState} {label : String}
    (related : FilteredRelated a label left right) {member tail : Ty}
    (emitted : RR.streamStep b (filteredRow σ left) label (filteredFirst left) = .emit member tail) :
    ∃ member' tail', RR.streamStep b (filteredRow σ right) label (filteredFirst right) = .emit member' tail' ∧
      InstantiationRelated σ a b (.type member) (.type member') ∧
      InstantiationRelated σ a b (.stream tail label false) (.stream tail' label false) := by
  obtain ⟨n,hit⟩ := source_stream_hit b emitted
  obtain ⟨next,k,filtered,row,mode⟩ := D.realized_hit_filtered valid hit
  obtain ⟨payload,other,payloadRelated⟩ := filtered.related
    (fun x y link => D.filteredStep_related valid label link) related
  obtain ⟨otherMode,count,imageHit⟩ := D.filtered_hit_image valid other
  have nodes := filtered_payload_nodes (b := b) payloadRelated mode otherMode
  refine ⟨payload.1,filteredRow σ payload.2,streamStep_of_hit b imageHit,nodes.1,?_⟩
  simpa only [row] using nodes.2

theorem Discharges.related_stream_closed
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {left right : FilteredState} {label : String}
    (related : FilteredRelated a label left right) :
    (graph b).label (.stream (filteredRow σ left) label (filteredFirst left)) =
      (graph b).label (.stream (filteredRow σ right) label (filteredFirst right)) ∧
    Children (InstantiationRelated σ a b)
      ((graph b).successors (.stream (filteredRow σ left) label (filteredFirst left)))
      ((graph b).successors (.stream (filteredRow σ right) label (filteredFirst right))) := by
  cases one : RR.streamStep b (filteredRow σ left) label (filteredFirst left) with
  | emit member tail =>
    obtain ⟨member',tail',two,members,tails⟩ := D.related_stream_emits valid related one
    constructor
    · simp [graph,observe,one,two]
    · simp only [graph,observe,one,two]
      exact ⟨members,tails,True.intro⟩
  | «end» ending =>
    cases two : RR.streamStep b (filteredRow σ right) label (filteredFirst right) with
    | «end» ending' => simp [graph,observe,one,two,Children]
    | emit member tail =>
      obtain ⟨_,_,impossible,_⟩ := D.related_stream_emits valid related.symm two
      rw [one] at impossible
      contradiction

end Obend.Core.Proofs.Templates
