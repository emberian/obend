module
public import Obend.Core.TypeGraphResource
public import Obend.Core.TypeGraphAlias
@[expose] public section
namespace Obend.Core.AliasExposure
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

def headIsComputation : Head → Bool
  | .constructor observation => observation.tag == .computation
  | _ => false

theorem constructorHead_isComputation (t : Ty) :
    headIsComputation (constructorHead t) = t.isComputation := by
  cases t <;> rfl

theorem aliasChain_isComputation {assumptions : Assumptions} {start finish : Ty} {path : List Nat}
    (chain : AliasChain assumptions start path finish) : start.isComputation = finish.isComputation := by
  induction chain with
  | nil => rfl
  | cons found pure nested ih =>
    change false = _
    rw [← ih,pure]

theorem stopped_isComputation {assumptions : Assumptions} {visited : List Nat}
    {finish : Ty} {head : Head} (stopped : Stopped assumptions visited finish head) :
    headIsComputation head = finish.isComputation := by
  cases stopped with
  | productive t nonvariable => exact constructorHead_isComputation _
  | unbound => rfl
  | activity => rfl
  | cycle => rfl

/-- The activity barrier remains unconditional, including malformed assumption
environments: no transparent alias path changes the syntactic activity head. -/
theorem expose_isComputation (assumptions : Assumptions) (t : Ty) :
    headIsComputation (expose assumptions t) = t.isComputation := by
  obtain ⟨path,finish,chain,_,_,stopped⟩ := exposeWalk_trace assumptions
    (assumptions.bounds.map Prod.fst) [] (initial_covers assumptions) t
  have ending := stopped_isComputation stopped
  change headIsComputation (expose assumptions t) = finish.isComputation at ending
  exact ending.trans (aliasChain_isComputation chain).symm

end Obend.Core.AliasExposure

namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

inductive HeadShape where
  | nominal (index : Nat)
  | unproductive (representative : Nat)
  | ordinary (tag : Tag)
  | row
  | streamEnd | streamEmit
  deriving DecidableEq, Repr

def labelHead : Label → HeadShape
  | .nominal index => .nominal index
  | .unproductive representative => .unproductive representative
  | .ordinary tag _ => .ordinary tag
  | .row _ _ _ => .row
  | .streamEnd => .streamEnd
  | .streamEmit => .streamEmit

theorem equivalent_head {assumptions : Assumptions} {left right : Ty}
    (related : Equivalent assumptions left right) :
    labelHead ((graph assumptions).label (.type left)) =
      labelHead ((graph assumptions).label (.type right)) :=
  congrArg labelHead (Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related).1

def labelIsComputation : Label → Bool
  | .ordinary .computation _ => true
  | _ => false

theorem observed_isComputation (assumptions : Assumptions) (t : Ty) :
    labelIsComputation ((graph assumptions).label (.type t)) = t.isComputation := by
  rw [← expose_isComputation assumptions t]
  cases exposed : expose assumptions t with
  | nominal index => simp [graph,observe,exposed,labelIsComputation,headIsComputation]
  | unproductive index => simp [graph,observe,exposed,labelIsComputation,headIsComputation]
  | constructor observation =>
    cases tag : observation.tag <;>
      simp [graph,observe,exposed,tag,rowTag,rowObservation,labelIsComputation,headIsComputation]

theorem equivalent_isComputation {assumptions : Assumptions} {left right : Ty}
    (related : Equivalent assumptions left right) : left.isComputation = right.isComputation := by
  have labels := (Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related).1
  have activity := congrArg labelIsComputation labels
  simpa only [observed_isComputation] using activity

theorem candidate_isComputation {assumptions : Assumptions} {left right : Ty}
    (accepted : candidate assumptions left right = true) : left.isComputation = right.isComputation :=
  equivalent_isComputation ((candidate_iff _ _ _).mp accepted)

/-- Non-row exposed constructors agree componentwise. Rows instead use their
named stream interface and residual, never their raw field spines. -/
theorem equivalent_exposed_components {assumptions : Assumptions} {left right : Ty}
    {one two : Constructor} (related : Equivalent assumptions left right)
    (leftHead : expose assumptions left = .constructor one)
    (rightHead : expose assumptions right = .constructor two)
    (leftNonrow : rowTag one.tag ≠ true) (rightNonrow : rowTag two.tag ≠ true) :
    one.tag = two.tag ∧ Children (Equivalent assumptions) one.children two.children := by
  obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related
  have labelEq : Label.ordinary one.tag (RR.shareable assumptions left) =
      Label.ordinary two.tag (RR.shareable assumptions right) := by
    simpa [graph,observe,leftHead,rightHead,leftNonrow,rightNonrow] using labels
  refine ⟨(Label.ordinary.inj labelEq).1,?_⟩
  have mapped : Children (Obend.Core.FinitePresentation.Bisimilar (graph assumptions))
      (one.children.map Node.type) (two.children.map Node.type) := by
    simpa [graph,observe,leftHead,rightHead,leftNonrow,rightNonrow] using children
  exact (Obend.Core.FinitePresentation.children_map_iff Node.type _ _ _).mp mapped

theorem arrow_components {assumptions : Assumptions} {reuse reuse' : Reuse}
    {quantity quantity' : Quantity} {domain codomain domain' codomain' : Ty}
    (related : Equivalent assumptions (.arrow reuse quantity domain codomain)
      (.arrow reuse' quantity' domain' codomain')) :
    reuse = reuse' ∧ quantity = quantity' ∧ Equivalent assumptions domain domain' ∧
      Equivalent assumptions codomain codomain' := by
  obtain ⟨tags,children⟩ := equivalent_exposed_components related
    (show expose assumptions (.arrow reuse quantity domain codomain) =
      .constructor ⟨.arrow reuse quantity,[domain,codomain]⟩ by
      simp [expose,exposeWalk,constructorHead])
    (show expose assumptions (.arrow reuse' quantity' domain' codomain') =
      .constructor ⟨.arrow reuse' quantity',[domain',codomain']⟩ by
      simp [expose,exposeWalk,constructorHead]) (by simp [rowTag]) (by simp [rowTag])
  have parameters : reuse = reuse' ∧ quantity = quantity' := Tag.arrow.inj tags
  exact ⟨parameters.1,parameters.2,children.1,children.2.1⟩

theorem computation_components {assumptions : Assumptions}
    {plan response result plan' response' result' : Ty}
    (related : Equivalent assumptions (.computation plan response result)
      (.computation plan' response' result')) :
    Equivalent assumptions plan plan' ∧ Equivalent assumptions response response' ∧
      Equivalent assumptions result result' := by
  have children := (Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related).2
  have components : Children (Obend.Core.FinitePresentation.Bisimilar (graph assumptions))
      [.type plan,.type response,.type result] [.type plan',.type response',.type result'] := by
    simpa [graph,observe_computation] using children
  exact ⟨components.1,components.2.1,components.2.2.1⟩

theorem specification_components {assumptions : Assumptions}
    {metadata extension metadata' extension' : Ty}
    (related : Equivalent assumptions (.specification metadata extension)
      (.specification metadata' extension')) :
    Equivalent assumptions metadata metadata' ∧ Equivalent assumptions extension extension' := by
  have children := (Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related).2
  have components : Children (Obend.Core.FinitePresentation.Bisimilar (graph assumptions))
      [.type metadata,.type extension] [.type metadata',.type extension'] := by
    simpa [graph,observe_specification] using children
  exact ⟨components.1,components.2.1⟩

theorem prototype_components {assumptions : Assumptions} {spec target spec' target' : Ty}
    (related : Equivalent assumptions (.prototype spec target) (.prototype spec' target')) :
    Equivalent assumptions spec spec' ∧ Equivalent assumptions target target' := by
  have children := (Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related).2
  have components : Children (Obend.Core.FinitePresentation.Bisimilar (graph assumptions))
      [.type spec,.type target] [.type spec',.type target'] := by
    simpa [graph,observe_prototype] using children
  exact ⟨components.1,components.2.1⟩

theorem variant_components {assumptions : Assumptions} {row row' : Ty}
    (related : Equivalent assumptions (.variant row) (.variant row')) :
    Equivalent assumptions row row' := by
  have children := (Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related).2
  have components : Children (Obend.Core.FinitePresentation.Bisimilar (graph assumptions))
      [.type row] [.type row'] := by
    simpa [graph,observe_variant] using children
  exact components.1

end Obend.Core.TypeGraph
