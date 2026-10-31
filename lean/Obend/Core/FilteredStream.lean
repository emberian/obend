module
public import Obend.Core.RelationalRowSearch
public import Obend.Core.SubstitutionResourceCongruence
public import Obend.Core.SubstitutionResidual
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
namespace Search
export Obend.Core.RowSearch (Step StepLift Hit find OptionLift find_related)
end Search
set_option autoImplicit false

/-- Source streams retain their original row quotient until a nominal residual
is reached. Expanded states then execute the actual instantiated nominal image. -/
inductive FilteredState where
  | source (row : Ty) (first : Bool)
  | expanded (row : Ty) (first : Bool)
  deriving DecidableEq

def nominalResidual : TailKind → Option Nat
  | .nominal j => some j
  | _ => none

def filteredStep (σ : Nat → Ty) (a b : Assumptions) (label : String) :
    FilteredState → Search.Step FilteredState (Ty × FilteredState)
  | .source row first =>
    match RR.streamStep a row label first with
    | .emit member tail =>
      if first || !RR.shareable b (member.instantiate σ) then
        .emit (member.instantiate σ,.source tail false)
      else .skip (.source tail false)
    | .end _ =>
      match nominalResidual (tailKind (RR.residual a row)) with
      | some j => .skip (.expanded (σ j) first)
      | none => .stop
  | .expanded row first =>
    match RowHit.step b label first row with
    | .emit (member,tail) => .emit (member,.expanded tail false)
    | .skip tail => .skip (.expanded tail first)
    | .stop => .stop

/-- Residual kind is required: source end-stream observations alone discard
the nominal tail which may expand to new fields after instantiation. -/
inductive FilteredRelated (a : Assumptions) (label : String) :
    FilteredState → FilteredState → Prop where
  | source {left right : Ty} {first : Bool} :
      StreamEquivalent a left right label first →
      tailKind (RR.residual a left) = tailKind (RR.residual a right) →
      FilteredRelated a label (.source left first) (.source right first)
  | expanded (row : Ty) (first : Bool) :
      FilteredRelated a label (.expanded row first) (.expanded row first)

def FilteredPayloadRelated (σ : Nat → Ty) (a : Assumptions) (label : String)
    (left right : Ty × FilteredState) : Prop :=
  left = right ∨ ∃ l r, Equivalent a l r ∧ left.1 = l.instantiate σ ∧
    right.1 = r.instantiate σ ∧ FilteredRelated a label left.2 right.2

theorem FilteredRelated.symm {a : Assumptions} {label : String} {left right : FilteredState}
    (related : FilteredRelated a label left right) : FilteredRelated a label right left := by
  cases related with
  | source streams kinds =>
    exact .source ((FP.bisimilar_equivalence (graph a)).symm streams) kinds.symm
  | expanded row first => exact .expanded row first

/-- Newly shareable hidden emissions are skipped in lockstep because source
equivalence preserves their exact instantiated resource flags. -/
theorem Discharges.filteredStep_related
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) (label : String)
    {left right : FilteredState} (related : FilteredRelated a label left right) :
    Search.StepLift (FilteredRelated a label) (FilteredPayloadRelated σ a label)
      (filteredStep σ a b label left) (filteredStep σ a b label right) := by
  cases related with
  | expanded row first =>
    cases observed : RowHit.step b label first row with
    | stop => simp only [filteredStep,observed]; exact .stop
    | skip tail => simp only [filteredStep,observed]; exact .skip (.expanded tail first)
    | emit payload =>
      cases payload with
      | mk member tail =>
        simp only [filteredStep,observed]
        exact .emit (Or.inl rfl)
  | @source left right first streams kinds =>
    obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ streams
    cases one : RR.streamStep a left label first with
    | «end» ending =>
      cases two : RR.streamStep a right label first with
      | emit member tail => simp [graph,observe,one,two] at labels
      | «end» ending' =>
        simp only [filteredStep,one,two,kinds]
        cases nominalResidual (tailKind (RR.residual a right)) with
        | none => exact .stop
        | some j => exact .skip (.expanded (σ j) first)
    | emit member tail =>
      cases two : RR.streamStep a right label first with
      | «end» ending => simp [graph,observe,one,two] at labels
      | emit member' tail' =>
        have nested : Equivalent a member member' ∧ StreamEquivalent a tail tail' label false := by
          simpa [graph,observe,one,two,Obend.Core.FiniteBisimulation.Children,
            Equivalent,StreamEquivalent] using children
        have tails : FilteredRelated a label (.source tail false) (.source tail' false) := by
          apply FilteredRelated.source nested.2
          rw [← Obend.Core.RecursiveRows.residual_emit one,
            ← Obend.Core.RecursiveRows.residual_emit two]
          exact kinds
        have resources : RR.shareable b (member.instantiate σ) = RR.shareable b (member'.instantiate σ) :=
          D.semantic_shareable_congr valid nested.1
        simp only [filteredStep,one,two,← resources]
        split
        · apply Obend.Core.RowSearch.StepLift.emit
          unfold FilteredPayloadRelated
          right
          exact ⟨member,member',nested.1,rfl,rfl,tails⟩
        · exact .skip tails

end Obend.Core.Proofs.Templates
