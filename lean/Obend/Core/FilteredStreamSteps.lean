module
public import Obend.Core.FilteredStream
public import Obend.Core.SubstitutionStreamSteps
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

def filteredRow (σ : Nat → Ty) : FilteredState → Ty
  | .source row _ => row.instantiate σ
  | .expanded row _ => row

def filteredFirst : FilteredState → Bool
  | .source _ first | .expanded _ first => first

theorem source_stream_hit (a : Assumptions) {row member tail : Ty}
    {label : String} {first : Bool}
    (emitted : RR.streamStep a row label first = .emit member tail) :
    ∃ n, Search.Hit (RowHit.step a label first) row (member,tail) n := by
  have projected : Obend.Core.RowSearch.find (RowHit.step a label first) (support a row row) row =
      some (member,tail) := by
    rw [← RowHit.scan_projection]
    exact congrArg RowHit.emission emitted
  exact Obend.Core.RowSearch.find_sound _ _ _ _ projected

/-- Source epsilon prefixes are already compressed by the source stream
scanner, and therefore do not consume a filtered-machine transition. -/
theorem filteredStep_source_skip (σ : Nat → Ty) (a b : Assumptions)
    {row tail : Ty} {label : String} {first : Bool}
    (skipped : RowHit.step a label first row = .skip tail) :
    filteredStep σ a b label (.source row first) =
      filteredStep σ a b label (.source tail first) := by
  have streams := RowHit.stream_skip_observe_eq a label first row tail skipped
  have residual := Obend.Core.RecursiveRows.residual_skip skipped
  cases one : RR.streamStep a row label first with
  | «end» ending =>
    cases two : RR.streamStep a tail label first with
    | emit member next => simp [observe,one,two] at streams
    | «end» ending' => simp only [filteredStep,one,two,residual]
  | emit member next =>
    cases two : RR.streamStep a tail label first with
    | «end» ending => simp [observe,one,two] at streams
    | emit member' next' =>
      have payload : member = member' ∧ next = next' := by
        simpa [observe,one,two] using streams
      simp only [filteredStep,one,two,payload.1,payload.2]

theorem filteredStep_source_emit (σ : Nat → Ty) (a b : Assumptions)
    {row member tail : Ty} {label : String} {first : Bool}
    (emitted : RowHit.step a label first row = .emit (member,tail)) :
    filteredStep σ a b label (.source row first) =
      if first || !RR.shareable b (member.instantiate σ) then
        .emit (member.instantiate σ,.source tail false) else .skip (.source tail false) := by
  have observation := RowHit.stream_emit_observe_eq a label first row member tail emitted
  cases result : RR.streamStep a row label first with
  | «end» ending => simp [observe,result] at observation
  | emit member' tail' =>
    have payload : member' = member ∧ tail' = tail := by
      simpa [observe,result] using observation
    simp only [filteredStep,result,payload.1,payload.2]

theorem filteredStep_source_nominal (σ : Nat → Ty) (a b : Assumptions)
    {row : Ty} {label : String} {first : Bool} {index : Nat}
    (observed : expose a row = .nominal index) :
    filteredStep σ a b label (.source row first) = .skip (.expanded (σ index) first) := by
  simp [filteredStep,RR.streamStep,Obend.Core.RecursiveRows.scanStream,observed,
    RR.residual,Obend.Core.RecursiveRows.scanResidual,tailKind,nominalResidual]

/-- Expanded nominal images run the ordinary target epsilon machine exactly. -/
theorem expanded_hit (σ : Nat → Ty) (a b : Assumptions) {row : Ty}
    {label : String} {first : Bool} {payload : Ty × Ty} {n : Nat}
    (hit : Search.Hit (RowHit.step b label first) row payload n) :
    Search.Hit (filteredStep σ a b label) (.expanded row first)
      (payload.1,.expanded payload.2 false) n := by
  induction hit with
  | emit row payload observed =>
    cases payload with
    | mk member tail =>
      apply Obend.Core.RowSearch.Hit.emit
      simp only [filteredStep,observed]
  | skip row next payload n observed nested ih =>
    apply Obend.Core.RowSearch.Hit.skip _ (.expanded next first) _ n _ ih
    simp only [filteredStep,observed]

end Obend.Core.Proofs.Templates
