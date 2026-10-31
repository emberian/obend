module
public import Obend.Core.FilteredStreamSteps
public import Obend.Core.ResidualNominalPath
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

/-- A finite filtered emission is realized by the actual substituted row.
Compressed source skips and newly safe hidden fields form finite target
prefixes; nominal dispatch shares the exposed target head with its image. -/
public theorem Discharges.filtered_hit_image
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {label : String} {state : FilteredState} {payload : Ty × FilteredState} {n : Nat}
    (hit : Search.Hit (filteredStep σ a b label) state payload n) :
    filteredFirst payload.2 = false ∧
      ∃ k, Search.Hit (RowHit.step b label (filteredFirst state))
        (filteredRow σ state) (payload.1, filteredRow σ payload.2) k := by
  induction hit with
  | emit state payload observed =>
    cases state with
    | source row first =>
      cases sourceStream : RR.streamStep a row label first with
      | «end» ending =>
        simp only [filteredStep,sourceStream] at observed
        cases dispatched : nominalResidual (tailKind (RR.residual a row)) <;>
          simp only [dispatched] at observed <;> contradiction
      | emit member tail =>
        simp only [filteredStep,sourceStream] at observed
        split at observed
        · rename_i retained
          cases observed
          obtain ⟨count,sourceHit⟩ := source_stream_hit a sourceStream
          refine ⟨rfl,count,?_⟩
          simpa only [filteredRow,filteredFirst] using D.stream_hit_instantiate valid sourceHit retained
        · contradiction
    | expanded row first =>
      cases targetStep : RowHit.step b label first row with
      | stop => simp only [filteredStep,targetStep] at observed; contradiction
      | skip next => simp only [filteredStep,targetStep] at observed; contradiction
      | emit targetPayload =>
        cases targetPayload with
        | mk member tail =>
          simp only [filteredStep,targetStep] at observed
          cases observed
          exact ⟨rfl,0,.emit row (member,tail) targetStep⟩
  | skip state next payload n observed nested ih =>
    cases state with
    | expanded row first =>
      cases targetStep : RowHit.step b label first row with
      | stop => simp only [filteredStep,targetStep] at observed; contradiction
      | emit targetPayload =>
        cases targetPayload with
        | mk member tail => simp only [filteredStep,targetStep] at observed; contradiction
      | skip tail =>
        simp only [filteredStep,targetStep] at observed
        cases observed
        obtain ⟨mode,count,imageHit⟩ := ih
        exact ⟨mode,count + 1,.skip row tail _ count targetStep imageHit⟩
    | source row first =>
      cases sourceStream : RR.streamStep a row label first with
      | emit member tail =>
        cases retained : (first || !RR.shareable b (member.instantiate σ)) with
        | true =>
          simp only [filteredStep,sourceStream,retained,↓reduceIte] at observed
          contradiction
        | false =>
          simp only [filteredStep,sourceStream,retained,Bool.false_eq_true,↓reduceIte] at observed
          cases observed
          have hiddenMode : first = false := by cases first <;> simp_all
          subst first
          obtain ⟨mode,count,imageHit⟩ := ih
          obtain ⟨sourceCount,sourceHit⟩ := source_stream_hit a sourceStream
          have path := D.stream_hit_hidden_path valid sourceHit retained
          refine ⟨mode,?_⟩
          exact (Obend.Core.RowSearch.hit_path_iff path).mpr ⟨count,imageHit⟩
      | «end» ending =>
        cases sourceResidual : RR.residual a row with
        | closed =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | productiveCycle =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | unproductive representative =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | nonRow terminal =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | nominal index =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          cases observed
          obtain ⟨mode,count,imageHit⟩ := ih
          have noemit : RowHit.emission (RR.streamStep a row label first) = none := by
            rw [sourceStream]
            rfl
          obtain ⟨endpoint,sourcePath,nominal⟩ :=
            Obend.Core.RecursiveRows.noemit_nominal_skipPath a row label first index sourceResidual noemit
          have targetPath := D.stream_path_instantiate valid sourcePath
          have sameHead := D.expose_instantiate_nominal nominal
          have sameStep : RowHit.step b label first (endpoint.instantiate σ) =
              RowHit.step b label first (σ index) := by
            unfold RowHit.step
            rw [sameHead]
          have endpointHit := Obend.Core.RowSearch.hit_of_step_eq sameStep.symm imageHit
          refine ⟨mode,?_⟩
          exact (Obend.Core.RowSearch.hit_path_iff targetPath).mpr ⟨count,endpointHit⟩

end Obend.Core.Proofs.Templates
