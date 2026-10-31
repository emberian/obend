module
public import Obend.Core.SubstitutionResidualTransport
@[expose] public section
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false
namespace RH
export Obend.Core.TypeGraph.RowHit (step emission scan_projection step_skip_support)
end RH

public theorem noemit_step_not_emit {a : Assumptions} {row : Ty} {label : String} {first : Bool}
    (noemit : RH.emission (streamStep a row label first) = none) (member tail : Ty) :
    RH.step a label first row ≠ .emit (member, tail) := by
  intro emitted
  have projected : RH.emission (streamStep a row label first) = some (member, tail) := by
    change RH.emission (scanStream a (support a row row) label first row) = _
    rw [RH.scan_projection, Obend.Core.RowSearch.find, emitted]
    simp only [left_mem_support, ↓reduceIte]
  rw [noemit] at projected
  contradiction

public theorem stream_skip_emission_eq {a : Assumptions} {row tail : Ty}
    {label : String} {first : Bool} (skipped : RH.step a label first row = .skip tail) :
    RH.emission (streamStep a row label first) =
      RH.emission (streamStep a tail label first) := by
  have path : Obend.Core.RowSearch.SkipPath (RH.step a label first) row tail :=
    .cons row tail tail skipped (.refl tail)
  have found := Obend.Core.RowSearch.find_path_eq (support a row row) (support a tail tail)
    (fun x y present skipped => RH.step_skip_support a row row x y label first present skipped)
    (fun x y present skipped => RH.step_skip_support a tail tail x y label first present skipped)
    (left_mem_support a row row) (left_mem_support a tail tail) path
  simpa only [streamStep, RH.scan_projection] using found

public theorem residual_hit_nominal_noemit_path {a : Assumptions} {row : Ty}
    {payload : Tail} {n : Nat} {label : String} {first : Bool}
    (hit : Obend.Core.RowSearch.Hit (residualStep a) row payload n) :
    ∀ index, payload = .nominal index → RH.emission (streamStep a row label first) = none →
    ∃ endpoint, Obend.Core.RowSearch.SkipPath (RH.step a label first) row endpoint ∧
      expose a endpoint = .nominal index := by
  induction hit with
  | emit row payload observed =>
    intro index nominal noemit
    rw [residualStep] at observed
    split at observed
    · rename_i terminal exposed
      cases observed
      cases nominal
      exact ⟨row, .refl row, exposed⟩
    · cases observed
      cases nominal
    · split at observed
      · cases observed
        cases nominal
      · contradiction
      · cases observed
        cases nominal
  | skip row next payload n observed nested ih =>
    intro index nominal noemit
    obtain ⟨name, member, exposed⟩ := residualStep_skip_exposed observed
    have skipped : RH.step a label first row = .skip next := by
      by_cases matched : (name == label && (first || !shareable a member)) = true
      · have emitted : RH.step a label first row = .emit (member, next) := by
          simp only [RH.step, exposed, matched, ↓reduceIte]
        exact False.elim (noemit_step_not_emit noemit member next emitted)
      · simp [RH.step, exposed, matched]
    have tailNoemit : RH.emission (streamStep a next label first) = none :=
      (stream_skip_emission_eq skipped).symm.trans noemit
    obtain ⟨endpoint, path, terminal⟩ := ih index nominal tailNoemit
    exact ⟨endpoint, .cons row next endpoint skipped path, terminal⟩

public theorem noemit_nominal_skipPath (a : Assumptions) (row : Ty) (label : String)
    (first : Bool) (index : Nat) (nominal : residual a row = .nominal index)
    (noemit : RH.emission (streamStep a row label first) = none) :
    ∃ endpoint, Obend.Core.RowSearch.SkipPath (RH.step a label first) row endpoint ∧
      expose a endpoint = .nominal index := by
  have found : Obend.Core.RowSearch.find (residualStep a) (support a row row) row =
      some (.nominal index) := by
    rw [residual_projection] at nominal
    cases searched : Obend.Core.RowSearch.find (residualStep a) (support a row row) row with
    | none => simp only [searched, Option.getD_none] at nominal; contradiction
    | some payload =>
      simp only [searched, Option.getD_some] at nominal
      simpa only [nominal] using searched
  obtain ⟨n, hit⟩ := Obend.Core.RowSearch.find_sound _ _ _ _ found
  exact residual_hit_nominal_noemit_path hit index rfl noemit

end Obend.Core.RecursiveRows
