module
public import Obend.Core.SubstitutionResidual
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.Proofs.Templates
namespace Search
export Obend.Core.RowSearch (find_iff_hit)
end Search
set_option autoImplicit false

public theorem ResidualRelated.tailKind {a : Assumptions} {left right : Tail}
    (related : ResidualRelated a left right) :
    Obend.Core.TypeGraph.tailKind left = Obend.Core.TypeGraph.tailKind right := by
  cases related <;> rfl

public theorem residualStep_skip_exposed {a : Assumptions} {row tail : Ty}
    (skipped : residualStep a row = .skip tail) :
    ∃ name member, expose a row = .constructor ⟨.field name, [member, tail]⟩ := by
  rw [residualStep] at skipped
  split at skipped
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at skipped
    · contradiction
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      cases skipped
      exact ⟨name, member, shape ▸ exposed⟩
    · contradiction

public theorem residualStep_skip {a : Assumptions} {row tail : Ty}
    (skipped : residualStep a row = .skip tail) : residual a row = residual a tail := by
  obtain ⟨name, member, observed⟩ := residualStep_skip_exposed skipped
  exact residual_exposed_field observed

public theorem residualStep_no_stop (a : Assumptions) (row : Ty) :
    residualStep a row ≠ .stop := by
  rw [residualStep]
  split <;> simp_all
  split <;> simp_all

public theorem residualStep_no_cycle (a : Assumptions) (row : Ty) :
    residualStep a row ≠ .emit .productiveCycle := by
  rw [residualStep]
  split <;> simp_all
  split <;> simp_all

public theorem residual_hit_payload_not_cycle {a : Assumptions} {row : Ty} {payload : Tail} {n : Nat}
    (hit : Search.Hit (residualStep a) row payload n) : payload ≠ .productiveCycle := by
  induction hit with
  | emit row p observed =>
    intro same
    subst p
    exact residualStep_no_cycle a row observed
  | skip row next p n observed nested ih => exact ih

public theorem residual_hit_no_cycle {a : Assumptions} {row : Ty} {n : Nat}
    (hit : Search.Hit (residualStep a) row .productiveCycle n) : False :=
  residual_hit_payload_not_cycle hit rfl

public theorem residual_cycle_iff_no_hit (a : Assumptions) (row : Ty) :
    residual a row = .productiveCycle ↔
      ∀ payload n, ¬ Search.Hit (residualStep a) row payload n := by
  have finds := fun payload => Search.find_iff_hit (residualStep a) (support a row row)
    (fun x y inside skipped => residualStep_skip_support a row row x y inside skipped)
    (p := payload) (left_mem_support a row row)
  constructor
  · intro cycle payload n hit
    have found := (finds payload).mpr ⟨n, hit⟩
    rw [residual_projection, found] at cycle
    simp only [Option.getD_some] at cycle
    subst payload
    exact residual_hit_no_cycle hit
  · intro nohit
    rw [residual_projection]
    cases found : Search.find (residualStep a) (support a row row) row with
    | none => rfl
    | some payload =>
      obtain ⟨n, hit⟩ := (finds payload).mp found
      exact False.elim (nohit payload n hit)

variable {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}

public theorem discharge_residualStep_skip
    (D : Discharges σ template instance_ extra) {row tail : Ty}
    (skipped : residualStep template row = .skip tail) :
    residualStep instance_ (row.instantiate σ) = .skip (tail.instantiate σ) := by
  obtain ⟨name, member, observed⟩ := residualStep_skip_exposed skipped
  have mapped := D.expose_instantiate_constructor observed
  simp only [residualStep, mapped, List.map_cons, List.map_nil]


public theorem discharge_residual_no_hit
    (D : Discharges σ template instance_ extra) {row : Ty}
    (nohit : ∀ payload n, ¬ Search.Hit (residualStep template) row payload n) :
    ∀ payload n, ¬ Search.Hit (residualStep instance_) (row.instantiate σ) payload n := by
  intro payload n
  induction n generalizing row with
  | zero =>
    intro hit
    cases source : residualStep template row with
    | stop => exact residualStep_no_stop template row source
    | emit p => exact nohit p 0 (.emit row p source)
    | skip tail =>
      have target := discharge_residualStep_skip D source
      cases hit with
      | emit _ _ observed => rw [target] at observed; contradiction
  | succ n ih =>
    intro hit
    cases source : residualStep template row with
    | stop => exact residualStep_no_stop template row source
    | emit p => exact nohit p 0 (.emit row p source)
    | skip tail =>
      have target := discharge_residualStep_skip D source
      have tailNoHit : ∀ p k, ¬ Search.Hit (residualStep template) tail p k := by
        intro p k nested
        exact nohit p (k + 1) (.skip row tail p k source nested)
      cases hit with
      | skip _ next _ k observed nested =>
        rw [target] at observed
        cases observed
        exact ih tailNoHit nested

public def instantiateResidual (σ : Nat → Ty) (a : Assumptions) : Tail → Tail
  | .closed => .closed
  | .productiveCycle => .productiveCycle
  | .nominal index => residual a (σ index)
  | .unproductive index => .unproductive index
  | .nonRow t => .nonRow (t.instantiate σ)

public theorem discharge_residual_emit
    (D : Discharges σ template instance_ extra) {row : Ty} {payload : Tail}
    (emitted : residualStep template row = .emit payload) :
    ResidualRelated instance_ (residual instance_ (row.instantiate σ))
      (instantiateResidual σ instance_ payload) := by
  cases exposed : expose template row with
  | nominal index =>
    simp only [residualStep, exposed] at emitted
    cases emitted
    exact residual_related_of_expose_eq (D.expose_instantiate_nominal exposed)
  | unproductive index =>
    simp only [residualStep, exposed] at emitted
    cases emitted
    have mapped := D.expose_instantiate_unproductive exposed
    simp only [residual, scanResidual, mapped, instantiateResidual]
    exact .unproductive index
  | constructor observation =>
    obtain ⟨source, present, raw⟩ := expose_origin (left_mem_support template row row) exposed
    cases source <;> simp only [constructorHead, Head.constructor.injEq] at raw
    all_goals try contradiction
    all_goals subst observation
    all_goals simp only [residualStep, exposed] at emitted
    all_goals try contradiction
    all_goals cases emitted
    all_goals have mapped := D.expose_instantiate_constructor exposed
    all_goals simp only [residual, scanResidual, mapped, List.map_cons, List.map_nil,
      instantiateResidual]
    all_goals first
      | exact .closed
      | exact .nonRow (Obend.Core.TypeGraph.equivalent_of_expose_eq rfl)

public theorem discharge_residual_hit
    (D : Discharges σ template instance_ extra) {row : Ty} {payload : Tail} {n : Nat}
    (hit : Search.Hit (residualStep template) row payload n) :
    ResidualRelated instance_ (residual instance_ (row.instantiate σ))
      (instantiateResidual σ instance_ payload) := by
  induction hit with
  | emit row payload observed => exact discharge_residual_emit D observed
  | skip row next payload n observed nested ih =>
    rw [residualStep_skip (discharge_residualStep_skip D observed)]
    exact ih

public theorem discharge_residual_instantiate
    (D : Discharges σ template instance_ extra) (row : Ty) :
    ResidualRelated instance_ (residual instance_ (row.instantiate σ))
      (instantiateResidual σ instance_ (residual template row)) := by
  by_cases cycle : residual template row = .productiveCycle
  · rw [cycle]
    have nohit := discharge_residual_no_hit D ((residual_cycle_iff_no_hit template row).mp cycle)
    rw [(residual_cycle_iff_no_hit instance_ (row.instantiate σ)).mpr nohit]
    exact .productiveCycle
  · have found : ∃ n, Search.Hit (residualStep template) row (residual template row) n := by
      have projection := residual_projection template row
      cases searched : Search.find (residualStep template) (support template row row) row with
      | none => simp only [searched, Option.getD_none] at projection; exact False.elim (cycle projection)
      | some payload =>
        simp only [searched, Option.getD_some] at projection
        rw [projection]
        exact (Search.find_iff_hit (residualStep template) (support template row row)
          (fun x y inside skipped => residualStep_skip_support template row row x y inside skipped)
          (left_mem_support template row row)).mp searched
    obtain ⟨n, hit⟩ := found
    exact discharge_residual_hit D hit

#assert_axioms ResidualRelated.tailKind residualStep_skip_exposed residualStep_skip residualStep_no_stop residualStep_no_cycle
  residual_hit_payload_not_cycle residual_hit_no_cycle residual_cycle_iff_no_hit discharge_residualStep_skip
  discharge_residual_no_hit discharge_residual_emit discharge_residual_hit discharge_residual_instantiate
end Obend.Core.RecursiveRows
