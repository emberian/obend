module
public import Obend.Core.TemplateDischarge
public import Obend.Core.AliasExposure
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

variable {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}

public theorem exposure_alias_not_rigid {assumptions : Assumptions} {index : Nat} {body : Ty}
    (found : assumptions.alias index = some body) : index ∉ assumptions.rigid := by
  intro member
  have rigid : assumptions.rigid.contains index = true := by simpa using member
  rw [Assumptions.alias_rigid rigid] at found
  cases found

public theorem Discharges.aliasChain_instantiate
    (D : Discharges σ template instance_ extra) {start finish : Ty} {path : List Nat}
    (chain : AliasChain template start path finish) :
    AliasChain instance_ (start.instantiate σ) path (finish.instantiate σ) := by
  induction chain with
  | nil t => exact .nil _
  | @cons index body finish path found pure chain ih =>
    have nonrigid := exposure_alias_not_rigid found
    have closed := D.closed index body nonrigid (Assumptions.alias_bound found)
    have target : instance_.alias index = some body := (D.aliases index nonrigid).trans found
    simpa only [Ty.instantiate, D.fixed index nonrigid, closed] using
      (AliasChain.cons target pure (by simpa only [closed] using ih))

public theorem aliasChain_expose {assumptions : Assumptions} {start finish : Ty}
    {path : List Nat} (chain : AliasChain assumptions start path finish) :
    expose assumptions start = expose assumptions finish := by
  induction chain with
  | nil => rfl
  | cons found pure chain ih => exact (expose_alias _ _ _ found pure).trans ih

public theorem aliasChain_path_nonrigid {start finish : Ty} {path : List Nat}
    (chain : AliasChain template start path finish) :
    ∀ index ∈ path, index ∉ template.rigid := by
  induction chain with
  | nil => simp
  | @cons index body finish path found pure chain ih =>
    intro other present
    rcases List.mem_cons.mp present with same | inside
    · subst other; exact exposure_alias_not_rigid found
    · exact ih other inside

/-- Exposure commutes with a discharging substitution. Nominal observations
are re-exposed because the image of a rigid variable can be an arbitrary row.
Transparent cycles retain their original representative. -/
public theorem Discharges.expose_instantiate
    (D : Discharges σ template instance_ extra) (t : Ty) :
    expose instance_ (t.instantiate σ) =
      match expose template t with
      | .constructor c => .constructor ⟨c.tag, c.children.map (Ty.instantiate σ)⟩
      | .nominal index => expose instance_ (σ index)
      | .unproductive representative => .unproductive representative := by
  obtain ⟨path, finish, chain, distinct, fresh, stopped⟩ :=
    exposeWalk_trace template (template.bounds.map Prod.fst) [] (initial_covers template) t
  change Stopped template (visitPath [] path) finish (expose template t) at stopped
  have mapped := D.aliasChain_instantiate chain
  have endpoint := aliasChain_expose mapped
  generalize sourceResult : expose template t = result at stopped ⊢
  cases stopped with
  | productive terminal nonvariable =>
    rw [endpoint]
    cases finish <;> simp_all [Ty.instantiate, expose, exposeWalk, constructorHead]
  | @unbound index notVisited absent =>
    simpa only [Ty.instantiate] using endpoint
  | @activity index body notVisited found blocked =>
    simpa only [Ty.instantiate] using endpoint
  | @cycle index repeated =>
    have inPath : index ∈ path := by simpa only [visitPath_reverse, List.append_nil,
      List.mem_reverse] using repeated
    have fixed : σ index = .variable index := D.fixed index (aliasChain_path_nonrigid chain index inPath)
    have replay := exposeWalk_replay mapped distinct (instance_.bounds.map Prod.fst) []
      (initial_covers instance_) (by simp)
    change expose instance_ (t.instantiate σ) =
      exposeWalk instance_ _ (visitPath [] path) _ ((Ty.variable index).instantiate σ) at replay
    rw [replay]
    simp only [Ty.instantiate, fixed]
    rw [exposeWalk]
    simp only [repeated, ↓reduceDIte]

public theorem Discharges.expose_instantiate_constructor
    (D : Discharges σ template instance_ extra) {t : Ty} {c : Constructor}
    (observed : expose template t = .constructor c) :
    expose instance_ (t.instantiate σ) =
      .constructor ⟨c.tag, c.children.map (Ty.instantiate σ)⟩ := by
  rw [D.expose_instantiate t, observed]

public theorem Discharges.expose_instantiate_nominal
    (D : Discharges σ template instance_ extra) {t : Ty} {index : Nat}
    (observed : expose template t = .nominal index) :
    expose instance_ (t.instantiate σ) = expose instance_ (σ index) := by
  rw [D.expose_instantiate t, observed]

public theorem Discharges.expose_instantiate_unproductive
    (D : Discharges σ template instance_ extra) {t : Ty} {representative : Nat}
    (observed : expose template t = .unproductive representative) :
    expose instance_ (t.instantiate σ) = .unproductive representative := by
  rw [D.expose_instantiate t, observed]

#assert_axioms exposure_alias_not_rigid Discharges.aliasChain_instantiate aliasChain_expose aliasChain_path_nonrigid
  Discharges.expose_instantiate Discharges.expose_instantiate_constructor
  Discharges.expose_instantiate_nominal Discharges.expose_instantiate_unproductive
end Obend.Core.Proofs.Templates
