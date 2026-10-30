module
public import Obend.Core.Assumptions
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

/-- What an instance must discharge. Non-rigid variables are left alone and keep their
bounds (which mention no rigid variable); each rigid variable's image supports its bound
(every member the bound discloses, at the bound's member type instantiated, and row-ness),
is shareable exactly when the template assumed it shareable, and is never an activity. -/
public structure Discharges (σ : Nat → Ty) (template instance_ : Assumptions) (extra : Nat) : Prop where
  fixed : ∀ j, j ∉ template.rigid → σ j = .variable j
  bounds : ∀ j, j ∉ template.rigid → instance_.bounds.lookup j = template.bounds.lookup j
  aliases : ∀ j, j ∉ template.rigid → instance_.alias j = template.alias j
  closed : ∀ j bound, j ∉ template.rigid → template.bounds.lookup j = some bound → bound.instantiate σ = bound
  lookup : ∀ k bound, k ∈ template.rigid → template.bounds.lookup k = some bound →
    ∀ fuel name member, bound.lookup template.bounds fuel name = some member →
      (σ k).lookup instance_.bounds (fuel + extra) name = some (member.instantiate σ)
  row : ∀ k bound, k ∈ template.rigid → template.bounds.lookup k = some bound →
    ∀ fuel, bound.isRow template.bounds fuel = true → (σ k).isRow instance_.bounds (fuel + extra) = true
  shareable : ∀ j, (σ j).shareableUnder instance_.shareableVariables = template.shareableVariables.contains j
  pure : ∀ j, (σ j).isComputation = false


end Obend.Core.Proofs.Templates
