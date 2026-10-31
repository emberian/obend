module
/- Syntactic validity implies greatest semantic resource safety, with alias-only
cycles safe. This proof is staged for the opaque-safe ResourceSemantics head. -/
public import Obend.Core.ResourceSemantics
public import Obend.Core.Check
@[expose] public section
namespace Obend.Core.ResourceValidity
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
namespace FS
export Obend.Core.FiniteSafety (Closed Safe)
end FS
set_option autoImplicit false

def observationHead (a : Assumptions) : Head → Bool × List Ty
  | .nominal index => (a.shareableVariables.contains index,[])
  | .unproductive _ => (true,[])
  | .constructor observation =>
    match observation.tag with
    | .natural | .label | .boolean | .emptyRow => (true,[])
    | .arrow reuse _ => (reuse == .reusable,[])
    | .custody _ | .computation => (false,[])
    | .field _ | .specification | .prototype | .variant => (true,observation.children)

/-- The exact finite premise used from `Assumptions.valid`. Keeping this helper
independent of `valid` lets it live below the checker in the eventual graph. -/
def BoundShareable (a : Assumptions) : Prop :=
  ∀ index body, a.shareableVariables.contains index = true →
    a.alias index = some body → body.shareableUnder a.shareableVariables = true

theorem valid_boundShareable {a : Assumptions} (valid : a.valid = true) : BoundShareable a := by
  intro index body listed found
  have checked := (Bool.and_eq_true_iff.mp valid).1
  have entry := (List.all_eq_true.mp checked) index (by simpa using listed)
  simpa [Assumptions.alias_bound found] using entry

private theorem constructor_head_safe (a : Assumptions) (t : Ty)
    (share : t.shareableUnder a.shareableVariables = true) :
    (observationHead a (constructorHead t)).1 = true ∧
      ∀ child ∈ (observationHead a (constructorHead t)).2,
        child.shareableUnder a.shareableVariables = true := by
  cases t <;> simp_all [observationHead,constructorHead,Ty.shareableUnder,Ty.shareable]

theorem walk_head_safe (a : Assumptions) (valid : BoundShareable a)
    (remaining visited : List Nat) (covers : Covers a visited remaining) (t : Ty)
    (share : t.shareableUnder a.shareableVariables = true) :
    (observationHead a (exposeWalk a remaining visited covers t)).1 = true ∧
      ∀ child ∈ (observationHead a (exposeWalk a remaining visited covers t)).2,
        child.shareableUnder a.shareableVariables = true := by
  cases t with
  | «variable» index =>
    simp only [Ty.shareableUnder] at share
    rw [exposeWalk]
    split
    · simp [observationHead]
    · rename_i seen
      split
      · simpa [observationHead] using share
      · rename_i body found
        split
        · simpa [observationHead] using share
        · exact walk_head_safe a valid (remaining.erase index) (index :: visited)
            (covers_step covers index) body (valid index body share found)
  | _ => simpa only [exposeWalk] using constructor_head_safe a _ share
termination_by remaining.length
decreasing_by
  have fresh : index ∈ remaining := (covers index _ (by assumption)).resolve_left (by assumption)
  rw [List.length_erase_of_mem fresh]
  have positive := List.length_pos_of_mem fresh
  omega

/-- A validated syntactic shareability premise supplies a closed greatest-safe
predicate. Alias-only cycles now close safely instead of contradicting it. -/
theorem shareableUnder_safe {a : Assumptions} (valid : BoundShareable a)
    (t : Ty) (share : t.shareableUnder a.shareableVariables = true) : FS.Safe (Obend.Core.ResourceSemantics.graph a) t := by
  refine ⟨fun child => child.shareableUnder a.shareableVariables = true,?_,share⟩
  intro child checked
  exact walk_head_safe a valid _ _ (initial_covers a) child checked

theorem valid_shareableUnder_safe {a : Assumptions} (valid : a.valid = true)
    (t : Ty) (share : t.shareableUnder a.shareableVariables = true) : FS.Safe (Obend.Core.ResourceSemantics.graph a) t :=
  shareableUnder_safe (valid_boundShareable valid) t share

theorem valid_shareableUnder_shareable {a : Assumptions} (valid : a.valid = true)
    (t : Ty) (share : t.shareableUnder a.shareableVariables = true) :
    Obend.Core.ResourceSemantics.shareable a t = true :=
  (Obend.Core.ResourceSemantics.shareable_iff a t).mpr
    (valid_shareableUnder_safe valid t share)

end Obend.Core.ResourceValidity
