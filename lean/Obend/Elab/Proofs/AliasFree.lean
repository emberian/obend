module
/- Agreement without aliases. When the assumptions declare no bounds, every type exposes its own
constructor (a variable is nominal), so the weak head is the canonical form, agreement keeps the
syntactic head and relates components, and the nominal resource predicate `shareableUnder`
coincides with the semantic one and is therefore invariant under agreement. These are the
facts preparation's completeness uses where the checker reads a representative it chose. -/
public import Obend.Core.Bidirectional
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphResource
public import Obend.AxiomPin

namespace Obend.Elab.Proofs.AliasFree
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional Obend.Core.TypeGraph
open Obend.Core.AliasExposure
set_option autoImplicit false

variable {a : Assumptions}

public theorem whnf_eq (none_ : a.bounds = []) (t : Ty) : whnf a t = t.canonical := by
  simp [whnf, none_, Assumptions.chase]

theorem alias_none (none_ : a.bounds = []) (index : Nat) : a.alias index = none := by
  simp [Assumptions.alias, none_]

theorem expose_eq (none_ : a.bounds = []) (t : Ty) : expose a t = constructorHead t := by
  cases t with
  | «variable» index => rw [expose_without_alias a index (alias_none none_ index)]; rfl
  | _ => simp [expose, exposeWalk]

/-- The shape agreement sees, read off the syntax. -/
@[expose] public def shapeOf : Ty → HeadShape
  | .variable index => .nominal index
  | .emptyRow | .field .. => .row
  | t => match constructorHead t with
    | .constructor observation => .ordinary observation.tag
    | .nominal index => .nominal index
    | .unproductive index => .unproductive index

theorem label_shape (none_ : a.bounds = []) (t : Ty) :
    labelHead ((graph a).label (.type t)) = shapeOf t := by
  cases t <;> simp [graph, observe, expose_eq none_, constructorHead, rowTag, labelHead, rowObservation, shapeOf]

public theorem shape_congr (none_ : a.bounds = []) {t u : Ty} (agrees : sameType a t u = true) :
    shapeOf t = shapeOf u := by
  have := equivalent_head ((sameType_iff _ _ _).mp agrees)
  rwa [label_shape none_, label_shape none_] at this

/-! ### Resources -/

theorem semantic_variable (none_ : a.bounds = []) (index : Nat) :
    Obend.Core.RecursiveRows.shareable a (.variable index) = a.shareableVariables.contains index := by
  apply Obend.Core.RecursiveRows.shareable_terminal
  simp [Obend.Core.ResourceSemantics.head, expose_eq none_, constructorHead]

public theorem shareable_semantic (none_ : a.bounds = []) :
    ∀ t : Ty, t.shareableUnder a.shareableVariables = Obend.Core.RecursiveRows.shareable a t
  | .variable index => by simp [Ty.shareableUnder, semantic_variable none_]
  | .natural => by simp [Ty.shareableUnder, Ty.shareable]
  | .label => by simp [Ty.shareableUnder, Ty.shareable]
  | .boolean => by simp [Ty.shareableUnder, Ty.shareable]
  | .emptyRow => by simp [Ty.shareableUnder, Ty.shareable]
  | .custody _ => by simp [Ty.shareableUnder, Ty.shareable]
  | .arrow .. => by simp [Ty.shareableUnder, Ty.shareable]
  | .computation .. => by simp [Ty.shareableUnder, Ty.shareable]
  | .field name member tail => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_field,
      shareable_semantic none_ member, shareable_semantic none_ tail]
  | .specification m e => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_specification,
      shareable_semantic none_ m, shareable_semantic none_ e]
  | .prototype s t => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_prototype,
      shareable_semantic none_ s, shareable_semantic none_ t]
  | .variant row => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_variant, shareable_semantic none_ row]

/-- Without aliases the nominal resource premise is invariant under agreement. -/
public theorem shareable_congr (none_ : a.bounds = []) {t u : Ty} (agrees : sameType a t u = true) :
    t.shareableUnder a.shareableVariables = u.shareableUnder a.shareableVariables := by
  rw [shareable_semantic none_, shareable_semantic none_]
  exact equivalent_shareable ((sameType_iff _ _ _).mp agrees)

/-! ### Heads and components -/

public theorem arrow_inv (none_ : a.bounds = []) {t : Ty} {r : Reuse} {q : Quantity} {d c : Ty}
    (agrees : sameType a t (.arrow r q d c) = true) :
    ∃ d' c', t = .arrow r q d' c' ∧ sameType a d' d = true ∧ sameType a c' c = true := by
  have shape := shape_congr none_ agrees
  cases t <;> simp [shapeOf, constructorHead] at shape
  rename_i r' q' d' c'
  obtain ⟨hr, hq, hd, hc⟩ := arrow_components ((sameType_iff _ _ _).mp agrees)
  subst hr; subst hq
  exact ⟨d', c', rfl, (sameType_iff _ _ _).mpr hd, (sameType_iff _ _ _).mpr hc⟩

public theorem variant_inv (none_ : a.bounds = []) {t row : Ty}
    (agrees : sameType a t (.variant row) = true) :
    ∃ row', t = .variant row' ∧ sameType a row' row = true := by
  have shape := shape_congr none_ agrees
  cases t <;> simp [shapeOf, constructorHead] at shape
  rename_i row'
  exact ⟨row', rfl, (sameType_iff _ _ _).mpr (variant_components ((sameType_iff _ _ _).mp agrees))⟩

public theorem specification_inv (none_ : a.bounds = []) {t m e : Ty}
    (agrees : sameType a t (.specification m e) = true) :
    ∃ m' e', t = .specification m' e' ∧ sameType a m' m = true ∧ sameType a e' e = true := by
  have shape := shape_congr none_ agrees
  cases t <;> simp [shapeOf, constructorHead] at shape
  rename_i m' e'
  obtain ⟨hm, he⟩ := specification_components ((sameType_iff _ _ _).mp agrees)
  exact ⟨m', e', rfl, (sameType_iff _ _ _).mpr hm, (sameType_iff _ _ _).mpr he⟩

public theorem computation_inv (none_ : a.bounds = []) {t p r x : Ty}
    (agrees : sameType a t (.computation p r x) = true) :
    ∃ p' r' x', t = .computation p' r' x' ∧ sameType a p' p = true ∧ sameType a r' r = true ∧
      sameType a x' x = true := by
  have shape := shape_congr none_ agrees
  cases t <;> simp [shapeOf, constructorHead] at shape
  rename_i p' r' x'
  obtain ⟨hp, hr, hx⟩ := computation_components ((sameType_iff _ _ _).mp agrees)
  exact ⟨p', r', x', rfl, (sameType_iff _ _ _).mpr hp, (sameType_iff _ _ _).mpr hr, (sameType_iff _ _ _).mpr hx⟩

/-- A type agreeing with a callable type is callable as written, at agreeing components. -/
public theorem callable_transport (none_ : a.bounds = []) :
    ∀ {target : Ty} {t : Ty} {r : Reuse} {q : Quantity} {d c : Ty},
    sameType a t target = true → callable target = .arrow r q d c →
    ∃ d' c', callable t = .arrow r q d' c' ∧ sameType a d' d = true ∧ sameType a c' c = true
  | .arrow r0 q0 d0 c0, t, r, q, d, c, agrees, shape => by
    simp only [callable, Ty.arrow.injEq] at shape
    obtain ⟨rfl, rfl, rfl, rfl⟩ := shape
    obtain ⟨d', c', rfl, hd, hc⟩ := arrow_inv none_ agrees
    exact ⟨d', c', rfl, hd, hc⟩
  | .specification m e, t, r, q, d, c, agrees, shape => by
    simp only [callable] at shape
    obtain ⟨m', e', rfl, _, he⟩ := specification_inv none_ agrees
    simpa only [callable] using callable_transport none_ he shape
  | .natural, _, _, _, _, _, _, shape | .label, _, _, _, _, _, _, shape | .boolean, _, _, _, _, _, _, shape
  | .variable _, _, _, _, _, _, _, shape | .emptyRow, _, _, _, _, _, _, shape
  | .field .., _, _, _, _, _, _, shape | .prototype .., _, _, _, _, _, _, shape
  | .custody _, _, _, _, _, _, _, shape | .variant _, _, _, _, _, _, _, shape
  | .computation .., _, _, _, _, _, _, shape => by simp [callable] at shape

/-- Lookup transports along agreement, in the checker's visited form. -/
public theorem lookupV_transport {t row : Ty} (agrees : sameType a t row = true) {name : String} {member : Ty}
    (found : lookupV a.bounds [] row name = some member) :
    ∃ member', lookupV a.bounds [] t name = some member' ∧ sameType a member' member = true := by
  obtain ⟨fuel, h⟩ := (lookupV_iff _ _ _ _).1 found
  obtain ⟨depth, member', h', related⟩ :=
    Obend.Core.TypeGraph.equivalent_lookup_transport ((sameType_iff _ _ _).mp agrees) fuel name member h
  exact ⟨member', (lookupV_iff _ _ _ _).2 ⟨depth, h'⟩, (sameType_iff _ _ _).mpr related⟩

#assert_axioms whnf_eq shape_congr shareable_semantic shareable_congr arrow_inv variant_inv
  specification_inv computation_inv callable_transport lookupV_transport
end Obend.Elab.Proofs.AliasFree
