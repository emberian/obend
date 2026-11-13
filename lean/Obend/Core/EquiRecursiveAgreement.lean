module
/- Public Boolean laws and head-chase unfolding for equi-recursive agreement,
defined directly from the finite type-graph bisimulation (`TypeGraph.candidate`). -/
public import Obend.Core.TypeGraphAlias
public import Obend.Core.FieldCongruence
public import Obend.Core.FiniteRowLaws
public section

namespace Obend.Core.Check
open Obend.Core.Ty
set_option autoImplicit false

/-- A canonical type with its declared alias head unfolded once: a transparent alias
variable whose bound is not an activity becomes its bound's canonical form; every
other type (rigid, unbound, any non-variable) is a fixed point. -/
@[expose] def Assumptions.unfoldHead (assumptions : Assumptions) : Ty → Ty
  | .variable index => match assumptions.alias index with
    | some bound => if bound.isComputation then .variable index else bound.canonical
    | none => .variable index
  | other => other

/-- `k` head unfoldings. -/
@[expose] def Assumptions.chase (assumptions : Assumptions) : Nat → Ty → Ty
  | 0, type => type
  | k + 1, type => assumptions.chase k (assumptions.unfoldHead type)

end Obend.Core.Check

namespace Obend.Core.EquiRecursiveAgreement
open Obend.Core.Ty Obend.Core.Check Obend.Core.TypeGraph
set_option autoImplicit false

private theorem insertCanonical_equivalent (assumptions : Assumptions) (row : Ty) (name : String) (member : Ty) :
    Equivalent assumptions (.field name member row) (row.insertCanonical name member) := by
  have eqv := equivalent_equivalence assumptions
  induction row with
  | field prior old tail _ ih =>
    simp only [Ty.insertCanonical]
    split
    · rename_i he
      subst prior
      split
      · rename_i hs
        exact finite_field_shadow assumptions name member old tail hs
      · exact eqv.refl _
    · rename_i hne
      split
      · exact eqv.refl _
      · exact eqv.trans (finite_field_commute assumptions name prior member old tail hne)
          (field_congruence (eqv.refl old) ih)
  | _ => exact eqv.refl _

private theorem canonical_equivalent (assumptions : Assumptions) (type : Ty) :
    Equivalent assumptions type type.canonical := by
  have eqv := equivalent_equivalence assumptions
  induction type with
  | arrow _ _ _ _ ia ib => exact arrow_congruence ia ib
  | field name _ _ im it =>
    exact eqv.trans (field_congruence im it) (insertCanonical_equivalent assumptions _ name _)
  | specification _ _ ia ib => exact specification_congruence ia ib
  | prototype _ _ ia ib => exact prototype_congruence ia ib
  | variant _ ia => exact variant_congruence ia
  | computation _ _ _ ia ib ic => exact computation_congruence ia ib ic
  | _ => exact eqv.refl _

private theorem unfoldHead_equivalent (assumptions : Assumptions) (type : Ty) :
    Equivalent assumptions type (assumptions.unfoldHead type) := by
  have eqv := equivalent_equivalence assumptions
  cases type with
  | «variable» index =>
    simp only [Assumptions.unfoldHead]
    cases ha : assumptions.alias index with
    | none => exact eqv.refl _
    | some bound =>
      simp only
      cases hc : bound.isComputation with
      | true => exact eqv.refl _
      | false =>
        exact eqv.trans (alias_equivalent assumptions index bound ha hc)
          (canonical_equivalent assumptions bound)
  | _ => exact eqv.refl _

private theorem chase_equivalent (assumptions : Assumptions) : ∀ (k : Nat) (type : Ty),
    Equivalent assumptions type (assumptions.chase k type)
  | 0, type => (equivalent_equivalence assumptions).refl type
  | k + 1, type =>
    (equivalent_equivalence assumptions).trans (unfoldHead_equivalent assumptions type)
      (chase_equivalent assumptions k (assumptions.unfoldHead type))

/-- Head-chased canonical fast-path followed by the finite visited-pair type-graph decision. -/
@[expose] def agrees (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  (assumptions.chase assumptions.bounds.length actual.canonical ==
    assumptions.chase assumptions.bounds.length expected.canonical) ||
    candidate assumptions actual expected

theorem agrees_iff (assumptions : Assumptions) (actual expected : Ty) :
    agrees assumptions actual expected = true ↔ Equivalent assumptions actual expected := by
  have eqv := equivalent_equivalence assumptions
  simp only [agrees, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (hch | hcand)
    · have ha := eqv.trans (canonical_equivalent assumptions actual)
        (chase_equivalent assumptions assumptions.bounds.length actual.canonical)
      have he := eqv.trans (canonical_equivalent assumptions expected)
        (chase_equivalent assumptions assumptions.bounds.length expected.canonical)
      rw [hch] at ha
      exact eqv.trans ha (eqv.symm he)
    · exact (candidate_iff assumptions actual expected).mp hcand
  · intro h
    exact Or.inr ((candidate_iff assumptions actual expected).mpr h)

theorem agrees_eq_candidate (assumptions : Assumptions) (actual expected : Ty) :
    agrees assumptions actual expected = candidate assumptions actual expected := by
  cases fast : agrees assumptions actual expected <;>
    cases graph : candidate assumptions actual expected <;> try rfl
  · have accepted := (agrees_iff assumptions actual expected).mpr
      ((candidate_iff assumptions actual expected).mp graph)
    simp only [fast, Bool.false_eq_true] at accepted
  · have accepted := (candidate_iff assumptions actual expected).mpr
      ((agrees_iff assumptions actual expected).mp fast)
    simp only [graph, Bool.false_eq_true] at accepted

theorem agrees_equivalence (assumptions : Assumptions) :
    Equivalence (fun actual expected => agrees assumptions actual expected = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro type
    exact (agrees_iff _ _ _).mpr ((equivalent_equivalence assumptions).refl type)
  · intro actual expected agreement
    exact (agrees_iff _ _ _).mpr
      ((equivalent_equivalence assumptions).symm ((agrees_iff _ _ _).mp agreement))
  · intro actual middle expected first second
    exact (agrees_iff _ _ _).mpr
      ((equivalent_equivalence assumptions).trans
        ((agrees_iff _ _ _).mp first) ((agrees_iff _ _ _).mp second))

theorem agrees_refl (assumptions : Assumptions) (type : Ty) :
    agrees assumptions type type = true := (agrees_equivalence assumptions).refl type

theorem agrees_symm {assumptions : Assumptions} {actual expected : Ty}
    (agreement : agrees assumptions actual expected = true) :
    agrees assumptions expected actual = true := (agrees_equivalence assumptions).symm agreement

theorem agrees_trans {assumptions : Assumptions} {a b c : Ty}
    (first : agrees assumptions a b = true) (second : agrees assumptions b c = true) :
    agrees assumptions a c = true := (agrees_equivalence assumptions).trans first second

theorem agrees_arrow {assumptions : Assumptions} {reuse : Reuse} {quantity : Quantity}
    {domain codomain domain' codomain' : Ty}
    (domains : agrees assumptions domain domain' = true)
    (codomains : agrees assumptions codomain codomain' = true) :
    agrees assumptions (.arrow reuse quantity domain codomain)
      (.arrow reuse quantity domain' codomain') = true :=
  (agrees_iff _ _ _).mpr (arrow_congruence
    ((agrees_iff _ _ _).mp domains) ((agrees_iff _ _ _).mp codomains))

theorem agrees_field {assumptions : Assumptions} {name : String}
    {member tail member' tail' : Ty}
    (members : agrees assumptions member member' = true)
    (tails : agrees assumptions tail tail' = true) :
    agrees assumptions (.field name member tail) (.field name member' tail') = true :=
  (agrees_iff _ _ _).mpr (field_congruence
    ((agrees_iff _ _ _).mp members) ((agrees_iff _ _ _).mp tails))

theorem agrees_specification {assumptions : Assumptions} {metadata extension metadata' extension' : Ty}
    (metadataRelated : agrees assumptions metadata metadata' = true)
    (extensionRelated : agrees assumptions extension extension' = true) :
    agrees assumptions (.specification metadata extension) (.specification metadata' extension') = true :=
  (agrees_iff _ _ _).mpr (specification_congruence
    ((agrees_iff _ _ _).mp metadataRelated) ((agrees_iff _ _ _).mp extensionRelated))

theorem agrees_prototype {assumptions : Assumptions} {spec target spec' target' : Ty}
    (specs : agrees assumptions spec spec' = true)
    (targets : agrees assumptions target target' = true) :
    agrees assumptions (.prototype spec target) (.prototype spec' target') = true :=
  (agrees_iff _ _ _).mpr (prototype_congruence
    ((agrees_iff _ _ _).mp specs) ((agrees_iff _ _ _).mp targets))

theorem agrees_variant {assumptions : Assumptions} {row row' : Ty}
    (rows : agrees assumptions row row' = true) :
    agrees assumptions (.variant row) (.variant row') = true :=
  (agrees_iff _ _ _).mpr (variant_congruence ((agrees_iff _ _ _).mp rows))

theorem agrees_computation {assumptions : Assumptions}
    {plan response result plan' response' result' : Ty}
    (plans : agrees assumptions plan plan' = true)
    (responses : agrees assumptions response response' = true)
    (results : agrees assumptions result result' = true) :
    agrees assumptions (.computation plan response result)
      (.computation plan' response' result') = true :=
  (agrees_iff _ _ _).mpr (computation_congruence
    ((agrees_iff _ _ _).mp plans) ((agrees_iff _ _ _).mp responses) ((agrees_iff _ _ _).mp results))

theorem agrees_alias (assumptions : Assumptions) (index : Nat) (body : Ty)
    (found : assumptions.alias index = some body) (pure : body.isComputation = false) :
    agrees assumptions (.variable index) body = true :=
  (agrees_iff _ _ _).mpr (alias_equivalent assumptions index body found pure)

theorem agrees_commute (assumptions : Assumptions) (name prior : String)
    (member old tail : Ty) (different : name ≠ prior) :
    agrees assumptions (.field name member (.field prior old tail))
      (.field prior old (.field name member tail)) = true :=
  (agrees_iff _ _ _).mpr (finite_field_commute assumptions name prior member old tail different)

theorem agrees_shadow (assumptions : Assumptions) (name : String) (member old tail : Ty)
    (share : old.shareable = true) :
    agrees assumptions (.field name member (.field name old tail)) (.field name member tail) = true :=
  (agrees_iff _ _ _).mpr (finite_field_shadow assumptions name member old tail share)

theorem canonical_sound (assumptions : Assumptions) (type : Ty) :
    agrees assumptions type type.canonical = true :=
  (agrees_iff _ _ _).mpr (canonical_equivalent assumptions type)

theorem agrees_unfoldHead (assumptions : Assumptions) (type : Ty) :
    agrees assumptions type (assumptions.unfoldHead type) = true :=
  (agrees_iff _ _ _).mpr (unfoldHead_equivalent assumptions type)

theorem agrees_chase (assumptions : Assumptions) (k : Nat) (type : Ty) :
    agrees assumptions type (assumptions.chase k type) = true :=
  (agrees_iff _ _ _).mpr (chase_equivalent assumptions k type)

end Obend.Core.EquiRecursiveAgreement
end
