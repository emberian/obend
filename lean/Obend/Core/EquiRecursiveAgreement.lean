module
/- Compatibility and public Boolean laws for equi-recursive agreement. This
comparison module imports the legacy checker through CanonicalExtension. -/
public import Obend.Core.TypeGraphAlias
public import Obend.Core.FieldCongruence
public import Obend.Core.FiniteRowLaws
public import Obend.Core.CanonicalExtension
@[expose] public section
namespace Obend.Core.EquiRecursiveAgreement
open Obend.Core.Ty Obend.Core.Check Obend.Core.TypeGraph
set_option autoImplicit false

/-- The finite graph decision, with no unfolding-depth parameter. -/
def agrees (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  candidate assumptions actual expected

theorem agrees_iff (assumptions : Assumptions) (actual expected : Ty) :
    agrees assumptions actual expected = true ↔ Equivalent assumptions actual expected :=
  candidate_iff assumptions actual expected

/-- All finite equations used by the former canonical agreement are actual
equations of the recursive graph meaning. -/
theorem canonical_laws (assumptions : Assumptions) :
    Obend.Core.CanonicalExtension.Laws (Equivalent assumptions) where
  refl := (equivalent_equivalence assumptions).refl
  symm := (equivalent_equivalence assumptions).symm
  trans := (equivalent_equivalence assumptions).trans
  arrow := by intro _ _ _ _ _ _ h k; exact arrow_congruence h k
  field := by intro _ _ _ _ _ h k; exact field_congruence h k
  specification := fun h k => specification_congruence h k
  prototype := fun h k => prototype_congruence h k
  variant := fun h => variant_congruence h
  computation := fun h k l => computation_congruence h k l
  commute := finite_field_commute assumptions
  shadow := finite_field_shadow assumptions

theorem canonical_sound (assumptions : Assumptions) (type : Ty) :
    agrees assumptions type type.canonical = true :=
  (agrees_iff _ _ _).mpr
    (Obend.Core.CanonicalExtension.canonical_sound (canonical_laws assumptions) type)

/-- Every previously accepted equality remains accepted, including transitive
alias chains and syntactically shareable shadow erasure. -/
theorem legacy_sameType_extends {assumptions : Assumptions} {actual expected : Ty}
    (old : Obend.Core.Check.sameType assumptions actual expected = true) :
    agrees assumptions actual expected = true :=
  (agrees_iff _ _ _).mpr
    (Obend.Core.CanonicalExtension.sameType_extends (canonical_laws assumptions) assumptions
      (alias_equivalent assumptions) old)

theorem agrees_equivalence (assumptions : Assumptions) :
    Equivalence (fun actual expected => agrees assumptions actual expected = true) :=
  candidate_equivalence assumptions

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

#assert_axioms canonical_laws canonical_sound legacy_sameType_extends agrees_iff agrees_equivalence
  agrees_refl agrees_symm agrees_trans agrees_arrow agrees_field agrees_specification agrees_prototype
  agrees_variant agrees_computation agrees_alias agrees_commute agrees_shadow
end Obend.Core.EquiRecursiveAgreement
