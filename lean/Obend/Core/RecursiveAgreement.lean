module
/- Public checker agreement: structural, equi-recursive and decided by a
finite visited-pair procedure. The historical head-chain relation and its
finite proofs remain available as legacySameType for the extension theorem. -/
public import Obend.Core.EquiRecursiveAgreement
public import Obend.Core.TypeGraphHead
@[expose] public section
namespace Obend.Core.Check
open Obend.Core.Ty
set_option autoImplicit false

def sameType (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  EquiRecursiveAgreement.agrees assumptions actual expected

theorem sameType_iff (assumptions : Assumptions) (actual expected : Ty) :
    sameType assumptions actual expected = true ↔ TypeGraph.Equivalent assumptions actual expected :=
  EquiRecursiveAgreement.agrees_iff assumptions actual expected

theorem sameType_refl (assumptions : Assumptions) (type : Ty) : sameType assumptions type type = true :=
  EquiRecursiveAgreement.agrees_refl assumptions type

theorem sameType_symm {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameType assumptions actual expected = true) : sameType assumptions expected actual = true :=
  EquiRecursiveAgreement.agrees_symm agreement

theorem sameType_trans {assumptions : Assumptions} {first middle last : Ty}
    (one : sameType assumptions first middle = true) (two : sameType assumptions middle last = true) :
    sameType assumptions first last = true := EquiRecursiveAgreement.agrees_trans one two

theorem sameType_equivalence (assumptions : Assumptions) :
    Equivalence (fun actual expected => sameType assumptions actual expected = true) :=
  EquiRecursiveAgreement.agrees_equivalence assumptions

theorem sameType_extends {assumptions : Assumptions} {actual expected : Ty}
    (old : legacySameType assumptions actual expected = true) : sameType assumptions actual expected = true :=
  EquiRecursiveAgreement.legacy_sameType_extends old

theorem sameStep_sameType {assumptions : Assumptions} {actual expected : Ty}
    (step : sameStep assumptions actual expected = true) : sameType assumptions actual expected = true :=
  sameType_extends (sameStep_legacySameType step)

theorem SameChain.sameType {assumptions : Assumptions} {first last : Ty}
    (chain : SameChain assumptions first last) : sameType assumptions first last = true :=
  sameType_extends chain.legacySameType

theorem sameType_isComputation {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameType assumptions actual expected = true) :
    actual.isComputation = expected.isComputation := TypeGraph.equivalent_isComputation ((sameType_iff _ _ _).mp agreement)

theorem sameType_canonical (assumptions : Assumptions) (type : Ty) :
    sameType assumptions type type.canonical = true := EquiRecursiveAgreement.canonical_sound assumptions type

theorem sameType_of_canonical (assumptions : Assumptions) {actual expected : Ty}
    (equal : actual.canonical = expected.canonical) : sameType assumptions actual expected = true := by
  have next := sameType_symm (sameType_canonical assumptions expected)
  rw [← equal] at next
  exact sameType_trans (sameType_canonical assumptions actual) next

theorem sameType_arrow {assumptions : Assumptions} {reuse : Reuse} {quantity : Quantity}
    {a b c d : Ty} (domains : sameType assumptions a b = true) (codomains : sameType assumptions c d = true) :
    sameType assumptions (.arrow reuse quantity a c) (.arrow reuse quantity b d) = true :=
  EquiRecursiveAgreement.agrees_arrow domains codomains

theorem sameType_field {assumptions : Assumptions} {name : String}
    {a b c d : Ty} (members : sameType assumptions a b = true) (tails : sameType assumptions c d = true) :
    sameType assumptions (.field name a c) (.field name b d) = true :=
  EquiRecursiveAgreement.agrees_field members tails

theorem sameType_specification {assumptions : Assumptions} {a b c d : Ty}
    (metadata : sameType assumptions a b = true) (extension : sameType assumptions c d = true) :
    sameType assumptions (.specification a c) (.specification b d) = true :=
  EquiRecursiveAgreement.agrees_specification metadata extension

theorem sameType_prototype {assumptions : Assumptions} {a b c d : Ty}
    (specs : sameType assumptions a b = true) (targets : sameType assumptions c d = true) :
    sameType assumptions (.prototype a c) (.prototype b d) = true :=
  EquiRecursiveAgreement.agrees_prototype specs targets

theorem sameType_variant {assumptions : Assumptions} {a b : Ty} (rows : sameType assumptions a b = true) :
    sameType assumptions (.variant a) (.variant b) = true := EquiRecursiveAgreement.agrees_variant rows

theorem sameType_computation {assumptions : Assumptions} {a b c d e f : Ty}
    (plans : sameType assumptions a b = true) (responses : sameType assumptions c d = true)
    (results : sameType assumptions e f = true) :
    sameType assumptions (.computation a c e) (.computation b d f) = true :=
  EquiRecursiveAgreement.agrees_computation plans responses results

end Obend.Core.Check
