module
/- The structural checker accepts the alias-domain identity when a present
annotation supplies its valid natural-domain representative. Missing or invalid
representatives retain a precise refusal; nominal resource checks still matter. -/
public import Obend.Core.Bidirectional
import all Obend.Core.Check

namespace Obend.Core.Proofs.EquiRecursiveBoundary
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
set_option autoImplicit false

@[expose] public def natAlias : Assumptions := ⟨[(0, .natural)], [], []⟩
@[expose] public def identityTerm : Term := .lam (.bound 0)
@[expose] public def naturalArrow : Ty := .arrow .reusable .unrestricted .natural .natural
@[expose] public def aliasDomainArrow : Ty := .arrow .reusable .unrestricted (.variable 0) .natural

/-- An interface for a proposed replacement equality. Its arrow rule preserves
quantity and reuse exactly; it does not impose any resource-predicate theorem. -/
public structure ArrowAgreementExtension (equivalent : Ty → Ty → Prop) : Prop where
  extendsCurrent : ∀ {a b}, sameType natAlias a b = true → equivalent a b
  arrow : ∀ {reuse quantity a a' b b'}, equivalent a a' → equivalent b b' →
    equivalent (.arrow reuse quantity a b) (.arrow reuse quantity a' b')

public theorem alias_agrees : sameType natAlias .natural (.variable 0) = true := by
  apply sameType_extends
  decide

public theorem alias_agrees_reverse : sameType natAlias (.variable 0) .natural = true :=
  sameType_symm alias_agrees

public theorem natural_arrow_agrees_alias_domain : sameType natAlias naturalArrow aliasDomainArrow = true := by
  apply (sameType_iff _ _ _).mpr
  exact Obend.Core.TypeGraph.arrow_congruence ((sameType_iff _ _ _).mp alias_agrees)
    ((Obend.Core.TypeGraph.equivalent_equivalence natAlias).refl .natural)

public theorem congruence_equates_arrows {equivalent : Ty → Ty → Prop}
    (extension : ArrowAgreementExtension equivalent) :
    equivalent naturalArrow aliasDomainArrow :=
  extension.arrow (extension.extendsCurrent alias_agrees)
    (extension.extendsCurrent (sameType_refl natAlias .natural))

/-- Equivalent domains need not have the same nominal shareability. -/
public theorem alias_shareability_differs :
    Ty.shareableUnder natAlias.shareableVariables .natural = true ∧
    Ty.shareableUnder natAlias.shareableVariables (.variable 0) = false := by decide

public theorem alias_binder_invalid :
    validContext natAlias.shareableVariables [⟨.natural, .unrestricted⟩] = true ∧
    validContext natAlias.shareableVariables [⟨.variable 0, .unrestricted⟩] = false := by decide

public theorem identity_derivation : PartialTyping natAlias [] identityTerm naturalArrow [] :=
  .lambda (annotation := ⟨.natural, .natural, .unrestricted, .reusable⟩)
    (.bound (binding := ⟨.natural, .unrestricted⟩) rfl) (by decide) (by decide) (by decide) (by decide)

@[expose] public def naturalIdentityAnnotation : LambdaAnnotation :=
  ⟨.natural, .natural, .unrestricted, .reusable⟩

@[expose] public def aliasIdentityAnnotation : LambdaAnnotation :=
  ⟨.variable 0, .natural, .unrestricted, .reusable⟩

@[expose] public def identityAnnotations : Annotations :=
  fun path => if path = [] then some naturalIdentityAnnotation else none

/-- Without a representative, checking still selects the expected alias binder,
whose nominal unrestricted resource premise is invalid. -/
public theorem identity_alias_check_refused (annotations : Annotations)
    (missing : annotations [] = none) :
    checkAt natAlias annotations [] [] identityTerm aliasDomainArrow =
      .error (.invalidContext []) := by
  have head : representativeHead natAlias annotations [] aliasDomainArrow = aliasDomainArrow := by
    rw [representativeHead, missing]
    rfl
  dsimp only [natAlias, aliasDomainArrow] at head
  have aliases := alias_agrees_reverse
  dsimp only [natAlias] at aliases
  simp [checkAt, elaborate, identityTerm, missing, head, aliasDomainArrow, natAlias,
    finish, aliases, need, variableUses, safeUses, safeQuantity, Quantity.fits, linearFree,
    validContext, reusableAllowed, reusableCaptures, List.getElem?_cons_zero,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Ty.shareable, checkedSynth]
  split <;> simp_all [need, safeUses, safeQuantity, Quantity.fits, linearFree, validContext, reusableAllowed,
    reusableCaptures, bind, Except.bind, pure, Except.pure, Ty.shareable]
  rename_i impossible
  exact False.elim (impossible .reusable .unrestricted (.variable 0) .natural rfl rfl rfl rfl)

public theorem identity_alias_top_refused (annotations : Annotations)
    (missing : annotations [] = none) :
    checkAgainst ⟨identityTerm, annotations, natAlias⟩ [] aliasDomainArrow =
      .error (.invalidContext []) := by
  unfold checkAgainst
  rw [identity_alias_check_refused annotations missing]
  rfl

/-- A present annotation with the same invalid alias binder is still refused. -/
public theorem identity_bad_annotation_refused (annotations : Annotations)
    (bad : annotations [] = some aliasIdentityAnnotation) :
    checkAt natAlias annotations [] [] identityTerm aliasDomainArrow =
      .error (.invalidContext []) := by
  have aliases := alias_agrees_reverse
  dsimp only [natAlias] at aliases
  simp [checkAt, elaborate, identityTerm, aliasDomainArrow, aliasIdentityAnnotation, bad,
    finish, aliases, need, variableUses, safeUses, safeQuantity, Quantity.fits, linearFree,
    validContext, natAlias, reusableAllowed, reusableCaptures, List.getElem?_cons_zero,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Ty.shareable, checkedSynth]

public theorem identity_bad_annotation_top_refused (annotations : Annotations)
    (bad : annotations [] = some aliasIdentityAnnotation) :
    checkAgainst ⟨identityTerm, annotations, natAlias⟩ [] aliasDomainArrow =
      .error (.invalidContext []) := by
  unfold checkAgainst
  rw [identity_bad_annotation_refused annotations bad]
  rfl

public theorem identity_alias_derivation : PartialTyping natAlias [] identityTerm aliasDomainArrow [] :=
  .conversion identity_derivation natural_arrow_agrees_alias_domain

/-- The repaired checker uses the supplied natural binder and then converts the
complete arrow to the requested equi-recursive domain. -/
public theorem identity_annotated_check_exact :
    checkAt natAlias identityAnnotations [] [] identityTerm aliasDomainArrow =
      .ok (⟨[], identity_alias_derivation⟩ : Against natAlias [] identityTerm aliasDomainArrow) := by
  have arrows := natural_arrow_agrees_alias_domain
  dsimp only [natAlias, naturalArrow, aliasDomainArrow] at arrows
  simp [checkAt, elaborate, identityTerm, aliasDomainArrow, identityAnnotations,
    naturalIdentityAnnotation, finish, sameType_refl, arrows,
    need, variableUses, safeUses, safeQuantity, Quantity.fits, linearFree, validContext, natAlias, reusableAllowed,
    reusableCaptures, naturalArrow, List.getElem?_cons_zero,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Ty.shareable, checkedSynth]

public theorem identity_annotated_check_accepted :
    ∃ checked, checkAt natAlias identityAnnotations [] [] identityTerm aliasDomainArrow = .ok checked :=
  ⟨_, identity_annotated_check_exact⟩

public theorem identity_annotated_top_accepted :
    ∃ checked, checkAgainst ⟨identityTerm, identityAnnotations, natAlias⟩ [] aliasDomainArrow = .ok checked := by
  unfold checkAgainst
  rw [identity_annotated_check_exact]
  simp [need, safeUses, validContext, natAlias, Assumptions.valid, Ty.isComputation,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- Canonicalization makes different shadow-retention decisions before a
structural comparison can unfold the equivalent field members. A replacement
must handle the retained hidden obligation, rather than compare canonical row
spines constructor-for-constructor. -/
public theorem canonical_shadow_spines_differ :
    (Ty.field "a" .boolean (.field "a" (.variable 0) .emptyRow)).canonical ≠
      (Ty.field "a" .boolean (.field "a" .natural .emptyRow)).canonical := by decide

public theorem canonical_retains_hidden_alias :
    (Ty.field "a" .boolean (.field "a" (.variable 0) .emptyRow)).canonical =
      .field "a" .boolean (.field "a" (.variable 0) .emptyRow) := by decide

public theorem canonical_discards_hidden_natural :
    (Ty.field "a" .boolean (.field "a" .natural .emptyRow)).canonical =
      .field "a" .boolean .emptyRow := by decide

/-- Field congruence forces these rows to agree even though canonicalization
retains a hidden alias on only one side. -/
public theorem field_congruence_crosses_shadow_spines
    {equivalent : Ty → Ty → Prop}
    (extendsCurrent : ∀ {a b}, sameType natAlias a b = true → equivalent a b)
    (field : ∀ {name a a' tail tail'}, equivalent a a' → equivalent tail tail' →
      equivalent (.field name a tail) (.field name a' tail')) :
    equivalent (.field "a" .boolean (.field "a" .natural .emptyRow))
      (.field "a" .boolean (.field "a" (.variable 0) .emptyRow)) :=
  field (extendsCurrent (sameType_refl natAlias .boolean))
    (field (extendsCurrent alias_agrees) (extendsCurrent (sameType_refl natAlias .emptyRow)))

/-- This exact witness records both sides of the annotation boundary: the
converted declarative term is accepted with a valid representative, while an
absent root annotation still exposes the invalid nominal alias binder. -/
public theorem representative_annotation_resolves_boundary :
    PartialTyping natAlias [] identityTerm aliasDomainArrow [] ∧
      (∀ annotations, annotations [] = none →
        checkAgainst ⟨identityTerm, annotations, natAlias⟩ [] aliasDomainArrow =
          .error (.invalidContext [])) ∧
      ∃ checked, checkAgainst ⟨identityTerm, identityAnnotations, natAlias⟩ [] aliasDomainArrow = .ok checked :=
  ⟨identity_alias_derivation, identity_alias_top_refused, identity_annotated_top_accepted⟩

end Obend.Core.Proofs.EquiRecursiveBoundary
