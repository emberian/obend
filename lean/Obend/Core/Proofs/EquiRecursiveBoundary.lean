module
/- Narrow migration boundaries: adding structural equality alone does not make
the current expected-type-directed lambda checker complete. These statements
deliberately leave `sameType` and the checker unchanged. -/
public import Obend.Core.Bidirectional
public import Obend.AxiomPin

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

public theorem alias_agrees : sameType natAlias .natural (.variable 0) = true := by decide

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
    (.bound (binding := ⟨.natural, .unrestricted⟩) rfl) (by decide) (by decide) (by decide)

/-- The expected domain is selected regardless of every supplied annotation.
The body conversion succeeds, then the unrestricted alias binder is rejected. -/
public theorem identity_alias_check_refused (annotations : Annotations) :
    checkAt natAlias annotations [] [] identityTerm aliasDomainArrow =
      .error (.invalidContext []) := by rfl

public theorem identity_alias_top_refused (annotations : Annotations) :
    checkAgainst ⟨identityTerm, annotations, natAlias⟩ [] aliasDomainArrow =
      .error (.invalidContext []) := by rfl

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

/-- Any declarative judgment retaining this lambda and admitting the proposed
conversion accepts the example that the current algorithm refuses. This avoids
asserting that the old `PartialTyping` already has structural conversion. -/
public theorem conversion_requires_checker_redesign
    {equivalent : Ty → Ty → Prop} (extension : ArrowAgreementExtension equivalent)
    (typed : Term → Ty → Prop)
    (includesCurrent : ∀ {t a u}, PartialTyping natAlias [] t a u → typed t a)
    (conversion : ∀ {t a b}, typed t a → equivalent a b → typed t b) :
    typed identityTerm aliasDomainArrow ∧
      ∀ annotations, checkAgainst ⟨identityTerm, annotations, natAlias⟩ [] aliasDomainArrow =
        .error (.invalidContext []) :=
  ⟨conversion (includesCurrent identity_derivation) (congruence_equates_arrows extension),
    identity_alias_top_refused⟩

#assert_axioms alias_agrees congruence_equates_arrows alias_shareability_differs
  alias_binder_invalid identity_derivation identity_alias_check_refused
  identity_alias_top_refused canonical_shadow_spines_differ canonical_retains_hidden_alias
  canonical_discards_hidden_natural field_congruence_crosses_shadow_spines
  conversion_requires_checker_redesign

end Obend.Core.Proofs.EquiRecursiveBoundary
