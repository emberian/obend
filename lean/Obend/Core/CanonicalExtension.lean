module
public import Obend.Core.LegacyAgreement
@[expose] public section
namespace Obend.Core.CanonicalExtension
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

/-- Finite equations sufficient to preserve the old checker equality. The row
laws apply to arbitrary tails, including non-row constructors. Hidden entries
may be erased only under the old syntactic shareability test. -/
structure Laws (E : Ty → Ty → Prop) : Prop where
  refl : ∀ a, E a a
  symm : ∀ {a b}, E a b → E b a
  trans : ∀ {a b c}, E a b → E b c → E a c
  arrow : ∀ reuse quantity {a b c d}, E a b → E c d →
    E (.arrow reuse quantity a c) (.arrow reuse quantity b d)
  field : ∀ name {a b c d}, E a b → E c d → E (.field name a c) (.field name b d)
  specification : ∀ {a b c d}, E a b → E c d → E (.specification a c) (.specification b d)
  prototype : ∀ {a b c d}, E a b → E c d → E (.prototype a c) (.prototype b d)
  variant : ∀ {a b}, E a b → E (.variant a) (.variant b)
  computation : ∀ {a b c d e f}, E a b → E c d → E e f →
    E (.computation a c e) (.computation b d f)
  commute : ∀ name prior member old tail, name ≠ prior →
    E (.field name member (.field prior old tail)) (.field prior old (.field name member tail))
  shadow : ∀ name member old tail, old.shareable = true →
    E (.field name member (.field name old tail)) (.field name member tail)

variable {E : Ty → Ty → Prop}

/-- Insertion is an equation even when its tail is not a canonical row. This
does not assert that insertion preserves arbitrary semantic equivalences. -/
theorem insertCanonical_sound (laws : Laws E) (row : Ty) (name : String) (member : Ty) :
    E (.field name member row) (row.insertCanonical name member) := by
  induction row with
  | field prior old tail _ ih =>
    simp only [Ty.insertCanonical]
    by_cases he : name = prior
    · subst prior
      by_cases hs : old.shareable = true
      · simpa only [if_pos rfl, hs, if_true] using laws.shadow name member old tail hs
      · simpa only [if_pos rfl, ite_true, if_neg hs] using laws.refl (.field name member (.field name old tail))
    · by_cases hl : name < prior
      · simpa only [if_neg he, if_pos hl] using laws.refl (.field name member (.field prior old tail))
      · simp only [if_neg he, if_neg hl]
        exact laws.trans (laws.commute name prior member old tail he)
          (laws.field prior (laws.refl old) ih)
  | _ => exact laws.refl _

/-- Insertion inherits constructor congruence through its finite equations;
no invariant on the shapes or ordering of the related tails is required. -/
theorem insertCanonical_congr (laws : Laws E) (name : String)
    {row row' member member' : Ty} (rows : E row row') (members : E member member') :
    E (row.insertCanonical name member) (row'.insertCanonical name member') := by
  exact laws.trans (laws.symm (insertCanonical_sound laws row name member))
    (laws.trans (laws.field name members rows) (insertCanonical_sound laws row' name member'))

theorem canonical_sound (laws : Laws E) (type : Ty) : E type type.canonical := by
  induction type with
  | arrow reuse quantity a b ia ib => exact laws.arrow reuse quantity ia ib
  | field name member tail im it =>
    exact laws.trans (laws.field name im it) (insertCanonical_sound laws _ _ _)
  | specification a b ia ib => exact laws.specification ia ib
  | prototype a b ia ib => exact laws.prototype ia ib
  | variant a ia => exact laws.variant ia
  | computation a b c ia ib ic => exact laws.computation ia ib ic
  | _ => exact laws.refl _

theorem of_canonical_eq (laws : Laws E) {a b : Ty}
    (equal : a.canonical = b.canonical) : E a b := by
  have back := laws.symm (canonical_sound laws b)
  rw [← equal] at back
  exact laws.trans (canonical_sound laws a) back

/-- The only extra equations needed for the old alias steps. The guard is
essential: declarations naming computations are opaque to old agreement. -/
theorem legacySameType_extends (laws : Laws E) (assumptions : Assumptions)
    (alias : ∀ index body, assumptions.alias index = some body →
      body.isComputation = false → E (.variable index) body)
    {actual expected : Ty} (agreement : legacySameType assumptions actual expected = true) :
    E actual expected := by
  have viaAlias : ∀ {index : Nat} {other : Ty}, (!other.isComputation) = true →
      (assumptions.alias index).map Ty.canonical = some other.canonical → E (.variable index) other := by
    intro index other pure found
    have pure : other.isComputation = false := by simpa using pure
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at found
    | some body =>
      have equal : body.canonical = other.canonical := by simpa [aliased] using found
      have bodyPure : body.isComputation = false := by
        rw [← Ty.canonical_isComputation, equal, Ty.canonical_isComputation]
        exact pure
      exact laws.trans (alias index body aliased bodyPure) (of_canonical_eq laws equal)
  apply legacySameType_lift E laws.refl laws.trans (agreement := agreement)
  intro a b step
  simp only [sameStep, Bool.or_eq_true] at step
  rcases step with (canonical | aliasActual) | aliasExpected
  · exact of_canonical_eq laws (by simpa using canonical)
  · cases a with
    | «variable» index =>
      exact viaAlias (Bool.and_eq_true_iff.mp aliasActual).1
        (by simpa using (Bool.and_eq_true_iff.mp aliasActual).2)
    | _ => simp at aliasActual
  · apply laws.symm
    cases b with
    | «variable» index =>
      exact viaAlias (Bool.and_eq_true_iff.mp aliasExpected).1
        (by simpa using (Bool.and_eq_true_iff.mp aliasExpected).2)
    | _ => simp at aliasExpected

#assert_axioms insertCanonical_sound insertCanonical_congr canonical_sound of_canonical_eq legacySameType_extends
end Obend.Core.CanonicalExtension
