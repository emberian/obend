module
/- Contexts that refine a derivation's context: agreeing binder types, and a quantity that is
the derivation's, or `affine` where the derivation's was not `unrestricted`, or
`unrestricted` at a shareable type. Every context premise the checker tests (`safeUses`,
`validContext`, `reusableCaptures`, `argumentAllowed`) transfers from a context to any
refinement of it when the assumptions declare no aliases. -/
public import Obend.Elab.Proofs.AliasFree
import all Obend.Core.Check

namespace Obend.Elab.Proofs.Refines
open Obend.Core.Ty Obend.Core.Check Obend.Elab.Proofs.AliasFree
set_option autoImplicit false

variable {a : Assumptions}

@[expose] public def QuantityRefines (a : Assumptions) (b' b : Binding) : Prop :=
  b'.quantity = b.quantity ∨ (b'.quantity = .affine ∧ b.quantity ≠ .unrestricted) ∨
    (b'.quantity = .unrestricted ∧ b'.type.shareableUnder a.shareableVariables = true)

@[expose] public def BindingRefines (a : Assumptions) (b' b : Binding) : Prop :=
  sameType a b'.type b.type = true ∧ QuantityRefines a b' b

public inductive Refines (a : Assumptions) : Context → Context → Prop where
  | nil : Refines a [] []
  | cons {b' b : Binding} {Γ' Γ : Context} : BindingRefines a b' b → Refines a Γ' Γ → Refines a (b' :: Γ') (b :: Γ)

public theorem refines_refl (Γ : Context) : Refines a Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons b rest ih => exact .cons ⟨sameType_refl _ _, .inl rfl⟩ ih

public theorem refines_cons {b' b : Binding} {Γ' Γ : Context} (head : BindingRefines a b' b)
    (tail : Refines a Γ' Γ) : Refines a (b' :: Γ') (b :: Γ) := .cons head tail

public theorem refines_same_quantity {Γ' Γ : Context} {t t' : Ty} {q : Quantity} (agrees : sameType a t' t = true)
    (tail : Refines a Γ' Γ) : Refines a (⟨t', q⟩ :: Γ') (⟨t, q⟩ :: Γ) := .cons ⟨agrees, .inl rfl⟩ tail

public theorem refines_length {Γ' Γ : Context} (h : Refines a Γ' Γ) : Γ'.length = Γ.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

public theorem refines_getElem {Γ' Γ : Context} (h : Refines a Γ' Γ) :
    ∀ {index : Nat} {binding : Binding}, Γ[index]? = some binding →
      ∃ binding', Γ'[index]? = some binding' ∧ BindingRefines a binding' binding := by
  induction h with
  | nil => intro index binding found; simp at found
  | cons head _ ih =>
    intro index binding found
    cases index with
    | zero => simp at found; subst found; exact ⟨_, rfl, head⟩
    | succ index => simpa using ih (by simpa using found)

theorem safeQuantity_refines {b' b : Binding} (h : QuantityRefines a b' b) {count : Nat}
    (safe : safeQuantity b.quantity count = true) : safeQuantity b'.quantity count = true := by
  rcases h with same | ⟨affine, notU⟩ | ⟨unrestricted, _⟩
  · rw [same]; exact safe
  · rw [affine]; cases hq : b.quantity <;> simp_all [safeQuantity] <;> omega
  · rw [unrestricted]; rfl

public theorem safeUses_refines {Γ' Γ : Context} (h : Refines a Γ' Γ) {uses : Uses}
    (safe : safeUses Γ uses = true) : safeUses Γ' uses = true := by
  induction h generalizing uses with
  | nil => exact safe
  | cons head _ ih =>
    cases uses with
    | nil => simp [safeUses] at safe
    | cons count rest =>
      simp only [safeUses, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        beq_iff_eq, Nat.add_right_cancel_iff] at safe ⊢
      have tail := ih (uses := rest) (by simp [safeUses, safe.1, safe.2.2])
      simp only [safeUses, Bool.and_eq_true, beq_iff_eq] at tail
      exact ⟨tail.1, safeQuantity_refines head.2 safe.2.1, tail.2⟩

public theorem validContext_refines (none_ : a.bounds = []) {Γ' Γ : Context} (h : Refines a Γ' Γ)
    (valid : validContext a.shareableVariables Γ = true) : validContext a.shareableVariables Γ' = true := by
  induction h with
  | nil => exact valid
  | @cons b' b _ _ head _ ih =>
    simp only [validContext, List.all_cons, Bool.and_eq_true] at valid ⊢
    refine ⟨?_, ih valid.2⟩
    have hb := valid.1
    rcases head with ⟨agrees, same | ⟨affine, _⟩ | ⟨unrestricted, share⟩⟩
    · rw [same, shareable_congr none_ agrees]; exact hb
    · simp [affine]
    · simp [share]

public theorem reusableCaptures_refines (none_ : a.bounds = []) {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {uses : Uses} (captures : reusableCaptures a.shareableVariables Γ uses = true) :
    reusableCaptures a.shareableVariables Γ' uses = true := by
  induction h generalizing uses with
  | nil => exact captures
  | @cons b' b _ _ head _ ih =>
    cases uses with
    | nil => simp [reusableCaptures] at captures
    | cons count rest =>
      simp only [reusableCaptures, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        beq_iff_eq, Nat.add_right_cancel_iff] at captures ⊢
      have tail := ih (uses := rest) (by simp [reusableCaptures, captures.1, captures.2.2])
      simp only [reusableCaptures, Bool.and_eq_true, beq_iff_eq] at tail
      refine ⟨tail.1, ?_, tail.2⟩
      have hb := captures.2.1
      rcases head with ⟨agrees, same | ⟨affine, notU⟩ | ⟨unrestricted, share⟩⟩
      · rw [same, shareable_congr none_ agrees]; exact hb
      · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hb ⊢
        rcases hb with zero | ⟨isU, _⟩
        · exact .inl zero
        · exact absurd (by simpa using isU) notU
      · simp [unrestricted, share]

public theorem reusableAllowed_refines (none_ : a.bounds = []) {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {reuse : Reuse} {uses : Uses} (allowed : reusableAllowed a reuse Γ uses = true) :
    reusableAllowed a reuse Γ' uses = true := by
  simp only [reusableAllowed, Bool.or_eq_true] at allowed ⊢
  exact allowed.imp id (reusableCaptures_refines none_ h)

/-- A refinement never makes a binder `linear` that was not (`QuantityRefines`), so an argument
that uses no `linear` hypothesis still uses none. -/
public theorem linearFree_refines {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {uses : Uses} (free : linearFree Γ uses = true) : linearFree Γ' uses = true := by
  induction h generalizing uses with
  | nil => exact free
  | @cons b' b _ _ head _ ih =>
    cases uses with
    | nil => rfl
    | cons count rest =>
      simp only [linearFree, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at free ⊢
      refine ⟨?_, ih free.2⟩
      have q := head.2
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at free ⊢
      rcases free.1 with zero | notLinear
      · exact .inl zero
      · refine .inr ?_
        rcases q with same | ⟨affine, _⟩ | ⟨unrestricted, _⟩
        · rw [same]; exact notLinear
        · rw [affine]; decide
        · rw [unrestricted]; decide

/-- Branches that agree on every `linear` binder of `Γ` agree on every `linear` binder of a
refinement, which has no `linear` binder `Γ` lacks. -/
public theorem branchesAgree_refines {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {first second : Uses} (agreeing : branchesAgree Γ first second = true) : branchesAgree Γ' first second = true := by
  induction h generalizing first second with
  | nil => cases first <;> cases second <;> rfl
  | @cons b' b _ _ head _ ih =>
    cases first with
    | nil => rfl
    | cons x first =>
      cases second with
      | nil => rfl
      | cons y second =>
        simp only [branchesAgree, Bool.and_eq_true] at agreeing ⊢
        refine ⟨?_, ih agreeing.2⟩
        have q := head.2
        have here := agreeing.1
        rcases q with same | ⟨affine, _⟩ | ⟨unrestricted, _⟩
        · rw [same]; exact here
        · rw [affine]; rfl
        · rw [unrestricted]; rfl

public theorem argumentAllowed_refines (none_ : a.bounds = []) {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {q : Quantity} {t t' : Ty} {uses : Uses} (agrees : sameType a t' t = true)
    (allowed : argumentAllowed a q Γ t uses = true) : argumentAllowed a q Γ' t' uses = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at allowed ⊢
  refine ⟨⟨by rw [sameType_isComputation agrees]; exact allowed.1.1,
    allowed.1.2.imp id (linearFree_refines h)⟩, ?_⟩
  rcases allowed.2 with notU | ⟨share, captures⟩
  · exact .inl notU
  · exact .inr ⟨by rw [shareable_congr none_ agrees]; exact share, reusableCaptures_refines none_ h captures⟩

end Obend.Elab.Proofs.Refines
