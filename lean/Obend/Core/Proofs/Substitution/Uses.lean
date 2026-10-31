module
/- Uses vectors under substitution and context extension; `typed_scoped`. -/
public import Obend.Tactic.Tooth
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Substitution.Defs
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
set_option autoImplicit false

public theorem fillTerm_zero (σ : Nat → Option AnnotatedTerm) (index : Nat) :
    fillTerm σ 0 index = match σ index with | some f => f.term | none => .bound index := by
  cases filled : σ index <;> simp [fillTerm, fillingAt, filled]

theorem fillingAt_succ (σ : Nat → Option AnnotatedTerm) (depth index : Nat) :
    fillingAt σ (depth + 1) (index + 1) = fillingAt σ depth index := by
  simp only [fillingAt, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

theorem fillingAt_succ_zero (σ : Nat → Option AnnotatedTerm) (depth : Nat) :
    fillingAt σ (depth + 1) 0 = none := by
  simp [fillingAt]

/-- Under a binder the term substitution is the same substitution one deeper: the fillings are
closed, so renaming them is the identity. -/
public theorem liftSubstitution_fillTerm (σ : Nat → Option AnnotatedTerm)
    (closed : ∀ x f, σ x = some f → Scoped 0 f.term) (depth : Nat) :
    liftSubstitution (fillTerm σ depth) = fillTerm σ (depth + 1) := by
  funext index
  cases index with
  | zero => simp [liftSubstitution, fillTerm, fillingAt_succ_zero]
  | succ index =>
    simp only [liftSubstitution, fillTerm, fillingAt_succ]
    cases h : fillingAt σ depth index with
    | none => simp [Term.rename]
    | some f =>
      have hf : Scoped 0 f.term := by
        unfold fillingAt at h
        split at h
        · exact closed _ _ h
        · cases h
      exact scoped_rename_identity hf Nat.succ (fun i hi => absurd hi (Nat.not_lt_zero i))

/-! ## Use vectors: pointwise order, and the split over an appended context -/

public theorem UsesLE.length {u v : Uses} (h : UsesLE u v) : u.length = v.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

public theorem UsesLE.refl : ∀ u : Uses, UsesLE u u
  | [] => .nil
  | _ :: u => .cons (Nat.le_refl _) (UsesLE.refl u)

public theorem UsesLE.zero : ∀ u : Uses, UsesLE (List.replicate u.length 0) u
  | [] => .nil
  | _ :: u => .cons (Nat.zero_le _) (UsesLE.zero u)

public theorem UsesLE.tail {u v : Uses} (h : UsesLE u v) : UsesLE u.tail v.tail := by
  cases h with
  | nil => exact .nil
  | cons _ h => exact h

public theorem UsesLE.add {a a' b b' : Uses} (ha : UsesLE a a') (hb : UsesLE b b') :
    UsesLE (addUses a b) (addUses a' b') := by
  induction ha generalizing b b' with
  | nil => cases hb <;> exact .nil
  | cons h _ ih =>
    cases hb with
    | nil => exact .nil
    | cons h' hb => exact .cons (Nat.add_le_add h h') (ih hb)

/-! ### Masked uses: what substitution does to a uses vector

A closed filling uses nothing, so substituting it for hypothesis `x` turns `x`'s count to zero and
leaves every other count as it was: the result's uses are the original's with the filled positions
masked. The mask is a function of the position alone, so two branches are masked alike and a
`linear` hypothesis on which they agreed still agrees (`UsesMasked.agree`). Bounded is not enough:
`UsesLE` would let one branch's count fall and not the other's. -/

/-- Keep the counts where `keep` holds, zero the rest. -/
@[expose] public def maskUses (keep : Nat → Bool) : Uses → Uses
  | [] => []
  | n :: u => (if keep 0 then n else 0) :: maskUses (fun i => keep (i + 1)) u

public theorem getElem?_maskUses : ∀ (keep : Nat → Bool) (u : Uses) (i : Nat),
    (maskUses keep u)[i]? = u[i]?.map (fun n => if keep i then n else 0)
  | _, [], _ => rfl
  | _, _ :: _, 0 => rfl
  | keep, _ :: u, i + 1 => by
    simp only [maskUses, List.getElem?_cons_succ]
    exact getElem?_maskUses (fun i => keep (i + 1)) u i

public theorem length_maskUses (keep : Nat → Bool) (u : Uses) : (maskUses keep u).length = u.length := by
  induction u generalizing keep with
  | nil => rfl
  | cons _ _ ih => simp [maskUses, ih]

public theorem maskUses_zipWith (keep : Nat → Bool) (f : Nat → Nat → Nat) (zero : f 0 0 = 0) :
    ∀ a b : Uses, maskUses keep (List.zipWith f a b) = List.zipWith f (maskUses keep a) (maskUses keep b) := by
  intro a b
  apply List.ext_getElem?
  intro i
  simp only [getElem?_maskUses, List.getElem?_zipWith]
  cases a[i]? <;> cases b[i]? <;> simp
  split <;> simp [zero]

public theorem maskUses_add (keep : Nat → Bool) (a b : Uses) :
    maskUses keep (addUses a b) = addUses (maskUses keep a) (maskUses keep b) :=
  maskUses_zipWith keep _ rfl a b

public theorem maskUses_join (keep : Nat → Bool) (a b : Uses) :
    maskUses keep (joinUses a b) = joinUses (maskUses keep a) (maskUses keep b) :=
  maskUses_zipWith keep _ rfl a b

public theorem maskUses_zero (keep : Nat → Bool) (Γ : Context) : maskUses keep (zeroUses Γ) = zeroUses Γ := by
  apply List.ext_getElem?
  intro i
  simp only [getElem?_maskUses, zeroUses, List.getElem?_replicate]
  split <;> simp

public theorem maskUses_variableUses (keep : Nat → Bool) (Γ : Context) (index : Nat) :
    maskUses keep (variableUses Γ index) = if keep index then variableUses Γ index else zeroUses Γ := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_maskUses]
  by_cases hi : i < Γ.length
  · have value : (variableUses Γ index)[i]? = some (if i = index then 1 else 0) := by
      simp [variableUses, hi]
    rw [value]
    by_cases e : i = index
    · subst e; by_cases hk : keep i <;> simp [hk, value, zeroUses, hi]
    · by_cases hk : keep index <;> simp [hk, e, value, zeroUses, hi]
  · have none_ : (variableUses Γ index)[i]? = none := by simp [variableUses, hi]
    rw [none_]
    by_cases hk : keep index <;> simp [hk, none_, zeroUses, hi]

public theorem maskUses_le (keep : Nat → Bool) : ∀ u : Uses, UsesLE (maskUses keep u) u
  | [] => .nil
  | n :: u => .cons (by split <;> omega) (maskUses_le _ u)

public theorem maskUses_tail (keep : Nat → Bool) (u : Uses) :
    (maskUses keep u).tail = maskUses (fun i => keep (i + 1)) u.tail := by
  cases u <;> rfl

public theorem maskUses_headD {keep : Nat → Bool} (kept : keep 0 = true) (u : Uses) :
    (maskUses keep u).headD 0 = u.headD 0 := by
  cases u <;> simp [maskUses, kept]

public theorem branchesAgree_maskUses : ∀ (Γ : Context) (keep : Nat → Bool) (a b : Uses),
    branchesAgree Γ a b = true → branchesAgree Γ (maskUses keep a) (maskUses keep b) = true
  | [], _, _, _, _ => by cases ‹Uses› <;> rfl
  | _ :: _, _, [], _, _ => rfl
  | _ :: _, _, _ :: _, [], _ => by simp [maskUses, branchesAgree]
  | d :: Γ, keep, x :: a, y :: b, h => by
    simp only [branchesAgree, Bool.and_eq_true] at h
    simp only [maskUses, branchesAgree, Bool.and_eq_true]
    refine ⟨?_, branchesAgree_maskUses Γ _ a b h.2⟩
    have := h.1
    cases hq : d.quantity <;> simp_all [Quantity.agrees] <;> split <;> simp_all

/-- What `σ` leaves in place at depth `depth`: the binders above, and every hypothesis it does not fill. -/
@[expose] public def keepAt (σ : Nat → Option AnnotatedTerm) (depth : Nat) (index : Nat) : Bool :=
  decide (index < depth) || (σ (index - depth)).isNone

public theorem keepAt_succ (σ : Nat → Option AnnotatedTerm) (depth : Nat) :
    (fun i => keepAt σ (depth + 1) (i + 1)) = keepAt σ depth := by
  funext i
  simp only [keepAt, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

public theorem keepAt_zero_succ (σ : Nat → Option AnnotatedTerm) (depth : Nat) : keepAt σ (depth + 1) 0 = true := by
  simp [keepAt]

/-- The uses after substitution are the uses before with the filled hypotheses masked. -/
@[expose] public def UsesMasked (σ : Nat → Option AnnotatedTerm) (depth : Nat) (u' u : Uses) : Prop :=
  u' = maskUses (keepAt σ depth) u

public theorem UsesMasked.le {σ : Nat → Option AnnotatedTerm} {depth : Nat} {u' u : Uses}
    (h : UsesMasked σ depth u' u) : UsesLE u' u := by
  rw [h]; exact maskUses_le _ u

public theorem UsesMasked.add {σ : Nat → Option AnnotatedTerm} {depth : Nat} {a a' b b' : Uses}
    (ha : UsesMasked σ depth a' a) (hb : UsesMasked σ depth b' b) :
    UsesMasked σ depth (addUses a' b') (addUses a b) := by
  unfold UsesMasked at *; rw [ha, hb, maskUses_add]

public theorem UsesMasked.join {σ : Nat → Option AnnotatedTerm} {depth : Nat} {a a' b b' : Uses}
    (ha : UsesMasked σ depth a' a) (hb : UsesMasked σ depth b' b) :
    UsesMasked σ depth (joinUses a' b') (joinUses a b) := by
  unfold UsesMasked at *; rw [ha, hb, maskUses_join]

public theorem UsesMasked.tail {σ : Nat → Option AnnotatedTerm} {depth : Nat} {u' u : Uses}
    (h : UsesMasked σ (depth + 1) u' u) : UsesMasked σ depth u'.tail u.tail := by
  unfold UsesMasked at *; rw [h, maskUses_tail, keepAt_succ]

public theorem UsesMasked.headD {σ : Nat → Option AnnotatedTerm} {depth : Nat} {u' u : Uses}
    (h : UsesMasked σ (depth + 1) u' u) : u'.headD 0 = u.headD 0 := by
  rw [h]; exact maskUses_headD (keepAt_zero_succ σ depth) u

public theorem UsesMasked.zero (σ : Nat → Option AnnotatedTerm) (depth : Nat) (Γ : Context) :
    UsesMasked σ depth (zeroUses Γ) (zeroUses Γ) := (maskUses_zero _ Γ).symm

public theorem UsesMasked.agree {σ : Nat → Option AnnotatedTerm} {depth : Nat} {Γ : Context} {a a' b b' : Uses}
    (ha : UsesMasked σ depth a' a) (hb : UsesMasked σ depth b' b) (h : branchesAgree Γ a b = true) :
    branchesAgree Γ a' b' = true := by
  rw [ha, hb]; exact branchesAgree_maskUses Γ _ a b h

public theorem UsesMasked.agreeArms {σ : Nat → Option AnnotatedTerm} {depth : Nat} {Γ : Context} {a a' b b' : Uses}
    {rest : List (String × Term)} {rest' : List (String × Term)} (same : rest'.isEmpty = rest.isEmpty)
    (ha : UsesMasked σ depth a' a) (hb : UsesMasked σ depth b' b) (h : (rest.isEmpty || branchesAgree Γ a b) = true) :
    (rest'.isEmpty || branchesAgree Γ a' b') = true := by
  rw [same]
  simp only [Bool.or_eq_true] at h ⊢
  exact h.imp id (ha.agree hb)

public theorem UsesMasked.variable {σ : Nat → Option AnnotatedTerm} {depth : Nat} {Γ : Context} {index : Nat}
    (kept : keepAt σ depth index = true) : UsesMasked σ depth (variableUses Γ index) (variableUses Γ index) := by
  unfold UsesMasked; rw [maskUses_variableUses, if_pos kept]

public theorem UsesMasked.filled {σ : Nat → Option AnnotatedTerm} {depth : Nat} {Γ : Context} {index : Nat}
    (dropped : keepAt σ depth index = false) : UsesMasked σ depth (zeroUses Γ) (variableUses Γ index) := by
  unfold UsesMasked; rw [maskUses_variableUses, if_neg (by simp [dropped])]

public theorem keepAt_of_fillingAt_none {σ : Nat → Option AnnotatedTerm} {depth index : Nat}
    (h : fillingAt σ depth index = none) : keepAt σ depth index = true := by
  unfold fillingAt at h; unfold keepAt
  split at h
  · simp [h]
  · rename_i lt; simp; omega

public theorem keepAt_of_fillingAt_some {σ : Nat → Option AnnotatedTerm} {depth index : Nat} {f : AnnotatedTerm}
    (h : fillingAt σ depth index = some f) : keepAt σ depth index = false := by
  unfold fillingAt at h; unfold keepAt
  split at h
  · rename_i le; simp [h]; omega
  · cases h

theorem zipAll_of_le {P : Binding × Nat → Bool}
    (hP : ∀ b m n, n ≤ m → P (b, m) = true → P (b, n) = true) {u v : Uses} (h : UsesLE u v) :
    ∀ Γ : Context, (Γ.zip v).all P = true → (Γ.zip u).all P = true := by
  induction h with
  | nil => intro Γ _; cases Γ <;> rfl
  | cons hab _ ih =>
    intro Γ hall
    cases Γ with
    | nil => rfl
    | cons b Γ =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall ⊢
      exact ⟨hP _ _ _ hab hall.1, ih Γ hall.2⟩

theorem safeQuantity_anti (q : Quantity) {m n : Nat} (h : n ≤ m) (hm : safeQuantity q m = true) :
    safeQuantity q n = true := by
  cases q <;> simp [safeQuantity] at hm ⊢ <;> omega

public theorem safeUses_of_le {Γ : Context} {u v : Uses} (h : UsesLE u v) (hv : safeUses Γ v = true) :
    safeUses Γ u = true := by
  simp only [safeUses, Bool.and_eq_true, beq_iff_eq] at hv ⊢
  exact ⟨h.length.trans hv.1, zipAll_of_le (fun b m n hnm hm => safeQuantity_anti b.quantity hnm hm) h Γ hv.2⟩

public theorem reusableCaptures_of_le {variables : List Nat} {Γ : Context} {u v : Uses} (h : UsesLE u v)
    (hv : reusableCaptures variables Γ v = true) : reusableCaptures variables Γ u = true := by
  simp only [reusableCaptures, Bool.and_eq_true, beq_iff_eq] at hv ⊢
  refine ⟨h.length.trans hv.1, zipAll_of_le ?_ h Γ hv.2⟩
  intro b m n hnm hm
  simp only [Bool.or_eq_true, beq_iff_eq] at hm ⊢
  rcases hm with hm | hm
  · exact .inl (by omega)
  · exact .inr hm

public theorem reusableAllowed_of_le {asm : Assumptions} {reuse : Reuse} {Γ : Context} {u v : Uses}
    (h : UsesLE u v) (hv : reusableAllowed asm reuse Γ v = true) : reusableAllowed asm reuse Γ u = true := by
  simp only [reusableAllowed, Bool.or_eq_true] at hv ⊢
  rcases hv with hv | hv
  · exact .inl hv
  · exact .inr (reusableCaptures_of_le h hv)

public theorem linearFree_of_le {Γ : Context} {u v : Uses} (h : UsesLE u v) (hv : linearFree Γ v = true) :
    linearFree Γ u = true := by
  unfold linearFree at hv ⊢
  refine zipAll_of_le ?_ h Γ hv
  intro b m n hnm hm
  simp only [Bool.or_eq_true, beq_iff_eq] at hm ⊢
  rcases hm with hm | hm
  · exact .inl (by omega)
  · exact .inr hm

public theorem argumentAllowed_of_le {asm : Assumptions} {quantity : Quantity} {Γ : Context} {type : Ty}
    {u v : Uses} (h : UsesLE u v) (hv : argumentAllowed asm quantity Γ type v = true) :
    argumentAllowed asm quantity Γ type u = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true] at hv ⊢
  refine ⟨⟨hv.1.1, ?_⟩, ?_⟩
  · rcases hv.1.2 with hq | hl
    · exact .inl hq
    · exact .inr (linearFree_of_le h hl)
  rcases hv.2 with hq | ⟨hs, hc⟩
  · exact .inl hq
  · exact .inr ⟨hs, reusableCaptures_of_le h hc⟩

public theorem length_zeroUses (Γ : Context) : (zeroUses Γ).length = Γ.length := by simp [zeroUses]

public theorem length_variableUses (Γ : Context) (i : Nat) : (variableUses Γ i).length = Γ.length := by
  simp [variableUses]

public theorem length_addUses {a b : Uses} (h : a.length = b.length) : (addUses a b).length = a.length := by
  simp [addUses, List.length_zipWith, h]

public theorem zeroUses_append (Δ Ψ : Context) : zeroUses (Δ ++ Ψ) = zeroUses Δ ++ zeroUses Ψ := by
  simp [zeroUses, List.replicate_append_replicate]

public theorem variableUses_append_left {Δ : Context} (Ψ : Context) {i : Nat} (h : i < Δ.length) :
    variableUses (Δ ++ Ψ) i = variableUses Δ i ++ zeroUses Ψ := by
  simp only [variableUses, zeroUses, List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.eq_replicate_iff.mpr ⟨by simp, fun x hx => ?_⟩
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  simp only [Function.comp]
  rw [if_neg]
  omega

theorem addUses_append {a b z z' : Uses} (h : a.length = b.length) :
    addUses (a ++ z) (b ++ z') = addUses a b ++ addUses z z' := List.zipWith_append h

theorem addUses_zeroUses (Ψ : Context) : addUses (zeroUses Ψ) (zeroUses Ψ) = zeroUses Ψ := by
  simp [addUses, zeroUses]

theorem zipAll_zero {P : Binding × Nat → Bool} (hP : ∀ b, P (b, 0) = true) :
    ∀ Ψ : Context, (Ψ.zip (zeroUses Ψ)).all P = true
  | [] => rfl
  | b :: Ψ => by
    simp only [zeroUses, List.length_cons, List.replicate_succ, List.zip_cons_cons, List.all_cons, hP,
      Bool.true_and]
    exact zipAll_zero hP Ψ

theorem zipAll_append_zero {P : Binding × Nat → Bool} (hP : ∀ b, P (b, 0) = true) (Δ Ψ Ψ' : Context)
    {a : Uses} (ha : a.length = Δ.length) :
    ((Δ ++ Ψ').zip (a ++ zeroUses Ψ')).all P = ((Δ ++ Ψ).zip (a ++ zeroUses Ψ)).all P := by
  rw [List.zip_append ha.symm, List.zip_append ha.symm, List.all_append, List.all_append,
    zipAll_zero hP, zipAll_zero hP]

public theorem safeUses_append_zero {Δ Ψ Ψ' : Context} {a : Uses} (ha : a.length = Δ.length)
    (h : safeUses (Δ ++ Ψ) (a ++ zeroUses Ψ) = true) : safeUses (Δ ++ Ψ') (a ++ zeroUses Ψ') = true := by
  simp only [safeUses, Bool.and_eq_true, beq_iff_eq, List.length_append, length_zeroUses] at h ⊢
  refine ⟨by omega, ?_⟩
  rw [zipAll_append_zero (fun b => by cases b.quantity <;> rfl) Δ Ψ Ψ' ha]
  exact h.2

public theorem reusableCaptures_append_zero {variables : List Nat} {Δ Ψ Ψ' : Context} {a : Uses}
    (ha : a.length = Δ.length) (h : reusableCaptures variables (Δ ++ Ψ) (a ++ zeroUses Ψ) = true) :
    reusableCaptures variables (Δ ++ Ψ') (a ++ zeroUses Ψ') = true := by
  simp only [reusableCaptures, Bool.and_eq_true, beq_iff_eq, List.length_append, length_zeroUses] at h ⊢
  refine ⟨by omega, ?_⟩
  rw [zipAll_append_zero (fun b => by simp) Δ Ψ Ψ' ha]
  exact h.2

public theorem validContext_append (variables : List Nat) (Δ Ψ : Context) :
    validContext variables (Δ ++ Ψ) = (validContext variables Δ && validContext variables Ψ) := by
  simp [validContext, List.all_append]

public theorem reusableAllowed_append_zero {asm : Assumptions} {reuse : Reuse} {Δ Ψ Ψ' : Context} {a : Uses}
    (ha : a.length = Δ.length) (h : reusableAllowed asm reuse (Δ ++ Ψ) (a ++ zeroUses Ψ) = true) :
    reusableAllowed asm reuse (Δ ++ Ψ') (a ++ zeroUses Ψ') = true := by
  simp only [reusableAllowed, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact .inl h
  · exact .inr (reusableCaptures_append_zero ha h)

public theorem linearFree_append_zero {Δ Ψ Ψ' : Context} {a : Uses} (ha : a.length = Δ.length)
    (h : linearFree (Δ ++ Ψ) (a ++ zeroUses Ψ) = true) : linearFree (Δ ++ Ψ') (a ++ zeroUses Ψ') = true := by
  unfold linearFree at h ⊢
  rw [zipAll_append_zero (fun b => by simp) Δ Ψ Ψ' ha]
  exact h

public theorem argumentAllowed_append_zero {asm : Assumptions} {quantity : Quantity} {type : Ty}
    {Δ Ψ Ψ' : Context} {a : Uses} (ha : a.length = Δ.length)
    (h : argumentAllowed asm quantity (Δ ++ Ψ) type (a ++ zeroUses Ψ) = true) :
    argumentAllowed asm quantity (Δ ++ Ψ') type (a ++ zeroUses Ψ') = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  refine ⟨⟨h.1.1, ?_⟩, ?_⟩
  · rcases h.1.2 with hq | hl
    · exact .inl hq
    · exact .inr (linearFree_append_zero ha hl)
  rcases h.2 with hq | ⟨hs, hc⟩
  · exact .inl hq
  · exact .inr ⟨hs, reusableCaptures_append_zero ha hc⟩

/-! ## A checked term is scoped by its context -/

/-- Every hypothesis a typed term mentions is bound by its context. -/
public theorem typed_scoped {asm : Assumptions} {context : Context} {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping asm context term type uses) : Scoped context.length term := by
  refine PartialTyping.rec
    (motive_1 := fun context term _ _ _ => Scoped context.length term)
    (motive_2 := fun context fields _ _ _ => ∀ f ∈ fields, Scoped context.length f.2)
    (motive_3 := fun context arms _ _ _ _ => ∀ arm ∈ arms, Scoped (context.length + 1) arm.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intros; rename_i found; exact .bound (List.getElem?_eq_some_iff.mp found).1
  · intros; exact .natural _
  · intros; exact .boolean _
  · intros; exact .label _
  · intros; rename_i ih; exact .lam ih
  · intros; assumption
  · intros; rename_i ih₁ ih₂; exact .app ih₁ ih₂
  · intros; rename_i ih; exact .record ih
  · intros; rename_i ih; exact .get ih
  · intros; rename_i ih₁ ih₂; exact .extend ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .specification ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .prototype ih₁ ih₂
  · intros; rename_i ih; exact .reflect ih
  · intros; rename_i ih; exact .metadata ih
  · intros; rename_i ih; exact .project ih
  · intros; rename_i ih₁ ih₂; exact .mix ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .fix ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .binary ih₁ ih₂
  · intros; rename_i ih₁ ih₂ ih₃; exact .condition ih₁ ih₂ ih₃
  · intros; rename_i ih; exact .inject ih
  · intros; rename_i ih₁ ih₂; exact .case ih₁ ih₂
  · intros; rename_i ih₁ ih₂ ih₃; exact .ifBool ih₁ ih₂ ih₃
  · intros; rename_i ih; exact .perform ih
  · intros; rename_i ih; exact .done ih
  · intros; rename_i ih₁ ih₂; exact .case ih₁ ih₂
  · intros; rename_i hf; simp at hf
  · intros; rename_i ih₁ ih₂ f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ih₁
    · exact ih₂ f hf
  · intros; rename_i harm; simp at harm
  · intros; rename_i ih₁ ih₂ arm harm
    rcases List.mem_cons.mp harm with rfl | harm
    · exact ih₁
    · exact ih₂ arm harm

/-! ## Transport: a scoped term checks the same in any valid extension of its context, at any
position, with more fuel -/

public theorem shift_child {ann ann' : Annotations} {pos pos' : List Nat}
    (h : ∀ rest, ann' (pos' ++ rest) = ann (pos ++ rest)) (k : Nat) :
    ∀ rest, ann' ((pos' ++ [k]) ++ rest) = ann ((pos ++ [k]) ++ rest) := by
  intro rest; simpa [List.append_assoc] using h (k :: rest)

public theorem shift_here {ann ann' : Annotations} {pos pos' : List Nat}
    (h : ∀ rest, ann' (pos' ++ rest) = ann (pos ++ rest)) : ann' pos' = ann pos := by
  simpa using h []

public theorem split_add {a₁ a₂ : Uses} (Ψ : Context) (h : a₁.length = a₂.length) :
    addUses (a₁ ++ zeroUses Ψ) (a₂ ++ zeroUses Ψ) = addUses a₁ a₂ ++ zeroUses Ψ := by
  rw [addUses_append h, addUses_zeroUses]

public theorem split_tail {a : Uses} (Ψ : Context) (h : a ≠ []) :
    (a ++ zeroUses Ψ).tail = a.tail ++ zeroUses Ψ :=
  List.tail_append_of_ne_nil h

public theorem length_joinUses {a b : Uses} (h : a.length = b.length) : (joinUses a b).length = a.length := by
  simp [joinUses, List.length_zipWith, h]

public theorem joinUses_zeroUses (Ψ : Context) : joinUses (zeroUses Ψ) (zeroUses Ψ) = zeroUses Ψ := by
  simp [joinUses, zeroUses]

public theorem split_join {a₁ a₂ : Uses} (Ψ : Context) (h : a₁.length = a₂.length) :
    joinUses (a₁ ++ zeroUses Ψ) (a₂ ++ zeroUses Ψ) = joinUses a₁ a₂ ++ zeroUses Ψ := by
  unfold joinUses; rw [List.zipWith_append h]; exact congrArg _ (joinUses_zeroUses Ψ)

public theorem branchesAgree_zero : ∀ Ψ : Context, branchesAgree Ψ (zeroUses Ψ) (zeroUses Ψ) = true
  | [] => rfl
  | b :: Ψ => by
    simp only [zeroUses, List.length_cons, List.replicate_succ, branchesAgree, Bool.and_eq_true]
    exact ⟨by cases b.quantity <;> rfl, branchesAgree_zero Ψ⟩

public theorem branchesAgree_append_zero {Δ Ψ : Context} {a b : Uses} (ha : a.length = Δ.length)
    (hb : b.length = Δ.length) : branchesAgree (Δ ++ Ψ) (a ++ zeroUses Ψ) (b ++ zeroUses Ψ) = branchesAgree Δ a b := by
  induction Δ generalizing a b with
  | nil =>
    cases a <;> cases b <;> simp_all
    exact branchesAgree_zero Ψ
  | cons d Δ ih =>
    cases a with
    | nil => simp at ha
    | cons x a =>
      cases b with
      | nil => simp at hb
      | cons y b =>
        simp only [List.cons_append, branchesAgree]
        rw [ih (by simpa using ha) (by simpa using hb)]

public theorem headD_append {a : Uses} (z : Uses) (h : a ≠ []) : (a ++ z).headD 0 = a.headD 0 := by
  cases a with
  | nil => exact absurd rfl h
  | cons => rfl

public theorem ne_nil_of_length_succ {a : Uses} {n : Nat} (h : a.length = n + 1) : a ≠ [] := by
  intro e; subst e; simp at h

end Obend.Core.Proofs.Substitution
