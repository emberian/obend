module
/- Typed open substitution (lane Sound, pass 3, 2026-11-01).

`t.substitute σ`, where `σ` puts `A` at index `d` of the context, checks in the context with `d`
erased, at the same type, when `A` checks at the binder's type and uses its hypotheses as an argument
passed to that binder may (`argumentAllowed`'s quantity clauses). The uses of the result are
pointwise at most `Image d ua u` (what `subst_counts` counts), and equal to it at every `linear`
position. Inner binders stay safe under a budget: `Image` of the whole term's uses is safe in the
shrunk context, which the redex supplies. -/
public import Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Check

namespace Obend.Core.Proofs.SubjectReduction
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences fieldOccurrences armOccurrences uses_determined)
set_option autoImplicit false

/-! ### Pointwise readings of the usage predicates -/

theorem zip_all_iff (f : Binding → Nat → Bool) : ∀ (Γ : Context) (u : Uses), u.length = Γ.length →
    ((Γ.zip u).all (fun p => f p.1 p.2) = true ↔ ∀ j b, Γ[j]? = some b → f b (u.getD j 0) = true)
  | [], [], _ => by simp
  | b :: Γ, c :: u, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    rw [zip_all_iff f Γ u (by simpa using h)]
    constructor
    · rintro ⟨h0, hr⟩ j b' hj
      cases j with
      | zero => simp at hj; subst hj; simpa using h0
      | succ j => simpa using hr j b' (by simpa using hj)
    · intro H
      exact ⟨by simpa using H 0 b rfl, fun j b' hj => by simpa using H (j + 1) b' (by simpa using hj)⟩
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem linearFree_iff {Γ : Context} {u : Uses} (hl : u.length = Γ.length) :
    linearFree Γ u = true ↔ ∀ j b, Γ[j]? = some b → u.getD j 0 = 0 ∨ b.quantity ≠ .linear := by
  unfold linearFree
  rw [zip_all_iff (fun b n => n == 0 || b.quantity != .linear) Γ u hl]
  simp

theorem captures_iff {V : List Nat} {Γ : Context} {u : Uses} :
    reusableCaptures V Γ u = true ↔ u.length = Γ.length ∧ ∀ j b, Γ[j]? = some b →
      u.getD j 0 = 0 ∨ (b.quantity = .unrestricted ∧ b.type.shareableUnder V = true) := by
  unfold reusableCaptures
  rw [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hl, h⟩
    exact ⟨hl, by
      have := (zip_all_iff (fun b n => n == 0 || (b.quantity == .unrestricted && b.type.shareableUnder V)) Γ u hl).mp h
      simpa using this⟩
  · rintro ⟨hl, h⟩
    exact ⟨hl, (zip_all_iff (fun b n => n == 0 || (b.quantity == .unrestricted && b.type.shareableUnder V)) Γ u hl).mpr
      (by simpa using h)⟩

theorem safeUses_iff {Γ : Context} {u : Uses} :
    safeUses Γ u = true ↔ u.length = Γ.length ∧ ∀ j b, Γ[j]? = some b → safeQuantity b.quantity (u.getD j 0) = true := by
  unfold safeUses
  rw [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hl, h⟩
    exact ⟨hl, (zip_all_iff (fun b n => safeQuantity b.quantity n) Γ u hl).mp h⟩
  · rintro ⟨hl, h⟩
    exact ⟨hl, (zip_all_iff (fun b n => safeQuantity b.quantity n) Γ u hl).mpr h⟩

theorem branchesAgree_of : ∀ {Γ : Context} {x y : Uses},
    (∀ j, LinearAt Γ j → x.getD j 0 = y.getD j 0) → branchesAgree Γ x y = true
  | [], _, _, _ => by simp [branchesAgree]
  | _ :: _, [], _, _ => by simp [branchesAgree]
  | _ :: _, _ :: _, [], _ => by simp [branchesAgree]
  | b :: Γ, p :: x, q :: y, h => by
    simp only [branchesAgree, Bool.and_eq_true]
    refine ⟨?_, branchesAgree_of fun j lin => by simpa using h (j + 1) (linearAt_cons.mpr lin)⟩
    by_cases lq : b.quantity = .linear
    · have := h 0 ⟨b, rfl, lq⟩
      simp at this; simp [Quantity.agrees, lq, this]
    · cases hq : b.quantity <;> simp_all [Quantity.agrees]

theorem safeQuantity_mono {q : Quantity} {m n : Nat} (h : safeQuantity q n = true) (le : m ≤ n) :
    safeQuantity q m = true := by
  cases q <;> simp [safeQuantity] at h ⊢ <;> omega

theorem fits_transport {q : Quantity} {m n : Nat} (h : q.fits n = true) (le : m ≤ n)
    (lin : q = .linear → m = n) : q.fits m = true := by
  cases q
  · simp [Quantity.fits] at h ⊢; omega
  · simp [Quantity.fits] at h ⊢; omega
  · rw [lin rfl]; exact h
  · rfl

theorem headD_getD (x : Uses) : x.headD 0 = x.getD 0 0 := by cases x <;> rfl

theorem getD_of_length_le {x : Uses} {j : Nat} (h : x.length ≤ j) : x.getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem validContext_eraseIdx {V : List Nat} {Γ : Context} (h : validContext V Γ = true) (d : Nat) :
    validContext V (Γ.eraseIdx d) = true := by
  unfold validContext at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro b hb
  exact h b (List.mem_of_mem_eraseIdx hb)

/-! ### Images, ordered -/

theorem image_mono {d : Nat} {ua x y : Uses} (h : ∀ i, x.getD i 0 ≤ y.getD i 0) (j : Nat) :
    Image d ua x j ≤ Image d ua y j := by
  unfold Image
  have h1 := h (skipAt d j)
  have h2 := Nat.mul_le_mul_right (ua.getD j 0) (h d)
  omega

theorem add_le_left {x y : Uses} (h : x.length = y.length) (i : Nat) : x.getD i 0 ≤ (addUses x y).getD i 0 :=
  (le_getD_of_add h i).1

theorem add_le_right {x y : Uses} (h : x.length = y.length) (i : Nat) : y.getD i 0 ≤ (addUses x y).getD i 0 :=
  (le_getD_of_add h i).2

theorem join_le_left {x y : Uses} (h : x.length = y.length) (i : Nat) : x.getD i 0 ≤ (joinUses x y).getD i 0 := by
  rw [getD_joinUses h]; omega

theorem join_le_right {x y : Uses} (h : x.length = y.length) (i : Nat) : y.getD i 0 ≤ (joinUses x y).getD i 0 := by
  rw [getD_joinUses h]; omega

theorem add_image_le {d : Nat} {ua x y x' y' : Uses} (hxy : x.length = y.length) (hxy' : x'.length = y'.length)
    (hx : ∀ j, x'.getD j 0 ≤ Image d ua x j) (hy : ∀ j, y'.getD j 0 ≤ Image d ua y j) (j : Nat) :
    (addUses x' y').getD j 0 ≤ Image d ua (addUses x y) j := by
  rw [getD_addUses hxy', image_add hxy]; have := hx j; have := hy j; omega

theorem join_image_le {d : Nat} {ua x y x' y' : Uses} (hxy : x.length = y.length) (hxy' : x'.length = y'.length)
    (hx : ∀ j, x'.getD j 0 ≤ Image d ua x j) (hy : ∀ j, y'.getD j 0 ≤ Image d ua y j) (j : Nat) :
    (joinUses x' y').getD j 0 ≤ Image d ua (joinUses x y) j := by
  rw [getD_joinUses hxy']
  have := Nat.le_trans (hx j) (image_mono (join_le_left hxy) j)
  have := Nat.le_trans (hy j) (image_mono (join_le_right hxy) j)
  omega

theorem image_zero_lift {d : Nat} {ua x : Uses} : Image (d + 1) (0 :: ua) x 0 = x.getD 0 0 := by
  simp [Image, skipAt]


/-! ### The typed substitution's data -/

/-- `σ` puts `A` at `d`; `A` checks at the binder's type in the shrunk context; and `A` uses its
hypotheses as an argument passed to the binder may: no `linear` one unless the binder is `linear`,
only reusable ones if it is `unrestricted`. -/
structure TSub (a : Assumptions) (Γ : Context) (d : Nat) (σ : Nat → Term) (A : Term) (ua : Uses) : Prop where
  subst : SubstAt σ d A
  binding : ∃ b, Γ[d]? = some b ∧ PartialTyping a (Γ.eraseIdx d) A b.type ua ∧
    (b.quantity = .linear ∨ linearFree (Γ.eraseIdx d) ua = true) ∧
    (b.quantity = .unrestricted → reusableCaptures a.shareableVariables (Γ.eraseIdx d) ua = true)

theorem TSub.sub {a : Assumptions} {Γ : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua : Uses}
    (S : TSub a Γ d σ A ua) : Sub a Γ d σ A ua := by
  obtain ⟨b, hb, hA, hl, _⟩ := S.binding
  exact ⟨⟨b, hb, hl⟩, S.subst, ⟨_, hA⟩⟩

theorem TSub.ua_length {a : Assumptions} {Γ : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua : Uses}
    (S : TSub a Γ d σ A ua) : ua.length = (Γ.eraseIdx d).length := by
  obtain ⟨b, hb, hA, _, _⟩ := S.binding
  exact source_uses_length hA

theorem TSub.lift {a : Assumptions} {Γ : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua : Uses}
    (S : TSub a Γ d σ A ua) (x : Binding) (valid : validContext a.shareableVariables [x] = true) :
    TSub a (x :: Γ) (d + 1) (liftSubstitution σ) (A.rename Nat.succ) (0 :: ua) := by
  have len := S.ua_length
  obtain ⟨b, hb, hA, hl, hu⟩ := S.binding
  refine ⟨substAt_lift S.subst, b, by simpa using hb, ?_, ?_, ?_⟩
  · simpa using Obend.Core.Proofs.Preservation.source_weaken hA x valid
  · rcases hl with q | free
    · exact .inl q
    · right; simpa [linearFree] using free
  · intro q
    have := hu q
    simp only [List.eraseIdx_cons_succ]
    simp only [reusableCaptures, Bool.and_eq_true, beq_iff_eq] at this ⊢
    simpa [List.zip_cons_cons, List.all_cons] using this

/-- What the substituted term may use: `Image` of the term's uses is safe in the shrunk context. -/
@[expose] def Budget (Γ : Context) (d : Nat) (ua u : Uses) : Prop :=
  ∀ j b, (Γ.eraseIdx d)[j]? = some b → safeQuantity b.quantity (Image d ua u j) = true

theorem budget_mono {Γ : Context} {d : Nat} {ua x y : Uses} (h : ∀ i, x.getD i 0 ≤ y.getD i 0)
    (budget : Budget Γ d ua y) : Budget Γ d ua x :=
  fun j b hb => safeQuantity_mono (budget j b hb) (image_mono h j)

theorem budget_lift {Γ : Context} {x : Binding} {d : Nat} {ua ub : Uses} (budget : Budget Γ d ua ub.tail)
    (safe : safeUses (x :: Γ) ub = true) : Budget (x :: Γ) (d + 1) (0 :: ua) ub := by
  intro j b hb
  simp only [List.eraseIdx_cons_succ] at hb
  cases j with
  | zero =>
    simp at hb; subst hb
    rw [image_zero_lift]
    exact (safeUses_iff.mp safe).2 0 _ rfl
  | succ j =>
    rw [image_tail]
    exact budget j b (by simpa using hb)

theorem safe_of_budget {Γ : Context} {d : Nat} {ua u u' : Uses} (budget : Budget Γ d ua u)
    (len : u'.length = (Γ.eraseIdx d).length) (le : ∀ j, u'.getD j 0 ≤ Image d ua u j) :
    safeUses (Γ.eraseIdx d) u' = true :=
  safeUses_iff.mpr ⟨len, fun j b hb => safeQuantity_mono (budget j b hb) (le j)⟩

/-! ### Premises transported through the substitution -/

section transport
variable {a : Assumptions} {Γ : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua u u' : Uses}

theorem image_linear_zero (S : TSub a Γ d σ A ua) (free : linearFree Γ u = true) {j : Nat}
    (lin : LinearAt (Γ.eraseIdx d) j) : Image d ua u j = 0 := by
  obtain ⟨b, hb, _, hl, _⟩ := S.binding
  unfold Image
  rw [linearFree_getD free (linearAt_skip lin)]
  rcases hl with q | freeA
  · rw [linearFree_getD free ⟨b, hb, q⟩]; simp
  · rw [linearFree_getD freeA lin]; simp

theorem linearFree_transport (S : TSub a Γ d σ A ua) (free : linearFree Γ u = true)
    (len : u'.length = (Γ.eraseIdx d).length) (le : ∀ j, u'.getD j 0 ≤ Image d ua u j) :
    linearFree (Γ.eraseIdx d) u' = true := by
  rw [linearFree_iff len]
  intro j b hb
  by_cases q : b.quantity = .linear
  · left; have := le j; rw [image_linear_zero S free ⟨b, hb, q⟩] at this; omega
  · exact .inr q

theorem captures_transport (S : TSub a Γ d σ A ua) (captures : reusableCaptures a.shareableVariables Γ u = true)
    (len : u'.length = (Γ.eraseIdx d).length) (le : ∀ j, u'.getD j 0 ≤ Image d ua u j) :
    reusableCaptures a.shareableVariables (Γ.eraseIdx d) u' = true := by
  obtain ⟨b0, hb0, _, _, hu⟩ := S.binding
  obtain ⟨_, hc⟩ := captures_iff.mp captures
  refine captures_iff.mpr ⟨len, fun j b hb => ?_⟩
  by_cases z : u'.getD j 0 = 0
  · exact .inl z
  · right
    have pos := le j
    unfold Image at pos
    by_cases hs : u.getD (skipAt d j) 0 = 0
    · rw [hs, Nat.zero_add] at pos
      have hd : u.getD d 0 ≠ 0 := fun e => by rw [e, Nat.zero_mul] at pos; omega
      have ha : ua.getD j 0 ≠ 0 := fun e => by rw [e, Nat.mul_zero] at pos; omega
      rcases hc d b0 hb0 with e | ⟨q, _⟩
      · exact absurd e hd
      · rcases (captures_iff.mp (hu q)).2 j b hb with e | r
        · exact absurd e ha
        · exact r
    · rcases hc (skipAt d j) b (by rw [← eraseIdx_getElem?]; exact hb) with e | r
      · exact absurd e hs
      · exact r

theorem argumentAllowed_transport (S : TSub a Γ d σ A ua) {q : Quantity} {X : Ty}
    (hu : u.length = Γ.length) (len : u'.length = (Γ.eraseIdx d).length) (le : ∀ j, u'.getD j 0 ≤ Image d ua u j)
    (allowed : argumentAllowed a q Γ X u = true) : argumentAllowed a q (Γ.eraseIdx d) X u' = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    beq_iff_eq] at allowed ⊢
  obtain ⟨⟨pure, lin⟩, unr⟩ := allowed
  refine ⟨⟨pure, ?_⟩, ?_⟩
  · rcases lin with l | free
    · exact .inl l
    · exact .inr (linearFree_transport S free len le)
  · rcases unr with n | ⟨share, cap⟩
    · exact .inl n
    · exact .inr ⟨share, captures_transport S cap len le⟩

theorem caseAllowed_transport (S : TSub a Γ d σ A ua) {q : Quantity}
    (len : u'.length = (Γ.eraseIdx d).length) (le : ∀ j, u'.getD j 0 ≤ Image d ua u j)
    (allowed : caseAllowed a q Γ u = true) : caseAllowed a q (Γ.eraseIdx d) u' = true := by
  simp only [caseAllowed, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at allowed ⊢
  obtain ⟨lin, unr⟩ := allowed
  refine ⟨?_, ?_⟩
  · rcases lin with l | free
    · exact .inl l
    · exact .inr (linearFree_transport S free len le)
  · rcases unr with n | cap
    · exact .inl n
    · exact .inr (captures_transport S cap len le)

theorem reusableAllowed_transport (S : TSub a Γ d σ A ua) {r : Reuse}
    (len : u'.length = (Γ.eraseIdx d).length) (le : ∀ j, u'.getD j 0 ≤ Image d ua u j)
    (allowed : reusableAllowed a r Γ u = true) : reusableAllowed a r (Γ.eraseIdx d) u' = true := by
  simp only [reusableAllowed, Bool.or_eq_true, bne_iff_ne, ne_eq] at allowed ⊢
  rcases allowed with n | cap
  · exact .inl n
  · exact .inr (captures_transport S cap len le)

/-- Two branches that agree before the substitution agree after it. -/
theorem agree_transport (S : TSub a Γ d σ A ua) {x y x' y' : Uses}
    (hx : x.length = Γ.length) (hy : y.length = Γ.length) (agree : branchesAgree Γ x y = true)
    (ex : ∀ j, LinearAt (Γ.eraseIdx d) j → x'.getD j 0 = Image d ua x j)
    (ey : ∀ j, LinearAt (Γ.eraseIdx d) j → y'.getD j 0 = Image d ua y j) :
    branchesAgree (Γ.eraseIdx d) x' y' = true := by
  refine branchesAgree_of fun j lin => ?_
  rw [ex j lin, ey j lin]
  obtain ⟨b, hb, _, hl, _⟩ := S.binding
  have hs := branchesAgree_getD agree hx hy (linearAt_skip lin)
  unfold Image
  rw [hs]
  rcases hl with q | free
  · rw [branchesAgree_getD agree hx hy ⟨b, hb, q⟩]
  · rw [linearFree_getD free lin]; simp

end transport

/-- The uses of a substituted derivation, at a `linear` position, are its image (`subst_counts`). -/
theorem lin_eq {a : Assumptions} {Γ : Context} {t : Term} {T T' : Ty} {u u' : Uses} {d : Nat} {σ : Nat → Term}
    {A : Term} {ua : Uses} (old : PartialTyping a Γ t T u)
    (new : PartialTyping a (Γ.eraseIdx d) (t.substitute σ) T' u') (S : Sub a Γ d σ A ua) :
    ∀ j, LinearAt (Γ.eraseIdx d) j → u'.getD j 0 = Image d ua u j := by
  intro j lin; rw [uses_determined new]; exact subst_counts old d σ A ua S j lin


/-- `image_bound` at every position of the shrunk context. -/
theorem image_bound_at {a : Assumptions} {context : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua : Uses}
    (S : Sub a context d σ A ua) {k : Nat} (hk : k < context.length) {j : Nat}
    (hj : j < (context.eraseIdx d).length) :
    (occurrences (context.eraseIdx d).length (σ k)).getD j 0 = Image d ua (variableUses context k) j := by
  obtain ⟨b, hb, _⟩ := S.binding
  obtain ⟨TA, hA⟩ := S.arg
  have hd : d < context.length := (List.getElem?_eq_some_iff.mp hb).1
  have len : (context.eraseIdx d).length = context.length - 1 := by simp [List.length_eraseIdx, hd]
  have hsk : skipAt d j < context.length := by unfold skipAt; split <;> omega
  simp only [Image, getD_variableUses, S.subst k]
  by_cases lt : k < d
  · have z : ¬ (d < context.length ∧ d = k) := by omega
    rw [if_pos lt, getD_occurrences_bound, if_neg z, Nat.zero_mul, Nat.add_zero]
    exact ind_eq (by unfold skipAt; constructor <;> intro h <;> split at * <;> omega)
  · by_cases eq : k = d
    · subst eq
      have z : ¬ (skipAt k j < context.length ∧ skipAt k j = k) := by unfold skipAt; split <;> omega
      rw [if_neg lt, if_pos rfl, if_neg z, if_pos ⟨hd, rfl⟩, Nat.zero_add, Nat.one_mul, ← uses_determined hA]
    · have z : ¬ (d < context.length ∧ d = k) := by omega
      rw [if_neg lt, if_neg eq, getD_occurrences_bound, if_neg z, Nat.zero_mul, Nat.add_zero]
      exact ind_eq (by unfold skipAt; constructor <;> intro h <;> split at * <;> omega)

/-- A variable, substituted. -/
theorem bound_subst {a : Assumptions} {Γ : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua : Uses}
    (S : TSub a Γ d σ A ua) {k : Nat} {binding : Binding} (found : Γ[k]? = some binding) :
    ∃ u', PartialTyping a (Γ.eraseIdx d) (σ k) binding.type u' ∧ ∀ j, u'.getD j 0 ≤ Image d ua (variableUses Γ k) j := by
  have hk : k < Γ.length := (List.getElem?_eq_some_iff.mp found).1
  have typed : ∃ u', PartialTyping a (Γ.eraseIdx d) (σ k) binding.type u' := by
    obtain ⟨b, hb, hA, _, _⟩ := S.binding
    rw [S.subst k]
    by_cases lt : k < d
    · rw [if_pos lt]
      exact ⟨_, .bound (by rw [eraseIdx_getElem?]; simpa [skipAt, lt] using found)⟩
    · by_cases eq : k = d
      · subst eq
        rw [if_neg lt, if_pos rfl]
        rw [found] at hb; cases hb
        exact ⟨_, hA⟩
      · rw [if_neg lt, if_neg eq]
        exact ⟨_, .bound (by
          rw [eraseIdx_getElem?]
          have : skipAt d (k - 1) = k := by unfold skipAt; split <;> omega
          rw [this]; exact found)⟩
  obtain ⟨u', h⟩ := typed
  refine ⟨u', h, fun j => ?_⟩
  rw [uses_determined h]
  by_cases hj : j < (Γ.eraseIdx d).length
  · exact Nat.le_of_eq (image_bound_at S.sub hk hj)
  · rw [getD_of_length_le (by rw [occurrences_length]; omega)]; exact Nat.zero_le _


/-- **Typed open substitution.** -/
theorem subst_typed {a : Assumptions} {Γ : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) :
    ∀ d σ A ua, TSub a Γ d σ A ua → Budget Γ d ua u →
      ∃ u', PartialTyping a (Γ.eraseIdx d) (t.substitute σ) T u' ∧ ∀ j, u'.getD j 0 ≤ Image d ua u j := by
  apply PartialTyping.rec
    (motive_1 := fun Γ t T u _ => ∀ d σ A ua, TSub a Γ d σ A ua → Budget Γ d ua u →
      ∃ u', PartialTyping a (Γ.eraseIdx d) (t.substitute σ) T u' ∧ ∀ j, u'.getD j 0 ≤ Image d ua u j)
    (motive_2 := fun Γ fields row u _ => ∀ d σ A ua, TSub a Γ d σ A ua → Budget Γ d ua u →
      ∃ u', FieldsTyping a (Γ.eraseIdx d) (fields.map fun field => (field.1, field.2.substitute σ)) row u' ∧
        ∀ j, u'.getD j 0 ≤ Image d ua u j)
    (motive_3 := fun Γ q arms row result u _ => ∀ d σ A ua, TSub a Γ d σ A ua → Budget Γ d ua u →
      ∃ u', ArmsTyping a (Γ.eraseIdx d) q
          (arms.map fun field => (field.1, field.2.substitute (liftSubstitution σ))) row result u' ∧
        (∀ j, u'.getD j 0 ≤ Image d ua u j) ∧ ∀ j, LinearAt (Γ.eraseIdx d) j → u'.getD j 0 = Image d ua u j)
    (t := typed)
  case bound =>
    intro Γ index binding found d σ A ua S budget
    simp only [Term.substitute]
    exact bound_subst S found
  case natural =>
    intro Γ value d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨_, .natural _ value, fun j => by rw [getD_zeroUses]; exact Nat.zero_le _⟩
  case boolean =>
    intro Γ value d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨_, .boolean _ value, fun j => by rw [getD_zeroUses]; exact Nat.zero_le _⟩
  case label =>
    intro Γ value d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨_, .label _ value, fun j => by rw [getD_zeroUses]; exact Nat.zero_le _⟩
  case lambda =>
    intro Γ body ann uses bodyTyped safe valid captures fits ih d σ A ua S budget
    have vx : validContext a.shareableVariables [⟨ann.domain, ann.parameter⟩] = true := by
      simp only [validContext, List.all_cons, List.all_nil, Bool.and_true] at valid ⊢
      exact (Bool.and_eq_true_iff.mp valid).1
    have S' := S.lift _ vx
    have B' := budget_lift budget safe
    obtain ⟨ub', hb', le⟩ := ih (d + 1) _ _ _ S' B'
    have e0 := lin_eq bodyTyped hb' S'.sub
    have sb := safe_of_budget B' (source_uses_length hb') le
    have vb := validContext_eraseIdx valid (d + 1)
    simp only [List.eraseIdx_cons_succ] at hb' e0 sb vb
    have bl := source_uses_length hb'
    have tl : ub'.tail.length = (Γ.eraseIdx d).length := by simp [bl]
    have tle : ∀ j, ub'.tail.getD j 0 ≤ Image d ua uses.tail j := fun j => by
      rw [getD_tail, ← image_tail]; exact le (j + 1)
    simp only [Term.substitute]
    refine ⟨ub'.tail, .lambda hb' sb vb (reusableAllowed_transport S tl tle captures) ?_, tle⟩
    rw [headD_getD] at fits ⊢
    refine fits_transport fits (by have := le 0; rwa [image_zero_lift] at this) (fun q => ?_)
    have := e0 0 ⟨_, rfl, q⟩
    rwa [image_zero_lift] at this
  case conversion =>
    intro Γ term actual expected uses prior agreement ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    exact ⟨u', .conversion h agreement, le⟩
  case application =>
    intro Γ fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped
      callableEq same allowed ihFn ihArg d σ A ua S budget
    have l := (source_uses_length fnTyped).trans (source_uses_length argTyped).symm
    obtain ⟨fu', hf, lef⟩ := ihFn d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨au', ha, lea⟩ := ihArg d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .application hf ha callableEq same
      (argumentAllowed_transport S (source_uses_length argTyped) (source_uses_length ha) lea allowed),
      add_image_le l ((source_uses_length hf).trans (source_uses_length ha).symm) lef lea⟩
  case record =>
    intro Γ fields row uses fieldsTyped ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .record h, le⟩
  case get =>
    intro Γ target targetType member uses name fuel targetTyped lookup free ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .get h lookup (linearFree_transport S free (source_uses_length h) le), le⟩
  case extend =>
    intro Γ target fields targetType row tu fu rowFuel targetTyped fieldsTyped isRow free ihTarget ihFields
      d σ A ua S budget
    have l := (source_uses_length targetTyped).trans (source_uses_length (PartialTyping.record fieldsTyped)).symm
    obtain ⟨tu', ht, let'⟩ := ihTarget d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨fu', hfs, lef⟩ := ihFields d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .extend ht hfs isRow (linearFree_transport S free (source_uses_length ht) let'),
      add_image_le l ((source_uses_length ht).trans (source_uses_length (PartialTyping.record hfs)).symm) let' lef⟩
  case specification =>
    intro Γ metadata extension metadataType extensionType mu eu metadataTyped extensionTyped mPure ePure free
      ihM ihE d σ A ua S budget
    have l := (source_uses_length metadataTyped).trans (source_uses_length extensionTyped).symm
    obtain ⟨mu', hm, lem⟩ := ihM d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨eu', he, lee⟩ := ihE d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .specification hm he mPure ePure (linearFree_transport S free (source_uses_length hm) lem),
      add_image_le l ((source_uses_length hm).trans (source_uses_length he).symm) lem lee⟩
  case prototype =>
    intro Γ spec target specType targetType su tu specTyped targetTyped sPure tPure ihS ihT d σ A ua S budget
    have l := (source_uses_length specTyped).trans (source_uses_length targetTyped).symm
    obtain ⟨su', hs, les⟩ := ihS d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨tu', ht, let'⟩ := ihT d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .prototype hs ht sPure tPure,
      add_image_le l ((source_uses_length hs).trans (source_uses_length ht).symm) les let'⟩
  case reflect =>
    intro Γ target specType targetType uses prior free ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .reflect h (linearFree_transport S free (source_uses_length h) le), le⟩
  case metadata =>
    intro Γ target metadataType extensionType uses prior free ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .metadata h (linearFree_transport S free (source_uses_length h) le), le⟩
  case project =>
    intro Γ target specType targetType uses prior free ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .project h (linearFree_transport S free (source_uses_length h) le), le⟩
  case mix =>
    intro Γ lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped
      lowerCallable upperCallable captures selfShare inheritedShare middleShare ihL ihU d σ A ua S budget
    have l := (source_uses_length lowerTyped).trans (source_uses_length upperTyped).symm
    obtain ⟨lu', hl, lel⟩ := ihL d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨uu', hu, leu⟩ := ihU d σ A ua S (budget_mono (add_le_right l) budget)
    have l' := (source_uses_length hl).trans (source_uses_length hu).symm
    have le := add_image_le l l' lel leu
    simp only [Term.substitute]
    exact ⟨_, .mix hl hu lowerCallable upperCallable
      (captures_transport S captures (by simp [addUses, source_uses_length hl, source_uses_length hu]) le)
      selfShare inheritedShare middleShare, le⟩
  case fix =>
    intro Γ spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare
      inheritedAllowed captures ihS ihI d σ A ua S budget
    have l := (source_uses_length specTyped).trans (source_uses_length inheritedTyped).symm
    obtain ⟨su', hs, les⟩ := ihS d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨iu', hi, lei⟩ := ihI d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .fix hs callableEq hi targetShare
      (argumentAllowed_transport S (source_uses_length inheritedTyped) (source_uses_length hi) lei inheritedAllowed)
      (captures_transport S captures (source_uses_length hs) les),
      add_image_le l ((source_uses_length hs).trans (source_uses_length hi).symm) les lei⟩
  case binary =>
    intro Γ primitive left right input output lu ru primitiveEq leftTyped rightTyped ihL ihR d σ A ua S budget
    have l := (source_uses_length leftTyped).trans (source_uses_length rightTyped).symm
    obtain ⟨lu', hl, lel⟩ := ihL d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨ru', hr, ler⟩ := ihR d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .binary primitiveEq hl hr,
      add_image_le l ((source_uses_length hl).trans (source_uses_length hr).symm) lel ler⟩
  case ifZero =>
    intro Γ value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe agreeing
      ihV ihZ ihS d σ A ua S budget
    have zl := source_uses_length zeroTyped
    have sl : su.tail.length = Γ.length := by simp [source_uses_length successorTyped]
    have jl : vu.length = (joinUses zu su.tail).length := by
      simp [joinUses, source_uses_length valueTyped, zl, sl]
    have vx : validContext a.shareableVariables [⟨.natural, .unrestricted⟩] = true := by
      simp [validContext, Ty.shareableUnder, Ty.shareable]
    have bj := budget_mono (add_le_right jl) budget
    obtain ⟨vu', hv, lev⟩ := ihV d σ A ua S (budget_mono (add_le_left jl) budget)
    obtain ⟨zu', hz, lez⟩ := ihZ d σ A ua S (budget_mono (join_le_left (zl.trans sl.symm)) bj)
    have S' := S.lift _ vx
    have B' := budget_lift (budget_mono (join_le_right (zl.trans sl.symm)) bj) successorSafe
    obtain ⟨su', hs, les⟩ := ihS (d + 1) _ _ _ S' B'
    have es := lin_eq successorTyped hs S'.sub
    have ss := safe_of_budget B' (source_uses_length hs) les
    simp only [List.eraseIdx_cons_succ] at hs es ss
    have stl : ∀ j, su'.tail.getD j 0 ≤ Image d ua su.tail j := fun j => by
      rw [getD_tail, ← image_tail]; exact les (j + 1)
    have ste : ∀ j, LinearAt (Γ.eraseIdx d) j → su'.tail.getD j 0 = Image d ua su.tail j := fun j lin => by
      rw [getD_tail, ← image_tail]; exact es (j + 1) (linearAt_cons.mpr lin)
    have zl' := source_uses_length hz
    have sl' : su'.tail.length = (Γ.eraseIdx d).length := by simp [source_uses_length hs]
    simp only [Term.substitute]
    exact ⟨_, .ifZero hv hz hs ss (agree_transport S zl sl agreeing (lin_eq zeroTyped hz S.sub) ste),
      add_image_le jl (by simp [joinUses, source_uses_length hv, zl', sl']) lev
        (join_image_le (zl.trans sl.symm) (zl'.trans sl'.symm) lez stl)⟩
  case inject =>
    intro Γ tag payload payloadType row uses fuel payloadTyped lookup pure ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .inject h lookup pure, le⟩
  case case =>
    intro Γ scrutinee arms row result su au q scrutineeTyped armsTyped distinct allowed ihS ihA d σ A ua S budget
    have l := (source_uses_length scrutineeTyped).trans (Obend.Core.Proofs.Preservation.arms_uses_length armsTyped).symm
    obtain ⟨su', hs, les⟩ := ihS d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨au', ha, lea, _⟩ := ihA d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .case hs ha (by simpa using distinct) (caseAllowed_transport S (source_uses_length hs) les allowed),
      add_image_le l ((source_uses_length hs).trans (Obend.Core.Proofs.Preservation.arms_uses_length ha).symm) les lea⟩
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped agreeing
      ihC ihT ihF d σ A ua S budget
    have tl := source_uses_length trueTyped
    have fl := source_uses_length falseTyped
    have jl : cu.length = (joinUses tu fu).length := by
      simp [joinUses, source_uses_length conditionTyped, tl, fl]
    have bj := budget_mono (add_le_right jl) budget
    obtain ⟨cu', hc, lec⟩ := ihC d σ A ua S (budget_mono (add_le_left jl) budget)
    obtain ⟨tu', ht, let'⟩ := ihT d σ A ua S (budget_mono (join_le_left (tl.trans fl.symm)) bj)
    obtain ⟨fu', hf, lef⟩ := ihF d σ A ua S (budget_mono (join_le_right (tl.trans fl.symm)) bj)
    have tl' := source_uses_length ht
    have fl' := source_uses_length hf
    simp only [Term.substitute]
    exact ⟨_, .ifBool hc ht hf (agree_transport S tl fl agreeing (lin_eq trueTyped ht S.sub) (lin_eq falseTyped hf S.sub)),
      add_image_le jl (by simp [joinUses, source_uses_length hc, tl', fl']) lec
        (join_image_le (tl.trans fl.symm) (tl'.trans fl'.symm) let' lef)⟩
  case perform =>
    intro Γ plan planType response uses planTyped isPlan isData ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .perform h isPlan isData, le⟩
  case done =>
    intro Γ value planType response result uses valueTyped pure ih d σ A ua S budget
    obtain ⟨u', h, le⟩ := ih d σ A ua S budget
    simp only [Term.substitute]
    exact ⟨u', .done h pure, le⟩
  case effectCase =>
    intro Γ scrutinee arms planType response row result su au q scrutineeTyped armsTyped pure distinct allowed
      ihS ihA d σ A ua S budget
    have l := (source_uses_length scrutineeTyped).trans (Obend.Core.Proofs.Preservation.arms_uses_length armsTyped).symm
    obtain ⟨su', hs, les⟩ := ihS d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨au', ha, lea, _⟩ := ihA d σ A ua S (budget_mono (add_le_right l) budget)
    simp only [Term.substitute]
    exact ⟨_, .effectCase hs ha pure (by simpa using distinct) (caseAllowed_transport S (source_uses_length hs) les allowed),
      add_image_le l ((source_uses_length hs).trans (Obend.Core.Proofs.Preservation.arms_uses_length ha).symm) les lea⟩
  case nil =>
    intro Γ d σ A ua S budget
    exact ⟨_, .nil _, fun j => by rw [getD_zeroUses]; exact Nat.zero_le _⟩
  case cons =>
    intro Γ name body rest type row bu ru bodyTyped restTyped pure ihBody ihRest d σ A ua S budget
    have l := (source_uses_length bodyTyped).trans (source_uses_length (PartialTyping.record restTyped)).symm
    obtain ⟨bu', hb, leb⟩ := ihBody d σ A ua S (budget_mono (add_le_left l) budget)
    obtain ⟨ru', hr, ler⟩ := ihRest d σ A ua S (budget_mono (add_le_right l) budget)
    exact ⟨_, .cons hb hr pure,
      add_image_le l ((source_uses_length hb).trans (source_uses_length (PartialTyping.record hr)).symm) leb ler⟩
  case nil =>
    intro Γ q result d σ A ua S budget
    refine ⟨_, .nil _ q result, fun j => by rw [getD_zeroUses]; exact Nat.zero_le _, fun j _ => ?_⟩
    rw [getD_zeroUses, image_zero]
  case cons =>
    intro Γ q name body rest payload row result bu ru bodyTyped safe shareable fits restTyped agreeing
      ihBody ihRest d σ A ua S budget
    have bl : bu.tail.length = Γ.length := by simp [source_uses_length bodyTyped]
    have rl := Obend.Core.Proofs.Preservation.arms_uses_length restTyped
    have S' := S.lift _ shareable
    have B' := budget_lift (budget_mono (join_le_left (bl.trans rl.symm)) budget) safe
    obtain ⟨bu', hb, leb⟩ := ihBody (d + 1) _ _ _ S' B'
    have eb := lin_eq bodyTyped hb S'.sub
    have sb := safe_of_budget B' (source_uses_length hb) leb
    simp only [List.eraseIdx_cons_succ] at hb eb sb
    obtain ⟨ru', hr, ler, er⟩ := ihRest d σ A ua S (budget_mono (join_le_right (bl.trans rl.symm)) budget)
    have btl : ∀ j, bu'.tail.getD j 0 ≤ Image d ua bu.tail j := fun j => by
      rw [getD_tail, ← image_tail]; exact leb (j + 1)
    have bte : ∀ j, LinearAt (Γ.eraseIdx d) j → bu'.tail.getD j 0 = Image d ua bu.tail j := fun j lin => by
      rw [getD_tail, ← image_tail]; exact eb (j + 1) (linearAt_cons.mpr lin)
    have bl' : bu'.tail.length = (Γ.eraseIdx d).length := by simp [source_uses_length hb]
    have rl' := Obend.Core.Proofs.Preservation.arms_uses_length hr
    have fits' : q.fits (bu'.headD 0) = true := by
      rw [headD_getD] at fits ⊢
      refine fits_transport fits (by have := leb 0; rwa [image_zero_lift] at this) (fun lq => ?_)
      have := eb 0 ⟨_, rfl, lq⟩
      rwa [image_zero_lift] at this
    simp only [List.map_cons]
    refine ⟨_, .cons hb sb shareable fits' hr ?_, join_image_le (bl.trans rl.symm) (bl'.trans rl'.symm) btl ler, ?_⟩
    · cases rest with
      | nil => simp
      | cons first others =>
        simp only [List.isEmpty_cons, Bool.false_or] at agreeing ⊢
        exact agree_transport S bl rl agreeing bte er
    · intro j lin
      rw [getD_joinUses (bl'.trans rl'.symm), bte j lin, er j lin]
      cases rest with
      | nil =>
        cases restTyped
        rw [image_joinZero Γ bl, image_zero]; simp
      | cons first others =>
        simp only [List.isEmpty_cons, Bool.false_or] at agreeing
        rw [image_join S.sub bl rl agreeing lin]

end Obend.Core.Proofs.SubjectReduction
