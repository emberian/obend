module
/- Filling typed holes (2026-11-06).

A term checked with declared holes (`PartialTyping.hole`) is checked once. Each fill is then
discharged by `fill_typed`: fillers typed at their holes' declared types, in their declared contexts,
using each `linear` variable exactly once, give the filled term a derivation at the same type, using
no more than the holed term did at any position that is not `unrestricted`, and exactly as much at
every `linear` one. The hole case is the hole's arguments substituted into the filler one variable
at a time, each step the typed open substitution (`subst_typed`). -/
public import Obend.Core.Proofs.SubjectReduction
public import Obend.Core.Proofs.TypedSubstitution
public import Obend.Core.Fill
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Check
import all Obend.Core.Proofs.Preservation.Base.Reusable

namespace Obend.Core.Proofs.FillTyping
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation Obend.Core.Proofs.SubjectReduction
open Obend.Core.Proofs.BidirectionalCompleteness (uses_determined)
set_option autoImplicit false

/-! ### Counts -/

theorem fits_safe {q : Quantity} {n : Nat} (h : q.fits n = true) : safeQuantity q n = true := by
  cases q <;> simp [Quantity.fits, safeQuantity] at h ⊢ <;> omega

theorem zip_zero_prefix (P : Binding × Nat → Bool) (hP : ∀ b, P (b, 0) = true) (Δ Γ : Context) (u : Uses) :
    ((Δ ++ Γ).zip (zeroUses Δ ++ u)).all P = (Γ.zip u).all P := by
  rw [List.zip_append (by simp [zeroUses]), List.all_append]
  have : (Δ.zip (zeroUses Δ)).all P = true := by
    rw [List.all_eq_true]; intro x hx
    obtain ⟨b, n⟩ := x
    have hn := List.of_mem_zip hx
    have : n = 0 := by simp [zeroUses] at hn; exact hn.2.2
    subst this; exact hP b
  simp [this]

theorem linearFree_zero_prefix (Δ Γ : Context) (u : Uses) :
    linearFree (Δ ++ Γ) (zeroUses Δ ++ u) = linearFree Γ u := by
  unfold linearFree
  exact zip_zero_prefix _ (fun _ => by simp) Δ Γ u

theorem captures_zero_prefix (V : List Nat) (Δ Γ : Context) (u : Uses) (hu : u.length = Γ.length) :
    reusableCaptures V (Δ ++ Γ) (zeroUses Δ ++ u) = reusableCaptures V Γ u := by
  unfold reusableCaptures
  rw [zip_zero_prefix _ (fun _ => by simp) Δ Γ u]
  simp [zeroUses, hu]

theorem getD_append_left' {w v : Uses} {j : Nat} (h : j < w.length) : (w ++ v).getD j 0 = w.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {w v : Uses} {j : Nat} (h : w.length ≤ j) :
    (w ++ v).getD j 0 = v.getD (j - w.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-! ### Weakening by a prefix -/

theorem weaken_prefix {asm : Assumptions} {Γ : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping asm Γ t T u) :
    ∀ Δ : Context, validContext asm.shareableVariables Δ = true →
      PartialTyping asm (Δ ++ Γ) (t.rename (· + Δ.length)) T (zeroUses Δ ++ u)
  | [], _ => by
    have : t.rename (fun x => x) = t := TermTraverse.scoped_rename_identity t Γ.length
        ((Obend.Core.Invariant.scoped_encode_iff _ _).mp (source_scoped typed)) (fun x => x) (fun _ _ => rfl)
    simpa [zeroUses, this] using typed
  | b :: Δ, valid => by
    have vb : validContext asm.shareableVariables [b] = true := by
      simp only [validContext, List.all_cons, List.all_nil, Bool.and_true] at valid ⊢
      exact (Bool.and_eq_true_iff.mp valid).1
    have vΔ : validContext asm.shareableVariables Δ = true := by
      simp only [validContext, List.all_cons, Bool.and_eq_true] at valid ⊢; exact valid.2
    have w := Obend.Core.Proofs.Preservation.source_weaken (weaken_prefix typed Δ vΔ) b vb
    rw [TermTraverse.rename_comp] at w
    have e : (fun i => (i + Δ.length).succ) = (· + (b :: Δ).length) := by
      funext i; simp [Nat.succ_eq_add_one]; omega
    rw [e] at w
    simpa [zeroUses, List.replicate_succ] using w

/-! ### The arguments, put for the filler's variables one at a time -/

/-- `as[i]` for variable `i` of the arguments' context, the rest closing the gap. -/
@[expose] public def peelSubst (as : List Term) (i : Nat) : Term :=
  if h : i < as.length then as[i] else .bound (i - as.length)

theorem peelSubst_nil : peelSubst [] = Term.bound := by
  funext i; simp [peelSubst]

theorem peelSubst_cons {Γ : Context} (a : Term) (as : List Term) (ha : Invariant.Scoped Γ.length a) :
    peelSubst (a :: as) = fun i =>
      (match i with | 0 => a.rename (· + as.length) | n + 1 => Term.bound n).substitute (peelSubst as) := by
  funext i
  cases i with
  | zero =>
    simp only [peelSubst, List.length_cons, Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero]
    rw [TermTraverse.rename_substitute]
    symm
    apply TermTraverse.scoped_substitute_identity a Γ.length ((Invariant.scoped_encode_iff _ _).mp ha)
    intro j _
    simp [peelSubst, show ¬ (j + as.length < as.length) by omega]
  | succ n =>
    simp only [Term.substitute]
    simp only [peelSubst, List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]
    split <;> simp_all

/-- The hole's arguments `rest`, typed in `Γ`, put for the variables `rest.map (·.2.1)` that precede
`Γ` in `g`'s context, one at a time by the typed open substitution. -/
theorem peel_typed {asm : Assumptions} {Γ : Context} {A : Ty} :
    ∀ (rest : List (Term × Binding × Uses)) (g : Term) (w v : Uses),
      PartialTyping asm (rest.map (·.2.1) ++ Γ) g A (w ++ v) →
      w.length = rest.length → v.length = Γ.length →
      (∀ (j : Nat) (b : Binding), (rest.map (·.2.1))[j]? = some b → b.quantity.fits (w.getD j 0) = true) →
      validContext asm.shareableVariables (rest.map (·.2.1)) = true →
      (∀ arg ∈ rest, PartialTyping asm Γ arg.1 arg.2.1.type arg.2.2) →
      (∀ arg ∈ rest, argumentAllowed asm arg.2.1.quantity Γ arg.2.1.type arg.2.2 = true) →
      safeUses Γ (addUses v ((rest.map (·.2.2)).foldr addUses (zeroUses Γ))) = true →
      ∃ u', PartialTyping asm Γ (g.substitute (peelSubst (rest.map (·.1)))) A u' ∧
        Below Γ u' (addUses v ((rest.map (·.2.2)).foldr addUses (zeroUses Γ))) ∧
        ∀ j, LinearAt Γ j → u'.getD j 0 = (addUses v ((rest.map (·.2.2)).foldr addUses (zeroUses Γ))).getD j 0
  | [], g, w, v, typed, hw, hv, _, _, _, _, _ => by
    have : w = [] := List.eq_nil_of_length_eq_zero hw
    subst this
    simp only [List.map_nil, List.nil_append, List.foldr_nil] at typed ⊢
    rw [peelSubst_nil, Obend.Core.Proofs.Preservation.add_zero_uses Γ v hv]
    have hg : g.substitute Term.bound = g :=
      TermTraverse.scoped_substitute_identity g Γ.length
        ((Invariant.scoped_encode_iff _ _).mp (source_scoped typed)) _ (fun _ _ => rfl)
    rw [hg]
    exact ⟨v, typed, fun _ _ _ _ => Nat.le_refl _, fun _ _ => rfl⟩
  | (a0, b0, u0) :: rest, g, w, v, typed, hw, hv, fits, validΔ, typedArgs, allowedArgs, safe => by
    obtain ⟨w0, w', rfl⟩ : ∃ w0 w', w = w0 :: w' := by
      cases w with
      | nil => simp at hw
      | cons w0 w' => exact ⟨w0, w', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hw
    simp only [List.map_cons, List.cons_append, List.foldr_cons] at typed fits validΔ safe ⊢
    -- notation
    have ta0 := typedArgs (a0, b0, u0) List.mem_cons_self
    have al0 := allowedArgs (a0, b0, u0) List.mem_cons_self
    simp only at ta0 al0
    have lu0 : u0.length = Γ.length := source_uses_length ta0
    have lS' : ((rest.map (·.2.2)).foldr addUses (zeroUses Γ)).length = Γ.length :=
      length_foldr_addUses _ _ (by simp [zeroUses]) (fun u hu => by
        obtain ⟨arg, h, rfl⟩ := List.mem_map.mp hu
        exact source_uses_length (typedArgs arg (List.mem_cons_of_mem _ h)))
    have lk : (rest.map (·.2.1)).length = rest.length := List.length_map _
    have validΔ' : validContext asm.shareableVariables (rest.map (·.2.1)) = true := by
      simp only [validContext, List.all_cons, Bool.and_eq_true] at validΔ ⊢; exact validΔ.2
    have vb0 : validContext asm.shareableVariables [b0] = true := by
      simp only [validContext, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at validΔ ⊢
      exact validΔ.1
    have fits0 : b0.quantity.fits w0 = true := by simpa using fits 0 b0 rfl
    -- the argument, weakened past the variables still to come
    have hA0 : PartialTyping asm (rest.map (·.2.1) ++ Γ) (a0.rename (· + rest.length)) b0.type
        (zeroUses (rest.map (·.2.1)) ++ u0) := by
      have := weaken_prefix ta0 (rest.map (·.2.1)) validΔ'
      rwa [lk] at this
    obtain ⟨lin0, unr0⟩ := allowed_parts al0
    have S : SubjectReduction.TSub asm (b0 :: (rest.map (·.2.1) ++ Γ)) 0
        (fun index => match index with | 0 => a0.rename (· + rest.length) | n + 1 => .bound n)
        (a0.rename (· + rest.length)) (zeroUses (rest.map (·.2.1)) ++ u0) := by
      refine ⟨substAt_instantiate _, b0, rfl, by simpa using hA0, ?_, ?_⟩
      · rcases lin0 with q | free
        · exact .inl q
        · right; simp only [List.eraseIdx_cons_zero]; rw [linearFree_zero_prefix]; exact free
      · intro q; simp only [List.eraseIdx_cons_zero]; rw [captures_zero_prefix _ _ _ _ lu0]; exact unr0 q
    -- a position of `Γ` that is not `unrestricted` counts the argument at most once
    have key0 : ∀ p b, Γ[p]? = some b → b.quantity ≠ .unrestricted → w0 * u0.getD p 0 ≤ u0.getD p 0 := by
      intro p b hp nu
      by_cases hz : u0.getD p 0 = 0
      · rw [hz]; simp
      · have hb0 : b0.quantity ≠ .unrestricted := by
          intro hq
          rcases (captures_iff.mp (unr0 hq)).2 p b hp with z | r
          · exact hz z
          · exact nu r.1
        have := fits_le fits0 hb0
        calc w0 * u0.getD p 0 ≤ 1 * u0.getD p 0 := Nat.mul_le_mul_right _ this
          _ = u0.getD p 0 := Nat.one_mul _
    have keylin : ∀ p, LinearAt Γ p → w0 * u0.getD p 0 = u0.getD p 0 := by
      intro p lin
      by_cases hz : u0.getD p 0 = 0
      · rw [hz]; simp
      · rcases lin0 with q | free
        · have : w0 = 1 := by simpa [q, Quantity.fits] using fits0
          simp [this]
        · exact absurd (linearFree_getD free lin) hz
    -- the image of the term's uses, position by position
    have lw' : w'.length = (rest.map (·.2.1)).length := by rw [lk]; exact hw
    have imageΔ : ∀ j, j < rest.length → Image 0 (zeroUses (rest.map (·.2.1)) ++ u0) (w0 :: (w' ++ v)) j =
        w'.getD j 0 := by
      intro j hj
      simp only [Image, skipAt, Nat.not_lt_zero, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero]
      rw [getD_append_left' (by omega), getD_append_left' (by simp [zeroUses]; omega), getD_zeroUses]
      simp
    have imageΓ : ∀ p, Image 0 (zeroUses (rest.map (·.2.1)) ++ u0) (w0 :: (w' ++ v)) (rest.length + p) =
        v.getD p 0 + w0 * u0.getD p 0 := by
      intro p
      simp only [Image, skipAt, Nat.not_lt_zero, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero]
      rw [getD_append_right' (by omega), getD_append_right' (by simp [zeroUses, lk])]
      simp [zeroUses, hw, lk]
    -- the budget
    have budget : SubjectReduction.Budget (b0 :: (rest.map (·.2.1) ++ Γ)) 0
        (zeroUses (rest.map (·.2.1)) ++ u0) (w0 :: (w' ++ v)) := by
      intro j b hb
      simp only [List.eraseIdx_cons_zero] at hb
      by_cases hj : j < rest.length
      · rw [imageΔ j hj]
        rw [List.getElem?_append_left (by rw [lk]; exact hj)] at hb
        exact fits_safe (by simpa using fits (j + 1) b (by simpa using hb))
      · obtain ⟨p, rfl⟩ : ∃ p, j = rest.length + p := ⟨j - rest.length, by omega⟩
        rw [imageΓ p]
        rw [List.getElem?_append_right (by rw [lk]; omega)] at hb
        simp only [lk, Nat.add_sub_cancel_left] at hb
        by_cases nu : b.quantity = .unrestricted
        · rw [nu]; rfl
        · have hs := (safeUses_iff.mp safe).2 p b hb
          rw [getD_addUses (hv.trans (by simp [addUses, lu0, lS'])), getD_addUses (lu0.trans lS'.symm)] at hs
          exact safeQuantity_mono hs (by have := key0 p b hb nu; omega)
    obtain ⟨u1, h1, le1⟩ := SubjectReduction.subst_typed typed 0 _ _ _ S budget
    simp only [List.eraseIdx_cons_zero] at h1
    have e1 := SubjectReduction.lin_eq typed (by simpa using h1) S.sub
    simp only [List.eraseIdx_cons_zero] at e1
    have l1 : u1.length = rest.length + Γ.length := by rw [source_uses_length h1]; simp [lk]
    -- split the result at the variables still to come
    have hsplit : u1 = u1.take rest.length ++ u1.drop rest.length := (List.take_append_drop _ _).symm
    have lt1 : (u1.take rest.length).length = rest.length := by simp [l1]
    have ld1 : (u1.drop rest.length).length = Γ.length := by simp [l1]
    have v1le : ∀ p b, Γ[p]? = some b → b.quantity ≠ .unrestricted →
        (u1.drop rest.length).getD p 0 ≤ v.getD p 0 + u0.getD p 0 := by
      intro p b hp nu
      have := le1 (rest.length + p)
      rw [imageΓ p] at this
      have hd : (u1.drop rest.length).getD p 0 = u1.getD (rest.length + p) 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [hd]; have := key0 p b hp nu; omega
    have v1lin : ∀ p, LinearAt Γ p → (u1.drop rest.length).getD p 0 = v.getD p 0 + u0.getD p 0 := by
      intro p lin
      obtain ⟨b, hb, q⟩ := lin
      have := e1 (rest.length + p) ⟨b, by rw [List.getElem?_append_right (by rw [lk]; omega)]; simpa [lk] using hb, q⟩
      rw [imageΓ p, keylin p ⟨b, hb, q⟩] at this
      have hd : (u1.drop rest.length).getD p 0 = u1.getD (rest.length + p) 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [hd, this]
    -- the sums
    have below : Below Γ (addUses (u1.drop rest.length) ((rest.map (·.2.2)).foldr addUses (zeroUses Γ)))
        (addUses v (addUses u0 ((rest.map (·.2.2)).foldr addUses (zeroUses Γ)))) := by
      intro p b hp nu
      rw [getD_addUses (ld1.trans lS'.symm), getD_addUses (hv.trans (by simp [addUses, lu0, lS'])),
        getD_addUses (lu0.trans lS'.symm)]
      have := v1le p b hp nu; omega
    have safe' : safeUses Γ (addUses (u1.drop rest.length) ((rest.map (·.2.2)).foldr addUses (zeroUses Γ))) = true :=
      safe_below safe (by simp [addUses, ld1, lS']) below
    have fits' : ∀ (j : Nat) (b : Binding), (rest.map (·.2.1))[j]? = some b → b.quantity.fits ((u1.take rest.length).getD j 0) = true := by
      intro j b hb
      have hj : j < rest.length := by have := (List.getElem?_eq_some_iff.mp hb).1; rwa [lk] at this
      have ht : (u1.take rest.length).getD j 0 = u1.getD j 0 := by
        simp [List.getD_eq_getElem?_getD, hj]
      have f0 := fits (j + 1) b (by simpa using hb)
      simp only [List.getD_cons_succ] at f0
      rw [ht]
      refine fits_transport (n := w'.getD j 0) f0 (by have := le1 j; rwa [imageΔ j hj] at this) (fun q => ?_)
      have := e1 j ⟨b, by rw [List.getElem?_append_left (by rw [lk]; exact hj)]; exact hb, q⟩
      rwa [imageΔ j hj] at this
    rw [hsplit] at h1
    obtain ⟨u', h', below', lin'⟩ := peel_typed rest _ (u1.take rest.length) (u1.drop rest.length) h1 lt1 ld1
      fits' validΔ' (fun arg h => typedArgs arg (List.mem_cons_of_mem _ h))
      (fun arg h => allowedArgs arg (List.mem_cons_of_mem _ h)) safe'
    refine ⟨u', ?_, below_trans below' below, fun p lin => ?_⟩
    · rw [peelSubst_cons a0 (rest.map (·.1)) (source_scoped ta0), ← TermTraverse.substitute_comp]
      simpa using h'
    · rw [lin' p lin, getD_addUses (ld1.trans lS'.symm), getD_addUses (hv.trans (by simp [addUses, lu0, lS'])),
        getD_addUses (lu0.trans lS'.symm), v1lin p lin]
      omega

/-- What a filler of a declared hole must be: typed at the declared type in the declared context,
a valid one, using each variable as its binding's quantity promises (`Quantity.fits`: a `linear`
one exactly once). -/
@[expose] public def FillerTyped (asm : Assumptions) (decl : HoleDecl) (f : Term) : Prop :=
  ∃ uf, PartialTyping asm decl.context f decl.type uf ∧
    validContext asm.shareableVariables decl.context = true ∧
    ∀ (j : Nat) (b : Binding), decl.context[j]? = some b → b.quantity.fits (uf.getD j 0) = true

/-- **The hole case.** A filler typed as its hole declares, under the hole's arguments, is typed
where the hole was, within the hole's uses and exact at every `linear` position. -/
theorem fill_hole_typed {asm : Assumptions} {Γ : Context} {decl : HoleDecl} {f : Term}
    {args : List (Term × Binding × Uses)} (filler : FillerTyped asm decl f)
    (hctx : args.map (·.2.1) = decl.context) (validΓ : validContext asm.shareableVariables Γ = true)
    (typedArgs : ∀ arg ∈ args, PartialTyping asm Γ arg.1 arg.2.1.type arg.2.2)
    (allowed : ∀ arg ∈ args, argumentAllowed asm arg.2.1.quantity Γ arg.2.1.type arg.2.2 = true)
    (safe : safeUses Γ ((args.map (·.2.2)).foldr addUses (zeroUses Γ)) = true) :
    ∃ u', PartialTyping asm Γ (f.substitute (listSubst (args.map (·.1)))) decl.type u' ∧
      Below Γ u' ((args.map (·.2.2)).foldr addUses (zeroUses Γ)) ∧
      ∀ j, LinearAt Γ j → u'.getD j 0 = ((args.map (·.2.2)).foldr addUses (zeroUses Γ)).getD j 0 := by
  obtain ⟨uf, typedF, validΔ, fits⟩ := filler
  have lS : ((args.map (·.2.2)).foldr addUses (zeroUses Γ)).length = Γ.length :=
    length_foldr_addUses _ _ (by simp [zeroUses]) (fun u hu => by
      obtain ⟨arg, h, rfl⟩ := List.mem_map.mp hu; exact source_uses_length (typedArgs arg h))
  have scopedF := source_scoped typedF
  obtain ⟨a, ha, hu, typedF'⟩ := Obend.Core.Proofs.TypedSubstitution.partialTyping_transport typedF [] Γ validΓ
    decl.context (by simp) scopedF
  simp only [zeroUses, List.length_nil, List.replicate_zero, List.append_nil] at hu
  subst hu
  rw [← hctx] at typedF' validΔ fits
  have := peel_typed args f uf (zeroUses Γ) typedF' (by rw [ha, ← hctx, List.length_map])
    (by simp [zeroUses]) fits validΔ typedArgs allowed (by rw [zero_add_uses Γ lS]; exact safe)
  rw [zero_add_uses Γ lS] at this
  obtain ⟨u', h', below, lin⟩ := this
  refine ⟨u', ?_, below, lin⟩
  have e : f.substitute (listSubst (args.map (·.1))) = f.substitute (peelSubst (args.map (·.1))) := by
    apply TermTraverse.scoped_substitution_congr f decl.context.length
      ((Invariant.scoped_encode_iff _ _).mp scopedF)
    intro i hi
    have hi' : i < args.length := by rw [← hctx] at hi; simpa using hi
    simp [listSubst, peelSubst, hi', List.getD_eq_getElem?_getD]
  rw [e]; exact h'

/-! ### Uses that a fill may lower -/

/-- `x'` uses no more than `x` at a position that is not `unrestricted`, and as much at a `linear`
one. -/
@[expose] public def Close (Γ : Context) (x' x : Uses) : Prop :=
  Below Γ x' x ∧ ∀ j, LinearAt Γ j → x'.getD j 0 = x.getD j 0

theorem close_refl (Γ : Context) (x : Uses) : Close Γ x x := ⟨fun _ _ _ _ => Nat.le_refl _, fun _ _ => rfl⟩

theorem close_trans {Γ : Context} {x y z : Uses} (h1 : Close Γ x y) (h2 : Close Γ y z) : Close Γ x z :=
  ⟨below_trans h1.1 h2.1, fun j lin => (h1.2 j lin).trans (h2.2 j lin)⟩

theorem close_add {Γ : Context} {x x' y y' : Uses} (hx : Close Γ x' x) (hy : Close Γ y' y)
    (l : x.length = y.length) (l' : x'.length = y'.length) : Close Γ (addUses x' y') (addUses x y) :=
  ⟨fun j b hb q => by
    rw [getD_addUses l', getD_addUses l]; have := hx.1 j b hb q; have := hy.1 j b hb q; omega,
   fun j lin => by rw [getD_addUses l', getD_addUses l, hx.2 j lin, hy.2 j lin]⟩

theorem close_join {Γ : Context} {x x' y y' : Uses} (hx : Close Γ x' x) (hy : Close Γ y' y)
    (l : x.length = y.length) (l' : x'.length = y'.length) : Close Γ (joinUses x' y') (joinUses x y) :=
  ⟨fun j b hb q => by
    rw [getD_joinUses l', getD_joinUses l]; have := hx.1 j b hb q; have := hy.1 j b hb q; omega,
   fun j lin => by rw [getD_joinUses l', getD_joinUses l, hx.2 j lin, hy.2 j lin]⟩

theorem close_tail {b : Binding} {Γ : Context} {x' x : Uses} (h : Close (b :: Γ) x' x) : Close Γ x'.tail x.tail :=
  ⟨fun j c hc q => by rw [getD_tail, getD_tail]; exact h.1 (j + 1) c (by simpa using hc) q,
   fun j lin => by rw [getD_tail, getD_tail]; exact h.2 (j + 1) (linearAt_cons.mpr lin)⟩

theorem safe_add_left' {Γ : Context} {x y : Uses} (safe : safeUses Γ (addUses x y) = true)
    (lx : x.length = Γ.length) (ly : y.length = Γ.length) : safeUses Γ x = true :=
  safe_mono safe lx (add_le_left (lx.trans ly.symm))

theorem safe_add_right' {Γ : Context} {x y : Uses} (safe : safeUses Γ (addUses x y) = true)
    (lx : x.length = Γ.length) (ly : y.length = Γ.length) : safeUses Γ y = true :=
  safe_mono safe ly (add_le_right (lx.trans ly.symm))

theorem safe_join_left' {Γ : Context} {x y : Uses} (safe : safeUses Γ (joinUses x y) = true)
    (lx : x.length = Γ.length) (ly : y.length = Γ.length) : safeUses Γ x = true :=
  safe_mono safe lx (join_le_left (lx.trans ly.symm))

theorem safe_join_right' {Γ : Context} {x y : Uses} (safe : safeUses Γ (joinUses x y) = true)
    (lx : x.length = Γ.length) (ly : y.length = Γ.length) : safeUses Γ y = true :=
  safe_mono safe ly (join_le_right (lx.trans ly.symm))

section transport
variable {asm : Assumptions} {Γ : Context} {x y : Uses}

theorem allowed_close (valid : validContext asm.shareableVariables Γ = true) {q : Quantity} {X : Ty}
    (allowed : argumentAllowed asm q Γ X y = true) (len : x.length = Γ.length) (c : Close Γ x y) :
    argumentAllowed asm q Γ X x = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    beq_iff_eq] at allowed ⊢
  obtain ⟨⟨pure, lin⟩, unr⟩ := allowed
  refine ⟨⟨pure, lin.imp id (fun free => linearFree_below free len c.1)⟩, ?_⟩
  rcases unr with n | ⟨share, cap⟩
  · exact .inl n
  · exact .inr ⟨share, captures_below valid cap len c.1⟩

theorem reusableAllowed_close (valid : validContext asm.shareableVariables Γ = true) {r : Reuse}
    (allowed : reusableAllowed asm r Γ y = true) (len : x.length = Γ.length) (c : Close Γ x y) :
    reusableAllowed asm r Γ x = true := by
  simp only [reusableAllowed, Bool.or_eq_true, bne_iff_ne, ne_eq] at allowed ⊢
  exact allowed.imp id (fun cap => captures_below valid cap len c.1)

theorem fits_close {b : Binding} {x' x : Uses} (h : b.quantity.fits (x.headD 0) = true)
    (c : Close (b :: Γ) x' x) : b.quantity.fits (x'.headD 0) = true := by
  rw [headD_getD] at h ⊢
  by_cases qu : b.quantity = .unrestricted
  · rw [qu]; rfl
  · exact fits_transport h (c.1 0 b rfl qu) (fun q => c.2 0 ⟨b, rfl, q⟩)

theorem agree_close {x' y' : Uses} (agree : branchesAgree Γ x y = true) (lx : x.length = Γ.length)
    (ly : y.length = Γ.length) (cx : Close Γ x' x) (cy : Close Γ y' y) : branchesAgree Γ x' y' = true :=
  branchesAgree_of fun j lin => by rw [cx.2 j lin, cy.2 j lin]; exact branchesAgree_getD agree lx ly lin

end transport

theorem valid_cons {V : List Nat} {b : Binding} {Γ : Context} (hb : validContext V [b] = true)
    (h : validContext V Γ = true) : validContext V (b :: Γ) = true := by
  simp only [validContext, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hb h ⊢
  exact ⟨hb, h⟩

/-! ### Filling -/

/-- Every filler `θ` gives is typed as its hole declares (`FillerTyped`). -/
@[expose] public def FillersTyped (asm : Assumptions) (θ : Nat → Option Term) : Prop :=
  ∀ n f decl, θ n = some f → asm.holes.lookup n = some decl → FillerTyped asm decl f

/-- **Filling typed holes.** A term checked with declared holes, in a valid context and within its
budget, is typed at the same type once its holes are filled by fillers typed as they are declared:
it uses no more at any position that is not `unrestricted`, and exactly as much at every `linear`
one. Nothing about the holed term is checked again. -/
public theorem fill_typed {asm : Assumptions} {Γ : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping asm Γ t T u) {θ : Nat → Option Term} (fillers : FillersTyped asm θ)
    (valid : validContext asm.shareableVariables Γ = true) (safe : safeUses Γ u = true) :
    ∃ u', PartialTyping asm Γ (t.fill θ) T u' ∧ Below Γ u' u ∧
      ∀ j, LinearAt Γ j → u'.getD j 0 = u.getD j 0 := by
  suffices h : validContext asm.shareableVariables Γ = true → safeUses Γ u = true →
      ∃ u', PartialTyping asm Γ (t.fill θ) T u' ∧ Close Γ u' u from h valid safe
  apply PartialTyping.rec
    (motive_1 := fun Γ t T u _ => validContext asm.shareableVariables Γ = true → safeUses Γ u = true →
      ∃ u', PartialTyping asm Γ (t.fill θ) T u' ∧ Close Γ u' u)
    (motive_2 := fun Γ fields row u _ => validContext asm.shareableVariables Γ = true → safeUses Γ u = true →
      ∃ u', FieldsTyping asm Γ (fields.map fun field => (field.1, field.2.fill θ)) row u' ∧ Close Γ u' u)
    (motive_3 := fun Γ q arms row result u _ => validContext asm.shareableVariables Γ = true →
      safeUses Γ u = true →
      ∃ u', ArmsTyping asm Γ q (arms.map fun arm => (arm.1, arm.2.fill θ)) row result u' ∧ Close Γ u' u)
    (t := typed)
  case bound =>
    intro Γ index binding found _ _
    simp only [Term.fill]; exact ⟨_, .bound found, close_refl _ _⟩
  case natural =>
    intro Γ value _ _
    simp only [Term.fill]; exact ⟨_, .natural _ value, close_refl _ _⟩
  case boolean =>
    intro Γ value _ _
    simp only [Term.fill]; exact ⟨_, .boolean _ value, close_refl _ _⟩
  case label =>
    intro Γ value _ _
    simp only [Term.fill]; exact ⟨_, .label _ value, close_refl _ _⟩
  case lambda =>
    intro Γ body ann uses bodyTyped safeB validB captures fits ih valid safe
    obtain ⟨ub', hb', cb⟩ := ih validB safeB
    have lb' := source_uses_length hb'
    simp only [Term.fill]
    refine ⟨ub'.tail, .lambda hb' (safe_below safeB lb' cb.1) validB
      (reusableAllowed_close valid captures (by simp [lb']) (close_tail cb)) (fits_close fits cb), close_tail cb⟩
  case conversion =>
    intro Γ term actual expected uses prior agreement ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    exact ⟨u', .conversion h agreement, c⟩
  case application =>
    intro Γ fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped
      callableEq same allowed ihFn ihArg valid safe
    have lf := source_uses_length fnTyped
    have la := source_uses_length argTyped
    obtain ⟨fu', hf, cf⟩ := ihFn valid (safe_add_left' safe lf la)
    obtain ⟨au', ha, ca⟩ := ihArg valid (safe_add_right' safe lf la)
    simp only [Term.fill]
    exact ⟨_, .application hf ha callableEq same (allowed_close valid allowed (source_uses_length ha) ca),
      close_add cf ca (lf.trans la.symm) ((source_uses_length hf).trans (source_uses_length ha).symm)⟩
  case record =>
    intro Γ fields row uses fieldsTyped distinct ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .record h (by simpa [labelsDistinct, List.map_map, Function.comp_def] using distinct), c⟩
  case get =>
    intro Γ target targetType member uses name fuel targetTyped lookup free ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .get h lookup (linearFree_below free (source_uses_length h) c.1), c⟩
  case extend =>
    intro Γ target fields targetType row tu fu rowFuel targetTyped fieldsTyped distinct isRow free ihTarget ihFields
      valid safe
    have lt := source_uses_length targetTyped
    have lf := fields_uses_length fieldsTyped
    obtain ⟨tu', ht, ct⟩ := ihTarget valid (safe_add_left' safe lt lf)
    obtain ⟨fu', hf, cf⟩ := ihFields valid (safe_add_right' safe lt lf)
    simp only [Term.fill]
    exact ⟨_, .extend ht hf (by simpa [labelsDistinct, List.map_map, Function.comp_def] using distinct) isRow
      (linearFree_below free (source_uses_length ht) ct.1),
      close_add ct cf (lt.trans lf.symm) ((source_uses_length ht).trans (fields_uses_length hf).symm)⟩
  case specification =>
    intro Γ metadata extension metadataType extensionType mu eu metadataTyped extensionTyped mPure ePure free
      ihM ihE valid safe
    have lm := source_uses_length metadataTyped
    have le := source_uses_length extensionTyped
    obtain ⟨mu', hm, cm⟩ := ihM valid (safe_add_left' safe lm le)
    obtain ⟨eu', he, ce⟩ := ihE valid (safe_add_right' safe lm le)
    simp only [Term.fill]
    exact ⟨_, .specification hm he mPure ePure (linearFree_below free (source_uses_length hm) cm.1),
      close_add cm ce (lm.trans le.symm) ((source_uses_length hm).trans (source_uses_length he).symm)⟩
  case prototype =>
    intro Γ spec target specType targetType su tu specTyped targetTyped sPure tPure ihS ihT valid safe
    have ls := source_uses_length specTyped
    have lt := source_uses_length targetTyped
    obtain ⟨su', hs, cs⟩ := ihS valid (safe_add_left' safe ls lt)
    obtain ⟨tu', ht, ct⟩ := ihT valid (safe_add_right' safe ls lt)
    simp only [Term.fill]
    exact ⟨_, .prototype hs ht sPure tPure,
      close_add cs ct (ls.trans lt.symm) ((source_uses_length hs).trans (source_uses_length ht).symm)⟩
  case reflect =>
    intro Γ target specType targetType uses prior free ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .reflect h (linearFree_below free (source_uses_length h) c.1), c⟩
  case metadata =>
    intro Γ target metadataType extensionType uses prior free ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .metadata h (linearFree_below free (source_uses_length h) c.1), c⟩
  case project =>
    intro Γ target specType targetType uses prior free ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .project h (linearFree_below free (source_uses_length h) c.1), c⟩
  case mix =>
    intro Γ lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped
      lowerCallable upperCallable captures selfShare inheritedShare middleShare ihL ihU valid safe
    have ll := source_uses_length lowerTyped
    have lu' := source_uses_length upperTyped
    obtain ⟨l', hl, cl⟩ := ihL valid (safe_add_left' safe ll lu')
    obtain ⟨r', hr, cr⟩ := ihU valid (safe_add_right' safe ll lu')
    have c := close_add cl cr (ll.trans lu'.symm) ((source_uses_length hl).trans (source_uses_length hr).symm)
    simp only [Term.fill]
    exact ⟨_, .mix hl hr lowerCallable upperCallable
      (captures_below valid captures (by simp [addUses, source_uses_length hl, source_uses_length hr]) c.1)
      selfShare inheritedShare middleShare, c⟩
  case fix =>
    intro Γ spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare
      inheritedAllowed captures ihS ihI valid safe
    have ls := source_uses_length specTyped
    have li := source_uses_length inheritedTyped
    obtain ⟨su', hs, cs⟩ := ihS valid (safe_add_left' safe ls li)
    obtain ⟨iu', hi, ci⟩ := ihI valid (safe_add_right' safe ls li)
    simp only [Term.fill]
    exact ⟨_, .fix hs callableEq hi targetShare (allowed_close valid inheritedAllowed (source_uses_length hi) ci)
      (captures_below valid captures (source_uses_length hs) cs.1),
      close_add cs ci (ls.trans li.symm) ((source_uses_length hs).trans (source_uses_length hi).symm)⟩
  case binary =>
    intro Γ primitive left right input output lu ru primitiveEq leftTyped rightTyped ihL ihR valid safe
    have ll := source_uses_length leftTyped
    have lr := source_uses_length rightTyped
    obtain ⟨l', hl, cl⟩ := ihL valid (safe_add_left' safe ll lr)
    obtain ⟨r', hr, cr⟩ := ihR valid (safe_add_right' safe ll lr)
    simp only [Term.fill]
    exact ⟨_, .binary primitiveEq hl hr,
      close_add cl cr (ll.trans lr.symm) ((source_uses_length hl).trans (source_uses_length hr).symm)⟩
  case ifZero =>
    intro Γ value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe agreeing
      ihV ihZ ihS valid safe
    have lv := source_uses_length valueTyped
    have lz := source_uses_length zeroTyped
    have ls : su.tail.length = Γ.length := by simp [source_uses_length successorTyped]
    have lj : (joinUses zu su.tail).length = Γ.length := by simp [joinUses, lz, ls]
    have validS : validContext asm.shareableVariables (⟨.natural, .unrestricted⟩ :: Γ) = true :=
      valid_cons (by simp [validContext, Ty.shareableUnder, Ty.shareable]) valid
    obtain ⟨vu', hv, cv⟩ := ihV valid (safe_add_left' safe lv lj)
    obtain ⟨zu', hz, cz⟩ := ihZ valid (safe_join_left' (safe_add_right' safe lv lj) lz ls)
    obtain ⟨su', hs, cs⟩ := ihS validS successorSafe
    have lz' := source_uses_length hz
    have ls' : su'.tail.length = Γ.length := by simp [source_uses_length hs]
    simp only [Term.fill]
    exact ⟨_, .ifZero hv hz hs (safe_below successorSafe (source_uses_length hs) cs.1)
        (agree_close agreeing lz ls cz (close_tail cs)),
      close_add cv (close_join cz (close_tail cs) (lz.trans ls.symm) (lz'.trans ls'.symm)) (lv.trans lj.symm)
        ((source_uses_length hv).trans (by simp [joinUses, lz', ls']))⟩
  case inject =>
    intro Γ tag payload payloadType row uses fuel payloadTyped lookup pure ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .inject h lookup pure, c⟩
  case case =>
    intro Γ scrutinee arms row result su au q scrutineeTyped armsTyped distinct allowed ihS ihA valid safe
    have ls := source_uses_length scrutineeTyped
    have la := Obend.Core.Proofs.Preservation.arms_uses_length armsTyped
    obtain ⟨su', hs, cs⟩ := ihS valid (safe_add_left' safe ls la)
    obtain ⟨au', ha, ca⟩ := ihA valid (safe_add_right' safe ls la)
    simp only [Term.fill]
    exact ⟨_, .case hs ha (by simpa [labelsDistinct, List.map_map, Function.comp_def] using distinct)
        (caseAllowed_below valid allowed (source_uses_length hs) cs.1),
      close_add cs ca (ls.trans la.symm)
        ((source_uses_length hs).trans (Obend.Core.Proofs.Preservation.arms_uses_length ha).symm)⟩
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped agreeing
      ihC ihT ihF valid safe
    have lc := source_uses_length conditionTyped
    have lt := source_uses_length trueTyped
    have lf := source_uses_length falseTyped
    have lj : (joinUses tu fu).length = Γ.length := by simp [joinUses, lt, lf]
    obtain ⟨cu', hc, cc⟩ := ihC valid (safe_add_left' safe lc lj)
    obtain ⟨tu', ht, ct⟩ := ihT valid (safe_join_left' (safe_add_right' safe lc lj) lt lf)
    obtain ⟨fu', hf, cf⟩ := ihF valid (safe_join_right' (safe_add_right' safe lc lj) lt lf)
    have lt' := source_uses_length ht
    have lf' := source_uses_length hf
    simp only [Term.fill]
    exact ⟨_, .ifBool hc ht hf (agree_close agreeing lt lf ct cf),
      close_add cc (close_join ct cf (lt.trans lf.symm) (lt'.trans lf'.symm)) (lc.trans lj.symm)
        ((source_uses_length hc).trans (by simp [joinUses, lt', lf']))⟩
  case perform =>
    intro Γ plan planType response uses planTyped isPlan isData ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .perform h isPlan isData, c⟩
  case done =>
    intro Γ value planType response result uses valueTyped pure ih valid safe
    obtain ⟨u', h, c⟩ := ih valid safe
    simp only [Term.fill]
    exact ⟨u', .done h pure, c⟩
  case effectCase =>
    intro Γ scrutinee arms planType response row result su au q scrutineeTyped armsTyped pure distinct allowed
      ihS ihA valid safe
    have ls := source_uses_length scrutineeTyped
    have la := Obend.Core.Proofs.Preservation.arms_uses_length armsTyped
    obtain ⟨su', hs, cs⟩ := ihS valid (safe_add_left' safe ls la)
    obtain ⟨au', ha, ca⟩ := ihA valid (safe_add_right' safe ls la)
    simp only [Term.fill]
    exact ⟨_, .effectCase hs ha pure (by simpa [labelsDistinct, List.map_map, Function.comp_def] using distinct)
        (caseAllowed_below valid allowed (source_uses_length hs) cs.1),
      close_add cs ca (ls.trans la.symm)
        ((source_uses_length hs).trans (Obend.Core.Proofs.Preservation.arms_uses_length ha).symm)⟩
  case split =>
    intro Γ target function names row functionType result tu fu targetTyped functionTyped nodup covers spine
      ihT ihF valid safe
    have lt := source_uses_length targetTyped
    have lf := source_uses_length functionTyped
    obtain ⟨tu', ht, ct⟩ := ihT valid (safe_add_left' safe lt lf)
    obtain ⟨fu', hf, cf⟩ := ihF valid (safe_add_right' safe lt lf)
    simp only [Term.fill]
    exact ⟨_, .split ht hf nodup covers
        (spine.transport fun q allowed => caseAllowed_below valid allowed (source_uses_length ht) ct.1),
      close_add ct cf (lt.trans lf.symm) ((source_uses_length ht).trans (source_uses_length hf).symm)⟩
  case hole =>
    intro Γ n σ decl args found hσ hctx typedArgs allowed ih valid safe
    subst hσ
    have lens : ∀ u ∈ args.map (·.2.2), u.length = Γ.length := by
      intro u hu; obtain ⟨arg, h, rfl⟩ := List.mem_map.mp hu; exact source_uses_length (typedArgs arg h)
    have lS : ((args.map (·.2.2)).foldr addUses (zeroUses Γ)).length = Γ.length :=
      length_foldr_addUses _ _ (by simp [zeroUses]) lens
    obtain ⟨m, hm, hp⟩ := exists_list_choice args (P := fun arg u' =>
        PartialTyping asm Γ (arg.1.fill θ) arg.2.1.type u' ∧ Close Γ u' arg.2.2)
      (fun arg h => ih arg h valid (safe_mono safe (source_uses_length (typedArgs arg h))
        (le_foldr_addUses _ _ (by simp [zeroUses]) lens _ (List.mem_map_of_mem h))))
    subst hm
    have cS : Close Γ ((m.map (·.2)).foldr addUses (zeroUses Γ))
        (((m.map Prod.fst).map (·.2.2)).foldr addUses (zeroUses Γ)) := by
      rw [List.map_map]
      exact (foldr_addUses_rel (R := fun x' x => Close Γ x' x ∧ x'.length = Γ.length ∧ x.length = Γ.length)
        (z := zeroUses Γ) (z' := zeroUses Γ)
        (fun ⟨h1, l1, k1⟩ ⟨h2, l2, k2⟩ => ⟨close_add h1 h2 (k1.trans k2.symm) (l1.trans l2.symm),
          by simp [addUses, l1, l2], by simp [addUses, k1, k2]⟩)
        ⟨close_refl _ _, by simp [zeroUses], by simp [zeroUses]⟩
        (fun p => p.1.2.2) (fun p => p.2) m
        (fun p hp' => ⟨(hp p hp').2, source_uses_length (hp p hp').1,
          source_uses_length (typedArgs p.1 (List.mem_map_of_mem hp'))⟩)).1
    have lS' : ((m.map (·.2)).foldr addUses (zeroUses Γ)).length = Γ.length :=
      length_foldr_addUses _ _ (by simp [zeroUses]) (fun u hu => by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hu; exact source_uses_length (hp p hp').1)
    let args' := m.map fun p => (p.1.1.fill θ, p.1.2.1, p.2)
    have hctx' : args'.map (·.2.1) = decl.context := by rw [← hctx]; simp [args', Function.comp_def]
    have typed' : ∀ arg ∈ args', PartialTyping asm Γ arg.1 arg.2.1.type arg.2.2 := by
      intro x hx; obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx; exact (hp p hp').1
    have allowed' : ∀ arg ∈ args', argumentAllowed asm arg.2.1.quantity Γ arg.2.1.type arg.2.2 = true := by
      intro x hx
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
      exact allowed_close valid (allowed p.1 (List.mem_map_of_mem hp')) (source_uses_length (hp p hp').1) (hp p hp').2
    have sum' : (args'.map (·.2.2)).foldr addUses (zeroUses Γ) = (m.map (·.2)).foldr addUses (zeroUses Γ) := by
      simp [args', Function.comp_def]
    have terms' : ((m.map Prod.fst).map (·.1)).map (fun t => t.fill θ) = args'.map (·.1) := by
      simp [args', Function.comp_def]
    simp only [Term.fill]
    cases hθ : θ n with
    | none =>
      refine ⟨_, PartialTyping.hole found terms' hctx' typed' allowed', ?_⟩
      rw [sum']; exact cS
    | some f =>
      have safe' : safeUses Γ ((args'.map (·.2.2)).foldr addUses (zeroUses Γ)) = true := by
        rw [sum']; exact safe_below safe lS' cS.1
      obtain ⟨u', h', below', lin'⟩ := fill_hole_typed (fillers n f decl hθ found) hctx' valid typed' allowed' safe'
      rw [sum'] at below' lin'
      refine ⟨u', ?_, close_trans ⟨below', lin'⟩ cS⟩
      rw [terms']; exact h'
  case nil =>
    intro Γ _ _
    exact ⟨_, .nil _, close_refl _ _⟩
  case cons =>
    intro Γ name body rest type row bu ru bodyTyped restTyped pure ihBody ihRest valid safe
    have lb := source_uses_length bodyTyped
    have lr := fields_uses_length restTyped
    obtain ⟨bu', hb, cb⟩ := ihBody valid (safe_add_left' safe lb lr)
    obtain ⟨ru', hr, cr⟩ := ihRest valid (safe_add_right' safe lb lr)
    exact ⟨_, .cons hb hr pure, close_add cb cr (lb.trans lr.symm)
      ((source_uses_length hb).trans (fields_uses_length hr).symm)⟩
  case nil =>
    intro Γ q result _ _
    exact ⟨_, .nil _ q result, close_refl _ _⟩
  case cons =>
    intro Γ q name body rest payload row result bu ru bodyTyped safeB shareable fits restTyped agreeing
      ihBody ihRest valid safe
    have lb : bu.tail.length = Γ.length := by simp [source_uses_length bodyTyped]
    have lr := Obend.Core.Proofs.Preservation.arms_uses_length restTyped
    obtain ⟨bu', hb, cb⟩ := ihBody (valid_cons shareable valid) safeB
    obtain ⟨ru', hr, cr⟩ := ihRest valid (safe_join_right' safe lb lr)
    have lb' : bu'.tail.length = Γ.length := by simp [source_uses_length hb]
    have lr' := Obend.Core.Proofs.Preservation.arms_uses_length hr
    refine ⟨_, .cons hb (safe_below safeB (source_uses_length hb) cb.1) shareable (fits_close fits cb) hr ?_,
      close_join (close_tail cb) cr (lb.trans lr.symm) (lb'.trans lr'.symm)⟩
    cases rest with
    | nil => simp
    | cons first others =>
      simp only [List.map_cons, List.isEmpty_cons, Bool.false_or] at agreeing ⊢
      exact agree_close agreeing lb lr (close_tail cb) cr

/-- `fill_typed` read as `step_preserves_typing` states its conclusion. -/
public theorem fill_preserves_typing {asm : Assumptions} {Γ : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping asm Γ t T u) {θ : Nat → Option Term} (fillers : FillersTyped asm θ)
    (valid : validContext asm.shareableVariables Γ = true) (safe : safeUses Γ u = true) :
    ∃ T' u', PartialTyping asm Γ (t.fill θ) T' u' ∧ sameType asm T' T = true ∧ Below Γ u' u ∧
      ∀ j, LinearAt Γ j → u'.getD j 0 = u.getD j 0 := by
  obtain ⟨u', h, below, lin⟩ := fill_typed typed fillers valid safe
  exact ⟨T, u', h, sameType_refl _ _, below, lin⟩

/-- **Checked once.** What the checker accepted with holes declared is typed after every fill the
fillers discharge, from the one derivation it returned: no fill is checked again. -/
public theorem checkAt_fill {asm : Assumptions} {annotations : Annotations} {Γ : Context} {path : List Nat}
    {t : Term} {T : Ty} {r : Bidirectional.Against asm Γ t T}
    (_checked : Bidirectional.checkAt asm annotations Γ path t T = .ok r)
    (valid : validContext asm.shareableVariables Γ = true) (safe : safeUses Γ r.uses = true)
    {θ : Nat → Option Term} (fillers : FillersTyped asm θ) :
    ∃ u', PartialTyping asm Γ (t.fill θ) T u' ∧ Below Γ u' r.uses ∧
      ∀ j, LinearAt Γ j → u'.getD j 0 = r.uses.getD j 0 :=
  fill_typed r.derivation fillers valid safe

end Obend.Core.Proofs.FillTyping
