module
/-
# Obend.Law.Proofs.Claim — a law in certifying shape means its claim (nano LANG-83, LANG-92)

* `guardedBy_sound`: a term in shape `guardedBy I k r` evaluates (under any substitution `σ`) to
  `inject "ok" _` only when `I` applied to `σ k` evaluated to `true`, or the term read a `relaw`
  occasion off `σ r` (`GuardedOk`).
* `keeps_step`: a law in shape that ADMITS a request whose occasion is not a relaw leaves a state
  that keeps the invariant (`Keeps`).
* `chain_keeps`: along a `Chain` of the law's steps (`LawStep`: it admits, and a relaw keeps the
  state), every state keeps the invariant once the first does.
* `keeps_guarded`: `Std.keeps S I` is in shape. `checkClaim_keeps`, `claim_chain_keeps`: what the
  claim check admitted bears the claim.

Ported from nanodregg `Lang/Proofs/Claim.lean` (origin/main `2dcc9ea`), over Core4's substitution
semantics instead of nano's environments.
-/
public import Obend.Law.Claim
public import Obend.Law.Std
public import Obend.Law.Proofs.Std
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag encode)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## Term equality and closedness -/

mutual
theorem treeEq_sound : ∀ {a b : Tree Tag}, treeEq a b = true → a = b
  | .var i, .var j, h => by simp [treeEq] at h; subst h; rfl
  | .bind a, .bind b, h => by simp only [treeEq] at h; rw [treeEq_sound h]
  | .node t cs, .node u ds, h => by
      simp only [treeEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, treesEq_sound h.2]
  | .var _, .bind _, h | .var _, .node _ _, h | .bind _, .var _, h | .bind _, .node _ _, h
  | .node _ _, .var _, h | .node _ _, .bind _, h => by simp [treeEq] at h
theorem treesEq_sound : ∀ {as bs : List (Tree Tag)}, treesEq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [treesEq, Bool.and_eq_true] at h
      rw [treeEq_sound h.1, treesEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [treesEq] at h
end

mutual
theorem treeEq_refl : ∀ (a : Tree Tag), treeEq a a = true
  | .var i => by simp [treeEq]
  | .bind a => by simp only [treeEq]; exact treeEq_refl a
  | .node t cs => by simp only [treeEq, decide_true, Bool.true_and]; exact treesEq_refl cs
theorem treesEq_refl : ∀ (as : List (Tree Tag)), treesEq as as = true
  | [] => rfl
  | a :: as => by simp only [treesEq, Bool.and_eq_true]; exact ⟨treeEq_refl a, treesEq_refl as⟩
end

public theorem termEq_sound {a b : Term} (h : termEq a b = true) : a = b :=
  Obend.Core.TermTraverse.encode_injective (treeEq_sound h)

theorem termEq_refl (a : Term) : termEq a a = true := treeEq_refl _

mutual
public theorem scopedB_sound : ∀ {n : Nat} {t : Tree Tag}, scopedB n t = true → Tree.Scoped n t
  | n, .var i, h => by simpa [scopedB, Tree.Scoped, Tree.All] using h
  | n, .bind b, h => by
      have ih : Tree.Scoped (n + 1) b := scopedB_sound (by simpa [scopedB] using h)
      simp only [Tree.Scoped, Tree.All]
      exact (Tree.all_congr _ _ _ (fun i => by cases i <;> simp)).1 ih
  | n, .node _ cs, h => by
      simp only [Tree.Scoped, Tree.All]
      exact scopedsB_sound (by simpa [scopedB] using h)
public theorem scopedsB_sound : ∀ {n : Nat} {cs : List (Tree Tag)}, scopedsB n cs = true →
    ∀ c ∈ cs, Tree.Scoped n c
  | _, [], _, _, hc => by simp at hc
  | n, c :: cs, h, d, hd => by
      simp only [scopedsB, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hd with same | hd
      · rw [same]; exact scopedB_sound h.1
      · exact scopedsB_sound h.2 d hd
end

/-- A closed term is fixed by every substitution. -/
public theorem closedB_subst {t : Term} (h : closedB t = true) (σ : Nat → Term) : t.substitute σ = t :=
  Obend.Core.TermTraverse.scoped_substitute_identity t 0 (scopedB_sound h) σ
    (fun i hi => absurd hi (Nat.not_lt_zero _))

/-! ## The checker is sound -/

/-- What a guarded `ok` means under `σ`: the invariant held of `σ k`, or a `relaw` was read at `r`. -/
@[expose] public def GuardedOk (I : Term) (k r : Nat) (σ : Nat → Term) : Prop :=
  Evaluates (.app I (σ k)) (.boolean true) ∨ ∃ x, Evaluates (.get (σ r) "occasion") (.inject "relaw" x)

theorem guardedOk_scons {I : Term} {k r : Nat} {p : Term} {σ : Nat → Term}
    (h : GuardedOk I (k + 1) (r + 1) (scons p σ)) : GuardedOk I k r σ := h

@[simp] public theorem subst_inject (σ : Nat → Term) (l : String) (t : Term) :
    (Term.inject l t).substitute σ = .inject l (t.substitute σ) := by
  simp [Term.substitute]

theorem isGuardCond_eq {I c : Term} {k : Nat} (h : isGuardCond I k c = true) : c = .app I (.bound k) := by
  unfold isGuardCond at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, termEq_sound h.2]
  · cases h

theorem isOccasion_eq {s : Term} {r : Nat} (h : isOccasion r s = true) : s = .get (.bound r) "occasion" := by
  unfold isOccasion at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  · cases h

mutual
/-- **The checker is sound.** A term in certifying shape means `ok` only through a guarded leaf. -/
public theorem guardedBy_sound {I : Term} (hI : closedB I = true) :
    ∀ {t : Term} {k r : Nat} {σ : Nat → Term} {w : Term},
      guardedBy I k r t = true → Evaluates (t.substitute σ) (.inject "ok" w) → GuardedOk I k r σ
  | .ifBool c a b, k, r, σ, w, hg, h => by
      simp only [guardedBy, Bool.and_eq_true, Bool.or_eq_true] at hg
      simp only [subst_ifBool] at h
      obtain ⟨bb, hc, hr⟩ := ifBool_inv h
      cases bb
      · exact guardedBy_sound hI hg.2 hr
      · simp only [↓reduceIte] at hr
        rcases hg.1 with hgc | hga
        · rw [isGuardCond_eq hgc] at hc
          simp only [subst_app, subst_bound, closedB_subst hI] at hc
          exact .inl hc
        · exact guardedBy_sound hI hga hr
  | .case s arms, k, r, σ, w, hg, h => by
      simp only [guardedBy] at hg
      obtain ⟨l, p, body, hs, hf, hb⟩ := case_subst_inv h
      rcases guardedArms_sound hI hg hf hb with ⟨hocc, rfl⟩ | hok
      · rw [isOccasion_eq hocc] at hs
        simp only [subst_get, subst_bound] at hs
        exact .inr ⟨p, hs⟩
      · exact guardedOk_scons hok
  | .inject l t, k, r, σ, w, hg, h => by
      simp only [guardedBy, bne_iff_ne, ne_eq] at hg
      simp only [subst_inject] at h
      have := evaluates_value (.inject _ _) h
      simp only [Term.inject.injEq] at this
      exact (hg this.1.symm).elim
  | .bound _, _, _, _, _, hg, _ | .lam _, _, _, _, _, hg, _ | .app _ _, _, _, _, _, hg, _
  | .mix _ _, _, _, _, _, hg, _ | .fix _ _, _, _, _, _, hg, _ | .specification _ _, _, _, _, _, hg, _
  | .prototype _ _, _, _, _, _, hg, _ | .reflect _, _, _, _, _, hg, _ | .metadata _, _, _, _, _, hg, _
  | .project _, _, _, _, _, hg, _ | .nat _, _, _, _, _, hg, _ | .boolean _, _, _, _, _, hg, _
  | .label _, _, _, _, _, hg, _ | .binary _ _ _, _, _, _, _, hg, _ | .extend _ _, _, _, _, _, hg, _
  | .record _, _, _, _, _, hg, _ | .get _ _, _, _, _, _, hg, _ | .ifZero _ _ _, _, _, _, _, hg, _
  | .perform _, _, _, _, _, hg, _ | .done _, _, _, _, _, hg, _ => by simp [guardedBy] at hg

/-- The arm a case ran is guarded, or is the `relaw` arm of a case on the occasion. -/
public theorem guardedArms_sound {I : Term} (hI : closedB I = true) :
    ∀ {arms : List (String × Term)} {k r : Nat} {occ : Bool} {l : String} {body : Term}
      {σ : Nat → Term} {w : Term},
      guardedArms I k r occ arms = true → arms.find? (fun arm => arm.1 == l) = some (l, body) →
      Evaluates (body.substitute σ) (.inject "ok" w) → (occ = true ∧ l = "relaw") ∨ GuardedOk I k r σ
  | [], _, _, _, _, _, _, _, _, hf, _ => by simp at hf
  | (l', b') :: arms, k, r, occ, l, body, σ, w, hg, hf, hb => by
      simp only [guardedArms, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
      by_cases hl : l' = l
      · subst hl
        simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and] at hf
        subst hf
        rcases hg.1 with ⟨hocc, rfl⟩ | hgb
        · exact .inl ⟨hocc, rfl⟩
        · exact .inr (guardedBy_sound hI hgb hb)
      · have hne : (l' == l) = false := by simp [hl]
        simp only [List.find?_cons, hne] at hf
        exact guardedArms_sound hI hg.2 hf hb
end

/-- **A law in shape that admits keeps the invariant**, on every occasion but a relaw. -/
public theorem keeps_step {I b : Term} {o n rq : Data} (hI : closedB I = true)
    (hg : guardedBy I 1 0 b = true) (h : Admits (law3 b) o n rq)
    (hrel : ∀ x, rq.field "occasion" ≠ some (.variant "relaw" x)) : Keeps I n := by
  obtain ⟨w, hw⟩ := (admits_iff b o n rq).1 h
  rcases guardedBy_sound hI hg hw with hk | ⟨x, hx⟩
  · exact hk
  · obtain ⟨y, hy, -⟩ := get_inject hx
    exact (hrel y hy).elim

/-- **Along the law's history every state keeps the invariant**, once the first does: a relaw
keeps the state (`LawStep`), every other admitted step is `keeps_step`. -/
public theorem chain_keeps {I b : Term} (hI : closedB I = true) (hg : guardedBy I 1 0 b = true) :
    ∀ {o : Data} {steps : List (Data × Data)}, Keeps I o → Chain (LawStep (law3 b)) o steps →
      ∀ s ∈ steps, Keeps I s.2
  | _, [], _, _, _, hs => nomatch hs
  | o, (rq, n) :: _, h0, .cons ⟨hadm, hkeep⟩ hch, s, hs => by
      have hn : Keeps I n := by
        by_cases hr : ∃ x, rq.field "occasion" = some (.variant "relaw" x)
        · obtain ⟨x, hx⟩ := hr
          rw [hkeep x hx]; exact h0
        · exact keeps_step hI hg hadm (fun x hx => hr ⟨x, hx⟩)
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hn
      · exact chain_keeps hI hg hn hch s hs

/-! ## `Std.keeps` is in shape, and what the claim check admits bears the claim -/

public theorem keeps_guarded (S : Ty) (I : Term) : guardedBy I 1 0 (lawBody (keeps S I)) = true := by
  simp [keeps, lawOf, law3, lawBody, lawCase, lawCase6, guard, okT, refusedT, guardedBy, guardedArms,
    isGuardCond, isOccasion, termEq_refl, At.new]

/-- The witness the claim check walked: the invariant is closed, the law is `λ λ λ b`, and `b` is
in certifying shape. -/
public theorem checkClaim_keeps {fields : List (String × Term)} {inv law : String}
    (h : checkClaim fields (.keeps inv law) = true) :
    ∃ I b, fields.lookup inv = some I ∧ fields.lookup law = some (law3 b) ∧ closedB I = true ∧
      guardedBy I 1 0 b = true := by
  simp only [checkClaim] at h
  split at h
  · rename_i I b hi hl
    simp only [Bool.and_eq_true] at h
    exact ⟨I, b, hi, hl, h.1, h.2⟩
  · cases h

/-- **A checked claim is a sentence about the law's history**: if the claim check admits
`keeps inv law`, then along every chain of the named law's steps from a state the named invariant
holds of, it holds of every state. -/
public theorem claim_chain_keeps {fields : List (String × Term)} {inv law : String}
    (h : checkClaim fields (.keeps inv law) = true) :
    ∃ I L, fields.lookup inv = some I ∧ fields.lookup law = some L ∧
      ∀ {o : Data} {steps : List (Data × Data)}, Keeps I o → Chain (LawStep L) o steps →
        ∀ s ∈ steps, Keeps I s.2 := by
  obtain ⟨I, b, hi, hl, hc, hg⟩ := checkClaim_keeps h
  exact ⟨I, law3 b, hi, hl, fun h0 hch => chain_keeps hc hg h0 hch⟩

/-! ## Teeth -/

/-- The run reached a boolean. -/
@[expose] public def boolOf : Option Term → Option Bool
  | some (.boolean b) => some b
  | _ => none

theorem boolOf_eval {t : Term} {b : Bool} (fuel : Nat) (h : boolOf (run fuel t) = some b) :
    Evaluates t (.boolean b) := by
  unfold boolOf at h
  split at h
  · cases h; exact run_sound fuel (by assumption)
  · cases h

/-- `total ≤ 5`. -/
@[expose] public def smallTotal : Term := .lam (leNat (.get (.bound 0) "total") (natT 5))

theorem keeps_tooth :
    checkClaim [("small", smallTotal), ("law", keeps unitTy smallTotal)] (.keeps "small" "law") = true ∧
      checkClaim [("small", smallTotal), ("law", bounded unitTy "total" 5)] (.keeps "small" "law") = false ∧
      checkClaim [("small", smallTotal), ("law", lawOf unitTy (fun _ => okT) (fun _ => okT) (fun _ => okT)
        (fun _ => okT) (fun _ => okT))] (.keeps "small" "law") = false ∧
      checkClaim [("small", .lam (leNat (.get (.bound 1) "total") (natT 5))),
        ("law", keeps unitTy (.lam (leNat (.get (.bound 1) "total") (natT 5))))] (.keeps "small" "law") = false ∧
      Keeps smallTotal (totalIs 5) ∧ ¬ Keeps smallTotal (totalIs 6) ∧ closedB smallTotal = true ∧
      Admits (keeps unitTy smallTotal) (totalIs 0) (totalIs 4) (rqBy "ann" "ann" writeO) ∧
      Refuses (keeps unitTy smallTotal) (totalIs 0) (totalIs 6) (rqBy "ann" "ann" (adoptO "L")) "invariant" :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    boolOf_eval 100 (by decide +kernel),
    fun h => by
      have h' : Evaluates (.app smallTotal (totalIs 6).term) (.boolean false) := boolOf_eval 100 (by decide +kernel)
      have := evaluates_unique h h'
      simp at this,
    by decide +kernel,
    admits_of_run 200 (by decide +kernel), refuses_of_run 200 (by decide +kernel)⟩

end Obend.Law
