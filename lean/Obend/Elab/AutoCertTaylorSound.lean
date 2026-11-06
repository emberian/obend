module
public import Obend.Elab.AutoCert
public import Obend.Analysis.TaylorModel
/-!
# What an accepted `taylor-model@1` certificate means

`taylorModelJudge.Meaning` (`Obend.Elab.AutoCert`) is computational: the certificate is the Taylor
model `evalTaylorModelExpr` computes, and its range lies inside the claimed bound. This file proves
what that says about functions, for the fragment of `TaylorModelExpr` that is polynomial arithmetic in
the variable plus `sin`/`cos` of the variable (`polyTrig`), at center `0`:

* `evalTaylorModelExpr_models`: the computed model encloses the expression's denotation, where
  `sin`/`cos` are those of any `AnalyticModel` (any pair of functions satisfying the Taylor–Lagrange
  remainder bounds the real functions satisfy);
* `taylorModelJudge_semantic`: if the judge accepts `(q, tm)`, then for every `x` in `q.domain` the
  expression's value at `x` lies in `q.claimedBound`.
-/
@[expose] public section

namespace Obend.Elab.AutoCert

open Obend.Analysis

set_option autoImplicit false

/-- Polynomial arithmetic in the variable, and `sin`/`cos` applied to the variable itself. -/
def TaylorModelExpr.polyTrig : TaylorModelExpr → Bool
  | .var => true
  | .const _ => true
  | .add a b => a.polyTrig && b.polyTrig
  | .sub a b => a.polyTrig && b.polyTrig
  | .scale _ a => a.polyTrig
  | .mul a b => a.polyTrig && b.polyTrig
  | .sin .var => true
  | .cos .var => true
  | _ => false

/-- The function a `polyTrig` expression denotes, with `sin`/`cos` from an `AnalyticModel`
(`0` outside the fragment). -/
def TaylorModelExpr.denote (R : Type) [M : AnalyticModel R] : TaylorModelExpr → CanonicalRat → CanonicalRat
  | .var => fun x => x
  | .const c => fun _ => c
  | .add a b => fun x => a.denote R x + b.denote R x
  | .sub a b => fun x => a.denote R x - b.denote R x
  | .scale c a => fun x => c * a.denote R x
  | .mul a b => fun x => a.denote R x * b.denote R x
  | .sin .var => M.sinFn
  | .cos .var => M.cosFn
  | _ => fun _ => 0

theorem isSubintervalOf_subset (a b : Interval) (h : a.isSubintervalOf b = true) : Interval.subset a b = true := by
  simpa [Interval.isSubintervalOf, Interval.subset] using h

/-- **Soundness of `evalTaylorModelExpr` on the polynomial–trigonometric fragment.** -/
theorem evalTaylorModelExpr_models (R : Type) [M : AnalyticModel R] (dom : Interval) (deg : Nat) :
    ∀ (e : TaylorModelExpr), e.polyTrig = true → ∀ tm, evalTaylorModelExpr dom 0 deg e = some tm →
      tm.center = 0 ∧ tm.domain = dom ∧ TaylorModel.Models (e.denote R) tm := by
  intro e
  induction e with
  | var =>
    intro _ tm h
    simp only [evalTaylorModelExpr, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, TaylorModel.var_models 0 dom⟩
  | const c =>
    intro _ tm h
    simp only [evalTaylorModelExpr, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, TaylorModel.const_models c 0 dom⟩
  | add a b iha ihb =>
    intro hf tm h
    simp only [TaylorModelExpr.polyTrig, Bool.and_eq_true] at hf
    simp only [evalTaylorModelExpr, bind, Option.bind] at h
    cases ha : evalTaylorModelExpr dom 0 deg a with
    | none => rw [ha] at h; contradiction
    | some ta =>
      rw [ha] at h
      cases hb : evalTaylorModelExpr dom 0 deg b with
      | none => rw [hb] at h; contradiction
      | some tb =>
        rw [hb] at h
        simp only [pure, Option.some.injEq] at h; subst h
        obtain ⟨ca, da, ma⟩ := iha hf.1 ta ha
        obtain ⟨cb, db, mb⟩ := ihb hf.2 tb hb
        exact ⟨ca, da, TaylorModel.add_models (by rw [ca, cb]) (by rw [da, db]) ma mb⟩
  | sub a b iha ihb =>
    intro hf tm h
    simp only [TaylorModelExpr.polyTrig, Bool.and_eq_true] at hf
    simp only [evalTaylorModelExpr, bind, Option.bind] at h
    cases ha : evalTaylorModelExpr dom 0 deg a with
    | none => rw [ha] at h; contradiction
    | some ta =>
      rw [ha] at h
      cases hb : evalTaylorModelExpr dom 0 deg b with
      | none => rw [hb] at h; contradiction
      | some tb =>
        rw [hb] at h
        simp only [pure, Option.some.injEq] at h; subst h
        obtain ⟨ca, da, ma⟩ := iha hf.1 ta ha
        obtain ⟨cb, db, mb⟩ := ihb hf.2 tb hb
        exact ⟨ca, da, TaylorModel.sub_models (by rw [ca, cb]) (by rw [da, db]) ma mb⟩
  | scale c a iha =>
    intro hf tm h
    simp only [TaylorModelExpr.polyTrig] at hf
    simp only [evalTaylorModelExpr, bind, Option.bind] at h
    cases ha : evalTaylorModelExpr dom 0 deg a with
    | none => rw [ha] at h; contradiction
    | some ta =>
      rw [ha] at h
      simp only [pure, Option.some.injEq] at h; subst h
      obtain ⟨ca, da, ma⟩ := iha hf ta ha
      exact ⟨ca, da, TaylorModel.scale_models c ma⟩
  | mul a b iha ihb =>
    intro hf tm h
    simp only [TaylorModelExpr.polyTrig, Bool.and_eq_true] at hf
    simp only [evalTaylorModelExpr, bind, Option.bind] at h
    cases ha : evalTaylorModelExpr dom 0 deg a with
    | none => rw [ha] at h; contradiction
    | some ta =>
      rw [ha] at h
      cases hb : evalTaylorModelExpr dom 0 deg b with
      | none => rw [hb] at h; contradiction
      | some tb =>
        rw [hb] at h
        simp only [pure, Option.some.injEq] at h; subst h
        obtain ⟨ca, da, ma⟩ := iha hf.1 ta ha
        obtain ⟨cb, db, mb⟩ := ihb hf.2 tb hb
        refine ⟨?_, ?_, TaylorModel.mul_models deg (by rw [ca, cb]) (by rw [da, db]) ma mb⟩
        · simp [tmMul, ca]
        · simp [tmMul, TaylorModel.deltaDomain, da]
  | exp a _ => intro hf; cases a <;> simp [TaylorModelExpr.polyTrig] at hf
  | ln1p a _ => intro hf; cases a <;> simp [TaylorModelExpr.polyTrig] at hf
  | sqrt1p a _ => intro hf; cases a <;> simp [TaylorModelExpr.polyTrig] at hf
  | sin a _ =>
    intro hf tm h
    cases a <;> simp [TaylorModelExpr.polyTrig] at hf
    simp only [evalTaylorModelExpr] at h
    split at h
    · rename_i hsub
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
      have hs := isSubintervalOf_subset _ _ hsub
      refine ⟨?_, ?_, tmSinCertified_models R dom hs⟩ <;> unfold tmSinCertified <;> split <;> rfl
    · contradiction
  | cos a _ =>
    intro hf tm h
    cases a <;> simp [TaylorModelExpr.polyTrig] at hf
    simp only [evalTaylorModelExpr] at h
    split at h
    · rename_i hsub
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
      have hs := isSubintervalOf_subset _ _ hsub
      refine ⟨?_, ?_, tmCosCertified_models R dom hs⟩ <;> unfold tmCosCertified <;> split <;> rfl
    · contradiction

/-- **What the `taylor-model@1` judge's acceptance means.** For a `polyTrig` query at center `0`,
an accepted certificate establishes that the expression, with `sin`/`cos` of any `AnalyticModel`,
takes values in the claimed bound at every point of the domain. -/
theorem taylorModelJudge_semantic (R : Type) [AnalyticModel R] (grade : Nat) (q : TaylorModelQuery)
    (tm : TaylorModel) (hc : q.center = 0) (hf : q.expr.polyTrig = true)
    (h : checkTaylorModelJudge grade q tm = .ok) :
    ∀ x, x ∈ q.domain → q.expr.denote R x ∈ q.claimedBound := by
  intro x hx
  obtain ⟨hv, hrange⟩ := checkTaylorModelJudge_sound grade q tm h
  unfold verifyTaylorModelCert at hv
  rw [hc] at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨⟨_, _⟩, _⟩, hm⟩ := hv
  cases he : evalTaylorModelExpr q.domain 0 q.degree q.expr with
  | none => rw [he] at hm; simp at hm
  | some comp =>
    rw [he] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨heq, _⟩ := hm
    subst heq
    obtain ⟨_, hdom, hmod⟩ := evalTaylorModelExpr_models R q.domain q.degree q.expr hf comp he
    have hx' : x ∈ comp.domain := by rw [hdom]; exact hx
    have hin := evalTaylorModelRange_encloses hmod hx'
    exact Interval.subset_sound (isSubintervalOf_subset _ _ hrange) hin

end Obend.Elab.AutoCert
