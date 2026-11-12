module
/-
# Obend.SymbolicZk.CompileToPiop — `Lookup` LogUp Weld, Multilinear Schwartz–Zippel & `Sumcheck` Compiler

Completes the `Lookup + LinMem + Before` → Multilinear PIOP & `Sumcheck` cryptographic weld on top of
`Obend.SymbolicZk.CompileToPiopCore`:
1. `Lookup` LogUp rational-fraction & inverse-free cleared-polynomial weld
   (`logUpFrac_iff_clearedPoly`, `logUpIdentity_complete`, `logUpIdentity_implies_lookup`) via
   constructive Cauchy residue extraction over `Goldilocks`.
2. `eqPoly`-weighted hypercube batching (`hypercubeSum_eqWeightedTable_eq_mleEval`), constructive
   multilinear Schwartz–Zippel grid bound (`mle_schwartzZippel_grid_bound`), and end-to-end
   `Sumcheck` compiler (`compileSymbolicTraceToSumcheck_complete` & `compileSymbolicTraceToSumcheck_sound`).
-/
public import Obend.SymbolicZk.CompileToPiopCore
import all Obend.SymbolicZk.CompileToPiopCore
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Crypto.Sumcheck

public section
namespace Obend.SymbolicZk.CompileToPiop

open Obend.Apps.ZkNtt (goldilocksPrime)
open Obend.Core.RangeSafe
open Obend.Crypto

set_option autoImplicit false

/-! ## 1. `Lookup` LogUp Logarithmic-Derivative Weld (`logUpIdentity_implies_lookup`) -/

def natToRing {R : Type} [CommRingOps R] : Nat → R
  | 0 => CommRingOps.zero
  | n + 1 => CommRingOps.add CommRingOps.one (natToRing n)

private theorem natToRing_add {R : Type} [LawfulCommRing R] :
    ∀ (a b : Nat), natToRing (R := R) (a + b) = CommRingOps.add (natToRing a) (natToRing b)
  | 0, _ => by simp [natToRing, LawfulCommRing.zero_add]
  | a + 1, b => by rw [Nat.succ_add, natToRing, natToRing, natToRing_add a b, LawfulCommRing.add_assoc]

theorem natToRing_goldilocks (n : Nat) : natToRing (R := Goldilocks) n = Goldilocks.ofNat n := by
  induction n with
  | zero => apply Goldilocks.ext; rfl
  | succ k ih =>
    simp only [natToRing, ih]
    have h1 : (CommRingOps.one : Goldilocks) = Goldilocks.ofNat 1 := by apply Goldilocks.ext; decide
    rw [h1, ← goldilocks_ofNat_add, Nat.add_comm]

def polyAddCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], qs => qs
  | ps, [] => ps
  | c :: cs, d :: ds => CommRingOps.add c d :: polyAddCoeffs cs ds

def polyAdd {R : Type} [CommRingOps R] (p q : RoundPoly R) : RoundPoly R :=
  ⟨polyAddCoeffs p.coeffs q.coeffs⟩

def polyScale {R : Type} [CommRingOps R] (s : R) (p : RoundPoly R) : RoundPoly R :=
  ⟨p.coeffs.map (CommRingOps.mul s)⟩

def polyMulCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], _ => []
  | c :: cs, qs => polyAddCoeffs (qs.map (CommRingOps.mul c)) (CommRingOps.zero :: polyMulCoeffs cs qs)

def polyMul {R : Type} [CommRingOps R] (p q : RoundPoly R) : RoundPoly R :=
  ⟨polyMulCoeffs p.coeffs q.coeffs⟩

theorem polyAddCoeffs_length_le {R : Type} [CommRingOps R] :
    ∀ (ps qs : List R), (polyAddCoeffs ps qs).length ≤ max ps.length qs.length
  | [], _ => by simp [polyAddCoeffs]
  | _ :: _, [] => by simp [polyAddCoeffs]
  | _ :: cs, _ :: ds => by have ih := polyAddCoeffs_length_le cs ds; simp only [polyAddCoeffs, List.length_cons]; omega

theorem evalCoeffs_add {R : Type} [LawfulCommRing R] :
    ∀ (ps qs : List R) (x : R),
      RoundPoly.evalCoeffs (polyAddCoeffs ps qs) x =
        CommRingOps.add (RoundPoly.evalCoeffs ps x) (RoundPoly.evalCoeffs qs x)
  | [], _, _ => by simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | _ :: _, [], _ => by simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | _ :: cs, _ :: ds, x => by
    simp only [polyAddCoeffs, RoundPoly.evalCoeffs, evalCoeffs_add cs ds x,
      LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem eval_polyAdd {R : Type} [LawfulCommRing R] (p q : RoundPoly R) (x : R) :
    (polyAdd p q).eval x = CommRingOps.add (p.eval x) (q.eval x) := evalCoeffs_add p.coeffs q.coeffs x

theorem evalCoeffs_scale {R : Type} [LawfulCommRing R] (s x : R) :
    ∀ ps : List R, RoundPoly.evalCoeffs (ps.map (CommRingOps.mul s)) x = CommRingOps.mul s (RoundPoly.evalCoeffs ps x)
  | [] => by simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | _ :: cs => by
    simp only [List.map_cons, RoundPoly.evalCoeffs, evalCoeffs_scale s x cs, LawfulCommRing.left_distrib]
    congr 1; rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x s, LawfulCommRing.mul_assoc]

theorem eval_polyScale {R : Type} [LawfulCommRing R] (s : R) (p : RoundPoly R) (x : R) :
    (polyScale s p).eval x = CommRingOps.mul s (p.eval x) := evalCoeffs_scale s x p.coeffs

theorem polyMulCoeffs_length_le {R : Type} [CommRingOps R] :
    ∀ {ps qs : List R} {A B : Nat},
      ps.length ≤ A → qs.length ≤ B + 1 → (polyMulCoeffs ps qs).length ≤ A + B
  | [], _, _, _, _, _ => Nat.zero_le _
  | _ :: _, _, 0, _, hA, _ => by simp at hA
  | c :: cs, qs, A + 1, _, hA, hB => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hA
    have hadd := polyAddCoeffs_length_le (qs.map (CommRingOps.mul c)) (CommRingOps.zero :: polyMulCoeffs cs qs)
    have ih := polyMulCoeffs_length_le hA hB
    simp only [List.length_map, List.length_cons] at hadd; simp only [polyMulCoeffs]; omega

theorem evalCoeffs_mul {R : Type} [LawfulCommRing R] :
    ∀ (ps qs : List R) (x : R),
      RoundPoly.evalCoeffs (polyMulCoeffs ps qs) x =
        CommRingOps.mul (RoundPoly.evalCoeffs ps x) (RoundPoly.evalCoeffs qs x)
  | [], _, _ => by simp [polyMulCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | _ :: cs, qs, x => by
    simp only [polyMulCoeffs, evalCoeffs_add, evalCoeffs_scale, RoundPoly.evalCoeffs,
      evalCoeffs_mul cs qs x, LawfulCommRing.zero_add, LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc]

theorem eval_polyMul {R : Type} [LawfulCommRing R] (p q : RoundPoly R) (x : R) :
    (polyMul p q).eval x = CommRingOps.mul (p.eval x) (q.eval x) := evalCoeffs_mul p.coeffs q.coeffs x

def logUpTableFracSum {F : Type} [LawfulField F] (γ : F) : List (F × Nat) → F
  | [] => CommRingOps.zero
  | (t, m) :: rest =>
    CommRingOps.add (CommRingOps.mul (natToRing m) (LawfulField.inv (CommRingOps.sub γ t)))
      (logUpTableFracSum γ rest)

def logUpQueryFracSum {F : Type} [LawfulField F] (γ : F) : List F → F
  | [] => CommRingOps.zero
  | q :: qs => CommRingOps.add (LawfulField.inv (CommRingOps.sub γ q)) (logUpQueryFracSum γ qs)

def logUpTablePoly {R : Type} [CommRingOps R] : List (R × Nat) → RoundPoly R × RoundPoly R
  | [] => (⟨[]⟩, ⟨[CommRingOps.one]⟩)
  | (t, m) :: rest =>
    let (num, den) := logUpTablePoly rest
    (polyAdd (polyScale (natToRing m) den) (mulLinFactor t num), mulLinFactor t den)

def logUpQueryPoly {R : Type} [CommRingOps R] : List R → RoundPoly R × RoundPoly R
  | [] => (⟨[]⟩, ⟨[CommRingOps.one]⟩)
  | q :: qs =>
    let (num, den) := logUpQueryPoly qs
    (polyAdd den (mulLinFactor q num), mulLinFactor q den)

def logUpTableEvalArray {R : Type} [CommRingOps R] (table : Array R) (mults : Array Nat) (γ : R) : R × R :=
  (table.zip mults).foldr
    (fun (t, m) (num, den) =>
      let dt := CommRingOps.sub γ t
      (CommRingOps.add (CommRingOps.mul (natToRing m) den) (CommRingOps.mul dt num), CommRingOps.mul dt den))
    (CommRingOps.zero, CommRingOps.one)

def logUpQueryEvalArray {R : Type} [CommRingOps R] (queries : Array R) (γ : R) : R × R :=
  queries.foldr
    (fun q (num, den) =>
      let dq := CommRingOps.sub γ q
      (CommRingOps.add den (CommRingOps.mul dq num), CommRingOps.mul dq den))
    (CommRingOps.zero, CommRingOps.one)

theorem logUpTablePoly_den_eq_charPoly {R : Type} [CommRingOps R] :
    ∀ pairs : List (R × Nat), (logUpTablePoly pairs).2 = charPoly (pairs.map Prod.fst)
  | [] => by simp [logUpTablePoly]
  | (_, _) :: rest => by simp [logUpTablePoly, logUpTablePoly_den_eq_charPoly rest]

theorem logUpQueryPoly_den_eq_charPoly {R : Type} [CommRingOps R] :
    ∀ qs : List R, (logUpQueryPoly qs).2 = charPoly qs
  | [] => by simp [logUpQueryPoly]
  | _ :: qs => by simp [logUpQueryPoly, logUpQueryPoly_den_eq_charPoly qs]

theorem logUpTablePoly_num_length {R : Type} [CommRingOps R] :
    ∀ pairs : List (R × Nat), (logUpTablePoly pairs).1.coeffs.length ≤ pairs.length
  | [] => Nat.zero_le _
  | (t, m) :: rest => by
    simp only [logUpTablePoly, List.length_cons, polyAdd]
    have hadd := polyAddCoeffs_length_le
      (polyScale (natToRing m) (logUpTablePoly rest).2).coeffs (mulLinFactor t (logUpTablePoly rest).1).coeffs
    have hden : (logUpTablePoly rest).2.coeffs.length = rest.length + 1 := by
      rw [logUpTablePoly_den_eq_charPoly, charPoly_length, List.length_map]
    have ih := logUpTablePoly_num_length rest
    simp only [polyScale, List.length_map, hden, mulLinFactor_length] at hadd ⊢; omega

theorem logUpQueryPoly_num_length {R : Type} [CommRingOps R] :
    ∀ qs : List R, (logUpQueryPoly qs).1.coeffs.length ≤ qs.length
  | [] => Nat.zero_le _
  | q :: qs => by
    simp only [logUpQueryPoly, List.length_cons, polyAdd]
    have hadd := polyAddCoeffs_length_le (logUpQueryPoly qs).2.coeffs (mulLinFactor q (logUpQueryPoly qs).1).coeffs
    have hden : (logUpQueryPoly qs).2.coeffs.length = qs.length + 1 := by
      rw [logUpQueryPoly_den_eq_charPoly, charPoly_length]
    have ih := logUpQueryPoly_num_length qs
    simp only [hden, mulLinFactor_length] at hadd ⊢; omega

theorem logUpTableEvalArray_eq_spec {R : Type} [LawfulCommRing R]
    (table : Array R) (mults : Array Nat) (γ : R) :
    let (nP, dP) := logUpTablePoly (table.toList.zip mults.toList)
    logUpTableEvalArray table mults γ = (nP.eval γ, dP.eval γ) := by
  unfold logUpTableEvalArray; rw [← Array.foldr_toList, Array.toList_zip]
  induction table.toList.zip mults.toList with
  | nil => simp [logUpTablePoly, RoundPoly.eval, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | cons hd tl ih =>
    rcases hd with ⟨t, m⟩; dsimp only at ih ⊢
    simp only [List.foldr_cons, logUpTablePoly, ih, eval_polyAdd, eval_polyScale, eval_mulLinFactor]

theorem logUpQueryEvalArray_eq_spec {R : Type} [LawfulCommRing R] (queries : Array R) (γ : R) :
    let (nP, dP) := logUpQueryPoly queries.toList
    logUpQueryEvalArray queries γ = (nP.eval γ, dP.eval γ) := by
  unfold logUpQueryEvalArray; rw [← Array.foldr_toList]
  induction queries.toList with
  | nil => simp [logUpQueryPoly, RoundPoly.eval, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | cons q qs ih =>
    dsimp only at ih ⊢; simp only [List.foldr_cons, logUpQueryPoly, ih, eval_polyAdd, eval_mulLinFactor]

theorem logUpTableFrac_eq_num_div_den {F : Type} [LawfulField F] (γ : F) :
    ∀ (pairs : List (F × Nat)), (∀ p ∈ pairs, γ ≠ p.1) →
      CommRingOps.mul (logUpTableFracSum γ pairs) ((logUpTablePoly pairs).2.eval γ) =
        (logUpTablePoly pairs).1.eval γ
  | [], _ => by simp [logUpTableFracSum, logUpTablePoly, RoundPoly.eval, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | (t, m) :: rest, hnoPole => by
    simp only [logUpTableFracSum, logUpTablePoly, eval_mulLinFactor, eval_polyAdd, eval_polyScale]
    have hgt : CommRingOps.sub γ t ≠ CommRingOps.zero :=
      fun h0 => hnoPole (t, m) List.mem_cons_self ((LawfulIntegralDomain.sub_eq_zero_iff γ t).mp h0)
    have ih := logUpTableFrac_eq_num_div_den γ rest (fun p hp => hnoPole p (List.mem_cons_of_mem _ hp))
    rw [LawfulCommRing.right_distrib]; congr 1
    · rw [← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_assoc (natToRing m) (LawfulField.inv (CommRingOps.sub γ t)) (CommRingOps.sub γ t),
          LawfulCommRing.mul_comm (LawfulField.inv (CommRingOps.sub γ t)) (CommRingOps.sub γ t),
          LawfulField.mul_inv_cancel _ hgt, LawfulCommRing.mul_one]
    · rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (logUpTableFracSum γ rest) _, LawfulCommRing.mul_assoc, ih]

theorem logUpQueryFrac_eq_num_div_den {F : Type} [LawfulField F] (γ : F) :
    ∀ (qs : List F), (∀ q ∈ qs, γ ≠ q) →
      CommRingOps.mul (logUpQueryFracSum γ qs) ((logUpQueryPoly qs).2.eval γ) =
        (logUpQueryPoly qs).1.eval γ
  | [], _ => by simp [logUpQueryFracSum, logUpQueryPoly, RoundPoly.eval, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | q :: qs, hnoPole => by
    simp only [logUpQueryFracSum, logUpQueryPoly, eval_mulLinFactor, eval_polyAdd]
    have hgq : CommRingOps.sub γ q ≠ CommRingOps.zero :=
      fun h0 => hnoPole q List.mem_cons_self ((LawfulIntegralDomain.sub_eq_zero_iff γ q).mp h0)
    have ih := logUpQueryFrac_eq_num_div_den γ qs (fun y hy => hnoPole y (List.mem_cons_of_mem _ hy))
    rw [LawfulCommRing.right_distrib]; congr 1
    · rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (LawfulField.inv _) _,
          LawfulField.mul_inv_cancel _ hgq, LawfulCommRing.one_mul]
    · rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (logUpQueryFracSum γ qs) _, LawfulCommRing.mul_assoc, ih]

/-- **Rational Fraction $\leftrightarrow$ Cleared Polynomial LogUp Equivalence (`logUpFrac_iff_clearedPoly`)**. -/
theorem logUpFrac_iff_clearedPoly {F : Type} [LawfulField F]
    (γ : F) (T : List F) (M : List Nat) (Q : List F)
    (hLen : M.length = T.length) (hNoPoleT : ∀ t ∈ T, γ ≠ t) (hNoPoleQ : ∀ q ∈ Q, γ ≠ q) :
    let (nT, dT) := logUpTablePoly (T.zip M)
    let (nQ, dQ) := logUpQueryPoly Q
    logUpTableFracSum γ (T.zip M) = logUpQueryFracSum γ Q ↔
      CommRingOps.mul (nT.eval γ) (dQ.eval γ) = CommRingOps.mul (nQ.eval γ) (dT.eval γ) := by
  dsimp only
  have hMapFst : (T.zip M).map Prod.fst = T := List.map_fst_zip (by omega)
  have hNoPoleZip : ∀ p ∈ T.zip M, γ ≠ p.1 := fun p hp => hNoPoleT p.1 (hMapFst ▸ List.mem_map_of_mem hp)
  have hdTNe : (logUpTablePoly (T.zip M)).2.eval γ ≠ CommRingOps.zero := by
    rw [logUpTablePoly_den_eq_charPoly, hMapFst]
    exact fun hz => hNoPoleT γ ((charPoly_eval_eq_zero_iff γ T).mp hz) rfl
  have hdQNe : (logUpQueryPoly Q).2.eval γ ≠ CommRingOps.zero := by
    rw [logUpQueryPoly_den_eq_charPoly]
    exact fun hz => hNoPoleQ γ ((charPoly_eval_eq_zero_iff γ Q).mp hz) rfl
  have hT := logUpTableFrac_eq_num_div_den γ (T.zip M) hNoPoleZip
  have hQ := logUpQueryFrac_eq_num_div_den γ Q hNoPoleQ
  constructor
  · intro hEq; rw [← hT, ← hQ, hEq, LawfulCommRing.mul_assoc,
      LawfulCommRing.mul_comm ((logUpTablePoly (T.zip M)).2.eval γ), ← LawfulCommRing.mul_assoc]
  · intro hCross; rw [← hT, ← hQ] at hCross
    have hCross' : CommRingOps.mul (CommRingOps.mul (logUpTableFracSum γ (T.zip M)) ((logUpQueryPoly Q).2.eval γ))
        ((logUpTablePoly (T.zip M)).2.eval γ) =
        CommRingOps.mul (CommRingOps.mul (logUpQueryFracSum γ Q) ((logUpQueryPoly Q).2.eval γ))
        ((logUpTablePoly (T.zip M)).2.eval γ) := by
      rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm ((logUpQueryPoly Q).2.eval γ),
          ← LawfulCommRing.mul_assoc, hCross]
    exact LawfulIntegralDomain.mul_right_cancel hdQNe (LawfulIntegralDomain.mul_right_cancel hdTNe hCross')

private theorem logUpTablePoly_zero_mults_eval {R : Type} [LawfulCommRing R] (γ : R) :
    ∀ T : List R, (logUpTablePoly (T.map fun t => (t, 0))).1.eval γ = CommRingOps.zero
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, logUpTablePoly, eval_polyAdd, eval_polyScale, eval_mulLinFactor,
      natToRing, LawfulCommRing.zero_mul, logUpTablePoly_zero_mults_eval γ ts,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem logUpTablePoly_bump_one {R : Type} [LawfulCommRing R] [DecidableEq R]
    (q γ : R) (f : R → Nat) :
    ∀ (T : List R), T.Nodup → q ∈ T →
      CommRingOps.mul (CommRingOps.sub γ q)
        ((logUpTablePoly (T.map fun t => (t, if t = q then f t + 1 else f t))).1.eval γ) =
      CommRingOps.add ((charPoly T).eval γ)
        (CommRingOps.mul (CommRingOps.sub γ q)
          ((logUpTablePoly (T.map fun t => (t, f t))).1.eval γ))
  | [], _, hq => nomatch hq
  | t₀ :: ts, hNd, hq => by
    rw [List.nodup_cons] at hNd
    by_cases htq : t₀ = q
    · subst htq
      have htsEq : (ts.map fun t => (t, if t = t₀ then f t + 1 else f t)) = ts.map (fun t => (t, f t)) :=
        List.map_congr_left fun t ht => by have hne : t ≠ t₀ := fun he => hNd.1 (he ▸ ht); simp [hne]
      simp only [List.map_cons, ↓reduceIte, htsEq, logUpTablePoly, eval_polyAdd, eval_polyScale,
        eval_mulLinFactor, logUpTablePoly_den_eq_charPoly, charPoly_cons]
      have hMapFst : (ts.map fun t => (t, f t)).map Prod.fst = ts := by simp [Function.comp_def]
      rw [hMapFst]
      change CommRingOps.mul (CommRingOps.sub γ t₀)
        (CommRingOps.add (CommRingOps.mul (CommRingOps.add CommRingOps.one (natToRing (f t₀))) ((charPoly ts).eval γ))
          (CommRingOps.mul (CommRingOps.sub γ t₀) ((logUpTablePoly (ts.map fun t => (t, f t))).1.eval γ))) = _
      rw [LawfulCommRing.right_distrib, LawfulCommRing.one_mul, LawfulCommRing.add_assoc, LawfulCommRing.left_distrib]
    · have hqTs : q ∈ ts := (List.mem_cons.mp hq).resolve_left (Ne.symm htq)
      have ih := logUpTablePoly_bump_one q γ f ts hNd.2 hqTs
      have htq' : ¬ (t₀ = q) := htq
      simp only [List.map_cons, htq', ↓reduceIte, logUpTablePoly, eval_polyAdd, eval_polyScale,
        eval_mulLinFactor, logUpTablePoly_den_eq_charPoly, charPoly_cons]
      have hFst1 : (ts.map fun t => (t, if t = q then f t + 1 else f t)).map Prod.fst = ts := by simp [Function.comp_def]
      have hFst2 : (ts.map fun t => (t, f t)).map Prod.fst = ts := by simp [Function.comp_def]
      rw [hFst1, hFst2, LawfulCommRing.left_distrib]
      have hComm : CommRingOps.mul (CommRingOps.sub γ q)
          (CommRingOps.mul (CommRingOps.sub γ t₀)
            ((logUpTablePoly (ts.map fun t => (t, if t = q then f t + 1 else f t))).1.eval γ)) =
          CommRingOps.mul (CommRingOps.sub γ t₀)
            (CommRingOps.mul (CommRingOps.sub γ q)
              ((logUpTablePoly (ts.map fun t => (t, if t = q then f t + 1 else f t))).1.eval γ)) := by
        rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub γ q), LawfulCommRing.mul_assoc]
      rw [hComm, ih, LawfulCommRing.left_distrib]
      rw [LawfulCommRing.add_comm (CommRingOps.mul (CommRingOps.sub γ q) _)
            (CommRingOps.add (CommRingOps.mul (CommRingOps.sub γ t₀) ((charPoly ts).eval γ)) _),
          LawfulCommRing.add_assoc, LawfulCommRing.left_distrib]
      congr 1; rw [LawfulCommRing.add_comm]; congr 1
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub γ t₀), LawfulCommRing.mul_assoc]

private theorem zip_map_self {α β : Type} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map (fun a => (a, f a))
  | [] => rfl
  | a :: as => by simp only [List.map_cons, List.zip_cons_cons, zip_map_self f as]

private theorem logUpTablePoly_map_den {R : Type} [CommRingOps R] (T : List R) (f : R → Nat) :
    (logUpTablePoly (T.map fun t => (t, f t))).2 = charPoly T := by
  rw [logUpTablePoly_den_eq_charPoly]; congr 1; simp [Function.comp_def]

/-- **Honest LogUp Cleared-Polynomial Completeness (`logUpIdentity_complete`)**. -/
theorem logUpIdentity_complete {R : Type} [LawfulCommRing R] [DecidableEq R]
    (T Q : List R) (hNd : T.Nodup) (hSub : ∀ q ∈ Q, q ∈ T) (γ : R) :
    let (nT, dT) := logUpTablePoly (T.zip (T.map (fun t => Q.count t)))
    let (nQ, dQ) := logUpQueryPoly Q
    CommRingOps.mul (nT.eval γ) (dQ.eval γ) = CommRingOps.mul (nQ.eval γ) (dT.eval γ) := by
  dsimp only; rw [zip_map_self, logUpTablePoly_map_den]
  induction Q with
  | nil =>
    have h0 : (T.map fun t => (t, ([] : List R).count t)) = T.map (fun t => (t, 0)) := by simp
    rw [h0, logUpTablePoly_zero_mults_eval]
    simp [logUpQueryPoly, RoundPoly.eval, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | cons q qs ih =>
    have hqT : q ∈ T := hSub q List.mem_cons_self
    have ih' := ih (fun y hy => hSub y (List.mem_cons_of_mem q hy))
    have hCountMap : (T.map fun t => (t, (q :: qs).count t)) =
        T.map (fun t => (t, if t = q then qs.count t + 1 else qs.count t)) := by
      apply List.map_congr_left; intro t _
      by_cases htq : t = q
      · subst htq; simp [List.count_cons_self]
      · simp [htq, List.count_cons_of_ne (Ne.symm htq)]
    rw [hCountMap]; simp only [logUpQueryPoly, eval_mulLinFactor, eval_polyAdd]
    rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm _ (CommRingOps.sub γ q),
        logUpTablePoly_bump_one q γ (fun t => qs.count t) T hNd hqT, LawfulCommRing.right_distrib,
        LawfulCommRing.mul_comm ((charPoly T).eval γ) ((logUpQueryPoly qs).2.eval γ),
        LawfulCommRing.mul_assoc (CommRingOps.sub γ q), ih', ← LawfulCommRing.mul_assoc,
        ← LawfulCommRing.right_distrib]

private def sumMultAt {F : Type} [DecidableEq F] (z : F) : List (F × Nat) → Nat
  | [] => 0
  | (t, m) :: rest => (if t = z then m else 0) + sumMultAt z rest

private theorem sumMultAt_of_not_mem {F : Type} [DecidableEq F] (z : F) :
    ∀ (pairs : List (F × Nat)), z ∉ pairs.map Prod.fst → sumMultAt z pairs = 0
  | [], _ => rfl
  | (t, _) :: rest, hnm => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnm
    have hne : t ≠ z := Ne.symm hnm.1
    simp [sumMultAt, hne, sumMultAt_of_not_mem z rest hnm.2]

private theorem sumMultAt_of_nodup_mem {F : Type} [DecidableEq F] (z : F) (m : Nat) :
    ∀ (pairs : List (F × Nat)), (pairs.map Prod.fst).Nodup → (z, m) ∈ pairs → sumMultAt z pairs = m
  | [], _, hm => nomatch hm
  | (t₀, m₀) :: rest, hNd, hm => by
    simp only [List.map_cons, List.nodup_cons] at hNd
    rcases List.mem_cons.mp hm with hEq | hRest
    · cases hEq; simp [sumMultAt, sumMultAt_of_not_mem z rest hNd.1]
    · have hzMem : z ∈ rest.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hRest
      have hne : t₀ ≠ z := fun he => hNd.1 (he ▸ hzMem)
      simp [sumMultAt, hne, sumMultAt_of_nodup_mem z m rest hNd.2 hRest]

private theorem logUpTableFracSum_residue_split {F : Type} [LawfulField F] [DecidableEq F]
    (z γ : F) (hgz : CommRingOps.sub γ z ≠ CommRingOps.zero) :
    ∀ (pairs : List (F × Nat)),
      CommRingOps.mul (CommRingOps.sub γ z) (logUpTableFracSum γ pairs) =
        CommRingOps.add (natToRing (sumMultAt z pairs))
          (CommRingOps.mul (CommRingOps.sub γ z)
            (logUpTableFracSum γ (pairs.filter fun p => decide (p.1 ≠ z))))
  | [] => by simp [logUpTableFracSum, sumMultAt, natToRing, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | (t, m) :: rest => by
    have ih := logUpTableFracSum_residue_split z γ hgz rest
    by_cases htz : t = z
    · subst htz
      simp only [logUpTableFracSum, sumMultAt, ↓reduceIte, List.filter_cons, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, LawfulCommRing.left_distrib, ih, natToRing_add]
      rw [LawfulCommRing.add_assoc]; congr 1
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub γ t) (natToRing m),
          LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel _ hgz, LawfulCommRing.mul_one]
    · simp only [logUpTableFracSum, sumMultAt, htz, ↓reduceIte, Nat.zero_add, List.filter_cons,
        ne_eq, not_false_eq_true, decide_true, LawfulCommRing.left_distrib, ih]
      rw [← LawfulCommRing.add_assoc, LawfulCommRing.add_comm _ (natToRing (sumMultAt z rest)),
          LawfulCommRing.add_assoc]

private theorem logUpQueryFracSum_residue_split {F : Type} [LawfulField F] [DecidableEq F]
    (z γ : F) (hgz : CommRingOps.sub γ z ≠ CommRingOps.zero) :
    ∀ (qs : List F),
      CommRingOps.mul (CommRingOps.sub γ z) (logUpQueryFracSum γ qs) =
        CommRingOps.add (natToRing (qs.count z))
          (CommRingOps.mul (CommRingOps.sub γ z)
            (logUpQueryFracSum γ (qs.filter fun q => decide (q ≠ z))))
  | [] => by simp [logUpQueryFracSum, natToRing, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | q :: qs => by
    have ih := logUpQueryFracSum_residue_split z γ hgz qs
    by_cases hqz : q = z
    · subst hqz
      simp only [logUpQueryFracSum, List.count_cons_self, List.filter_cons, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, LawfulCommRing.left_distrib, ih,
        LawfulField.mul_inv_cancel _ hgz]
      have hcnt : natToRing (R := F) (List.count q qs + 1) =
          CommRingOps.add CommRingOps.one (natToRing (List.count q qs)) := rfl
      rw [← LawfulCommRing.add_assoc, ← hcnt]
    · simp only [logUpQueryFracSum, List.count_cons_of_ne hqz, List.filter_cons, ne_eq, hqz,
        not_false_eq_true, decide_true, ↓reduceIte, LawfulCommRing.left_distrib, ih]
      rw [← LawfulCommRing.add_assoc, LawfulCommRing.add_comm _ (natToRing (qs.count z)),
          LawfulCommRing.add_assoc]

private theorem getElem_pair_mem_zip {α β : Type} :
    ∀ (xs : List α) (ys : List β) (i : Nat) (hx : i < xs.length) (hy : i < ys.length),
      (xs[i], ys[i]) ∈ xs.zip ys
  | _ :: _, _ :: _, 0, _, _ => List.mem_cons_self
  | _ :: xs, _ :: ys, i + 1, hx, hy =>
    List.mem_cons_of_mem _ (getElem_pair_mem_zip xs ys i (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy))

private theorem goldilocks_logUp_residue_eq
    (T : List Goldilocks) (M : List Nat) (Q : List Goldilocks) (z : Goldilocks)
    (hLen : M.length = T.length) (hDeg : 2 * (T.length + Q.length) + 3 ≤ goldilocksPrime)
    (hAll : ∀ γ : Goldilocks,
      CommRingOps.mul ((logUpTablePoly (T.zip M)).1.eval γ) ((logUpQueryPoly Q).2.eval γ) =
        CommRingOps.mul ((logUpQueryPoly Q).1.eval γ) ((logUpTablePoly (T.zip M)).2.eval γ)) :
    natToRing (R := Goldilocks) (sumMultAt z (T.zip M)) = natToRing (R := Goldilocks) (Q.count z) := by
  let tOther := (T.zip M).filter (fun p => decide (p.1 ≠ z))
  let qOther := Q.filter (fun q => decide (q ≠ z))
  let pTo := logUpTablePoly tOther; let pQo := logUpQueryPoly qOther
  let dCommon := polyMul pTo.2 pQo.2
  let P₁ := polyAdd (polyScale (natToRing (sumMultAt z (T.zip M))) dCommon) (mulLinFactor z (polyMul pTo.1 pQo.2))
  let P₂ := polyAdd (polyScale (natToRing (Q.count z)) dCommon) (mulLinFactor z (polyMul pQo.1 pTo.2))
  let S_excl := z :: (T ++ Q)
  have hMapFst : (T.zip M).map Prod.fst = T := List.map_fst_zip (by omega)
  have hAgree : ∀ γ : Goldilocks, γ ∉ S_excl → (P₁.sub P₂).eval γ = CommRingOps.zero := by
    intro γ hNotExcl
    have hgz : γ ≠ z := fun he => hNotExcl (he ▸ List.mem_cons_self)
    have hNoT : ∀ t ∈ T, γ ≠ t := fun t ht he =>
      hNotExcl (List.mem_cons_of_mem z (List.mem_append.mpr (.inl (he ▸ ht))))
    have hNoQ : ∀ q ∈ Q, γ ≠ q := fun q hq he =>
      hNotExcl (List.mem_cons_of_mem z (List.mem_append.mpr (.inr (he ▸ hq))))
    have hFracEq : logUpTableFracSum γ (T.zip M) = logUpQueryFracSum γ Q :=
      (logUpFrac_iff_clearedPoly γ T M Q hLen hNoT hNoQ).mpr (hAll γ)
    have hSubNe : CommRingOps.sub γ z ≠ CommRingOps.zero :=
      fun h0 => hgz ((LawfulIntegralDomain.sub_eq_zero_iff γ z).mp h0)
    have hSplitEq : CommRingOps.add (natToRing (sumMultAt z (T.zip M)))
        (CommRingOps.mul (CommRingOps.sub γ z) (logUpTableFracSum γ tOther)) =
        CommRingOps.add (natToRing (Q.count z))
        (CommRingOps.mul (CommRingOps.sub γ z) (logUpQueryFracSum γ qOther)) := by
      rw [← logUpTableFracSum_residue_split z γ hSubNe (T.zip M),
          ← logUpQueryFracSum_residue_split z γ hSubNe Q, hFracEq]
    have hToFrac := logUpTableFrac_eq_num_div_den γ tOther fun p hp =>
      hNoT p.1 (hMapFst ▸ List.mem_map_of_mem (f := Prod.fst) (List.mem_filter.mp hp).1)
    have hQoFrac := logUpQueryFrac_eq_num_div_den γ qOther fun q hq => hNoQ q (List.mem_filter.mp hq).1
    have hMulD := congrArg (fun u => CommRingOps.mul u (dCommon.eval γ)) hSplitEq
    have hSimpL : CommRingOps.mul (CommRingOps.add (natToRing (sumMultAt z (T.zip M)))
        (CommRingOps.mul (CommRingOps.sub γ z) (logUpTableFracSum γ tOther))) (dCommon.eval γ) = P₁.eval γ := by
      simp only [P₁, dCommon, eval_polyAdd, eval_polyScale, eval_mulLinFactor, eval_polyMul, LawfulCommRing.right_distrib]
      congr 1; rw [LawfulCommRing.mul_assoc (CommRingOps.sub γ z),
                   ← LawfulCommRing.mul_assoc (logUpTableFracSum γ tOther), hToFrac]
    have hSimpR : CommRingOps.mul (CommRingOps.add (natToRing (Q.count z))
        (CommRingOps.mul (CommRingOps.sub γ z) (logUpQueryFracSum γ qOther))) (dCommon.eval γ) = P₂.eval γ := by
      simp only [P₂, dCommon, eval_polyAdd, eval_polyScale, eval_mulLinFactor, eval_polyMul, LawfulCommRing.right_distrib]
      congr 1; rw [LawfulCommRing.mul_assoc (CommRingOps.sub γ z),
                   LawfulCommRing.mul_comm (pTo.2.eval γ) (pQo.2.eval γ),
                   ← LawfulCommRing.mul_assoc (logUpQueryFracSum γ qOther), hQoFrac]
    rw [hSimpL, hSimpR] at hMulD; rw [RoundPoly.eval_sub, hMulD, LawfulCommRing.sub_self]
  have htOLe : tOther.length ≤ T.length := by
    have hl := List.length_filter_le (fun p => decide (p.1 ≠ z)) (T.zip M); simp [hLen] at hl; exact hl
  have hqOLe : qOther.length ≤ Q.length := List.length_filter_le _ Q
  have hdToLen : pTo.2.coeffs.length ≤ T.length + 1 := by
    rw [logUpTablePoly_den_eq_charPoly, charPoly_length, List.length_map]; omega
  have hdQoLen : pQo.2.coeffs.length ≤ Q.length + 1 := by
    rw [logUpQueryPoly_den_eq_charPoly, charPoly_length]; omega
  have hnToLen : pTo.1.coeffs.length ≤ T.length := Nat.le_trans (logUpTablePoly_num_length tOther) htOLe
  have hnQoLen : pQo.1.coeffs.length ≤ Q.length := Nat.le_trans (logUpQueryPoly_num_length qOther) hqOLe
  have hdComLen : dCommon.coeffs.length ≤ (T.length + 1) + Q.length := polyMulCoeffs_length_le hdToLen hdQoLen
  have hm1Len : (polyMul pTo.1 pQo.2).coeffs.length ≤ T.length + Q.length := polyMulCoeffs_length_le hnToLen hdQoLen
  have hm2Len : (polyMul pQo.1 pTo.2).coeffs.length ≤ Q.length + T.length := polyMulCoeffs_length_le hnQoLen hdToLen
  have hP1Len : P₁.coeffs.length ≤ T.length + Q.length + 1 := by
    have ha := polyAddCoeffs_length_le (polyScale (natToRing (sumMultAt z (T.zip M))) dCommon).coeffs
      (mulLinFactor z (polyMul pTo.1 pQo.2)).coeffs
    simp only [P₁, polyAdd, polyScale, List.length_map, mulLinFactor_length] at ha ⊢
    change _ ≤ _ at hdComLen hm1Len; omega
  have hP2Len : P₂.coeffs.length ≤ T.length + Q.length + 1 := by
    have ha := polyAddCoeffs_length_le (polyScale (natToRing (Q.count z)) dCommon).coeffs
      (mulLinFactor z (polyMul pQo.1 pTo.2)).coeffs
    simp only [P₂, polyAdd, polyScale, List.length_map, mulLinFactor_length] at ha ⊢
    change _ ≤ _ at hdComLen hm2Len; omega
  have hDiffBound : (P₁.sub P₂).coeffs.length + S_excl.length ≤ goldilocksPrime := by
    have hs := subCoeffs_length_le P₁.coeffs P₂.coeffs
    simp only [S_excl, List.length_cons, List.length_append, RoundPoly.sub]; omega
  have hAll0 := goldilocks_all_coeffs_zero_of_eval_zero_except S_excl hDiffBound hAgree
  have hAtZ : (P₁.sub P₂).eval z = CommRingOps.zero := evalCoeffs_eq_zero_of_all_zero z _ hAll0
  rw [RoundPoly.eval_sub] at hAtZ
  have hEqZ := eq_of_sub_eq_zero hAtZ
  simp only [P₁, P₂, eval_polyAdd, eval_polyScale, eval_mulLinFactor, LawfulCommRing.sub_self,
    LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hEqZ
  have hdToNe : pTo.2.eval z ≠ CommRingOps.zero := by
    rw [logUpTablePoly_den_eq_charPoly]; intro hz
    rcases List.mem_map.mp ((charPoly_eval_eq_zero_iff z _).mp hz) with ⟨p, hp, hpEq⟩
    exact of_decide_eq_true (List.mem_filter.mp hp).2 hpEq
  have hdQoNe : pQo.2.eval z ≠ CommRingOps.zero := by
    rw [logUpQueryPoly_den_eq_charPoly]; intro hz
    exact of_decide_eq_true (List.mem_filter.mp ((charPoly_eval_eq_zero_iff z _).mp hz)).2 rfl
  have hdComNe : dCommon.eval z ≠ CommRingOps.zero := by
    rw [eval_polyMul]; exact LawfulIntegralDomain.mul_ne_zero hdToNe hdQoNe
  exact LawfulIntegralDomain.mul_right_cancel hdComNe hEqZ

/-- **Main `Lookup` LogUp Logarithmic-Derivative Weld (`logUpIdentity_implies_lookup`)**. -/
theorem logUpIdentity_implies_lookup
    (T : List Goldilocks) (M : List Nat) (Q S : List Goldilocks)
    (hS : S.Nodup) (hNd : T.Nodup) (hLen : M.length = T.length)
    (hDeg : 2 * (T.length + Q.length) + 3 ≤ goldilocksPrime) (hMBound : ∀ m ∈ M, m < goldilocksPrime) :
    let (nT, dT) := logUpTablePoly (T.zip M)
    let (nQ, dQ) := logUpQueryPoly Q
    (((∀ q ∈ Q, q ∈ T) ∧
      (∀ (i : Nat) (hti : i < T.length) (hmi : i < M.length), M[i] = Q.count T[i])) ∨
     (S.filter fun γ => decide (CommRingOps.mul (nT.eval γ) (dQ.eval γ) =
                                CommRingOps.mul (nQ.eval γ) (dT.eval γ))).length ≤
       T.length + Q.length) := by
  dsimp only
  let pT := logUpTablePoly (T.zip M); let pQ := logUpQueryPoly Q
  let diff := (polyMul pT.1 pQ.2).sub (polyMul pQ.1 pT.2)
  have hMapFst : (T.zip M).map Prod.fst = T := List.map_fst_zip (by omega)
  cases hdb : diff.coeffs.all (fun c => decide (c = CommRingOps.zero)) with
  | true =>
    left
    have hAll : ∀ γ : Goldilocks,
        CommRingOps.mul (pT.1.eval γ) (pQ.2.eval γ) = CommRingOps.mul (pQ.1.eval γ) (pT.2.eval γ) := by
      intro γ
      have hz : diff.eval γ = CommRingOps.zero :=
        evalCoeffs_eq_zero_of_all_zero γ _ (fun c hc => of_decide_eq_true (List.all_eq_true.mp hdb c hc))
      simp only [diff, RoundPoly.eval_sub, eval_polyMul] at hz
      exact eq_of_sub_eq_zero hz
    refine ⟨fun q hq => Decidable.byContradiction fun hqNotT => ?_, fun i hti hmi => ?_⟩
    · have hRes := goldilocks_logUp_residue_eq T M Q q hLen hDeg hAll
      have hqNotZip : q ∉ (T.zip M).map Prod.fst := by rw [hMapFst]; exact hqNotT
      rw [sumMultAt_of_not_mem q (T.zip M) hqNotZip, natToRing_goldilocks, natToRing_goldilocks] at hRes
      have hkPos : 1 ≤ Q.count q := List.count_pos_iff.mpr hq
      have hkLe : Q.count q ≤ Q.length := List.count_le_length
      have hv := congrArg Goldilocks.val hRes
      simp only [Goldilocks.ofNat, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : Q.count q < goldilocksPrime)] at hv
      omega
    · have hRes := goldilocks_logUp_residue_eq T M Q T[i] hLen hDeg hAll
      have hPair := getElem_pair_mem_zip T M i hti hmi
      have hNdZip : ((T.zip M).map Prod.fst).Nodup := by rw [hMapFst]; exact hNd
      rw [sumMultAt_of_nodup_mem T[i] M[i] (T.zip M) hNdZip hPair,
          natToRing_goldilocks, natToRing_goldilocks] at hRes
      have hmLt : M[i] < goldilocksPrime := hMBound M[i] (List.getElem_mem hmi)
      have hkLe : Q.count T[i] ≤ Q.length := List.count_le_length
      have hv := congrArg Goldilocks.val hRes
      simp only [Goldilocks.ofNat, Nat.mod_eq_of_lt hmLt,
        Nat.mod_eq_of_lt (by omega : Q.count T[i] < goldilocksPrime)] at hv
      exact hv
  | false =>
    right
    have hNz := exists_ne_zero_of_all_false diff.coeffs hdb
    have hnTLen : pT.1.coeffs.length ≤ T.length := by
      have hl := logUpTablePoly_num_length (T.zip M); simp [hLen] at hl; exact hl
    have hdQLen : pQ.2.coeffs.length ≤ Q.length + 1 := by
      rw [logUpQueryPoly_den_eq_charPoly, charPoly_length]; exact Nat.le_refl _
    have hnQLen : pQ.1.coeffs.length ≤ Q.length := logUpQueryPoly_num_length Q
    have hdTLen : pT.2.coeffs.length ≤ T.length + 1 := by
      rw [logUpTablePoly_den_eq_charPoly, hMapFst, charPoly_length]; exact Nat.le_refl _
    have hL1 := polyMulCoeffs_length_le hnTLen hdQLen
    have hL2 := polyMulCoeffs_length_le hnQLen hdTLen
    have hSub := subCoeffs_length_le (polyMul pT.1 pQ.2).coeffs (polyMul pQ.1 pT.2).coeffs
    have hDiffLen : diff.coeffs.length ≤ (T.length + Q.length) + 1 := by
      unfold diff polyMul at hSub ⊢; simp only [RoundPoly.sub] at hSub ⊢; omega
    have hFiltEq : S.filter (fun γ => decide (CommRingOps.mul (pT.1.eval γ) (pQ.2.eval γ) =
        CommRingOps.mul (pQ.1.eval γ) (pT.2.eval γ))) =
        S.filter (fun γ => decide (diff.eval γ = CommRingOps.zero)) := by
      apply List.filter_congr; intro γ _
      simp only [diff, RoundPoly.eval_sub, eval_polyMul, LawfulIntegralDomain.sub_eq_zero_iff]
    rw [hFiltEq]; exact schwartzZippel_roots_le_deg (T.length + Q.length) diff S hS hDiffLen hNz

/-! ## 2. `eqPoly`-Weighted Batching, Multilinear Schwartz–Zippel & `Sumcheck` Compiler -/

def zipMulPadded {R : Type} [CommRingOps R] : List R → List R → List R
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => CommRingOps.mul x y :: zipMulPadded xs ys

def eqWeightedTable {R : Type} [CommRingOps R] (tbl τ : List R) : List R :=
  zipMulPadded tbl ((hypercube τ.length).map (eqPoly τ))

private theorem innerProd_zipMulPadded_ones {R : Type} [LawfulCommRing R] :
    ∀ (xs ws : List R),
      innerProd (zipMulPadded xs ws) (ws.map fun _ => CommRingOps.one) = innerProd xs ws
  | [], _ => by simp [zipMulPadded, innerProd]
  | _ :: _, [] => by simp [zipMulPadded, innerProd]
  | _ :: xs, _ :: ws => by
    simp only [zipMulPadded, List.map_cons, innerProd, LawfulCommRing.mul_one, innerProd_zipMulPadded_ones xs ws]

theorem hypercubeSum_eqWeightedTable_eq_mleEval {R : Type} [LawfulCommRing R] (tbl τ : List R) :
    hypercubeSum τ.length (eqWeightedTable tbl τ) = mleEval tbl τ := by
  unfold hypercubeSum eqWeightedTable mleEval
  have hones : ((hypercube τ.length).map fun _ => (CommRingOps.one : R)) =
      ((hypercube τ.length).map (eqPoly τ)).map (fun _ => CommRingOps.one) := by simp [List.map_map]
  rw [hones, innerProd_zipMulPadded_ones]

private theorem mleEval_all_zero {R : Type} [LawfulCommRing R] :
    ∀ (tbl : List R) (ws : List R), (∀ x ∈ tbl, x = CommRingOps.zero) → innerProd tbl ws = CommRingOps.zero
  | [], _, _ => by simp [innerProd]
  | _ :: _, [], _ => by simp [innerProd]
  | x :: xs, _ :: ws, hz => by
    simp only [innerProd, hz x List.mem_cons_self, LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
      mleEval_all_zero xs ws (fun y hy => hz y (List.mem_cons_of_mem x hy))]

theorem mleEval_eq_zero_of_all_zero {R : Type} [LawfulCommRing R] (tbl τ : List R)
    (hz : ∀ x ∈ tbl, x = CommRingOps.zero) : mleEval tbl τ = CommRingOps.zero :=
  mleEval_all_zero tbl _ hz

def gridPoints {F : Type} : Nat → List F → List (List F)
  | 0, _ => [[]]
  | v + 1, S => S.flatMap fun r => (gridPoints v S).map (r :: ·)

private theorem flatMap_cons_grid_len {F : Type} (g : List (List F)) :
    ∀ l : List F, (l.flatMap fun r => g.map (r :: ·)).length = l.length * g.length
  | [] => by simp
  | _ :: xs => by simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
                    flatMap_cons_grid_len g xs, Nat.succ_mul]; omega

theorem gridPoints_length {F : Type} (S : List F) : ∀ v : Nat, (gridPoints v S).length = S.length ^ v
  | 0 => rfl
  | v + 1 => by rw [gridPoints, flatMap_cons_grid_len, gridPoints_length S v, Nat.pow_succ, Nat.mul_comm]

private def firstPairPoly {F : Type} [CommRingOps F] [DecidableEq F] : List F → RoundPoly F
  | [] => ⟨[]⟩
  | [lo] => ⟨[lo, CommRingOps.sub CommRingOps.zero lo]⟩
  | lo :: hi :: rest =>
    if decide (lo = CommRingOps.zero) && decide (hi = CommRingOps.zero) then firstPairPoly rest
    else ⟨[lo, CommRingOps.sub hi lo]⟩

private theorem firstPairPoly_spec {F : Type} [LawfulIntegralDomain F] [DecidableEq F] :
    ∀ (tbl : List F), (∃ x ∈ tbl, x ≠ CommRingOps.zero) →
      (firstPairPoly tbl).coeffs.length ≤ 2 ∧
      (∃ c ∈ (firstPairPoly tbl).coeffs, c ≠ CommRingOps.zero) ∧
      ∀ r : F, (∀ z ∈ foldFirstVar tbl r, z = CommRingOps.zero) → (firstPairPoly tbl).eval r = CommRingOps.zero
  | [], ⟨_, hm, _⟩ => nomatch hm
  | [lo], ⟨x, hm, hne⟩ => by
    simp only [List.mem_singleton] at hm; subst hm
    refine ⟨by simp [firstPairPoly], ⟨x, by simp [firstPairPoly], hne⟩, fun r hfold => ?_⟩
    simpa [firstPairPoly, RoundPoly.eval_linear] using hfold _ List.mem_cons_self
  | lo :: hi :: rest, ⟨x, hm, hne⟩ => by
    unfold firstPairPoly
    cases hBoth : decide (lo = CommRingOps.zero) && decide (hi = CommRingOps.zero) with
    | true =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hBoth
      have hRestNz : ∃ y ∈ rest, y ≠ CommRingOps.zero := by
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact absurd hBoth.1 hne
        · rcases List.mem_cons.mp hm' with rfl | hm''
          · exact absurd hBoth.2 hne
          · exact ⟨x, hm'', hne⟩
      obtain ⟨hl, hnz, hev⟩ := firstPairPoly_spec rest hRestNz
      exact ⟨hl, hnz, fun r hfold => hev r fun z hz => hfold z (List.mem_cons_of_mem _ hz)⟩
    | false =>
      refine ⟨by simp, ?_, fun r hfold => by simpa [RoundPoly.eval_linear] using hfold _ List.mem_cons_self⟩
      by_cases hlo0 : lo = CommRingOps.zero
      · refine ⟨CommRingOps.sub hi lo, by simp, fun hsub0 => ?_⟩
        have hhi0 : hi = CommRingOps.zero := hlo0 ▸ eq_of_sub_eq_zero hsub0
        simp [hlo0, hhi0] at hBoth
      · exact ⟨lo, by simp, hlo0⟩

private theorem filter_flatMap_eq_flatMap_filter {α β : Type} (p : β → Bool) (f : α → List β) :
    ∀ l : List α, (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p)
  | [] => rfl
  | a :: as => by simp [List.flatMap_cons, List.filter_append, filter_flatMap_eq_flatMap_filter p f as]

private theorem flatMap_partition_bound {α : Type} (bad : α → Bool) (cnt : α → Nat) (B G : Nat) :
    ∀ (l : List α), (∀ a ∈ l, bad a = true → cnt a ≤ B) → (∀ a ∈ l, bad a = false → cnt a ≤ G) →
      (l.foldr (fun a acc => cnt a + acc) 0) ≤ (l.filter bad).length * B + l.length * G
  | [], _, _ => Nat.zero_le _
  | a :: as, hB, hG => by
    have ih := flatMap_partition_bound bad cnt B G as
      (fun x hx => hB x (List.mem_cons_of_mem a hx)) (fun x hx => hG x (List.mem_cons_of_mem a hx))
    simp only [List.foldr_cons, List.filter_cons, List.length_cons, Nat.succ_mul]
    cases hba : bad a
    · have ha := hG a List.mem_cons_self hba; simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · have ha := hB a List.mem_cons_self hba; simp only [↓reduceIte, List.length_cons, Nat.succ_mul]; omega

private theorem flatMap_length_eq_foldr {α β : Type} (f : α → List β) :
    ∀ l : List α, (l.flatMap f).length = l.foldr (fun a acc => (f a).length + acc) 0
  | [] => rfl
  | a :: as => by simp [List.flatMap_cons, flatMap_length_eq_foldr f as]

/-- **Constructive Multilinear Schwartz–Zippel Grid Bound (`mle_schwartzZippel_grid_bound`)**. -/
theorem mle_schwartzZippel_grid_bound {F : Type} [LawfulIntegralDomain F] [DecidableEq F]
    (S : List F) (hS : S.Nodup) :
    ∀ (v : Nat) (tbl : List F), tbl.length ≤ 2 ^ v → (∃ x ∈ tbl, x ≠ CommRingOps.zero) →
      ((gridPoints v S).filter fun τ => decide (mleEval tbl τ = CommRingOps.zero)).length ≤
        v * S.length ^ (v - 1)
  | 0, tbl, hlen, ⟨x, hm, hne⟩ => by
    cases tbl with
    | nil => cases hm
    | cons _ tl =>
      cases tl with
      | cons _ _ => simp at hlen
      | nil =>
        simp only [List.mem_singleton] at hm; subst hm
        have hval : mleEval [x] [] = x := by
          simp [mleEval, hypercube, eqPoly, innerProd, LawfulCommRing.mul_one, LawfulCommRing.add_zero]
        simp [gridPoints, hval, hne]
  | v + 1, tbl, hlen, hnz => by
    simp only [Nat.add_sub_cancel]
    rw [gridPoints, filter_flatMap_eq_flatMap_filter, flatMap_length_eq_foldr]
    let bad : F → Bool := fun r => (foldFirstVar tbl r).all (fun z => decide (z = CommRingOps.zero))
    let subFilt : F → List (List F) := fun r =>
      ((gridPoints v S).map (r :: ·)).filter (fun τ => decide (mleEval tbl τ = CommRingOps.zero))
    have hSubEq : ∀ r : F, (subFilt r).length =
        ((gridPoints v S).filter (fun rs => decide (mleEval (foldFirstVar tbl r) rs = CommRingOps.zero))).length := by
      intro r; unfold subFilt; rw [List.filter_map, List.length_map]
      congr 1; apply List.filter_congr; intro rs _; simp only [Function.comp_def, mleEval_foldFirstVar]
    obtain ⟨hpLen, hpNz, hpEv⟩ := firstPairPoly_spec tbl hnz
    have hBadLe1 : (S.filter bad).length ≤ 1 := by
      have hSubBad : ∀ r ∈ S.filter bad, r ∈ S.filter (fun x => decide ((firstPairPoly tbl).eval x = CommRingOps.zero)) := by
        intro r hr; rw [List.mem_filter] at hr ⊢
        refine ⟨hr.1, decide_eq_true (hpEv r fun z hz => of_decide_eq_true (List.all_eq_true.mp hr.2 z hz))⟩
      exact Nat.le_trans (nodup_sublist_len_le _ _ (nodup_filter bad hS) hSubBad)
        (schwartzZippel_roots_le_deg 1 (firstPairPoly tbl) S hS hpLen hpNz)
    have hFoldLen : ∀ r : F, (foldFirstVar tbl r).length ≤ 2 ^ v := by
      intro r; rw [foldFirstVar_length]; rw [Nat.pow_succ] at hlen; omega
    have hBound := flatMap_partition_bound bad (fun r => (subFilt r).length) (S.length ^ v) (v * S.length ^ (v - 1)) S
      (fun r _ _ => by rw [hSubEq, ← gridPoints_length S v]; exact List.length_filter_le _ _)
      (fun r _ hgood => by
        rw [hSubEq]
        exact mle_schwartzZippel_grid_bound S hS v (foldFirstVar tbl r) (hFoldLen r)
          (exists_ne_zero_of_all_false (foldFirstVar tbl r) hgood))
    have hMulPow : S.length * (v * S.length ^ (v - 1)) = v * S.length ^ v := by
      cases v with
      | zero => simp
      | succ k =>
        simp only [Nat.add_sub_cancel]
        rw [← Nat.mul_assoc, Nat.mul_comm S.length (k + 1), Nat.mul_assoc,
            Nat.mul_comm S.length (S.length ^ k), ← Nat.pow_succ]
    rw [hMulPow] at hBound
    have hBadMul : (S.filter bad).length * S.length ^ v ≤ 1 * S.length ^ v :=
      Nat.mul_le_mul_right (S.length ^ v) hBadLe1
    rw [Nat.one_mul] at hBadMul
    rw [Nat.succ_mul, Nat.add_comm (v * S.length ^ v)]
    exact Nat.le_trans hBound (Nat.add_le_add_right hBadMul _)

structure SymbolicZkStmt where
  beforeConstraints : Array BeforeConstraint
  linmemInit : Array Goldilocks
  linmemProd : Array Goldilocks
  linmemCons : Array Goldilocks
  linmemFinal : Array Goldilocks
  lookupTable : Array Goldilocks
  lookupQueries : Array Goldilocks
  numVars : Nat
  deriving DecidableEq, Repr

structure SymbolicZkWitness where
  beforeBits : Array (Array Goldilocks)
  lookupMults : Array Nat
  deriving DecidableEq, Repr

@[expose] def stmtWitnessStructValid (stmt : SymbolicZkStmt) (wit : SymbolicZkWitness) : Bool :=
  decide (wit.beforeBits.size = stmt.beforeConstraints.size) &&
  (stmt.beforeConstraints.toList.zip wit.beforeBits.toList).all (fun p =>
    beforeWidthSafe p.1.bitWidth && decide (p.1.lhs < 2 ^ p.1.bitWidth) &&
    decide (p.1.rhs ≤ 2 ^ p.1.bitWidth) && decide (p.2.size = p.1.bitWidth)) &&
  decide stmt.lookupTable.toList.Nodup &&
  decide (wit.lookupMults.size = stmt.lookupTable.size) &&
  wit.lookupMults.toList.all (fun m => decide (m < goldilocksPrime)) &&
  decide (2 * (stmt.lookupTable.size + stmt.lookupQueries.size) + 3 ≤ goldilocksPrime)

def beforeResidualList : List (BeforeConstraint × Array Goldilocks) → List Goldilocks
  | [] => []
  | (c, bits) :: rest =>
    (bits.toList.map boolBitResidual) ++ [beforeSlackResidualArray c.lhs c.rhs bits] ++ beforeResidualList rest

def symbolicResidualVector (stmt : SymbolicZkStmt) (wit : SymbolicZkWitness)
    (γLin γLup : Goldilocks) : List Goldilocks :=
  let bef := beforeResidualList (stmt.beforeConstraints.toList.zip wit.beforeBits.toList)
  let linRes := CommRingOps.sub
    (charPolyEvalArray (stmt.linmemInit ++ stmt.linmemProd) γLin)
    (charPolyEvalArray (stmt.linmemCons ++ stmt.linmemFinal) γLin)
  let (nT, dT) := logUpTableEvalArray stmt.lookupTable wit.lookupMults γLup
  let (nQ, dQ) := logUpQueryEvalArray stmt.lookupQueries γLup
  let lupRes := CommRingOps.sub (CommRingOps.mul nT dQ) (CommRingOps.mul nQ dT)
  bef ++ [linRes, lupRes]

def batchedSymbolicPiopTable (stmt : SymbolicZkStmt) (wit : SymbolicZkWitness)
    (γLin γLup : Goldilocks) (τ : List Goldilocks) : List Goldilocks :=
  eqWeightedTable (symbolicResidualVector stmt wit γLin γLup) τ

def SymbolicSemanticsValid (stmt : SymbolicZkStmt) (wit : SymbolicZkWitness) : Prop :=
  (∀ c ∈ stmt.beforeConstraints.toList, c.lhs < c.rhs) ∧
  (stmt.linmemInit.toList ++ stmt.linmemProd.toList).Perm
    (stmt.linmemCons.toList ++ stmt.linmemFinal.toList) ∧
  (∀ q ∈ stmt.lookupQueries.toList, q ∈ stmt.lookupTable.toList) ∧
  (∀ (i : Nat) (hti : i < stmt.lookupTable.toList.length) (hmi : i < wit.lookupMults.toList.length),
    wit.lookupMults.toList[i] = stmt.lookupQueries.toList.count stmt.lookupTable.toList[i])

private theorem beforeResidualList_zero_implies_lt :
    ∀ (cs : List BeforeConstraint) (bs : List (Array Goldilocks)),
      bs.length = cs.length →
      (∀ p ∈ cs.zip bs,
        beforeWidthSafe p.1.bitWidth = true ∧ p.1.lhs < 2 ^ p.1.bitWidth ∧
        p.1.rhs ≤ 2 ^ p.1.bitWidth ∧ p.2.size = p.1.bitWidth) →
      (∀ r ∈ beforeResidualList (cs.zip bs), r = CommRingOps.zero) →
      ∀ c ∈ cs, c.lhs < c.rhs
  | [], _, _, _, _, _, hc => nomatch hc
  | _ :: _, [], hlen, _, _, _, _ => by simp at hlen
  | c :: cs, bits :: bs, hlen, hvalid, hz, c', hc' => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [List.zip_cons_cons, beforeResidualList] at hvalid hz
    rcases List.mem_cons.mp hc' with hEq | htail
    · subst hEq
      obtain ⟨hW, ha, hb, hsz⟩ := hvalid (c', bits) List.mem_cons_self
      apply (beforePolyConstraint_iff_lt c'.lhs c'.rhs c'.bitWidth hW ha hb).mp
      refine ⟨bits, hsz, fun bit hbit => ?_, ?_⟩
      · exact hz _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_map_of_mem hbit)))))
      · exact hz _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl)))))
    · exact beforeResidualList_zero_implies_lt cs bs hlen
        (fun p hp => hvalid p (List.mem_cons_of_mem _ hp))
        (fun r hr => hz r (List.mem_append.mpr (.inr hr))) c' htail

private theorem beforeResidualList_compile_all_zero :
    ∀ (cs : List BeforeConstraint),
      (∀ c ∈ cs, beforeWidthSafe c.bitWidth = true ∧ c.lhs < 2 ^ c.bitWidth ∧ c.rhs ≤ 2 ^ c.bitWidth ∧ c.lhs < c.rhs) →
      ∀ r ∈ beforeResidualList (cs.zip (cs.map compileBeforeWitness)), r = CommRingOps.zero
  | [], _, _, hr => nomatch hr
  | c :: cs, hok, r, hr => by
    obtain ⟨hW, ha, hb, hlt⟩ := hok c List.mem_cons_self
    obtain ⟨_, hall, hslack⟩ := compileBeforeWitness_residuals_zero c hW ha hb hlt
    simp only [List.map_cons, List.zip_cons_cons, beforeResidualList, List.mem_append, List.mem_map,
      List.mem_singleton] at hr
    rcases hr with (⟨b, hbMem, rfl⟩ | rfl) | hrest
    · exact hall b hbMem
    · exact hslack
    · exact beforeResidualList_compile_all_zero cs (fun x hx => hok x (List.mem_cons_of_mem c hx)) r hrest

/-- **Honest SymbolicZkVM-to-Sumcheck Completeness (`compileSymbolicTraceToSumcheck_complete`)**. -/
theorem compileSymbolicTraceToSumcheck_complete
    (stmt : SymbolicZkStmt) (maxDeg : Nat) (hDeg : 1 ≤ maxDeg)
    (γLin γLup : Goldilocks) (τ : List Goldilocks) (hτ : τ.length = stmt.numVars)
    (tr : Transcript .relationBound)
    (hBef : ∀ c ∈ stmt.beforeConstraints.toList,
      beforeWidthSafe c.bitWidth = true ∧ c.lhs < 2 ^ c.bitWidth ∧ c.rhs ≤ 2 ^ c.bitWidth ∧ c.lhs < c.rhs)
    (hLin : (stmt.linmemInit.toList ++ stmt.linmemProd.toList).Perm
      (stmt.linmemCons.toList ++ stmt.linmemFinal.toList))
    (hNd : stmt.lookupTable.toList.Nodup)
    (hLup : ∀ q ∈ stmt.lookupQueries.toList, q ∈ stmt.lookupTable.toList)
    (hLupDeg : 2 * (stmt.lookupTable.size + stmt.lookupQueries.size) + 3 ≤ goldilocksPrime) :
    let wit : SymbolicZkWitness :=
      { beforeBits := stmt.beforeConstraints.map compileBeforeWitness
        lookupMults := stmt.lookupTable.map (fun t => stmt.lookupQueries.toList.count t) }
    let tbl := batchedSymbolicPiopTable stmt wit γLin γLup τ
    let (rounds, claim, trOut) := honestSumcheckProver stmt.numVars tbl tr
    stmtWitnessStructValid stmt wit = true ∧
    (∀ r ∈ symbolicResidualVector stmt wit γLin γLup, r = CommRingOps.zero) ∧
    verifySumcheck maxDeg stmt.numVars CommRingOps.zero rounds tr = some (claim, trOut) ∧
    claim.expectedVal = mleEval tbl claim.point := by
  dsimp only
  let wit : SymbolicZkWitness :=
    { beforeBits := stmt.beforeConstraints.map compileBeforeWitness
      lookupMults := stmt.lookupTable.map (fun t => stmt.lookupQueries.toList.count t) }
  have hValid : stmtWitnessStructValid stmt wit = true := by
    unfold stmtWitnessStructValid
    have h1 : decide (wit.beforeBits.size = stmt.beforeConstraints.size) = true := by simp [wit]
    have h2 : (stmt.beforeConstraints.toList.zip wit.beforeBits.toList).all (fun p =>
        beforeWidthSafe p.1.bitWidth && decide (p.1.lhs < 2 ^ p.1.bitWidth) &&
        decide (p.1.rhs ≤ 2 ^ p.1.bitWidth) && decide (p.2.size = p.1.bitWidth)) = true := by
      simp only [wit, Array.toList_map, zip_map_self, List.all_eq_true]
      intro p hp; rcases List.mem_map.mp hp with ⟨c, hc, rfl⟩
      obtain ⟨hW, ha, hb, hlt⟩ := hBef c hc
      obtain ⟨hsz, _, _⟩ := compileBeforeWitness_residuals_zero c hW ha hb hlt
      simp [hW, ha, hb, hsz]
    have h3 : decide stmt.lookupTable.toList.Nodup = true := decide_eq_true hNd
    have h4 : decide (wit.lookupMults.size = stmt.lookupTable.size) = true := by simp [wit]
    have h5 : wit.lookupMults.toList.all (fun m => decide (m < goldilocksPrime)) = true := by
      simp only [wit, Array.toList_map, List.all_eq_true]
      intro m hm; rcases List.mem_map.mp hm with ⟨t, _, rfl⟩
      have hle : stmt.lookupQueries.toList.count t ≤ stmt.lookupQueries.toList.length := List.count_le_length
      have hszQ : stmt.lookupQueries.toList.length = stmt.lookupQueries.size := Array.length_toList
      exact decide_eq_true (by omega)
    have h6 : decide (2 * (stmt.lookupTable.size + stmt.lookupQueries.size) + 3 ≤ goldilocksPrime) = true :=
      decide_eq_true hLupDeg
    simp [h1, h2, h3, h4, h5, h6]
  have hAllZero : ∀ r ∈ symbolicResidualVector stmt wit γLin γLup, r = CommRingOps.zero := by
    intro r hr
    simp only [symbolicResidualVector, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hbef | rfl | rfl
    · simp only [wit, Array.toList_map] at hbef
      exact beforeResidualList_compile_all_zero stmt.beforeConstraints.toList hBef r hbef
    · rw [charPolyEvalArray_eq_spec, charPolyEvalArray_eq_spec, Array.toList_append, Array.toList_append,
          charPoly_perm hLin, LawfulCommRing.sub_self]
    · have hTev := logUpTableEvalArray_eq_spec stmt.lookupTable wit.lookupMults γLup
      have hQev := logUpQueryEvalArray_eq_spec stmt.lookupQueries γLup
      simp only [wit, Array.toList_map] at hTev
      have hComp := logUpIdentity_complete stmt.lookupTable.toList stmt.lookupQueries.toList hNd hLup γLup
      dsimp only at hTev hQev hComp
      rw [hTev, hQev, hComp, LawfulCommRing.sub_self]
  have hSumZero : hypercubeSum stmt.numVars (batchedSymbolicPiopTable stmt wit γLin γLup τ) = CommRingOps.zero := by
    rw [← hτ]; unfold batchedSymbolicPiopTable
    rw [hypercubeSum_eqWeightedTable_eq_mleEval]
    exact mleEval_eq_zero_of_all_zero _ τ hAllZero
  have hHonest := honestSumcheckProver_completeness hDeg stmt.numVars
    (batchedSymbolicPiopTable stmt wit γLin γLup τ) tr
  dsimp only at hHonest; rw [hSumZero] at hHonest
  exact ⟨hValid, hAllZero, hHonest.1, hHonest.2⟩

/-- **Cryptographic SymbolicZkVM-to-Sumcheck Soundness Weld (`compileSymbolicTraceToSumcheck_sound`)**. -/
theorem compileSymbolicTraceToSumcheck_sound
    (stmt : SymbolicZkStmt) (wit : SymbolicZkWitness) (maxDeg : Nat)
    (γLin γLup : Goldilocks) (τ : List Goldilocks) (hτ : τ.length = stmt.numVars)
    (rounds : List (RoundPoly Goldilocks)) (tr : Transcript .relationBound)
    (claim : EvalClaim Goldilocks stmt.numVars) (trFinal : Transcript .relationBound)
    (hStruct : stmtWitnessStructValid stmt wit = true)
    (hAcc : verifySumcheck maxDeg stmt.numVars CommRingOps.zero rounds tr = some (claim, trFinal)) :
    let resVec := symbolicResidualVector stmt wit γLin γLup
    let tbl := batchedSymbolicPiopTable stmt wit γLin γLup τ
    let linLhs := stmt.linmemInit.toList ++ stmt.linmemProd.toList
    let linRhs := stmt.linmemCons.toList ++ stmt.linmemFinal.toList
    let (nT, dT) := logUpTablePoly (stmt.lookupTable.toList.zip wit.lookupMults.toList)
    let (nQ, dQ) := logUpQueryPoly stmt.lookupQueries.toList
    SymbolicSemanticsValid stmt wit ∨
    (¬ linLhs.Perm linRhs ∧ (charPoly linLhs).eval γLin = (charPoly linRhs).eval γLin) ∨
    (¬ ((∀ q ∈ stmt.lookupQueries.toList, q ∈ stmt.lookupTable.toList) ∧
        (∀ (i : Nat) (hti : i < stmt.lookupTable.toList.length) (hmi : i < wit.lookupMults.toList.length),
          wit.lookupMults.toList[i] = stmt.lookupQueries.toList.count stmt.lookupTable.toList[i])) ∧
      CommRingOps.mul (nT.eval γLup) (dQ.eval γLup) = CommRingOps.mul (nQ.eval γLup) (dT.eval γLup)) ∨
    ((∃ r ∈ resVec, r ≠ CommRingOps.zero) ∧ mleEval resVec τ = CommRingOps.zero) ∨
    ExistsRoundRootHit stmt.numVars tbl rounds tr ∨
    claim.expectedVal ≠ mleEval tbl claim.point := by
  dsimp only
  let resVec := symbolicResidualVector stmt wit γLin γLup
  let tbl := batchedSymbolicPiopTable stmt wit γLin γLup τ
  by_cases hSumEq0 : hypercubeSum stmt.numVars tbl = CommRingOps.zero
  · have hMle0 : mleEval resVec τ = CommRingOps.zero := by
      have hs := hSumEq0; rw [← hτ] at hs
      unfold tbl batchedSymbolicPiopTable at hs
      rwa [hypercubeSum_eqWeightedTable_eq_mleEval] at hs
    cases hResB : resVec.all (fun r => decide (r = CommRingOps.zero)) with
    | false =>
      exact .inr (.inr (.inr (.inl ⟨exists_ne_zero_of_all_false resVec hResB, hMle0⟩)))
    | true =>
      have hResAll0 : ∀ r ∈ resVec, r = CommRingOps.zero :=
        fun r hr => of_decide_eq_true (List.all_eq_true.mp hResB r hr)
      simp only [stmtWitnessStructValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hStruct
      rcases hStruct with ⟨⟨⟨⟨⟨hBefSz, hBefAll⟩, _hNd⟩, hMultSz⟩, _hMultBound⟩, _hLupDeg⟩
      have hBefValid : ∀ c ∈ stmt.beforeConstraints.toList, c.lhs < c.rhs := by
        apply beforeResidualList_zero_implies_lt stmt.beforeConstraints.toList wit.beforeBits.toList
          (by simpa using hBefSz)
        · intro p hp; have hp' := hBefAll p hp; exact ⟨hp'.1.1.1, hp'.1.1.2, hp'.1.2, hp'.2⟩
        · intro r hr; exact hResAll0 r (by simp [resVec, symbolicResidualVector, hr])
      have hLinRes0 : CommRingOps.sub (charPolyEvalArray (stmt.linmemInit ++ stmt.linmemProd) γLin)
          (charPolyEvalArray (stmt.linmemCons ++ stmt.linmemFinal) γLin) = CommRingOps.zero :=
        hResAll0 _ (by simp [resVec, symbolicResidualVector])
      rw [charPolyEvalArray_eq_spec, charPolyEvalArray_eq_spec, Array.toList_append, Array.toList_append] at hLinRes0
      have hLinEvalEq := eq_of_sub_eq_zero hLinRes0
      let linLhs := stmt.linmemInit.toList ++ stmt.linmemProd.toList
      let linRhs := stmt.linmemCons.toList ++ stmt.linmemFinal.toList
      by_cases hCharEq : charPoly linLhs = charPoly linRhs
      · have hLinPerm : linLhs.Perm linRhs := (charPoly_eq_iff_perm linLhs linRhs).mp hCharEq
        have hLupRes0 := hResAll0 (CommRingOps.sub
            (CommRingOps.mul (logUpTableEvalArray stmt.lookupTable wit.lookupMults γLup).1
                             (logUpQueryEvalArray stmt.lookupQueries γLup).2)
            (CommRingOps.mul (logUpQueryEvalArray stmt.lookupQueries γLup).1
                             (logUpTableEvalArray stmt.lookupTable wit.lookupMults γLup).2))
            (by simp [resVec, symbolicResidualVector])
        have hTev := logUpTableEvalArray_eq_spec stmt.lookupTable wit.lookupMults γLup
        have hQev := logUpQueryEvalArray_eq_spec stmt.lookupQueries γLup
        dsimp only at hTev hQev; rw [hTev, hQev] at hLupRes0
        have hLupCross := eq_of_sub_eq_zero hLupRes0
        let lupSubB := stmt.lookupQueries.toList.all (fun q => decide (q ∈ stmt.lookupTable.toList))
        let lupMultB := decide (wit.lookupMults.toList =
          stmt.lookupTable.toList.map (fun t => stmt.lookupQueries.toList.count t))
        cases hLupB : (lupSubB && lupMultB) with
        | true =>
          have hAnd := Bool.and_eq_true _ _ |>.mp hLupB
          have hSubOk : ∀ q ∈ stmt.lookupQueries.toList, q ∈ stmt.lookupTable.toList :=
            fun q hq => of_decide_eq_true (List.all_eq_true.mp hAnd.1 q hq)
          have hMultEq : wit.lookupMults.toList =
              stmt.lookupTable.toList.map (fun t => stmt.lookupQueries.toList.count t) :=
            of_decide_eq_true hAnd.2
          refine .inl ⟨hBefValid, hLinPerm, hSubOk, fun i hti hmi => ?_⟩
          have hget := congrArg (fun l => l[i]?) hMultEq
          rw [List.getElem?_eq_getElem hmi, List.getElem?_map, List.getElem?_eq_getElem hti] at hget
          exact Option.some.inj hget
        | false =>
          refine .inr (.inr (.inl ⟨fun ⟨hqSub, hmIdx⟩ => ?_, hLupCross⟩))
          have hSubTrue : lupSubB = true := List.all_eq_true.mpr fun q hq => decide_eq_true (hqSub q hq)
          have hMultEq : wit.lookupMults.toList =
              stmt.lookupTable.toList.map (fun t => stmt.lookupQueries.toList.count t) :=
            List.ext_getElem (by simp; simpa using hMultSz) fun i h1 h2 => by
              simp only [List.getElem_map]; exact hmIdx i (by simp at h2; exact h2) h1
          have hMultTrue : lupMultB = true := decide_eq_true hMultEq
          rw [hSubTrue, hMultTrue] at hLupB; cases hLupB
      · exact .inr (.inl ⟨fun hp => hCharEq (charPoly_perm hp), hLinEvalEq⟩)
  · rcases verifySumcheck_sound_dichotomy maxDeg stmt.numVars tbl CommRingOps.zero rounds tr claim trFinal
        hAcc (Ne.symm hSumEq0) with hEvalNe | hHit
    · exact .inr (.inr (.inr (.inr (.inr hEvalNe))))
    · exact .inr (.inr (.inr (.inr (.inl hHit))))

private theorem sampleWitnessStructValid :
    stmtWitnessStructValid
      { beforeConstraints := #[⟨2, 5, 4⟩], linmemInit := #[Goldilocks.ofNat 10],
        linmemProd := #[Goldilocks.ofNat 20], linmemCons := #[Goldilocks.ofNat 20],
        linmemFinal := #[Goldilocks.ofNat 10], lookupTable := #[Goldilocks.ofNat 10, Goldilocks.ofNat 20],
        lookupQueries := #[Goldilocks.ofNat 20, Goldilocks.ofNat 10, Goldilocks.ofNat 20], numVars := 3 }
      { beforeBits := #[#[CommRingOps.zero, CommRingOps.one, CommRingOps.zero, CommRingOps.zero]],
        lookupMults := #[1, 2] } = true := by decide

theorem stmtWitnessStructValid_complete (numVars : Nat) :
    ∃ (stmt : SymbolicZkStmt) (wit : SymbolicZkWitness),
      stmt.numVars = numVars ∧ stmtWitnessStructValid stmt wit = true :=
  ⟨{ beforeConstraints := #[⟨2, 5, 4⟩], linmemInit := #[Goldilocks.ofNat 10],
     linmemProd := #[Goldilocks.ofNat 20], linmemCons := #[Goldilocks.ofNat 20],
     linmemFinal := #[Goldilocks.ofNat 10], lookupTable := #[Goldilocks.ofNat 10, Goldilocks.ofNat 20],
     lookupQueries := #[Goldilocks.ofNat 20, Goldilocks.ofNat 10, Goldilocks.ofNat 20], numVars := numVars },
   { beforeBits := #[#[CommRingOps.zero, CommRingOps.one, CommRingOps.zero, CommRingOps.zero]],
     lookupMults := #[1, 2] }, rfl, sampleWitnessStructValid⟩

example : stmtWitnessStructValid
    { beforeConstraints := #[⟨2, 5, 4⟩], linmemInit := #[Goldilocks.ofNat 10],
      linmemProd := #[Goldilocks.ofNat 20], linmemCons := #[Goldilocks.ofNat 20],
      linmemFinal := #[Goldilocks.ofNat 10], lookupTable := #[Goldilocks.ofNat 10, Goldilocks.ofNat 20],
      lookupQueries := #[Goldilocks.ofNat 20, Goldilocks.ofNat 10, Goldilocks.ofNat 20], numVars := 3 }
    { beforeBits := #[#[CommRingOps.zero, CommRingOps.one, CommRingOps.zero, CommRingOps.zero]],
      lookupMults := #[1, 2] } = true := sampleWitnessStructValid

end Obend.SymbolicZk.CompileToPiop
end
