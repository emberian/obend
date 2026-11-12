module
/-
# Obend.Analysis.SimplicialFeecFem — CAD-Conforming Simplicial FEEC, Prager–Synge Continuum PDE Error Certificates & Thomson–Dirichlet Capacitance Brackets

End-to-end verified finite element exterior calculus (`FEEC`) and continuum elliptic PDE
certification over exact rational arithmetic (`Rat`), bridging constructive solid geometry
(`Obend.Hardware.GeometryCAM.FRepExpr`) to certified physical functionals:
1. Verified 2D triangular & 3D tetrahedral simplicial geometry (`SimplexMesh2D`, `SimplexMesh3D`,
   `checkMeshConformingAndCadValid`) bridged to `GeometryCAM.FRepExpr`.
2. Whitney $W^0$ ($P_1$ Lagrange) potentials, $3\times 3$ element stiffness assembly $K_T$, global
   Dirichlet-connected stiffness SPD (`stiffnessMatrix_spd_on_dirichlet_free`), and $H(\mathrm{div})$
   Raviart–Thomas ($RT_0$) equilibrated fluxes (`checkRt0Equilibrated`).
3. Element-by-element Green's identity (`rt0_elem_greens_identity_p2`), global $RT_0$ weak
   equilibration (`rt0_global_greens_equilibration_p1`), constant-free Prager–Synge hypercircle
   error bounds (`pragerSynge_hypercircle_identity`, `pragerSynge_continuum_error_bound`), two-sided
   Thomson–Dirichlet capacitance brackets (`thomsonDirichlet_capacitance_bracket`), and total
   `Obend.Judge` instance `feecPragerSyngeJudge` (`"feec-prager-synge@1"`).
-/
public import Obend.Hardware.GeometryCAM
public import Obend.Judge.Class

public section

namespace Obend.Analysis.SimplicialFeecFem

open Obend.Hardware.GeometryCAM

set_option autoImplicit false

/-! ## 0. Exact Rational Arithmetic & Finite Sum Helpers -/

@[expose] def ratAbs (q : Rat) : Rat := if 0 ≤ q then q else -q

theorem ratAbs_nonneg (q : Rat) : 0 ≤ ratAbs q := by unfold ratAbs; split <;> grind
theorem ratAbs_le_iff (q b : Rat) : ratAbs q ≤ b ↔ (-b ≤ q ∧ q ≤ b) := by unfold ratAbs; split <;> grind
theorem rat_sq_nonneg (q : Rat) : 0 ≤ q * q := rat_sq_nonneg' q

theorem rat_sq_pos_of_ne_zero {q : Rat} (hne : q ≠ 0) : 0 < q * q := by
  have h0 := rat_sq_nonneg q
  have hmul : q * q ≠ 0 := fun h => by
    rcases Rat.mul_eq_zero.mp h with h1 | h2
    · exact hne h1
    · exact hne h2
  grind

theorem rat_div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]; exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr hb))
theorem rat_div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]; exact Rat.mul_pos ha (Rat.inv_pos.mpr hb)
theorem rat_div_le_of_mul_le {a b c : Rat} (hb : 0 < b) (h : a ≤ c * b) : a / b ≤ c := by
  have hCancel := Rat.div_mul_cancel (a := a) (Rat.ne_of_gt hb)
  rcases @Rat.le_total (a / b) c with hle | hge
  · exact hle
  · by_cases heq : a / b = c
    · grind
    · have := Rat.mul_lt_mul_of_pos_right (show c < a / b by grind) hb; grind
theorem rat_le_div_of_mul_le {a b c : Rat} (hb : 0 < b) (h : c * b ≤ a) : c ≤ a / b := by
  have hCancel := Rat.div_mul_cancel (a := a) (Rat.ne_of_gt hb)
  rcases @Rat.le_total c (a / b) with hle | hge
  · exact hle
  · by_cases heq : c = a / b
    · grind
    · have := Rat.mul_lt_mul_of_pos_right (show a / b < c by grind) hb; grind
private theorem list_getD_mem_of_lt {α : Type} :
    ∀ (xs : List α) (d : α) {k : Nat}, k < xs.length → xs.getD k d ∈ xs
  | [], _, _, hk => by simp at hk
  | x :: _, _, 0, _ => List.mem_cons_self ..
  | x :: rest, d, k + 1, hk =>
    List.mem_cons_of_mem x (list_getD_mem_of_lt rest d (by simp at hk; omega))

private theorem list_erase_nodup_props {α : Type} [DecidableEq α] (y : α) :
    ∀ (xs : List α), xs.Nodup →
      (xs.erase y).length ≤ xs.length ∧ (∀ z ∈ xs.erase y, z ∈ xs ∧ z ≠ y)
  | [], _ => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | x :: rest, hnd => by
    obtain ⟨hxNot, hndRest⟩ := List.nodup_cons.mp hnd
    simp only [List.erase_cons]
    by_cases hxy : x == y
    · have heq := eq_of_beq hxy; subst heq
      simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
      exact ⟨by omega, fun z hz => ⟨List.mem_cons_of_mem x hz, fun hzx => hxNot (hzx ▸ hz)⟩⟩
    · simp only [hxy, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      obtain ⟨hlen, hmem⟩ := list_erase_nodup_props y rest hndRest
      refine ⟨by omega, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact ⟨List.mem_cons_self .., fun hzy => by subst hzy; simp at hxy⟩
      · obtain ⟨hzIn, hzNe⟩ := hmem z hz'
        exact ⟨List.mem_cons_of_mem x hzIn, hzNe⟩

@[expose] def sumList {α : Type} : List α → (α → Rat) → Rat
  | [], _ => 0
  | x :: xs, f => f x + sumList xs f

theorem sumList_congr {α : Type} {xs : List α} {f g : α → Rat}
    (h : ∀ x ∈ xs, f x = g x) : sumList xs f = sumList xs g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [sumList]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem sumList_add {α : Type} (xs : List α) (f g : α → Rat) :
    sumList xs (fun x => f x + g x) = sumList xs f + sumList xs g := by
  induction xs with
  | nil => simp only [sumList]; grind
  | cons _ _ ih => simp only [sumList, ih]; grind
theorem sumList_scale {α : Type} (c : Rat) (xs : List α) (f : α → Rat) :
    sumList xs (fun x => c * f x) = c * sumList xs f := by
  induction xs with
  | nil => simp only [sumList]; grind
  | cons _ _ ih => simp only [sumList, ih]; grind
theorem sumList_append {α : Type} (xs ys : List α) (f : α → Rat) :
    sumList (xs ++ ys) f = sumList xs f + sumList ys f := by
  induction xs with
  | nil => simp only [List.nil_append, sumList]; grind
  | cons _ _ ih => simp only [List.cons_append, sumList, ih]; grind
theorem sumList_nonneg {α : Type} {xs : List α} {f : α → Rat}
    (h : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ sumList xs f := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons x rest ih =>
    simp only [sumList]
    have hx := h x (List.mem_cons_self ..)
    have hr := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    grind

theorem sumList_eq_zero_imp_all_zero {α : Type} {xs : List α} {f : α → Rat}
    (hnn : ∀ x ∈ xs, 0 ≤ f x) (hsum : sumList xs f = 0) :
    ∀ x ∈ xs, f x = 0 := by
  induction xs with
  | nil => intro _ hm; cases hm
  | cons x rest ih =>
    simp only [sumList] at hsum
    have hx := hnn x (List.mem_cons_self ..)
    have hrest := sumList_nonneg (xs := rest) (fun y hy => hnn y (List.mem_cons_of_mem x hy))
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · grind
    · exact ih (fun z hz => hnn z (List.mem_cons_of_mem x hz)) (by grind) y hy'

theorem sumList_erase_eq {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (y : α) (f : α → Rat), y ∈ xs →
      sumList xs f = f y + sumList (xs.erase y) f
  | [], _, _, hm => by cases hm
  | x :: rest, y, f, hm => by
    simp only [List.erase_cons]
    by_cases hxy : x == y
    · have heq := eq_of_beq hxy; subst heq; simp [sumList]
    · simp only [hxy, Bool.false_eq_true, ↓reduceIte, sumList]
      have hyRest : y ∈ rest := by
        rcases List.mem_cons.mp hm with rfl | hmem
        · simp at hxy
        · exact hmem
      have ih := sumList_erase_eq rest y f hyRest
      grind

/-- **Involution Cancellation Lemma (`sumList_zero_of_involution`)**. -/
theorem sumList_zero_of_involution {α : Type} [DecidableEq α]
    (π : α → α) (g : α → Rat) :
    ∀ (n : Nat) (xs : List α),
      xs.length ≤ n → xs.Nodup →
      (∀ x ∈ xs, π x ∈ xs) → (∀ x ∈ xs, π (π x) = x) → (∀ x ∈ xs, g x + g (π x) = 0) →
      sumList xs g = 0
  | 0, [], _, _, _, _, _ => rfl
  | 0, _ :: _, hlen, _, _, _, _ => by simp at hlen
  | _ + 1, [], _, _, _, _, _ => rfl
  | n + 1, x :: rest, hlen, hnodup, hclosed, hinv, hcancel => by
    have hxMem : x ∈ x :: rest := List.mem_cons_self ..
    obtain ⟨hxNotRest, hnodupRest⟩ := List.nodup_cons.mp hnodup
    by_cases hself : π x = x
    · have hgx : g x = 0 := by have hc := hcancel x hxMem; rw [hself] at hc; grind
      have hclosedRest : ∀ z ∈ rest, π z ∈ rest := fun z hz => by
        rcases List.mem_cons.mp (hclosed z (List.mem_cons_of_mem x hz)) with heq | hmem
        · have hzEq : z = x := by
            have := hinv z (List.mem_cons_of_mem x hz); rw [heq, hself] at this; exact this.symm
          exact absurd (hzEq ▸ hz) hxNotRest
        · exact hmem
      have ih := sumList_zero_of_involution π g n rest (by simp at hlen; omega) hnodupRest
        hclosedRest (fun z hz => hinv z (List.mem_cons_of_mem x hz))
        (fun z hz => hcancel z (List.mem_cons_of_mem x hz))
      simp only [sumList, hgx, ih]; grind
    · have hyMemRest : π x ∈ rest := by
        rcases List.mem_cons.mp (hclosed x hxMem) with heq | hmem
        · exact absurd heq hself
        · exact hmem
      obtain ⟨hlenE, hmemE⟩ := list_erase_nodup_props (π x) rest hnodupRest
      let rest' := rest.erase (π x)
      have hlenRest' : rest'.length ≤ n := by dsimp only [rest']; simp at hlen; omega
      have hclosedRest' : ∀ z ∈ rest', π z ∈ rest' := fun z hz => by
        obtain ⟨hzRest, hzNeY⟩ := hmemE z hz
        have hpzNeX : π z ≠ x := fun heq => by
          have := hinv z (List.mem_cons_of_mem x hzRest); rw [heq] at this; exact hzNeY this.symm
        have hpzNeY : π z ≠ π x := fun heq => by
          have h1 := hinv z (List.mem_cons_of_mem x hzRest)
          have h2 := hinv x hxMem
          exact hxNotRest ((show z = x by rw [← h1, heq, h2]) ▸ hzRest)
        rcases List.mem_cons.mp (hclosed z (List.mem_cons_of_mem x hzRest)) with heq | hmem
        · exact absurd heq hpzNeX
        · exact (List.mem_erase_of_ne hpzNeY).mpr hmem
      have hMemSub : ∀ z ∈ rest', z ∈ x :: rest :=
        fun z hz => List.mem_cons_of_mem x (hmemE z hz).1
      have ih := sumList_zero_of_involution π g n rest' hlenRest' (hnodupRest.erase (π x))
        hclosedRest' (fun z hz => hinv z (hMemSub z hz)) (fun z hz => hcancel z (hMemSub z hz))
      have herase := sumList_erase_eq rest (π x) g hyMemRest
      have hpair := hcancel x hxMem
      simp only [sumList]; rw [herase]
      change g x + (g (π x) + sumList rest' g) = 0
      rw [ih]; grind

/-! ## 1. Verified CAD-to-Mesh Simplicial Geometry (2D Triangles & 3D Tetrahedra) -/

structure Point2Q where
  x : Rat
  y : Rat
  deriving DecidableEq, Repr
private theorem mkPoint2Q_eq {x1 y1 x2 y2 : Rat} (hx : x1 = x2) (hy : y1 = y2) :
    Point2Q.mk x1 y1 = Point2Q.mk x2 y2 := by subst hx; subst hy; rfl
def add2Q (u v : Point2Q) : Point2Q := ⟨u.x + v.x, u.y + v.y⟩
def sub2Q (u v : Point2Q) : Point2Q := ⟨u.x - v.x, u.y - v.y⟩
def scale2Q (c : Rat) (u : Point2Q) : Point2Q := ⟨c * u.x, c * u.y⟩
def dot2Q (u v : Point2Q) : Rat := u.x * v.x + u.y * v.y
def normSq2Q (u : Point2Q) : Rat := dot2Q u u
def mid2Q (u v : Point2Q) : Point2Q := ⟨(u.x + v.x) / 2, (u.y + v.y) / 2⟩
structure Mat2Q where
  a11 : Rat
  a12 : Rat
  a21 : Rat
  a22 : Rat
  deriving DecidableEq, Repr

def Mat2Q.det (M : Mat2Q) : Rat := M.a11 * M.a22 - M.a12 * M.a21
def Mat2Q.mulVec (M : Mat2Q) (v : Point2Q) : Point2Q :=
  ⟨M.a11 * v.x + M.a12 * v.y, M.a21 * v.x + M.a22 * v.y⟩
def Mat2Q.quadForm (M : Mat2Q) (v : Point2Q) : Rat := dot2Q v (M.mulVec v)
def Mat2Q.inv (M : Mat2Q) : Mat2Q :=
  let d := M.det; ⟨M.a22 / d, (-M.a12) / d, (-M.a21) / d, M.a11 / d⟩
def Mat2Q.isotropic (eps : Rat) : Mat2Q := ⟨eps, 0, 0, eps⟩
def Mat2Q.isSpd (M : Mat2Q) : Prop := M.a12 = M.a21 ∧ 0 < M.a11 ∧ 0 < M.det
def Mat2Q.isSpdB (M : Mat2Q) : Bool :=
  decide (M.a12 = M.a21) && decide (0 < M.a11) && decide (0 < M.det)

theorem mat2Q_quadForm_symm {M : Mat2Q} (hsym : M.a12 = M.a21) (u w : Point2Q) :
    dot2Q u (M.mulVec w) = dot2Q w (M.mulVec u) := by
  unfold Mat2Q.mulVec dot2Q; rw [hsym]; grind

theorem mat2Q_sylvester_identity {M : Mat2Q} (hsym : M.a12 = M.a21) (v : Point2Q) :
    M.a11 * M.quadForm v =
      (M.a11 * v.x + M.a12 * v.y) * (M.a11 * v.x + M.a12 * v.y) + M.det * (v.y * v.y) := by
  unfold Mat2Q.quadForm Mat2Q.mulVec dot2Q Mat2Q.det; rw [hsym]; grind

theorem mat2Q_spd_quadForm_nonneg {M : Mat2Q} (hSpd : M.isSpd) (v : Point2Q) :
    0 ≤ M.quadForm v := by
  obtain ⟨hsym, ha11, hdet⟩ := hSpd
  have hid := mat2Q_sylvester_identity hsym v
  have hsq1 := rat_sq_nonneg (M.a11 * v.x + M.a12 * v.y)
  have hdetTerm := Rat.mul_nonneg (Rat.le_of_lt hdet) (rat_sq_nonneg v.y)
  rcases @Rat.le_total 0 (M.quadForm v) with hpos | hneg
  · exact hpos
  · by_cases hz : M.quadForm v = 0
    · grind
    · have := Rat.mul_lt_mul_of_pos_left (show M.quadForm v < 0 by grind) ha11; grind

theorem mat2Q_spd_quadForm_pos {M : Mat2Q} (hSpd : M.isSpd) (v : Point2Q)
    (hne : v.x ≠ 0 ∨ v.y ≠ 0) : 0 < M.quadForm v := by
  obtain ⟨hsym, ha11, hdet⟩ := hSpd
  have hid := mat2Q_sylvester_identity hsym v
  have hprodPos : 0 < M.a11 * M.quadForm v := by
    by_cases hvy : v.y = 0
    · have hvx : v.x ≠ 0 := by
        rcases hne with hx | hy
        · exact hx
        · exact absurd hvy hy
      have hlinNe : M.a11 * v.x + M.a12 * v.y ≠ 0 := by
        rw [hvy]; intro h0
        rcases Rat.mul_eq_zero.mp (show M.a11 * v.x = 0 by grind) with h1 | h2
        · grind
        · exact hvx h2
      have hsqPos := rat_sq_pos_of_ne_zero hlinNe
      have hvy0 : M.det * (v.y * v.y) = 0 := by rw [hvy]; grind
      grind
    · have hsq1 := rat_sq_nonneg (M.a11 * v.x + M.a12 * v.y)
      have hdetPos := Rat.mul_pos hdet (rat_sq_pos_of_ne_zero hvy)
      grind
  rcases @Rat.le_total (M.quadForm v) 0 with hle | hge
  · have := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt ha11); grind
  · by_cases hz : M.quadForm v = 0
    · rw [hz] at hprodPos; grind
    · grind

theorem mat2Q_inv_mulVec_cancel {M : Mat2Q} (hdet : M.det ≠ 0) (v : Point2Q) :
    M.inv.mulVec (M.mulVec v) = v ∧ M.mulVec (M.inv.mulVec v) = v := by
  unfold Mat2Q.inv Mat2Q.mulVec
  have c22 := Rat.div_mul_cancel (a := M.a22) hdet
  have c12 := Rat.div_mul_cancel (a := -M.a12) hdet
  have c21 := Rat.div_mul_cancel (a := -M.a21) hdet
  have c11 := Rat.div_mul_cancel (a := M.a11) hdet
  have hd : M.a11 * M.a22 - M.a12 * M.a21 = M.det := rfl
  have eqL1 : ((M.a22 / M.det) * (M.a11 * v.x + M.a12 * v.y) +
      ((-M.a12) / M.det) * (M.a21 * v.x + M.a22 * v.y) - v.x) * M.det = 0 := by grind
  have eqL2 : (((-M.a21) / M.det) * (M.a11 * v.x + M.a12 * v.y) +
      (M.a11 / M.det) * (M.a21 * v.x + M.a22 * v.y) - v.y) * M.det = 0 := by grind
  have eqR1 : (M.a11 * ((M.a22 / M.det) * v.x + ((-M.a12) / M.det) * v.y) +
      M.a12 * (((-M.a21) / M.det) * v.x + (M.a11 / M.det) * v.y) - v.x) * M.det = 0 := by grind
  have eqR2 : (M.a21 * ((M.a22 / M.det) * v.x + ((-M.a12) / M.det) * v.y) +
      M.a22 * (((-M.a21) / M.det) * v.x + (M.a11 / M.det) * v.y) - v.y) * M.det = 0 := by grind
  cases v
  refine ⟨mkPoint2Q_eq ?_ ?_, mkPoint2Q_eq ?_ ?_⟩
  · rcases Rat.mul_eq_zero.mp eqL1 with h | h; · grind
    exact absurd h hdet
  · rcases Rat.mul_eq_zero.mp eqL2 with h | h; · grind
    exact absurd h hdet
  · rcases Rat.mul_eq_zero.mp eqR1 with h | h; · grind
    exact absurd h hdet
  · rcases Rat.mul_eq_zero.mp eqR2 with h | h; · grind
    exact absurd h hdet

theorem mat2Q_inv_spd {M : Mat2Q} (hSpd : M.isSpd) : M.inv.isSpd := by
  obtain ⟨hsym, ha11, hdet⟩ := hSpd
  have hne : M.det ≠ 0 := Rat.ne_of_gt hdet
  have ha22 : 0 < M.a22 := by
    have hd : M.a11 * M.a22 = M.det + M.a12 * M.a12 := by unfold Mat2Q.det; rw [hsym]; grind
    have hsq := rat_sq_nonneg M.a12
    rcases @Rat.le_total M.a22 0 with hle | hge
    · have := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt ha11); grind
    · by_cases hz : M.a22 = 0
      · rw [hz] at hd; grind
      · grind
  refine ⟨by unfold Mat2Q.inv; rw [hsym], rat_div_pos ha22 hdet, ?_⟩
  unfold Mat2Q.inv Mat2Q.det; dsimp only
  have c22 := Rat.div_mul_cancel (a := M.a22) hne
  have c12 := Rat.div_mul_cancel (a := -M.a12) hne
  have c21 := Rat.div_mul_cancel (a := -M.a21) hne
  have c11 := Rat.div_mul_cancel (a := M.a11) hne
  have hd : M.a11 * M.a22 - M.a12 * M.a21 = M.det := rfl
  let detInv := (M.a22 / M.det) * (M.a11 / M.det) - ((-M.a12) / M.det) * ((-M.a21) / M.det)
  have hEq : (detInv * M.det) * M.det = M.det := by dsimp only [detInv]; grind
  change 0 < detInv
  rcases @Rat.le_total detInv 0 with hle | hge
  · have h1 := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hdet)
    have h2 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hdet)
    grind
  · by_cases hz : detInv = 0
    · rw [hz] at hEq; grind
    · grind

structure TriElement2D where
  i0 : Nat
  i1 : Nat
  i2 : Nat
  eps : Mat2Q
  sourceF : Rat
  deriving DecidableEq, Repr
def jacobian2D (v0 v1 v2 : Point2Q) : Mat2Q := ⟨v1.x - v0.x, v2.x - v0.x, v1.y - v0.y, v2.y - v0.y⟩
def twiceArea2D (v0 v1 v2 : Point2Q) : Rat := (jacobian2D v0 v1 v2).det
def elemArea2D (v0 v1 v2 : Point2Q) : Rat := twiceArea2D v0 v1 v2 / 2
def sumEdgeLenSq2D (v0 v1 v2 : Point2Q) : Rat :=
  normSq2Q (sub2Q v1 v0) + normSq2Q (sub2Q v2 v1) + normSq2Q (sub2Q v0 v2)
structure Point3Q where
  x : Rat
  y : Rat
  z : Rat
  deriving DecidableEq, Repr
structure TetElement3D where
  i0 : Nat
  i1 : Nat
  i2 : Nat
  i3 : Nat
  epsScalar : Rat
  sourceF : Rat
  deriving DecidableEq, Repr

def sixVolume3D (v0 v1 v2 v3 : Point3Q) : Rat :=
  let dx1 := v1.x - v0.x; let dy1 := v1.y - v0.y; let dz1 := v1.z - v0.z
  let dx2 := v2.x - v0.x; let dy2 := v2.y - v0.y; let dz2 := v2.z - v0.z
  let dx3 := v3.x - v0.x; let dy3 := v3.y - v0.y; let dz3 := v3.z - v0.z
  dx1 * (dy2 * dz3 - dz2 * dy3) - dy1 * (dx2 * dz3 - dz2 * dx3) + dz1 * (dx2 * dy3 - dy2 * dx3)

def tetVolume3D (v0 v1 v2 v3 : Point3Q) : Rat := sixVolume3D v0 v1 v2 v3 / 6

def p1TetGrad3D (v0 v1 v2 v3 : Point3Q) (u0 u1 u2 u3 : Rat) : Point3Q :=
  let d := sixVolume3D v0 v1 v2 v3
  let dx1 := v1.x - v0.x; let dy1 := v1.y - v0.y; let dz1 := v1.z - v0.z
  let dx2 := v2.x - v0.x; let dy2 := v2.y - v0.y; let dz2 := v2.z - v0.z
  let dx3 := v3.x - v0.x; let dy3 := v3.y - v0.y; let dz3 := v3.z - v0.z
  let du1 := u1 - u0; let du2 := u2 - u0; let du3 := u3 - u0
  ⟨((dy2 * dz3 - dz2 * dy3) * du1 + (dz1 * dy3 - dy1 * dz3) * du2 + (dy1 * dz2 - dz1 * dy2) * du3) / d,
   ((dz2 * dx3 - dx2 * dz3) * du1 + (dx1 * dz3 - dz1 * dx3) * du2 + (dz1 * dx2 - dx1 * dz2) * du3) / d,
   ((dx2 * dy3 - dy2 * dx3) * du1 + (dy1 * dx3 - dx1 * dy3) * du2 + (dx1 * dy2 - dy1 * dx2) * du3) / d⟩

structure Rt0ElementFlux3D where
  ax : Rat
  ay : Rat
  az : Rat
  b : Rat
  deriving DecidableEq, Repr
def rt0Div3D (σ : Rt0ElementFlux3D) : Rat := 3 * σ.b
structure SimplexMesh3D where
  verts : List Point3Q
  tets : List TetElement3D
  deriving DecidableEq, Repr

def checkTetMeshOriented (m : SimplexMesh3D) : Bool :=
  !m.tets.isEmpty &&
  m.tets.all (fun K =>
    let n := m.verts.length
    decide (K.i0 < n ∧ K.i1 < n ∧ K.i2 < n ∧ K.i3 < n) &&
    decide (0 < K.epsScalar) &&
    decide (0 < sixVolume3D (m.verts.getD K.i0 ⟨0, 0, 0⟩) (m.verts.getD K.i1 ⟨0, 0, 0⟩)
      (m.verts.getD K.i2 ⟨0, 0, 0⟩) (m.verts.getD K.i3 ⟨0, 0, 0⟩)))

example :
    checkTetMeshOriented
      { verts := [⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩]
        tets := [{ i0 := 0, i1 := 1, i2 := 2, i3 := 3, epsScalar := 1, sourceF := 0 }] } = true := by
  decide +kernel

theorem tetMeshOriented_sound (m : SimplexMesh3D) (hOk : checkTetMeshOriented m = true) :
    (∀ K ∈ m.tets,
      0 < tetVolume3D (m.verts.getD K.i0 ⟨0, 0, 0⟩) (m.verts.getD K.i1 ⟨0, 0, 0⟩)
            (m.verts.getD K.i2 ⟨0, 0, 0⟩) (m.verts.getD K.i3 ⟨0, 0, 0⟩) ∧
      ∀ u0 u1 u2 u3 c : Rat,
        p1TetGrad3D (m.verts.getD K.i0 ⟨0, 0, 0⟩) (m.verts.getD K.i1 ⟨0, 0, 0⟩)
          (m.verts.getD K.i2 ⟨0, 0, 0⟩) (m.verts.getD K.i3 ⟨0, 0, 0⟩)
          (u0 + c) (u1 + c) (u2 + c) (u3 + c) =
        p1TetGrad3D (m.verts.getD K.i0 ⟨0, 0, 0⟩) (m.verts.getD K.i1 ⟨0, 0, 0⟩)
          (m.verts.getD K.i2 ⟨0, 0, 0⟩) (m.verts.getD K.i3 ⟨0, 0, 0⟩) u0 u1 u2 u3) := by
  unfold checkTetMeshOriented at hOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hOk
  intro K hK
  refine ⟨rat_div_pos (hOk.2 K hK).2 (by grind), fun u0 u1 u2 u3 c => ?_⟩
  unfold p1TetGrad3D
  rw [show (u1 + c) - (u0 + c) = u1 - u0 by grind,
      show (u2 + c) - (u0 + c) = u2 - u0 by grind,
      show (u3 + c) - (u0 + c) = u3 - u0 by grind]

/-! ### 1B. CAD Boundary Roles, Conforming 2D Mesh Topology & `GeometryCAM.FRepExpr` Bridge -/

inductive VertexCadRole where
  | interior
  | outerBoundary
  | conductorBoundary (conductorId : Nat)
  deriving DecidableEq, Repr

structure SimplexMesh2D where
  verts : List Point2Q
  vertRoles : List VertexCadRole
  tris : List TriElement2D
  dirichletEdges : List (Nat × Nat)
  neumannEdges : List (Nat × Nat)
  deriving DecidableEq, Repr

def getVert2D (verts : List Point2Q) (i : Nat) : Point2Q := verts.getD i ⟨0, 0⟩
def triHalfEdges (t : TriElement2D) : List (Nat × Nat) := [(t.i0, t.i1), (t.i1, t.i2), (t.i2, t.i0)]
def allMeshHalfEdges (mesh : SimplexMesh2D) : List (Nat × Nat) := mesh.tris.flatMap triHalfEdges

def pointStrictlyInsideSegmentB (va vb vm : Point2Q) : Bool :=
  let dx := vb.x - va.x; let dy := vb.y - va.y
  let wx := vm.x - va.x; let wy := vm.y - va.y
  let lenSq := dx * dx + dy * dy; let proj := wx * dx + wy * dy
  decide (dx * wy = dy * wx) && decide (0 < proj) && decide (proj < lenSq)

def checkVertexRespectsFRep (v : Point2Q) (role : VertexCadRole)
    (cadDomain cadConductorCutout : FRepExpr) (zSlice tauCad : Rat) : Bool :=
  match role with
  | .interior => decide (evalFRepQ v.x v.y zSlice cadDomain ≤ 0)
  | .outerBoundary => decide (ratAbs (evalFRepQ v.x v.y zSlice cadDomain) ≤ tauCad)
  | .conductorBoundary _ =>
    decide (evalFRepQ v.x v.y zSlice cadDomain ≤ tauCad) &&
    decide (ratAbs (evalFRepQ v.x v.y zSlice cadConductorCutout) ≤ tauCad)

def checkMeshRespectsFRepDomain (mesh : SimplexMesh2D)
    (cadDomain cadConductorCutout : FRepExpr) (zSlice tauCad : Rat) : Bool :=
  decide (0 ≤ tauCad) &&
  decide (mesh.vertRoles.length = mesh.verts.length) &&
  (List.range mesh.verts.length).all (fun idx =>
    checkVertexRespectsFRep (getVert2D mesh.verts idx) (mesh.vertRoles.getD idx .interior)
      cadDomain cadConductorCutout zSlice tauCad)

def triBoundingQBox (v0 v1 v2 : Point2Q) (zSlice : Rat) : QBox where
  x := ⟨min v0.x (min v1.x v2.x), max v0.x (max v1.x v2.x)⟩
  y := ⟨min v0.y (min v1.y v2.y), max v0.y (max v1.y v2.y)⟩
  z := ⟨zSlice, zSlice⟩

theorem triBoundingQBox_frep_enclosure_sound
    (v0 v1 v2 : Point2Q) (zSlice l0 l1 l2 : Rat) (e : FRepExpr)
    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) (hsum : l0 + l1 + l2 = 1) :
    let px := l0 * v0.x + l1 * v1.x + l2 * v2.x
    let py := l0 * v0.y + l1 * v1.y + l2 * v2.y
    (evalFRepIntervalQ (triBoundingQBox v0 v1 v2 zSlice) e).contains (evalFRepQ px py zSlice e) := by
  intro px py; apply frepQ_enclosure_sound
  unfold QBox.contains QIv.contains triBoundingQBox; dsimp only
  have xmin : min v0.x (min v1.x v2.x) ≤ v0.x ∧ min v0.x (min v1.x v2.x) ≤ v1.x ∧
      min v0.x (min v1.x v2.x) ≤ v2.x := by rw [Rat.min_def, Rat.min_def]; split <;> split <;> grind
  have xmax : v0.x ≤ max v0.x (max v1.x v2.x) ∧ v1.x ≤ max v0.x (max v1.x v2.x) ∧
      v2.x ≤ max v0.x (max v1.x v2.x) := by rw [Rat.max_def, Rat.max_def]; split <;> split <;> grind
  have ymin : min v0.y (min v1.y v2.y) ≤ v0.y ∧ min v0.y (min v1.y v2.y) ≤ v1.y ∧
      min v0.y (min v1.y v2.y) ≤ v2.y := by rw [Rat.min_def, Rat.min_def]; split <;> split <;> grind
  have ymax : v0.y ≤ max v0.y (max v1.y v2.y) ∧ v1.y ≤ max v0.y (max v1.y v2.y) ∧
      v2.y ≤ max v0.y (max v1.y v2.y) := by rw [Rat.max_def, Rat.max_def]; split <;> split <;> grind
  have x0 := Rat.mul_le_mul_of_nonneg_left xmin.1 hl0
  have x1 := Rat.mul_le_mul_of_nonneg_left xmin.2.1 hl1
  have x2 := Rat.mul_le_mul_of_nonneg_left xmin.2.2 hl2
  have X0 := Rat.mul_le_mul_of_nonneg_left xmax.1 hl0
  have X1 := Rat.mul_le_mul_of_nonneg_left xmax.2.1 hl1
  have X2 := Rat.mul_le_mul_of_nonneg_left xmax.2.2 hl2
  have y0 := Rat.mul_le_mul_of_nonneg_left ymin.1 hl0
  have y1 := Rat.mul_le_mul_of_nonneg_left ymin.2.1 hl1
  have y2 := Rat.mul_le_mul_of_nonneg_left ymin.2.2 hl2
  have Y0 := Rat.mul_le_mul_of_nonneg_left ymax.1 hl0
  have Y1 := Rat.mul_le_mul_of_nonneg_left ymax.2.1 hl1
  have Y2 := Rat.mul_le_mul_of_nonneg_left ymax.2.2 hl2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨Rat.le_refl, Rat.le_refl⟩⟩
  · have : (l0 + l1 + l2) * min v0.x (min v1.x v2.x) = min v0.x (min v1.x v2.x) := by rw [hsum]; grind
    grind
  · have : (l0 + l1 + l2) * max v0.x (max v1.x v2.x) = max v0.x (max v1.x v2.x) := by rw [hsum]; grind
    grind
  · have : (l0 + l1 + l2) * min v0.y (min v1.y v2.y) = min v0.y (min v1.y v2.y) := by rw [hsum]; grind
    grind
  · have : (l0 + l1 + l2) * max v0.y (max v1.y v2.y) = max v0.y (max v1.y v2.y) := by rw [hsum]; grind
    grind

def checkTriElementValid (verts : List Point2Q) (maxAspectRatio : Rat) (t : TriElement2D) : Bool :=
  let n := verts.length
  let v0 := getVert2D verts t.i0; let v1 := getVert2D verts t.i1; let v2 := getVert2D verts t.i2
  let d := twiceArea2D v0 v1 v2
  decide (t.i0 < n ∧ t.i1 < n ∧ t.i2 < n) &&
  decide (t.i0 ≠ t.i1 ∧ t.i1 ≠ t.i2 ∧ t.i2 ≠ t.i0) &&
  decide (0 < d) &&
  decide (sumEdgeLenSq2D v0 v1 v2 ≤ maxAspectRatio * d) &&
  t.eps.isSpdB

def checkMeshTopologyConforming (mesh : SimplexMesh2D) : Bool :=
  let hes := allMeshHalfEdges mesh
  let bdry := mesh.dirichletEdges ++ mesh.neumannEdges
  !mesh.tris.isEmpty &&
  decide hes.Nodup &&
  decide bdry.Nodup &&
  hes.all (fun e =>
    let hasOpp := hes.contains (e.2, e.1)
    let inDir := mesh.dirichletEdges.contains e
    let inNeu := mesh.neumannEdges.contains e
    (hasOpp && !inDir && !inNeu) || (!hasOpp && (inDir != inNeu))) &&
  bdry.all (fun e => hes.contains e && !hes.contains (e.2, e.1)) &&
  hes.all (fun e =>
    let va := getVert2D mesh.verts e.1; let vb := getVert2D mesh.verts e.2
    (List.range mesh.verts.length).all (fun m =>
      decide (m = e.1 ∨ m = e.2) || !pointStrictlyInsideSegmentB va vb (getVert2D mesh.verts m)))

@[expose] def checkMeshConformingAndCadValid (mesh : SimplexMesh2D)
    (cadDomain cadConductorCutout : FRepExpr) (zSlice tauCad maxAspectRatio : Rat) : Bool :=
  mesh.tris.all (checkTriElementValid mesh.verts maxAspectRatio) &&
  checkMeshTopologyConforming mesh &&
  checkMeshRespectsFRepDomain mesh cadDomain cadConductorCutout zSlice tauCad

def unitSquareCadFRep : FRepExpr :=
  .csgInter
    (.csgInter (.sub (.const 0) .varX) (.sub .varX (.const 1)))
    (.csgInter (.sub (.const 0) .varY) (.sub .varY (.const 1)))

def unitSquareCapMesh : SimplexMesh2D where
  verts := [⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩]
  vertRoles := [.outerBoundary, .outerBoundary, .conductorBoundary 1, .conductorBoundary 1]
  tris :=
    [ { i0 := 0, i1 := 1, i2 := 2, eps := Mat2Q.isotropic 4, sourceF := 0 }
    , { i0 := 0, i1 := 2, i2 := 3, eps := Mat2Q.isotropic 4, sourceF := 0 } ]
  dirichletEdges := [(0, 1), (2, 3)]
  neumannEdges := [(1, 2), (3, 0)]

example :
    checkMeshConformingAndCadValid unitSquareCapMesh unitSquareCadFRep
      (.sub .varY (.const 1)) 0 (1 / 100) 10 = true := by decide +kernel

theorem checkMeshConformingAndCadValid_sound
    (mesh : SimplexMesh2D) (cadDomain cadConductorCutout : FRepExpr)
    (zSlice tauCad maxAspectRatio : Rat)
    (hOk : checkMeshConformingAndCadValid mesh cadDomain cadConductorCutout
             zSlice tauCad maxAspectRatio = true) :
    mesh.tris ≠ [] ∧
    (allMeshHalfEdges mesh).Nodup ∧
    0 ≤ tauCad ∧
    (∀ t ∈ mesh.tris,
      let v0 := getVert2D mesh.verts t.i0
      let v1 := getVert2D mesh.verts t.i1
      let v2 := getVert2D mesh.verts t.i2
      0 < twiceArea2D v0 v1 v2 ∧
      0 < elemArea2D v0 v1 v2 ∧
      sumEdgeLenSq2D v0 v1 v2 ≤ maxAspectRatio * twiceArea2D v0 v1 v2 ∧
      t.eps.isSpd) ∧
    (∀ idx < mesh.verts.length,
      mesh.vertRoles.getD idx .interior = .interior →
        evalFRepQ (getVert2D mesh.verts idx).x (getVert2D mesh.verts idx).y zSlice cadDomain ≤ 0) := by
  unfold checkMeshConformingAndCadValid checkMeshTopologyConforming checkMeshRespectsFRepDomain at hOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨hTris, hTopo⟩, hCad⟩ := hOk
  have hNonEmpty : mesh.tris ≠ [] := fun hnil => by
    have hne := hTopo.1.1.1.1.1; rw [hnil] at hne; simp at hne
  refine ⟨hNonEmpty, hTopo.1.1.1.1.2, hCad.1.1, ?_, ?_⟩
  · intro t ht
    have hEl := hTris t ht
    unfold checkTriElementValid Mat2Q.isSpdB at hEl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hEl
    exact ⟨hEl.1.1.2, rat_div_pos hEl.1.1.2 (by grind), hEl.1.2, ⟨hEl.2.1.1, hEl.2.1.2, hEl.2.2⟩⟩
  · intro idx hlt hRole
    have hV := hCad.2 idx (List.mem_range.mpr hlt)
    unfold checkVertexRespectsFRep at hV
    rw [hRole] at hV; exact of_decide_eq_true hV

theorem invertedTriangle_refused
    (mesh : SimplexMesh2D) (cadDomain cadConductorCutout : FRepExpr)
    (zSlice tauCad maxAspectRatio : Rat) (t : TriElement2D) (ht : t ∈ mesh.tris)
    (hInv : twiceArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1)
              (getVert2D mesh.verts t.i2) ≤ 0) :
    checkMeshConformingAndCadValid mesh cadDomain cadConductorCutout
      zSlice tauCad maxAspectRatio = false := by
  cases hB : checkMeshConformingAndCadValid mesh cadDomain cadConductorCutout zSlice tauCad maxAspectRatio
  · rfl
  · have hS := (checkMeshConformingAndCadValid_sound mesh cadDomain cadConductorCutout zSlice tauCad maxAspectRatio hB).2.2.2.1 t ht
    have := hS.1; grind

/-! ## 2. Whitney $W^0$ ($P_1$ Lagrange) Potentials, Stiffness Assembly & $RT_0$ Equilibrated Fluxes -/

def p1EdgeTrace (uh : List Rat) (a b : Nat) (s : Rat) : Rat :=
  (1 - s) * uh.getD a 0 + s * uh.getD b 0

theorem p1_shared_edge_trace_continuous (uh : List Rat) (a b : Nat) (s : Rat) :
    p1EdgeTrace uh a b s = p1EdgeTrace uh b a (1 - s) := by
  unfold p1EdgeTrace; grind

def p1ElemGrad (verts : List Point2Q) (t : TriElement2D) (uh : List Rat) : Point2Q :=
  let v0 := getVert2D verts t.i0; let v1 := getVert2D verts t.i1; let v2 := getVert2D verts t.i2
  let d := twiceArea2D v0 v1 v2
  let du1 := uh.getD t.i1 0 - uh.getD t.i0 0
  let du2 := uh.getD t.i2 0 - uh.getD t.i0 0
  ⟨((v2.y - v0.y) * du1 - (v1.y - v0.y) * du2) / d,
   (-(v2.x - v0.x) * du1 + (v1.x - v0.x) * du2) / d⟩

theorem p1ElemGrad_zero_implies_const (verts : List Point2Q) (t : TriElement2D) (uh : List Rat)
    (hPos : 0 < twiceArea2D (getVert2D verts t.i0) (getVert2D verts t.i1) (getVert2D verts t.i2))
    (hZero : p1ElemGrad verts t uh = ⟨0, 0⟩) :
    uh.getD t.i0 0 = uh.getD t.i1 0 ∧ uh.getD t.i1 0 = uh.getD t.i2 0 := by
  unfold p1ElemGrad at hZero
  injection hZero with hx hy
  let v0 := getVert2D verts t.i0; let v1 := getVert2D verts t.i1; let v2 := getVert2D verts t.i2
  let d := twiceArea2D v0 v1 v2
  have hne : d ≠ 0 := Rat.ne_of_gt hPos
  have hx' : (v2.y - v0.y) * (uh.getD t.i1 0 - uh.getD t.i0 0) -
      (v1.y - v0.y) * (uh.getD t.i2 0 - uh.getD t.i0 0) = 0 := by
    have := Rat.div_mul_cancel (a := (v2.y - v0.y) * (uh.getD t.i1 0 - uh.getD t.i0 0) -
      (v1.y - v0.y) * (uh.getD t.i2 0 - uh.getD t.i0 0)) hne
    change _ / d = 0 at hx; rw [hx] at this; grind
  have hy' : -(v2.x - v0.x) * (uh.getD t.i1 0 - uh.getD t.i0 0) +
      (v1.x - v0.x) * (uh.getD t.i2 0 - uh.getD t.i0 0) = 0 := by
    have := Rat.div_mul_cancel (a := -(v2.x - v0.x) * (uh.getD t.i1 0 - uh.getD t.i0 0) +
      (v1.x - v0.x) * (uh.getD t.i2 0 - uh.getD t.i0 0)) hne
    change _ / d = 0 at hy; rw [hy] at this; grind
  have hdDef : (v1.x - v0.x) * (v2.y - v0.y) - (v2.x - v0.x) * (v1.y - v0.y) = d := rfl
  have u10 : uh.getD t.i1 0 - uh.getD t.i0 0 = 0 := by
    rcases Rat.mul_eq_zero.mp (show d * (uh.getD t.i1 0 - uh.getD t.i0 0) = 0 by grind) with h | h
    · exact absurd h hne
    · exact h
  have u20 : uh.getD t.i2 0 - uh.getD t.i0 0 = 0 := by
    rcases Rat.mul_eq_zero.mp (show d * (uh.getD t.i2 0 - uh.getD t.i0 0) = 0 by grind) with h | h
    · exact absurd h hne
    · exact h
  grind

def p1BasisGrad (v0 v1 v2 : Point2Q) : Fin 3 → Point2Q
  | ⟨0, _⟩ => let d := twiceArea2D v0 v1 v2; ⟨(v1.y - v2.y) / d, (v2.x - v1.x) / d⟩
  | ⟨1, _⟩ => let d := twiceArea2D v0 v1 v2; ⟨(v2.y - v0.y) / d, (v0.x - v2.x) / d⟩
  | ⟨2, _⟩ => let d := twiceArea2D v0 v1 v2; ⟨(v0.y - v1.y) / d, (v1.x - v0.x) / d⟩

def elemLocalDof (uh : List Rat) (t : TriElement2D) : Fin 3 → Rat
  | ⟨0, _⟩ => uh.getD t.i0 0
  | ⟨1, _⟩ => uh.getD t.i1 0
  | ⟨2, _⟩ => uh.getD t.i2 0

def elemStiffnessEntry (verts : List Point2Q) (t : TriElement2D) (a b : Fin 3) : Rat :=
  let v0 := getVert2D verts t.i0; let v1 := getVert2D verts t.i1; let v2 := getVert2D verts t.i2
  elemArea2D v0 v1 v2 * dot2Q (p1BasisGrad v0 v1 v2 a) (t.eps.mulVec (p1BasisGrad v0 v1 v2 b))

def elemStiffnessBilinear (verts : List Point2Q) (t : TriElement2D) (uh wh : List Rat) : Rat :=
  let v0 := getVert2D verts t.i0; let v1 := getVert2D verts t.i1; let v2 := getVert2D verts t.i2
  elemArea2D v0 v1 v2 * dot2Q (p1ElemGrad verts t uh) (t.eps.mulVec (p1ElemGrad verts t wh))

theorem elemStiffnessMatrix_matches_bilinear
    (verts : List Point2Q) (t : TriElement2D) (uh wh : List Rat) :
    let fin3 : List (Fin 3) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
    sumList fin3 (fun a => sumList fin3 (fun b =>
      elemLocalDof uh t a * elemStiffnessEntry verts t a b * elemLocalDof wh t b)) =
    elemStiffnessBilinear verts t uh wh := by
  dsimp only [sumList, elemLocalDof, elemStiffnessEntry, elemStiffnessBilinear, p1BasisGrad, p1ElemGrad,
    Mat2Q.mulVec, dot2Q]
  repeat rw [Rat.div_def]
  grind

def globalStiffnessForm (mesh : SimplexMesh2D) (uh wh : List Rat) : Rat :=
  sumList mesh.tris (fun t => elemStiffnessBilinear mesh.verts t uh wh)

def primalDirichletEnergy (mesh : SimplexMesh2D) (uh : List Rat) : Rat :=
  globalStiffnessForm mesh uh uh

def stepDirichletPinned (tris : List TriElement2D) (pinned : Nat → Bool) : Nat → Bool :=
  fun v =>
    pinned v ||
    tris.any (fun t =>
      decide (v = t.i0 ∨ v = t.i1 ∨ v = t.i2) && (pinned t.i0 || pinned t.i1 || pinned t.i2))

def iterDirichletPinned : Nat → List TriElement2D → (Nat → Bool) → (Nat → Bool)
  | 0, _, pinned => pinned
  | k + 1, tris, pinned => iterDirichletPinned k tris (stepDirichletPinned tris pinned)

def checkDirichletConnected (mesh : SimplexMesh2D) (dirichletVerts : List Nat) : Bool :=
  let reach := iterDirichletPinned mesh.verts.length mesh.tris (fun v => dirichletVerts.contains v)
  (List.range mesh.verts.length).all reach

example : checkDirichletConnected unitSquareCapMesh [0, 1] = true := by decide +kernel

private theorem iterDirichletPinned_preserves_zero
    (tris : List TriElement2D) (uh : List Rat)
    (hConst : ∀ t ∈ tris, uh.getD t.i0 0 = uh.getD t.i1 0 ∧ uh.getD t.i1 0 = uh.getD t.i2 0) :
    ∀ (k : Nat) (pinned : Nat → Bool),
      (∀ v, pinned v = true → uh.getD v 0 = 0) →
      ∀ v, iterDirichletPinned k tris pinned v = true → uh.getD v 0 = 0
  | 0, pinned, hPin, v, hv => hPin v hv
  | k + 1, pinned, hPin, v, hv => by
    apply iterDirichletPinned_preserves_zero tris uh hConst k (stepDirichletPinned tris pinned) ?_ v hv
    intro w hw; unfold stepDirichletPinned at hw
    simp only [Bool.or_eq_true] at hw
    rcases hw with hOld | hNew
    · exact hPin w hOld
    · obtain ⟨t, htMem, htProp⟩ := List.any_eq_true.mp hNew
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at htProp
      have hc := hConst t htMem
      rcases htProp.2 with (hp | hp) | hp
      · have z := hPin t.i0 hp; rcases htProp.1 with rfl | rfl | rfl <;> grind
      · have z := hPin t.i1 hp; rcases htProp.1 with rfl | rfl | rfl <;> grind
      · have z := hPin t.i2 hp; rcases htProp.1 with rfl | rfl | rfl <;> grind

/-- **Global Stiffness Matrix Symmetry & Strict Positive-Definiteness (`stiffnessMatrix_spd_on_dirichlet_free`)**. -/
theorem stiffnessMatrix_spd_on_dirichlet_free
    (mesh : SimplexMesh2D) (dirichletVerts : List Nat)
    (hGeom : ∀ t ∈ mesh.tris,
      0 < twiceArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2) ∧
      t.eps.isSpd)
    (hConn : checkDirichletConnected mesh dirichletVerts = true) :
    (∀ u w : List Rat, globalStiffnessForm mesh u w = globalStiffnessForm mesh w u) ∧
    (∀ u : List Rat, 0 ≤ globalStiffnessForm mesh u u) ∧
    (∀ u : List Rat,
      (∀ d ∈ dirichletVerts, u.getD d 0 = 0) →
      (∃ i < mesh.verts.length, u.getD i 0 ≠ 0) →
      0 < globalStiffnessForm mesh u u) := by
  have hElemNonneg : ∀ (u : List Rat) (t : TriElement2D), t ∈ mesh.tris →
      0 ≤ elemStiffnessBilinear mesh.verts t u u := fun u t ht => by
    obtain ⟨hd, hSpd⟩ := hGeom t ht
    exact Rat.mul_nonneg (Rat.le_of_lt (rat_div_pos hd (by grind)))
      (mat2Q_spd_quadForm_nonneg hSpd (p1ElemGrad mesh.verts t u))
  refine ⟨fun u w => sumList_congr (fun t ht => by
      unfold elemStiffnessBilinear; rw [mat2Q_quadForm_symm (hGeom t ht).2.1]),
    fun u => sumList_nonneg (hElemNonneg u), ?_⟩
  intro u hDir ⟨i, hiLt, hiNe⟩
  have hNonneg : 0 ≤ globalStiffnessForm mesh u u := sumList_nonneg (hElemNonneg u)
  by_cases hZero : globalStiffnessForm mesh u u = 0
  · have hAllElemZero := sumList_eq_zero_imp_all_zero (hElemNonneg u) hZero
    have hConst : ∀ t ∈ mesh.tris, u.getD t.i0 0 = u.getD t.i1 0 ∧ u.getD t.i1 0 = u.getD t.i2 0 := by
      intro t ht
      obtain ⟨hd, hSpd⟩ := hGeom t ht
      have he0 := hAllElemZero t ht
      unfold elemStiffnessBilinear at he0
      have hAreaPos : 0 < elemArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1)
          (getVert2D mesh.verts t.i2) := rat_div_pos hd (by grind)
      have hQuadZero : t.eps.quadForm (p1ElemGrad mesh.verts t u) = 0 := by
        rcases Rat.mul_eq_zero.mp he0 with ha | hq
        · grind
        · exact hq
      have hGradZero : p1ElemGrad mesh.verts t u = ⟨0, 0⟩ := by
        let g := p1ElemGrad mesh.verts t u
        by_cases hgx : g.x = 0
        · by_cases hgy : g.y = 0
          · cases hg : p1ElemGrad mesh.verts t u with | mk gx gy =>
            dsimp only [g] at hgx hgy; rw [hg] at hgx hgy; subst hgx; subst hgy; rfl
          · have := mat2Q_spd_quadForm_pos hSpd g (Or.inr hgy); grind
        · have := mat2Q_spd_quadForm_pos hSpd g (Or.inl hgx); grind
      exact p1ElemGrad_zero_implies_const mesh.verts t u hd hGradZero
    unfold checkDirichletConnected at hConn
    simp only [List.all_eq_true] at hConn
    have hiZero := iterDirichletPinned_preserves_zero mesh.tris u hConst mesh.verts.length
      (fun v => dirichletVerts.contains v) (fun v hv => hDir v (List.contains_iff_mem.mp hv))
      i (hConn i (List.mem_range.mpr hiLt))
    exact absurd hiZero hiNe
  · grind

/-! ### 2B. $H(\mathrm{div})$ Raviart–Thomas ($RT_0$) Equilibrated Fluxes -/

structure Rt0ElementFlux2D where
  ax : Rat
  ay : Rat
  b : Rat
  deriving DecidableEq, Repr

def rt0Eval (σ : Rt0ElementFlux2D) (p : Point2Q) : Point2Q := ⟨σ.ax + σ.b * p.x, σ.ay + σ.b * p.y⟩
def rt0Div (σ : Rt0ElementFlux2D) : Rat := 2 * σ.b
def edgeOutwardNormal (va vb : Point2Q) : Point2Q := ⟨vb.y - va.y, -(vb.x - va.x)⟩

theorem rt0_edge_normal_flux_constant (σ : Rt0ElementFlux2D) (va vb : Point2Q) (s : Rat) :
    let xs : Point2Q := ⟨(1 - s) * va.x + s * vb.x, (1 - s) * va.y + s * vb.y⟩
    dot2Q (rt0Eval σ xs) (edgeOutwardNormal va vb) =
      dot2Q (rt0Eval σ va) (edgeOutwardNormal va vb) := by
  unfold rt0Eval edgeOutwardNormal dot2Q; dsimp only; grind

def rt0HalfEdgeFlux (verts : List Point2Q) (σ : Rt0ElementFlux2D) (e : Nat × Nat) : Rat :=
  let va := getVert2D verts e.1; let vb := getVert2D verts e.2
  dot2Q (rt0Eval σ va) (edgeOutwardNormal va vb)

def allHalfEdgeSlots : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 => allHalfEdgeSlots k ++ [(k, 0), (k, 1), (k, 2)]
def slotHalfEdge (mesh : SimplexMesh2D) (slot : Nat × Nat) : Nat × Nat :=
  match mesh.tris[slot.1]? with
  | some t =>
    if slot.2 == 0 then (t.i0, t.i1) else if slot.2 == 1 then (t.i1, t.i2) else (t.i2, t.i0)
  | none => (0, 0)
def slotNormalFlux (mesh : SimplexMesh2D) (flux : List Rt0ElementFlux2D) (slot : Nat × Nat) : Rat :=
  rt0HalfEdgeFlux mesh.verts (flux.getD slot.1 ⟨0, 0, 0⟩) (slotHalfEdge mesh slot)
def partnerHalfEdgeSlot (mesh : SimplexMesh2D) (slot : Nat × Nat) : Nat × Nat :=
  let e := slotHalfEdge mesh slot
  match (allHalfEdgeSlots mesh.tris.length).find? (fun s' => slotHalfEdge mesh s' == (e.2, e.1)) with
  | some opp => opp
  | none => slot

@[expose] def checkRt0Equilibrated (mesh : SimplexMesh2D) (flux : List Rt0ElementFlux2D) : Bool :=
  let nT := mesh.tris.length
  let slots := allHalfEdgeSlots nT
  decide (flux.length = nT) &&
  (List.range nT).all (fun k =>
    let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    let σ := flux.getD k ⟨0, 0, 0⟩
    decide (rt0Div σ + t.sourceF = 0)) &&
  slots.all (fun slot =>
    let opp := partnerHalfEdgeSlot mesh slot
    let e := slotHalfEdge mesh slot
    if opp != slot then
      decide (partnerHalfEdgeSlot mesh opp = slot) &&
      decide (slotHalfEdge mesh opp = (e.2, e.1)) &&
      decide (slotNormalFlux mesh flux slot + slotNormalFlux mesh flux opp = 0)
    else
      mesh.dirichletEdges.contains e ||
      (mesh.neumannEdges.contains e && decide (slotNormalFlux mesh flux slot = 0)))

def unitSquareExactFlux : List Rt0ElementFlux2D := [⟨0, -4, 0⟩, ⟨0, -4, 0⟩]

example : checkRt0Equilibrated unitSquareCapMesh unitSquareExactFlux = true := by decide +kernel

/-! ## 3. Element-by-Element Green's Identity, Prager–Synge Hypercircle & Thomson–Dirichlet Brackets -/

structure P2ElemDofs where
  w0 : Rat
  w1 : Rat
  w2 : Rat
  w01 : Rat
  w12 : Rat
  w20 : Rat
  deriving DecidableEq, Repr

def p1ToP2Dofs (wh : List Rat) (t : TriElement2D) : P2ElemDofs :=
  let w0 := wh.getD t.i0 0; let w1 := wh.getD t.i1 0; let w2 := wh.getD t.i2 0
  { w0 := w0, w1 := w1, w2 := w2
    w01 := (w0 + w1) / 2, w12 := (w1 + w2) / 2, w20 := (w2 + w0) / 2 }

def p2ScaledGradAt (v0 v1 v2 : Point2Q) (c0 c1 c2 : Rat) : Point2Q :=
  ⟨c0 * (v1.y - v2.y) + c1 * (v2.y - v0.y) + c2 * (v0.y - v1.y),
   c0 * (v2.x - v1.x) + c1 * (v0.x - v2.x) + c2 * (v1.x - v0.x)⟩

def p2ScaledGradMid01 (v0 v1 v2 : Point2Q) (w : P2ElemDofs) : Point2Q :=
  p2ScaledGradAt v0 v1 v2 (w.w0 + 2 * w.w01) (w.w1 + 2 * w.w01) (-w.w2 + 2 * w.w12 + 2 * w.w20)
def p2ScaledGradMid12 (v0 v1 v2 : Point2Q) (w : P2ElemDofs) : Point2Q :=
  p2ScaledGradAt v0 v1 v2 (-w.w0 + 2 * w.w01 + 2 * w.w20) (w.w1 + 2 * w.w12) (w.w2 + 2 * w.w12)
def p2ScaledGradMid20 (v0 v1 v2 : Point2Q) (w : P2ElemDofs) : Point2Q :=
  p2ScaledGradAt v0 v1 v2 (w.w0 + 2 * w.w20) (-w.w1 + 2 * w.w01 + 2 * w.w12) (w.w2 + 2 * w.w20)

def elemIntSigmaDotGradP2 (v0 v1 v2 : Point2Q) (σ : Rt0ElementFlux2D) (w : P2ElemDofs) : Rat :=
  let d := twiceArea2D v0 v1 v2
  (elemArea2D v0 v1 v2 / 3) *
    (dot2Q (rt0Eval σ (mid2Q v0 v1)) (scale2Q (1 / d) (p2ScaledGradMid01 v0 v1 v2 w)) +
     dot2Q (rt0Eval σ (mid2Q v1 v2)) (scale2Q (1 / d) (p2ScaledGradMid12 v0 v1 v2 w)) +
     dot2Q (rt0Eval σ (mid2Q v2 v0)) (scale2Q (1 / d) (p2ScaledGradMid20 v0 v1 v2 w)))

def elemIntDivSigmaMulP2 (v0 v1 v2 : Point2Q) (σ : Rt0ElementFlux2D) (w : P2ElemDofs) : Rat :=
  (elemArea2D v0 v1 v2 / 3) * (rt0Div σ * (w.w01 + w.w12 + w.w20))

def simpsonEdgeAvg (wp wpq wq : Rat) : Rat := (wp + 4 * wpq + wq) / 6

def elemBoundaryFluxIntegralP2 (v0 v1 v2 : Point2Q) (σ : Rt0ElementFlux2D) (w : P2ElemDofs) : Rat :=
  dot2Q (rt0Eval σ v0) (edgeOutwardNormal v0 v1) * simpsonEdgeAvg w.w0 w.w01 w.w1 +
  dot2Q (rt0Eval σ v1) (edgeOutwardNormal v1 v2) * simpsonEdgeAvg w.w1 w.w12 w.w2 +
  dot2Q (rt0Eval σ v2) (edgeOutwardNormal v2 v0) * simpsonEdgeAvg w.w2 w.w20 w.w0

/-- **Exact Element-by-Element Green's Identity on Triangles (`rt0_elem_greens_identity_p2`)**. -/
theorem rt0_elem_greens_identity_p2
    (v0 v1 v2 : Point2Q) (σ : Rt0ElementFlux2D) (w : P2ElemDofs)
    (hPos : 0 < twiceArea2D v0 v1 v2) :
    elemIntSigmaDotGradP2 v0 v1 v2 σ w + elemIntDivSigmaMulP2 v0 v1 v2 σ w =
      elemBoundaryFluxIntegralP2 v0 v1 v2 σ w := by
  let d := twiceArea2D v0 v1 v2
  have hne : d ≠ 0 := Rat.ne_of_gt hPos
  have hScaleCancel : ∀ (p q : Point2Q),
      (elemArea2D v0 v1 v2 / 3) * dot2Q p (scale2Q (1 / d) q) = dot2Q p q / 6 := fun p q => by
    unfold elemArea2D scale2Q dot2Q
    have hc := Rat.div_mul_cancel (a := (1 : Rat)) hne
    have hmul : ((twiceArea2D v0 v1 v2 / 2 / 3) * (p.x * ((1 / d) * q.x) + p.y * ((1 / d) * q.y)) -
        (p.x * q.x + p.y * q.y) / 6) * d = 0 := by grind
    rcases Rat.mul_eq_zero.mp hmul with h | h
    · grind
    · exact absurd h hne
  have hLhs : elemIntSigmaDotGradP2 v0 v1 v2 σ w =
      (dot2Q (rt0Eval σ (mid2Q v0 v1)) (p2ScaledGradMid01 v0 v1 v2 w) +
       dot2Q (rt0Eval σ (mid2Q v1 v2)) (p2ScaledGradMid12 v0 v1 v2 w) +
       dot2Q (rt0Eval σ (mid2Q v2 v0)) (p2ScaledGradMid20 v0 v1 v2 w)) / 6 := by
    unfold elemIntSigmaDotGradP2
    have h1 := hScaleCancel (rt0Eval σ (mid2Q v0 v1)) (p2ScaledGradMid01 v0 v1 v2 w)
    have h2 := hScaleCancel (rt0Eval σ (mid2Q v1 v2)) (p2ScaledGradMid12 v0 v1 v2 w)
    have h3 := hScaleCancel (rt0Eval σ (mid2Q v2 v0)) (p2ScaledGradMid20 v0 v1 v2 w)
    dsimp only [d] at h1 h2 h3; grind
  rw [hLhs]
  unfold elemIntDivSigmaMulP2 elemBoundaryFluxIntegralP2 edgeOutwardNormal simpsonEdgeAvg
  unfold elemArea2D twiceArea2D jacobian2D Mat2Q.det rt0Div rt0Eval mid2Q
  unfold p2ScaledGradMid01 p2ScaledGradMid12 p2ScaledGradMid20 p2ScaledGradAt dot2Q
  dsimp only
  grind

private theorem allHalfEdgeSlots_first_lt : ∀ (n : Nat) (x : Nat × Nat),
    x ∈ allHalfEdgeSlots n → x.1 < n
  | 0, _, hm => by cases hm
  | k + 1, x, hm => by
    simp only [allHalfEdgeSlots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hPrev | rfl | rfl | rfl
    · exact Nat.lt_succ_of_lt (allHalfEdgeSlots_first_lt k x hPrev)
    · omega
    · omega
    · omega

private theorem triple_slots_nodup (k : Nat) : ([(k, 0), (k, 1), (k, 2)] : List (Nat × Nat)).Nodup := by
  refine List.nodup_cons.mpr ⟨by simp, List.nodup_cons.mpr ⟨by simp, List.nodup_cons.mpr ⟨by simp, ?_⟩⟩⟩
  exact (by decide : ([] : List (Nat × Nat)).Nodup)
private theorem allHalfEdgeSlots_nodup : ∀ n : Nat, (allHalfEdgeSlots n).Nodup
  | 0 => by decide
  | k + 1 => by
    simp only [allHalfEdgeSlots]
    exact List.nodup_append.mpr ⟨allHalfEdgeSlots_nodup k, triple_slots_nodup k, fun x hx y hy hxy => by
      subst hxy; have hlt := allHalfEdgeSlots_first_lt k x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl <;> omega⟩
private theorem slotHalfEdge_partner_mem (mesh : SimplexMesh2D) (slot : Nat × Nat)
    (hMem : slot ∈ allHalfEdgeSlots mesh.tris.length) :
    partnerHalfEdgeSlot mesh slot ∈ allHalfEdgeSlots mesh.tris.length := by
  unfold partnerHalfEdgeSlot; dsimp only; split
  · exact List.mem_of_find?_eq_some ‹_›
  · exact hMem
private theorem sumList_range_succ (n : Nat) (f : Nat → Rat) :
    sumList (List.range (n + 1)) f = sumList (List.range n) f + f n := by
  rw [List.range_succ, sumList_append]; simp only [sumList]; grind
private theorem sumList_slots_split (n : Nat) (g : (Nat × Nat) → Rat) :
    sumList (allHalfEdgeSlots n) g =
      sumList (List.range n) (fun k => g (k, 0) + g (k, 1) + g (k, 2)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [allHalfEdgeSlots]; rw [sumList_append, ih, sumList_range_succ]; simp only [sumList]; grind

/-- **Global $RT_0$ Weak Equilibration Theorem (`rt0_global_greens_equilibration_p1`)**. -/
theorem rt0_global_greens_equilibration_p1
    (mesh : SimplexMesh2D) (flux : List Rt0ElementFlux2D) (wh : List Rat)
    (hOriented : ∀ t ∈ mesh.tris,
      0 < twiceArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2))
    (hEq : checkRt0Equilibrated mesh flux = true)
    (hDirZero : ∀ e ∈ mesh.dirichletEdges, wh.getD e.1 0 = 0 ∧ wh.getD e.2 0 = 0) :
    sumList (List.range mesh.tris.length) (fun k =>
      let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
      let σ := flux.getD k ⟨0, 0, 0⟩
      elemIntSigmaDotGradP2 (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1)
        (getVert2D mesh.verts t.i2) σ (p1ToP2Dofs wh t)) =
    sumList (List.range mesh.tris.length) (fun k =>
      let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
      elemArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2) *
        t.sourceF * ((wh.getD t.i0 0 + wh.getD t.i1 0 + wh.getD t.i2 0) / 3)) := by
  unfold checkRt0Equilibrated at hEq
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hEq
  obtain ⟨⟨_, hDivAll⟩, hSlotAll⟩ := hEq
  let edgeTerm : (Nat × Nat) → Rat := fun slot =>
    let e := slotHalfEdge mesh slot
    slotNormalFlux mesh flux slot * ((wh.getD e.1 0 + wh.getD e.2 0) / 2)
  have hBdrySumZero : sumList (allHalfEdgeSlots mesh.tris.length) edgeTerm = 0 := by
    apply sumList_zero_of_involution (partnerHalfEdgeSlot mesh) edgeTerm
      (allHalfEdgeSlots mesh.tris.length).length (allHalfEdgeSlots mesh.tris.length)
      (Nat.le_refl _) (allHalfEdgeSlots_nodup mesh.tris.length) (slotHalfEdge_partner_mem mesh)
    · intro slot hSlot
      have hs := hSlotAll slot hSlot
      split at hs
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hs; exact hs.1.1
      · rename_i hNotDiff
        have hSame : partnerHalfEdgeSlot mesh slot = slot := by revert hNotDiff; simp
        rw [hSame, hSame]
    · intro slot hSlot
      have hs := hSlotAll slot hSlot
      split at hs
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        dsimp only [edgeTerm]; rw [hs.1.2]; have := hs.2; grind
      · rename_i hNotDiff
        have hSame : partnerHalfEdgeSlot mesh slot = slot := by revert hNotDiff; simp
        rw [hSame]; dsimp only [edgeTerm]
        simp only [Bool.or_eq_true] at hs
        rcases hs with hInDir | hInNeu
        · have hz := hDirZero (slotHalfEdge mesh slot) (List.contains_iff_mem.mp hInDir)
          rw [hz.1, hz.2]; grind
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hInNeu
          rw [hInNeu.2]; grind
  rw [sumList_slots_split] at hBdrySumZero
  have hPointwise : ∀ k ∈ List.range mesh.tris.length,
      let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
      let σ := flux.getD k ⟨0, 0, 0⟩
      elemIntSigmaDotGradP2 (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1)
        (getVert2D mesh.verts t.i2) σ (p1ToP2Dofs wh t) =
      (elemArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2) *
        t.sourceF * ((wh.getD t.i0 0 + wh.getD t.i1 0 + wh.getD t.i2 0) / 3)) +
      (edgeTerm (k, 0) + edgeTerm (k, 1) + edgeTerm (k, 2)) := by
    intro k hk; dsimp only
    have hkLt : k < mesh.tris.length := List.mem_range.mp hk
    let dflt : TriElement2D := { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    let t := mesh.tris.getD k dflt
    let σ := flux.getD k ⟨0, 0, 0⟩
    have htSome : mesh.tris[k]? = some t := by simp [t, List.getD_eq_getElem?_getD, hkLt]
    have hGreen := rt0_elem_greens_identity_p2
      (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2)
      σ (p1ToP2Dofs wh t) (hOriented t (list_getD_mem_of_lt mesh.tris dflt hkLt))
    have hDivK : rt0Div σ = -t.sourceF := by
      have hd := hDivAll k hk; dsimp only [t, σ] at hd ⊢; grind
    have hIntDiv : elemIntDivSigmaMulP2 (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1)
        (getVert2D mesh.verts t.i2) σ (p1ToP2Dofs wh t) =
        -(elemArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2) *
          t.sourceF * ((wh.getD t.i0 0 + wh.getD t.i1 0 + wh.getD t.i2 0) / 3)) := by
      unfold elemIntDivSigmaMulP2 p1ToP2Dofs; rw [hDivK]; grind
    have hE0 : slotHalfEdge mesh (k, 0) = (t.i0, t.i1) := by simp [slotHalfEdge, htSome]
    have hE1 : slotHalfEdge mesh (k, 1) = (t.i1, t.i2) := by simp [slotHalfEdge, htSome]
    have hE2 : slotHalfEdge mesh (k, 2) = (t.i2, t.i0) := by simp [slotHalfEdge, htSome]
    have hBdryEq : elemBoundaryFluxIntegralP2 (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1)
        (getVert2D mesh.verts t.i2) σ (p1ToP2Dofs wh t) =
        edgeTerm (k, 0) + edgeTerm (k, 1) + edgeTerm (k, 2) := by
      unfold elemBoundaryFluxIntegralP2 p1ToP2Dofs simpsonEdgeAvg
      dsimp only [edgeTerm, slotNormalFlux, rt0HalfEdgeFlux]
      rw [hE0, hE1, hE2]; dsimp only [σ]; grind
    dsimp only [t, σ, dflt] at hGreen hIntDiv hBdryEq; grind
  rw [sumList_congr hPointwise, sumList_add, hBdrySumZero]; grind

/-! ### 3B. Exact 3-Midpoint Prager–Synge Error Estimator $\eta_{\text{PS}}^2(u_h, \sigma_h)$ & Continuum Hypercircle -/

def pragerSyngeElemSq (verts : List Point2Q) (t : TriElement2D)
    (uh : List Rat) (σ : Rt0ElementFlux2D) : Rat :=
  let v0 := getVert2D verts t.i0; let v1 := getVert2D verts t.i1; let v2 := getVert2D verts t.i2
  let epsGrad := t.eps.mulVec (p1ElemGrad verts t uh)
  let epsInv := t.eps.inv
  let r01 := add2Q (rt0Eval σ (mid2Q v0 v1)) epsGrad
  let r12 := add2Q (rt0Eval σ (mid2Q v1 v2)) epsGrad
  let r20 := add2Q (rt0Eval σ (mid2Q v2 v0)) epsGrad
  (elemArea2D v0 v1 v2 / 3) *
    (epsInv.quadForm r01 + epsInv.quadForm r12 + epsInv.quadForm r20)

@[expose] def pragerSyngeEstimatorSq (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D) : Rat :=
  sumList (List.range mesh.tris.length) (fun k =>
    let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    let σ := flux.getD k ⟨0, 0, 0⟩
    pragerSyngeElemSq mesh.verts t uh σ)

theorem pragerSyngeEstimatorSq_nonneg
    (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D)
    (hGeom : ∀ t ∈ mesh.tris,
      0 < twiceArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2) ∧
      t.eps.isSpd) :
    0 ≤ pragerSyngeEstimatorSq mesh uh flux := by
  unfold pragerSyngeEstimatorSq
  apply sumList_nonneg; intro k hk
  have hkLt : k < mesh.tris.length := List.mem_range.mp hk
  let dflt : TriElement2D := { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
  obtain ⟨hd, hSpd⟩ := hGeom _ (list_getD_mem_of_lt mesh.tris dflt hkLt)
  have hInvSpd := mat2Q_inv_spd hSpd
  dsimp only [pragerSyngeElemSq, elemArea2D]
  have hwPos := rat_div_nonneg (b := 3) (Rat.le_of_lt (rat_div_pos (b := 2) hd (by grind))) (by grind)
  dsimp only [dflt] at hwPos hInvSpd
  exact Rat.mul_nonneg hwPos (Rat.add_nonneg
    (Rat.add_nonneg (mat2Q_spd_quadForm_nonneg hInvSpd _) (mat2Q_spd_quadForm_nonneg hInvSpd _))
    (mat2Q_spd_quadForm_nonneg hInvSpd _))

structure ContinuumEnergySpace (Field : Type) where
  add : Field → Field → Field
  sub : Field → Field → Field
  scale : Rat → Field → Field
  innerEps : Field → Field → Rat
  inner_symm : ∀ f g, innerEps f g = innerEps g f
  inner_nonneg : ∀ f, 0 ≤ innerEps f f
  norm_add_expand : ∀ f g,
    innerEps (add f g) (add f g) = innerEps f f + 2 * innerEps f g + innerEps g g
  norm_sub_symm : ∀ f g,
    innerEps (sub f g) (sub f g) = innerEps (sub g f) (sub g f)
  sub_add_cancel : ∀ a b, add (sub a b) b = a
  sub_add_cancel_mid : ∀ a b c, add (sub a b) (add c b) = add c a
  norm_linComb_expand : ∀ (a b : Rat) (f g : Field),
    innerEps (add (scale a f) (scale b g)) (add (scale a f) (scale b g)) =
      (a * a) * innerEps f f + 2 * (a * b) * innerEps f g + (b * b) * innerEps g g

def ContinuumEnergySpace.normSq {Field : Type} (H : ContinuumEnergySpace Field) (f : Field) : Rat :=
  H.innerEps f f

abbrev MeshMidpointField := Nat → Point2Q × Point2Q × Point2Q

def meshContinuumEnergySpace (mesh : SimplexMesh2D)
    (hGeom : ∀ t ∈ mesh.tris,
      0 < twiceArea2D (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1) (getVert2D mesh.verts t.i2) ∧
      t.eps.isSpd) : ContinuumEnergySpace MeshMidpointField where
  add f g k := ⟨add2Q (f k).1 (g k).1, add2Q (f k).2.1 (g k).2.1, add2Q (f k).2.2 (g k).2.2⟩
  sub f g k := ⟨sub2Q (f k).1 (g k).1, sub2Q (f k).2.1 (g k).2.1, sub2Q (f k).2.2 (g k).2.2⟩
  scale c f k := ⟨scale2Q c (f k).1, scale2Q c (f k).2.1, scale2Q c (f k).2.2⟩
  innerEps f g := sumList (List.range mesh.tris.length) (fun k =>
    let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    let v0 := getVert2D mesh.verts t.i0; let v1 := getVert2D mesh.verts t.i1; let v2 := getVert2D mesh.verts t.i2
    (elemArea2D v0 v1 v2 / 3) *
      (dot2Q (f k).1 (t.eps.mulVec (g k).1) +
       dot2Q (f k).2.1 (t.eps.mulVec (g k).2.1) +
       dot2Q (f k).2.2 (t.eps.mulVec (g k).2.2)))
  inner_symm f g := sumList_congr (fun k hk => by
    let dflt : TriElement2D := { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    have hsym := (hGeom _ (list_getD_mem_of_lt mesh.tris dflt (List.mem_range.mp hk))).2.1
    dsimp only
    rw [mat2Q_quadForm_symm hsym (f k).1, mat2Q_quadForm_symm hsym (f k).2.1, mat2Q_quadForm_symm hsym (f k).2.2])
  inner_nonneg f := sumList_nonneg (fun k hk => by
    let dflt : TriElement2D := { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    obtain ⟨hd, hSpd⟩ := hGeom _ (list_getD_mem_of_lt mesh.tris dflt (List.mem_range.mp hk))
    dsimp only; unfold elemArea2D
    have hw := rat_div_nonneg (b := 3) (Rat.le_of_lt (rat_div_pos (b := 2) hd (by grind))) (by grind)
    have q1 := mat2Q_spd_quadForm_nonneg hSpd (f k).1
    have q2 := mat2Q_spd_quadForm_nonneg hSpd (f k).2.1
    have q3 := mat2Q_spd_quadForm_nonneg hSpd (f k).2.2
    unfold Mat2Q.quadForm at q1 q2 q3; dsimp only [dflt] at hw
    exact Rat.mul_nonneg hw (by grind))
  norm_add_expand f g := by
    rw [← sumList_scale, ← sumList_add, ← sumList_add]
    refine sumList_congr (fun k hk => ?_)
    let dflt : TriElement2D := { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    have hsym := (hGeom _ (list_getD_mem_of_lt mesh.tris dflt (List.mem_range.mp hk))).2.1
    dsimp only [add2Q, Mat2Q.mulVec, dot2Q]
    dsimp only [dflt] at hsym; rw [hsym]; grind
  norm_sub_symm f g := sumList_congr (fun k _ => by dsimp only [sub2Q, Mat2Q.mulVec, dot2Q]; grind)
  sub_add_cancel a b := funext (fun k => by
    dsimp only [add2Q, sub2Q]
    rcases a k with ⟨⟨ax1, ay1⟩, ⟨ax2, ay2⟩, ⟨ax3, ay3⟩⟩
    rcases b k with ⟨⟨bx1, by1⟩, ⟨bx2, by2⟩, ⟨bx3, by3⟩⟩
    exact Prod.ext (mkPoint2Q_eq (by grind) (by grind))
      (Prod.ext (mkPoint2Q_eq (by grind) (by grind)) (mkPoint2Q_eq (by grind) (by grind))))
  sub_add_cancel_mid a b c := funext (fun k => by
    dsimp only [add2Q, sub2Q]
    rcases a k with ⟨⟨ax1, ay1⟩, ⟨ax2, ay2⟩, ⟨ax3, ay3⟩⟩
    rcases b k with ⟨⟨bx1, by1⟩, ⟨bx2, by2⟩, ⟨bx3, by3⟩⟩
    rcases c k with ⟨⟨cx1, cy1⟩, ⟨cx2, cy2⟩, ⟨cx3, cy3⟩⟩
    exact Prod.ext (mkPoint2Q_eq (by grind) (by grind))
      (Prod.ext (mkPoint2Q_eq (by grind) (by grind)) (mkPoint2Q_eq (by grind) (by grind))))
  norm_linComb_expand a b f g := by
    rw [← sumList_scale, ← sumList_scale, ← sumList_scale, ← sumList_add, ← sumList_add]
    refine sumList_congr (fun k hk => ?_)
    let dflt : TriElement2D := { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    have hsym := (hGeom _ (list_getD_mem_of_lt mesh.tris dflt (List.mem_range.mp hk))).2.1
    dsimp only [add2Q, scale2Q, Mat2Q.mulVec, dot2Q]
    dsimp only [dflt] at hsym; rw [hsym]; grind

/-- **Exact Prager–Synge Hypercircle Identity (`pragerSynge_hypercircle_identity`)**. -/
theorem pragerSynge_hypercircle_identity
    {Field : Type} (H : ContinuumEnergySpace Field)
    (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D)
    (gradU gradUh epsInvSigma : Field)
    (hOrtho : H.innerEps (H.sub gradUh gradU) (H.add epsInvSigma gradU) = 0)
    (hEmbed : H.normSq (H.add epsInvSigma gradUh) = pragerSyngeEstimatorSq mesh uh flux) :
    H.normSq (H.sub gradU gradUh) + H.normSq (H.add epsInvSigma gradU) =
      pragerSyngeEstimatorSq mesh uh flux := by
  unfold ContinuumEnergySpace.normSq at hEmbed ⊢
  have hCancel := H.sub_add_cancel_mid gradUh gradU epsInvSigma
  have hExp := H.norm_add_expand (H.sub gradUh gradU) (H.add epsInvSigma gradU)
  rw [hCancel, hEmbed, hOrtho, ← H.norm_sub_symm gradU gradUh] at hExp
  grind

/-- **Constant-Free Prager–Synge Continuum PDE Error Bound (`pragerSynge_continuum_error_bound`)**. -/
theorem pragerSynge_continuum_error_bound
    {Field : Type} (H : ContinuumEnergySpace Field)
    (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D)
    (gradU gradUh epsInvSigma : Field)
    (hOrtho : H.innerEps (H.sub gradUh gradU) (H.add epsInvSigma gradU) = 0)
    (hEmbed : H.normSq (H.add epsInvSigma gradUh) = pragerSyngeEstimatorSq mesh uh flux) :
    H.normSq (H.sub gradU gradUh) ≤ pragerSyngeEstimatorSq mesh uh flux := by
  have hId := pragerSynge_hypercircle_identity H mesh uh flux gradU gradUh epsInvSigma hOrtho hEmbed
  have hDualNonneg : 0 ≤ H.normSq (H.add epsInvSigma gradU) := H.inner_nonneg _
  grind

/-! ### 3C. Thomson–Dirichlet Two-Sided Capacitance / Inductance Brackets -/

def dualComplementaryEnergy (mesh : SimplexMesh2D) (flux : List Rt0ElementFlux2D) : Rat :=
  sumList (List.range mesh.tris.length) (fun k =>
    let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    let σ := flux.getD k ⟨0, 0, 0⟩
    let v0 := getVert2D mesh.verts t.i0; let v1 := getVert2D mesh.verts t.i1; let v2 := getVert2D mesh.verts t.i2
    let epsInv := t.eps.inv
    (elemArea2D v0 v1 v2 / 3) *
      (epsInv.quadForm (rt0Eval σ (mid2Q v0 v1)) +
       epsInv.quadForm (rt0Eval σ (mid2Q v1 v2)) +
       epsInv.quadForm (rt0Eval σ (mid2Q v2 v0))))

def dualNetElectrodeCharge (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D) : Rat :=
  -sumList (List.range mesh.tris.length) (fun k =>
    let t := mesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
    let σ := flux.getD k ⟨0, 0, 0⟩
    elemIntSigmaDotGradP2 (getVert2D mesh.verts t.i0) (getVert2D mesh.verts t.i1)
      (getVert2D mesh.verts t.i2) σ (p1ToP2Dofs uh t))

@[expose] def capacitanceLowerBound (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D) : Rat :=
  let q := dualNetElectrodeCharge mesh uh flux
  (q * q) / dualComplementaryEnergy mesh flux

@[expose] def capacitanceUpperBound (mesh : SimplexMesh2D) (uh : List Rat) : Rat :=
  primalDirichletEnergy mesh uh

/-- **Two-Sided Thomson–Dirichlet Capacitance/Inductance Bracket (`thomsonDirichlet_capacitance_bracket`)**. -/
theorem thomsonDirichlet_capacitance_bracket
    {Field : Type} (H : ContinuumEnergySpace Field)
    (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D)
    (gradU gradUh epsInvSigma : Field) (cTrue : Rat)
    (hcTrue : cTrue = H.normSq gradU)
    (hPrimalEmbed : H.normSq gradUh = capacitanceUpperBound mesh uh)
    (hDualEmbed : H.normSq epsInvSigma = dualComplementaryEnergy mesh flux)
    (hDualPos : 0 < dualComplementaryEnergy mesh flux)
    (hLaplaceWeak : H.innerEps gradU (H.sub gradUh gradU) = 0)
    (hChargePairing : H.innerEps gradU epsInvSigma = -dualNetElectrodeCharge mesh uh flux) :
    capacitanceLowerBound mesh uh flux ≤ cTrue ∧
    cTrue ≤ capacitanceUpperBound mesh uh := by
  unfold ContinuumEnergySpace.normSq at hcTrue hPrimalEmbed hDualEmbed
  constructor
  · unfold capacitanceLowerBound
    let Edual := dualComplementaryEnergy mesh flux
    let Q := dualNetElectrodeCharge mesh uh flux
    apply rat_div_le_of_mul_le hDualPos
    have hPosComb := H.inner_nonneg (H.add (H.scale Edual gradU) (H.scale Q epsInvSigma))
    rw [H.norm_linComb_expand, ← hcTrue, hDualEmbed, hChargePairing] at hPosComb
    have hFactor : 0 ≤ Edual * (cTrue * Edual - Q * Q) := by dsimp only [Edual, Q] at hPosComb ⊢; grind
    rcases @Rat.le_total (Q * Q) (cTrue * Edual) with hle | hge
    · exact hle
    · by_cases heq : Q * Q = cTrue * Edual
      · grind
      · have := Rat.mul_lt_mul_of_pos_left (show cTrue * Edual - Q * Q < 0 by grind) hDualPos
        grind
  · have hId := H.sub_add_cancel gradUh gradU
    have hExp := H.norm_add_expand (H.sub gradUh gradU) gradU
    rw [hId, H.inner_symm (H.sub gradUh gradU) gradU, hLaplaceWeak, hPrimalEmbed, ← hcTrue] at hExp
    have hErrNonneg := H.inner_nonneg (H.sub gradUh gradU)
    grind

theorem thomsonDirichlet_unit_charge_bracket
    {Field : Type} (H : ContinuumEnergySpace Field)
    (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D)
    (gradU gradUh epsInvSigma : Field) (cTrue : Rat)
    (hcTrue : cTrue = H.normSq gradU)
    (hPrimalEmbed : H.normSq gradUh = capacitanceUpperBound mesh uh)
    (hDualEmbed : H.normSq epsInvSigma = dualComplementaryEnergy mesh flux)
    (hDualPos : 0 < dualComplementaryEnergy mesh flux)
    (hLaplaceWeak : H.innerEps gradU (H.sub gradUh gradU) = 0)
    (hChargePairing : H.innerEps gradU epsInvSigma = -dualNetElectrodeCharge mesh uh flux)
    (hUnitCharge : dualNetElectrodeCharge mesh uh flux = 1) :
    1 / dualComplementaryEnergy mesh flux ≤ cTrue ∧
    cTrue ≤ capacitanceUpperBound mesh uh := by
  have hBr := thomsonDirichlet_capacitance_bracket H mesh uh flux gradU gradUh epsInvSigma cTrue
    hcTrue hPrimalEmbed hDualEmbed hDualPos hLaplaceWeak hChargePairing
  unfold capacitanceLowerBound at hBr; dsimp only at hBr
  rw [hUnitCharge, show (1 : Rat) * 1 = 1 by grind] at hBr
  exact hBr

/-! ### 3D. Total `Obend.Judge` Instance (`feecPragerSyngeJudge`, `"feec-prager-synge@1"`) -/

@[expose] def feecFormatName : String := "feec-prager-synge@1"

structure FeecPdeProblem2D where
  mesh : SimplexMesh2D
  cadDomain : FRepExpr
  cadConductorCutout : FRepExpr
  zSlice : Rat
  tauCad : Rat
  maxAspectRatio : Rat
  dirichletGroundVerts : List Nat
  dirichletHotVerts : List Nat
  errorTolSq : Rat
  deriving DecidableEq, Repr

structure FeecPragerSyngeCert2D where
  uh : List Rat
  flux : List Rt0ElementFlux2D
  deriving DecidableEq, Repr

inductive FeecClause where
  | invalidOrInvertedElement | nonConformingMeshTopology | cadBoundaryViolation
  | disconnectedDirichlet | negativeErrorBudget | potentialBoundaryMismatch
  | brokenRt0Equilibration | errorBudgetExceeded
  deriving DecidableEq, Repr

def feecRefutes : FeecClause → Bool
  | .invalidOrInvertedElement | .nonConformingMeshTopology | .cadBoundaryViolation
  | .disconnectedDirichlet | .negativeErrorBudget => true
  | .potentialBoundaryMismatch | .brokenRt0Equilibration | .errorBudgetExceeded => false

def checkPotentialDirichletBC (prob : FeecPdeProblem2D) (uh : List Rat) : Bool :=
  decide (uh.length = prob.mesh.verts.length) &&
  prob.dirichletGroundVerts.all (fun v => decide (uh.getD v 0 = 0)) &&
  prob.dirichletHotVerts.all (fun v => decide (uh.getD v 0 = 1))

def guardFeec (b : Bool) (cl : FeecClause) (rest : Judge.Verdict FeecClause) :
    Judge.Verdict FeecClause :=
  if b then rest else .refused cl []

private theorem guardFeec_cases (b : Bool) (cl : FeecClause) (rest v : Judge.Verdict FeecClause)
    (h : guardFeec b cl rest = v) :
    (b = false ∧ v = .refused cl []) ∨ (b = true ∧ rest = v) := by
  cases b
  · exact Or.inl ⟨rfl, h.symm⟩
  · exact Or.inr ⟨rfl, h⟩

@[expose] def checkFeecPragerSynge (prob : FeecPdeProblem2D) (cert : FeecPragerSyngeCert2D) :
    Judge.Verdict FeecClause :=
  guardFeec (prob.mesh.tris.all (checkTriElementValid prob.mesh.verts prob.maxAspectRatio))
    .invalidOrInvertedElement <|
  guardFeec (checkMeshTopologyConforming prob.mesh) .nonConformingMeshTopology <|
  guardFeec (checkMeshRespectsFRepDomain prob.mesh prob.cadDomain prob.cadConductorCutout
    prob.zSlice prob.tauCad) .cadBoundaryViolation <|
  guardFeec (checkDirichletConnected prob.mesh (prob.dirichletGroundVerts ++ prob.dirichletHotVerts))
    .disconnectedDirichlet <|
  guardFeec (decide (0 ≤ prob.errorTolSq)) .negativeErrorBudget <|
  guardFeec (checkPotentialDirichletBC prob cert.uh) .potentialBoundaryMismatch <|
  guardFeec (checkRt0Equilibrated prob.mesh cert.flux) .brokenRt0Equilibration <|
  guardFeec (decide (pragerSyngeEstimatorSq prob.mesh cert.uh cert.flux ≤ prob.errorTolSq))
    .errorBudgetExceeded .ok

structure CertifiedFeecPde (prob : FeecPdeProblem2D) (cert : FeecPragerSyngeCert2D) : Prop where
  elemsValid : ∀ t ∈ prob.mesh.tris,
    let n := prob.mesh.verts.length
    let v0 := getVert2D prob.mesh.verts t.i0
    let v1 := getVert2D prob.mesh.verts t.i1
    let v2 := getVert2D prob.mesh.verts t.i2
    (t.i0 < n ∧ t.i1 < n ∧ t.i2 < n) ∧
    (t.i0 ≠ t.i1 ∧ t.i1 ≠ t.i2 ∧ t.i2 ≠ t.i0) ∧
    0 < twiceArea2D v0 v1 v2 ∧
    sumEdgeLenSq2D v0 v1 v2 ≤ prob.maxAspectRatio * twiceArea2D v0 v1 v2 ∧
    t.eps.isSpd
  topoConforming : checkMeshTopologyConforming prob.mesh = true
  cadValid : checkMeshRespectsFRepDomain prob.mesh prob.cadDomain prob.cadConductorCutout
    prob.zSlice prob.tauCad = true
  dirichletConn : checkDirichletConnected prob.mesh
    (prob.dirichletGroundVerts ++ prob.dirichletHotVerts) = true
  tolNonneg : 0 ≤ prob.errorTolSq
  bcMatch : cert.uh.length = prob.mesh.verts.length ∧
    (∀ v ∈ prob.dirichletGroundVerts, cert.uh.getD v 0 = 0) ∧
    (∀ v ∈ prob.dirichletHotVerts, cert.uh.getD v 0 = 1)
  rt0Equil : checkRt0Equilibrated prob.mesh cert.flux = true
  estimatorWithinBudget : pragerSyngeEstimatorSq prob.mesh cert.uh cert.flux ≤ prob.errorTolSq
  continuumErrorBound : ∀ {Field : Type} (H : ContinuumEnergySpace Field)
    (gradU gradUh epsInvSigma : Field),
    H.innerEps (H.sub gradUh gradU) (H.add epsInvSigma gradU) = 0 →
    H.normSq (H.add epsInvSigma gradUh) = pragerSyngeEstimatorSq prob.mesh cert.uh cert.flux →
    H.normSq (H.sub gradU gradUh) ≤ prob.errorTolSq

def FeecDecidableFragment (prob : FeecPdeProblem2D) : Prop :=
  checkMeshConformingAndCadValid prob.mesh prob.cadDomain prob.cadConductorCutout
    prob.zSlice prob.tauCad prob.maxAspectRatio = true ∧
  checkDirichletConnected prob.mesh (prob.dirichletGroundVerts ++ prob.dirichletHotVerts) = true ∧
  0 ≤ prob.errorTolSq

theorem checkFeecPragerSynge_sound {prob : FeecPdeProblem2D} {cert : FeecPragerSyngeCert2D}
    (hOk : checkFeecPragerSynge prob cert = .ok) : CertifiedFeecPde prob cert := by
  unfold checkFeecPragerSynge at hOk
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h1, hOk⟩; · cases hv
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h2, hOk⟩; · cases hv
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h3, hOk⟩; · cases hv
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h4, hOk⟩; · cases hv
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h5, hOk⟩; · cases hv
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h6, hOk⟩; · cases hv
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h7, hOk⟩; · cases hv
  rcases guardFeec_cases _ _ _ _ hOk with ⟨_, hv⟩ | ⟨h8, _⟩; · cases hv
  have hEst : pragerSyngeEstimatorSq prob.mesh cert.uh cert.flux ≤ prob.errorTolSq :=
    of_decide_eq_true h8
  refine ⟨?_, h2, h3, h4, of_decide_eq_true h5, ?_, h7, hEst, ?_⟩
  · intro t ht
    have hEl := List.all_eq_true.mp h1 t ht
    unfold checkTriElementValid Mat2Q.isSpdB at hEl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hEl
    exact ⟨hEl.1.1.1.1, hEl.1.1.1.2, hEl.1.1.2, hEl.1.2, ⟨hEl.2.1.1, hEl.2.1.2, hEl.2.2⟩⟩
  · unfold checkPotentialDirichletBC at h6
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h6
    exact ⟨h6.1.1, h6.1.2, h6.2⟩
  · intro Field H gradU gradUh epsInvSigma hOrtho hEmbed
    exact Rat.le_trans
      (pragerSynge_continuum_error_bound H prob.mesh cert.uh cert.flux gradU gradUh epsInvSigma hOrtho hEmbed)
      hEst

theorem checkFeecPragerSynge_refuted {prob : FeecPdeProblem2D} {cert : FeecPragerSyngeCert2D}
    {k : FeecClause} {p : List Nat}
    (hRef : checkFeecPragerSynge prob cert = .refused k p)
    (hIsRef : feecRefutes k = true) (cert' : FeecPragerSyngeCert2D) :
    ¬ CertifiedFeecPde prob cert' := by
  intro hc
  unfold checkFeecPragerSynge at hRef
  rcases guardFeec_cases _ _ _ _ hRef with ⟨hb, _⟩ | ⟨_, hRef⟩
  · have hAll : prob.mesh.tris.all (checkTriElementValid prob.mesh.verts prob.maxAspectRatio) = true := by
      rw [List.all_eq_true]; intro t ht
      obtain ⟨hBnd, hDist, hd, hAsp, hSpd⟩ := hc.elemsValid t ht
      unfold checkTriElementValid Mat2Q.isSpdB
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨hBnd, hDist⟩, hd⟩, hAsp⟩, ⟨⟨hSpd.1, hSpd.2.1⟩, hSpd.2.2⟩⟩
    rw [hAll] at hb; cases hb
  rcases guardFeec_cases _ _ _ _ hRef with ⟨hb, _⟩ | ⟨_, hRef⟩
  · rw [hc.topoConforming] at hb; cases hb
  rcases guardFeec_cases _ _ _ _ hRef with ⟨hb, _⟩ | ⟨_, hRef⟩
  · rw [hc.cadValid] at hb; cases hb
  rcases guardFeec_cases _ _ _ _ hRef with ⟨hb, _⟩ | ⟨_, hRef⟩
  · rw [hc.dirichletConn] at hb; cases hb
  rcases guardFeec_cases _ _ _ _ hRef with ⟨hb, _⟩ | ⟨_, hRef⟩
  · exact (of_decide_eq_false hb) hc.tolNonneg
  rcases guardFeec_cases _ _ _ _ hRef with ⟨_, hv⟩ | ⟨_, hRef⟩
  · injection hv with hkEq _; subst hkEq; cases hIsRef
  rcases guardFeec_cases _ _ _ _ hRef with ⟨_, hv⟩ | ⟨_, hRef⟩
  · injection hv with hkEq _; subst hkEq; cases hIsRef
  rcases guardFeec_cases _ _ _ _ hRef with ⟨_, hv⟩ | ⟨_, hRef⟩
  · injection hv with hkEq _; subst hkEq; cases hIsRef
  cases hRef

theorem checkFeecPragerSynge_complete {prob : FeecPdeProblem2D} {cert : FeecPragerSyngeCert2D}
    (hFrag : FeecDecidableFragment prob) (hc : CertifiedFeecPde prob cert) :
    checkFeecPragerSynge prob cert = .ok := by
  obtain ⟨hMeshOk, hConn, hTol⟩ := hFrag
  unfold checkMeshConformingAndCadValid at hMeshOk
  simp only [Bool.and_eq_true] at hMeshOk
  have hBc : checkPotentialDirichletBC prob cert.uh = true := by
    unfold checkPotentialDirichletBC
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨hc.bcMatch.1, hc.bcMatch.2.1⟩, hc.bcMatch.2.2⟩
  unfold checkFeecPragerSynge guardFeec
  rw [hMeshOk.1.1, hMeshOk.1.2, hMeshOk.2, hConn, decide_eq_true hTol, hBc, hc.rt0Equil,
      decide_eq_true hc.estimatorWithinBudget]
  simp

instance feecPragerSyngeJudge : Obend.Judge FeecPdeProblem2D FeecPragerSyngeCert2D where
  Clause := FeecClause
  Meaning := CertifiedFeecPde
  check := fun _ prob cert => checkFeecPragerSynge prob cert
  sound := fun h => checkFeecPragerSynge_sound h
  refutes := feecRefutes
  refuted := fun h hk c' => checkFeecPragerSynge_refuted h hk c'
  Fragment := FeecDecidableFragment
  complete := fun hf ⟨c, hc⟩ => ⟨c, 0, checkFeecPragerSynge_complete hf hc⟩
  mono := fun _ _ => rfl

def unitSquareCapProblem : FeecPdeProblem2D where
  mesh := unitSquareCapMesh
  cadDomain := unitSquareCadFRep
  cadConductorCutout := .sub .varY (.const 1)
  zSlice := 0
  tauCad := 1 / 100
  maxAspectRatio := 10
  dirichletGroundVerts := [0, 1]
  dirichletHotVerts := [2, 3]
  errorTolSq := 0

def unitSquareCapCert : FeecPragerSyngeCert2D where
  uh := [0, 0, 1, 1]
  flux := unitSquareExactFlux

example : checkFeecPragerSynge unitSquareCapProblem unitSquareCapCert = .ok := by decide +kernel
example : feecPragerSyngeJudge.Fragment unitSquareCapProblem := by
  unfold Judge.Fragment feecPragerSyngeJudge FeecDecidableFragment; decide +kernel

theorem feecFragment_inhabited_for_tol (tolSq : Rat) (hTol : 0 ≤ tolSq) :
    feecPragerSyngeJudge.Fragment { unitSquareCapProblem with errorTolSq := tolSq } := by
  unfold Judge.Fragment feecPragerSyngeJudge FeecDecidableFragment; dsimp only
  exact ⟨by decide +kernel, by decide +kernel, hTol⟩

end Obend.Analysis.SimplicialFeecFem
end
