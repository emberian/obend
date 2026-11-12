module
public import Obend.Analysis.Diff
public import Obend.Judge.Class
/-!
# Certificates for first-order hyperbolic systems (`Obend.Analysis.HyperbolicPdeCert`)

A conservation law `∂_t U + ∂_x F(U) = 0` in `m` variables is hyperbolic at a state when the flux
Jacobian `A = DF(U)` has real eigenvalues and a full set of eigenvectors; equivalently (Friedrichs)
when some symmetric positive definite `H` makes `H·A` symmetric. The judge `hyperbolic-fvm@1` checks
a certificate of that at a state and gives the first-order finite-volume scheme its energy estimate.

* The Jacobian is computed in the kernel by forward-mode dual numbers (`Obend.Analysis.Diff`,
  `HyperbolicSystem.jacobian`); a Jacobian the certificate claims is compared with it, never used.
* `IsEigenSystem`: `A·R = R·Λ`, `R⁻¹·R = R·R⁻¹ = I` over the rationals. In the characteristic
  variables `R⁻¹·v` the system decouples (`char_flux`), and `H = R⁻ᵀ·diag(w)·R⁻¹`, `w > 0`, is a
  Friedrichs symmetrizer: `charForm_pos`, `charForm_flux_symm`, `charForm_flux_le`.
* LeVeque's wave-fluctuation splitting (Finite Volume Methods for Hyperbolic Problems, §4.12):
  `fluctuation_sum` (`A⁻Δ + A⁺Δ = A·Δ`), `fluctuation_zero`, and with the checked Roe condition
  `Certified.fluctuation` (`= F(U_R) - F(U_L)`). The minmod limiter's TVD bounds: `minmod_tvd`.
* `rusanov_energy_run`: under `ν·a ≤ 1` and `|λ_k| ≤ a` the Rusanov (local Lax–Friedrichs) update
  on a periodic grid never increases `Σ_i U_iᵀ·H·U_i`, over any number of steps.
* `hyperbolicPdeJudge`: `check_sound`, `check_refuted` (the object-level clauses, and an eigenvalue
  beyond `aMax` once its eigenpair is verified), `check_complete` (any certificate with the meaning
  yields an accepted one). Accepted below: Maxwell's equations in one dimension, the longitudinal
  part of Munz's perfectly hyperbolic Maxwell system (divergence cleaning), Burgers at a Roe state.

The energy estimate is for the scheme with the frozen matrix `A`: exact for a linear flux (Maxwell),
the linearization at the state otherwise.
-/

public section

namespace Obend.Analysis.HyperbolicPde

set_option autoImplicit false

/-! ## Finite sums, vectors and matrices over the rationals -/

/-- `Σ_{i<n} f i`. -/
def sumTo : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

theorem rat_le_of_eq {a b : Rat} (h : a = b) : a ≤ b := by subst h; exact Rat.le_refl

theorem sumTo_congr {n : Nat} {f g : Nat → Rat} (h : ∀ i, i < n → f i = g i) : sumTo n f = sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumTo_add (n : Nat) (f g : Nat → Rat) : sumTo n (fun i => f i + g i) = sumTo n f + sumTo n g := by
  induction n with
  | zero => simp [sumTo]; grind
  | succ n ih => simp only [sumTo, ih]; grind

theorem sumTo_mul_left (n : Nat) (c : Rat) (f : Nat → Rat) : sumTo n (fun i => c * f i) = c * sumTo n f := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; grind

theorem sumTo_zero (n : Nat) : sumTo n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo, ih]; grind

theorem sumTo_comm (n m : Nat) (f : Nat → Nat → Rat) :
    sumTo n (fun i => sumTo m (fun j => f i j)) = sumTo m (fun j => sumTo n (fun i => f i j)) := by
  induction n with
  | zero => simp only [sumTo]; exact (sumTo_zero m).symm
  | succ n ih => simp only [sumTo, ih]; rw [← sumTo_add]

theorem sumTo_le {n : Nat} {f g : Nat → Rat} (h : ∀ i, i < n → f i ≤ g i) : sumTo n f ≤ sumTo n g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [sumTo]
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h n (Nat.lt_succ_self n)
    grind

theorem sumTo_nonneg {n : Nat} {f : Nat → Rat} (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ sumTo n f := by
  have := sumTo_le (f := fun _ => 0) (g := f) h
  rw [sumTo_zero] at this; exact this

/-- A sum of non-negative terms with a positive one is positive. -/
theorem sumTo_pos {n : Nat} {f : Nat → Rat} (h : ∀ i, i < n → 0 ≤ f i) (k : Nat) (hk : k < n)
    (hpos : 0 < f k) : 0 < sumTo n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumTo]
    have h0 := sumTo_nonneg (fun i hi => h i (Nat.lt_succ_of_lt hi))
    by_cases hkn : k = n
    · subst hkn; grind
    · have := ih (fun i hi => h i (Nat.lt_succ_of_lt hi)) (by omega)
      have := h n (Nat.lt_succ_self n)
      grind

/-- `Σ_{j<n} δ_{ij}·f j = f i` for `i < n`. -/
theorem sumTo_delta (n i : Nat) (hi : i < n) (f : Nat → Rat) :
    sumTo n (fun j => (if i = j then 1 else 0) * f j) = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumTo]
    by_cases hin : i = n
    · subst hin
      have : sumTo i (fun j => (if i = j then (1 : Rat) else 0) * f j) = sumTo i (fun _ => 0) :=
        sumTo_congr (fun j hj => by have : ¬ i = j := by omega
                                    simp only [this, ↓reduceIte]; grind)
      rw [this, sumTo_zero]; simp only [↓reduceIte]; grind
    · rw [ih (by omega)]; simp only [hin, ↓reduceIte]; grind

/-- The first term taken out: `Σ_{i<n+1} f i = f 0 + Σ_{i<n} f (i+1)`. -/
theorem sumTo_succ_front (n : Nat) (f : Nat → Rat) : sumTo (n + 1) f = f 0 + sumTo n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumTo]; grind
  | succ n ih => rw [sumTo, ih]; simp only [sumTo]; grind

abbrev Vec := Nat → Rat
abbrev Mat := Nat → Nat → Rat

/-- The matrix-vector product on the first `m` coordinates. -/
def mulVec (m : Nat) (A : Mat) (v : Vec) : Vec := fun i => sumTo m (fun j => A i j * v j)

def dot (m : Nat) (u v : Vec) : Rat := sumTo m (fun i => u i * v i)

theorem mulVec_congr {m : Nat} {A B : Mat} {u v : Vec} {i : Nat} (hA : ∀ j, j < m → A i j = B i j)
    (h : ∀ j, j < m → u j = v j) : mulVec m A u i = mulVec m B v i :=
  sumTo_congr (fun j hj => by rw [hA j hj, h j hj])

theorem mulVec_lin (m : Nat) (A : Mat) (a b : Rat) (u v : Vec) (i : Nat) :
    mulVec m A (fun j => a * u j + b * v j) i = a * mulVec m A u i + b * mulVec m A v i := by
  simp only [mulVec]
  rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_add]
  exact sumTo_congr (fun j _ => by grind)

theorem mulVec_mulVec (m : Nat) (A B : Mat) (v : Vec) (i : Nat) :
    mulVec m A (mulVec m B v) i = sumTo m (fun k => sumTo m (fun j => A i j * B j k) * v k) := by
  simp only [mulVec]
  have h1 : sumTo m (fun j => A i j * sumTo m (fun k => B j k * v k))
      = sumTo m (fun j => sumTo m (fun k => A i j * (B j k * v k))) :=
    sumTo_congr (fun j _ => (sumTo_mul_left m _ _).symm)
  rw [h1, sumTo_comm]
  refine sumTo_congr (fun k _ => ?_)
  have h2 : sumTo m (fun j => A i j * (B j k * v k)) = sumTo m (fun j => v k * (A i j * B j k)) :=
    sumTo_congr (fun j _ => by grind)
  rw [h2, sumTo_mul_left]; grind

/-! ## Real eigenstructure and characteristic variables -/

/-- `A` has the eigenvectors `R` (columns), eigenvalues `lam` and coordinate map `Rinv` on the first
`m` coordinates: `A·R = R·Λ`, `Rinv·R = I`, `R·Rinv = I`. All eigenvalues are rational, so real. -/
structure IsEigenSystem (m : Nat) (A R Rinv : Mat) (lam : Vec) : Prop where
  eig : ∀ i k, i < m → k < m → sumTo m (fun j => A i j * R j k) = lam k * R i k
  left : ∀ i j, i < m → j < m → sumTo m (fun k => Rinv i k * R k j) = if i = j then 1 else 0
  right : ∀ i j, i < m → j < m → sumTo m (fun k => R i k * Rinv k j) = if i = j then 1 else 0

namespace IsEigenSystem
variable {m : Nat} {A R Rinv : Mat} {lam : Vec}

/-- Every vector is the combination of the eigenvectors with its characteristic coordinates. -/
theorem expand (h : IsEigenSystem m A R Rinv lam) (v : Vec) (i : Nat) (hi : i < m) :
    mulVec m R (mulVec m Rinv v) i = v i := by
  rw [mulVec_mulVec, ← sumTo_delta m i hi v]
  exact sumTo_congr (fun k hk => by rw [h.right i k hi hk])

/-- The characteristic coordinates of a combination of eigenvectors are its coefficients. -/
theorem coords (h : IsEigenSystem m A R Rinv lam) (α : Vec) (k : Nat) (hk : k < m) :
    mulVec m Rinv (mulVec m R α) k = α k := by
  rw [mulVec_mulVec, ← sumTo_delta m k hk α]
  exact sumTo_congr (fun j hj => by rw [h.left k j hk hj])

/-- `A·(R·α) = R·(Λ·α)`. -/
theorem flux_combination (h : IsEigenSystem m A R Rinv lam) (α : Vec) (i : Nat) (hi : i < m) :
    mulVec m A (mulVec m R α) i = mulVec m R (fun k => lam k * α k) i := by
  rw [mulVec_mulVec]
  exact sumTo_congr (fun k hk => by rw [h.eig i k hi hk]; grind)

/-- **The system decouples in characteristic variables**: coordinate `k` of `A·v` is `λ_k` times
coordinate `k` of `v`. -/
theorem char_flux (h : IsEigenSystem m A R Rinv lam) (v : Vec) (k : Nat) (hk : k < m) :
    mulVec m Rinv (mulVec m A v) k = lam k * mulVec m Rinv v k := by
  have e1 : mulVec m Rinv (mulVec m A v) k
      = mulVec m Rinv (mulVec m R (fun k => lam k * mulVec m Rinv v k)) k := by
    refine mulVec_congr (fun _ _ => rfl) (fun i hi => ?_)
    rw [← h.flux_combination _ i hi]
    exact mulVec_congr (fun _ _ => rfl) (fun j hj => (h.expand v j hj).symm)
  rw [e1, h.coords _ k hk]

/-- Column `k` of `R` is an eigenvector. -/
theorem eigenvector (h : IsEigenSystem m A R Rinv lam) (k i : Nat) (hk : k < m) (hi : i < m) :
    mulVec m A (fun j => R j k) i = lam k * R i k := h.eig i k hi hk

/-- An eigenvector is not zero: its own characteristic coordinate is `1`. -/
theorem eigenvector_coord (h : IsEigenSystem m A R Rinv lam) (k : Nat) (hk : k < m) :
    mulVec m Rinv (fun j => R j k) k = 1 := by
  have := h.left k k hk hk
  simp only [↓reduceIte] at this
  exact this

end IsEigenSystem

/-! ## The symmetrizer and the energy form

For positive weights `w`, `H = Rinvᵀ·diag(w)·Rinv` is a Friedrichs symmetrizer of `A`: symmetric
positive definite, with `H·A` symmetric. Its quadratic form is `Σ_k w_k·(Rinv v)_k²`, the energy in
characteristic variables. -/

/-- The energy form `Σ_k w_k·(Rinv u)_k·(Rinv v)_k`. -/
def charForm (m : Nat) (w : Vec) (Rinv : Mat) (u v : Vec) : Rat :=
  sumTo m (fun k => w k * (mulVec m Rinv u k * mulVec m Rinv v k))

/-- `Rinvᵀ·diag(w)·Rinv`, entry by entry. -/
def gram (m : Nat) (w : Vec) (Rinv : Mat) : Mat := fun i j => sumTo m (fun k => w k * (Rinv k i * Rinv k j))

theorem dot_gram (m : Nat) (w : Vec) (Rinv : Mat) (u v : Vec) :
    dot m u (mulVec m (gram m w Rinv) v) = charForm m w Rinv u v := by
  have h1 : ∀ i, mulVec m (gram m w Rinv) v i = sumTo m (fun k => (w k * mulVec m Rinv v k) * Rinv k i) := by
    intro i
    simp only [mulVec, gram]
    have a : sumTo m (fun j => sumTo m (fun k => w k * (Rinv k i * Rinv k j)) * v j)
        = sumTo m (fun j => sumTo m (fun k => v j * (w k * (Rinv k i * Rinv k j)))) :=
      sumTo_congr (fun j _ => by rw [sumTo_mul_left]; grind)
    rw [a, sumTo_comm]
    refine sumTo_congr (fun k _ => ?_)
    have b : sumTo m (fun j => v j * (w k * (Rinv k i * Rinv k j)))
        = sumTo m (fun j => (w k * Rinv k i) * (Rinv k j * v j)) := sumTo_congr (fun j _ => by grind)
    rw [b, sumTo_mul_left]; grind
  simp only [dot, charForm]
  have h2 : sumTo m (fun i => u i * mulVec m (gram m w Rinv) v i)
      = sumTo m (fun i => sumTo m (fun k => u i * ((w k * mulVec m Rinv v k) * Rinv k i))) :=
    sumTo_congr (fun i _ => by rw [h1 i, sumTo_mul_left])
  rw [h2, sumTo_comm]
  refine sumTo_congr (fun k _ => ?_)
  have c : sumTo m (fun i => u i * ((w k * mulVec m Rinv v k) * Rinv k i))
      = sumTo m (fun i => (w k * mulVec m Rinv v k) * (Rinv k i * u i)) := sumTo_congr (fun i _ => by grind)
  rw [c, sumTo_mul_left]; simp only [mulVec]; grind

theorem charForm_symm (m : Nat) (w : Vec) (Rinv : Mat) (u v : Vec) :
    charForm m w Rinv u v = charForm m w Rinv v u :=
  sumTo_congr (fun k _ => by grind)

namespace IsEigenSystem
variable {m : Nat} {A R Rinv : Mat} {lam : Vec}

/-- **Positive definite**: the energy of a vector that is not zero is positive. -/
theorem charForm_pos (h : IsEigenSystem m A R Rinv lam) (w : Vec) (hw : ∀ k, k < m → 0 < w k)
    (v : Vec) (i : Nat) (hi : i < m) (hv : v i ≠ 0) : 0 < charForm m w Rinv v v := by
  have hnn : ∀ k, k < m → 0 ≤ w k * (mulVec m Rinv v k * mulVec m Rinv v k) := fun k hk =>
    Rat.mul_nonneg (Rat.le_of_lt (hw k hk)) (Interval.rat_sq_nonneg _)
  -- some characteristic coordinate is not zero, or `v = R·(Rinv v)` would vanish at `i`
  have hex : ¬ ∀ k, k < m → mulVec m Rinv v k = 0 := by
    intro hz
    have e := h.expand v i hi
    have : mulVec m R (mulVec m Rinv v) i = sumTo m (fun _ => 0) :=
      sumTo_congr (fun k hk => by rw [hz k hk]; grind)
    rw [this, sumTo_zero] at e
    exact hv e.symm
  have hfind : ∀ n, n ≤ m → (∀ k, k < n → mulVec m Rinv v k = 0) ∨ ∃ k, k < n ∧ mulVec m Rinv v k ≠ 0 := by
    intro n
    induction n with
    | zero => intro _; left; intro k hk; omega
    | succ n ih =>
      intro hn
      rcases ih (by omega) with hz | ⟨k, hk, hne⟩
      · by_cases hn0 : mulVec m Rinv v n = 0
        · left; intro k hk
          by_cases hkn : k = n
          · subst hkn; exact hn0
          · exact hz k (by omega)
        · right; exact ⟨n, by omega, hn0⟩
      · right; exact ⟨k, by omega, hne⟩
  rcases hfind m (Nat.le_refl m) with hz | ⟨k, hk, hne⟩
  · exact absurd hz hex
  · refine sumTo_pos hnn k hk ?_
    have hsq : 0 < mulVec m Rinv v k * mulVec m Rinv v k := by
      have := Interval.rat_sq_nonneg (mulVec m Rinv v k)
      have hne2 : mulVec m Rinv v k * mulVec m Rinv v k ≠ 0 := by
        intro e; rcases Rat.mul_eq_zero.mp e with e | e <;> exact hne e
      grind
    exact Rat.mul_pos (hw k hk) hsq

/-- The flux form in characteristic variables: `⟨u, A·v⟩_H = Σ_k w_k·λ_k·(Rinv u)_k·(Rinv v)_k`. -/
theorem charForm_flux (h : IsEigenSystem m A R Rinv lam) (w : Vec) (u v : Vec) :
    charForm m w Rinv u (mulVec m A v)
      = sumTo m (fun k => w k * (lam k * (mulVec m Rinv u k * mulVec m Rinv v k))) :=
  sumTo_congr (fun k hk => by rw [h.char_flux v k hk]; grind)

/-- **Friedrichs symmetry**: `H·A` is symmetric. -/
theorem charForm_flux_symm (h : IsEigenSystem m A R Rinv lam) (w : Vec) (u v : Vec) :
    charForm m w Rinv u (mulVec m A v) = charForm m w Rinv (mulVec m A u) v := by
  rw [charForm_symm m w Rinv (mulVec m A u) v, h.charForm_flux, h.charForm_flux]
  exact sumTo_congr (fun k _ => by grind)

/-- **Wave speeds bound the flux form**: `|⟨v, A·v⟩_H| ≤ a·⟨v, v⟩_H` when every `|λ_k| ≤ a`. -/
theorem charForm_flux_le (h : IsEigenSystem m A R Rinv lam) (w : Vec) (hw : ∀ k, k < m → 0 ≤ w k)
    (a : Rat) (ha : ∀ k, k < m → -a ≤ lam k ∧ lam k ≤ a) (v : Vec) :
    -(a * charForm m w Rinv v v) ≤ charForm m w Rinv v (mulVec m A v) ∧
    charForm m w Rinv v (mulVec m A v) ≤ a * charForm m w Rinv v v := by
  rw [h.charForm_flux]
  simp only [charForm]
  rw [← sumTo_mul_left]
  have key : ∀ k, k < m →
      -(a * (w k * (mulVec m Rinv v k * mulVec m Rinv v k)))
        ≤ w k * (lam k * (mulVec m Rinv v k * mulVec m Rinv v k)) ∧
      w k * (lam k * (mulVec m Rinv v k * mulVec m Rinv v k))
        ≤ a * (w k * (mulVec m Rinv v k * mulVec m Rinv v k)) := by
    intro k hk
    have hq := Rat.mul_nonneg (hw k hk) (Interval.rat_sq_nonneg (mulVec m Rinv v k))
    have m1 := Rat.mul_le_mul_of_nonneg_right (ha k hk).1 hq
    have m2 := Rat.mul_le_mul_of_nonneg_right (ha k hk).2 hq
    constructor <;> grind
  constructor
  · have := sumTo_le (f := fun k => -(a * (w k * (mulVec m Rinv v k * mulVec m Rinv v k))))
      (g := fun k => w k * (lam k * (mulVec m Rinv v k * mulVec m Rinv v k))) (fun k hk => (key k hk).1)
    have e : sumTo m (fun k => -(a * (w k * (mulVec m Rinv v k * mulVec m Rinv v k))))
        = -sumTo m (fun k => a * (w k * (mulVec m Rinv v k * mulVec m Rinv v k))) := by
      rw [show (fun k => -(a * (w k * (mulVec m Rinv v k * mulVec m Rinv v k))))
        = (fun k => (-1) * (a * (w k * (mulVec m Rinv v k * mulVec m Rinv v k)))) from funext (fun k => by grind),
        sumTo_mul_left]; grind
    rw [e] at this; exact this
  · exact sumTo_le (fun k hk => (key k hk).2)

end IsEigenSystem

/-! ## Wave-fluctuation splitting (LeVeque)

The jump `Δ = U_R - U_L` across a cell face is split into waves `W_k = α_k·r_k`, `α = Rinv·Δ`; the
left-going fluctuation `A⁻Δ` collects the waves with negative speed, the right-going `A⁺Δ` those
with positive speed. -/

def negPart (x : Rat) : Rat := if x < 0 then x else 0
def posPart (x : Rat) : Rat := if x < 0 then 0 else x

/-- `A⁻Δ = Σ_k min(λ_k, 0)·α_k·r_k`. -/
def amdq (m : Nat) (R Rinv : Mat) (lam : Vec) (Δ : Vec) : Vec :=
  fun i => sumTo m (fun k => R i k * (negPart (lam k) * mulVec m Rinv Δ k))

/-- `A⁺Δ = Σ_k max(λ_k, 0)·α_k·r_k`. -/
def apdq (m : Nat) (R Rinv : Mat) (lam : Vec) (Δ : Vec) : Vec :=
  fun i => sumTo m (fun k => R i k * (posPart (lam k) * mulVec m Rinv Δ k))

/-- **Conservation of the splitting**: `A⁻Δ + A⁺Δ = A·Δ`, for every jump. -/
theorem fluctuation_sum {m : Nat} {A R Rinv : Mat} {lam : Vec} (h : IsEigenSystem m A R Rinv lam)
    (Δ : Vec) (i : Nat) (hi : i < m) :
    amdq m R Rinv lam Δ i + apdq m R Rinv lam Δ i = mulVec m A Δ i := by
  simp only [amdq, apdq]
  rw [← sumTo_add]
  have e : mulVec m A Δ i = mulVec m A (mulVec m R (mulVec m Rinv Δ)) i :=
    mulVec_congr (fun _ _ => rfl) (fun j hj => (h.expand Δ j hj).symm)
  rw [e, h.flux_combination _ i hi]
  refine sumTo_congr (fun k _ => ?_)
  simp only [negPart, posPart]; split <;> grind

/-- **Consistency**: no jump, no waves. -/
theorem fluctuation_zero (m : Nat) (R Rinv : Mat) (lam : Vec) (Δ : Vec) (hΔ : ∀ j, j < m → Δ j = 0) (i : Nat) :
    amdq m R Rinv lam Δ i = 0 ∧ apdq m R Rinv lam Δ i = 0 := by
  have hα : ∀ k, mulVec m Rinv Δ k = 0 := fun k => by
    have : mulVec m Rinv Δ k = sumTo m (fun _ => 0) := sumTo_congr (fun j hj => by rw [hΔ j hj]; grind)
    rw [this, sumTo_zero]
  constructor
  · have : amdq m R Rinv lam Δ i = sumTo m (fun _ => 0) := sumTo_congr (fun k _ => by rw [hα k]; grind)
    rw [this, sumTo_zero]
  · have : apdq m R Rinv lam Δ i = sumTo m (fun _ => 0) := sumTo_congr (fun k _ => by rw [hα k]; grind)
    rw [this, sumTo_zero]

/-! ## The minmod limiter -/

/-- The smaller in magnitude of two slopes of the same sign, `0` if their signs differ. -/
def minmod (a b : Rat) : Rat :=
  if 0 < a ∧ 0 < b then (if a ≤ b then a else b)
  else if a < 0 ∧ b < 0 then (if a ≤ b then b else a)
  else 0

/-- Linear data keeps its slope. -/
theorem minmod_self (d : Rat) : minmod d d = d := by
  unfold minmod; split
  · simp
  · split
    · simp
    · grind

theorem minmod_comm (a b : Rat) : minmod a b = minmod b a := by
  unfold minmod; (repeat' split) <;> grind

/-- Mirror symmetry. -/
theorem minmod_neg (a b : Rat) : minmod (-a) (-b) = -minmod a b := by
  unfold minmod; (repeat' split) <;> grind

/-- At an extremum (slopes of opposite sign, or one of them zero) the limited slope is `0`. -/
theorem minmod_sign_change (a b : Rat) (h : a * b ≤ 0) : minmod a b = 0 := by
  unfold minmod
  split
  · rename_i hp; have := Rat.mul_pos hp.1 hp.2; grind
  · split
    · rename_i hn
      have := Rat.mul_pos (by grind : (0 : Rat) < -a) (by grind : (0 : Rat) < -b); grind
    · rfl

/-- **The TVD bounds**: the limited slope is a fraction in `[0, 1]` of each one-sided slope
(Harten's condition, the region `0 ≤ φ(r) ≤ min(1, r)` of Sweby's diagram). -/
theorem minmod_tvd (a b : Rat) :
    0 ≤ minmod a b * a ∧ minmod a b * a ≤ a * a ∧ 0 ≤ minmod a b * b ∧ minmod a b * b ≤ b * b := by
  have ha := Interval.rat_sq_nonneg a
  have hb := Interval.rat_sq_nonneg b
  unfold minmod
  split
  · rename_i hp
    have hab := Rat.mul_pos hp.1 hp.2
    split
    · rename_i hle
      have := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hp.2)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
    · rename_i hle
      have := Rat.mul_le_mul_of_nonneg_right (by grind : b ≤ a) (Rat.le_of_lt hp.1)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
  · split
    · rename_i hn
      have hab := Rat.mul_pos (by grind : (0 : Rat) < -a) (by grind : (0 : Rat) < -b)
      split
      · rename_i hle
        have := Rat.mul_le_mul_of_nonneg_right (by grind : -b ≤ -a) (by grind : (0 : Rat) ≤ -a)
        refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
      · rename_i hle
        have := Rat.mul_le_mul_of_nonneg_right (by grind : -a ≤ -b) (by grind : (0 : Rat) ≤ -b)
        refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ## Energy decay of the first-order scheme

The Rusanov (local Lax–Friedrichs) finite-volume update on a periodic grid of `n` cells, with
`ν = Δt/Δx` and numerical viscosity `a`:
`U_i ← U_i - (ν/2)·A·(U_{i+1} - U_{i-1}) + (ν·a/2)·(U_{i+1} - 2·U_i + U_{i-1})`.
In characteristic variables each component is the convex combination
`(1 - ν·a)·x_i + (ν/2)·(a - λ_k)·x_{i+1} + (ν/2)·(a + λ_k)·x_{i-1}` under the CFL condition
`ν·a ≤ 1` and `|λ_k| ≤ a`, so its square is at most the same combination of the squares, and summing
over the periodic grid the energy does not grow. -/

def nextCell (n i : Nat) : Nat := if i + 1 = n then 0 else i + 1
def prevCell (n i : Nat) : Nat := if i = 0 then n - 1 else i - 1

theorem sumTo_next (n : Nat) (f : Nat → Rat) : sumTo n (fun i => f (nextCell n i)) = sumTo n f := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [sumTo_succ_front n f, sumTo]
    have : sumTo n (fun i => f (nextCell (n + 1) i)) = sumTo n (fun i => f (i + 1)) :=
      sumTo_congr (fun i hi => by have : ¬ (i + 1 = n + 1) := by omega
                                  simp only [nextCell, this, ↓reduceIte])
    rw [this]; simp only [nextCell, ↓reduceIte]; grind

theorem sumTo_prev (n : Nat) (f : Nat → Rat) : sumTo n (fun i => f (prevCell n i)) = sumTo n f := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [sumTo_succ_front n (fun i => f (prevCell (n + 1) i))]
    simp only [prevCell, ↓reduceIte, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false,
      sumTo]
    grind

theorem sumTo_shift3 (n : Nat) (a b c : Rat) (f : Nat → Rat) :
    sumTo n (fun i => a * f i + b * f (nextCell n i) + c * f (prevCell n i)) = (a + b + c) * sumTo n f := by
  rw [sumTo_add, sumTo_add, sumTo_mul_left, sumTo_mul_left n b (fun i => f (nextCell n i)),
    sumTo_mul_left n c (fun i => f (prevCell n i)), sumTo_next, sumTo_prev]
  grind

/-- One step of the scheme on a periodic grid of `n` cells. -/
def rusanovStep (m : Nat) (A : Mat) (a ν : Rat) (n : Nat) (U : Nat → Vec) : Nat → Vec := fun i c =>
  U i c - ν / 2 * mulVec m A (fun j => U (nextCell n i) j - U (prevCell n i) j) c
    + ν * a / 2 * (U (nextCell n i) c - 2 * U i c + U (prevCell n i) c)

/-- The discrete energy `Σ_i ⟨U_i, U_i⟩_H`. -/
def gridEnergy (m : Nat) (w : Vec) (Rinv : Mat) (n : Nat) (U : Nat → Vec) : Rat :=
  sumTo n (fun i => charForm m w Rinv (U i) (U i))

theorem mulVec_lin4 (m : Nat) (A : Mat) (a b c d : Rat) (u v x y : Vec) (i : Nat) :
    mulVec m A (fun j => a * u j + b * v j + c * x j + d * y j) i
      = a * mulVec m A u i + b * mulVec m A v i + c * mulVec m A x i + d * mulVec m A y i := by
  simp only [mulVec]
  rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_add, ← sumTo_add,
    ← sumTo_add]
  exact sumTo_congr (fun j _ => by grind)

/-- Jensen's inequality for three points. -/
theorem convex_sq (p q r x y z : Rat) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : p + q + r = 1) :
    (p * x + q * y + r * z) * (p * x + q * y + r * z) ≤ p * (x * x) + q * (y * y) + r * (z * z) := by
  have hr' : r = 1 - p - q := by grind
  subst hr'
  have id : p * (x * x) + q * (y * y) + (1 - p - q) * (z * z)
      - (p * x + q * y + (1 - p - q) * z) * (p * x + q * y + (1 - p - q) * z)
      = p * q * ((x - y) * (x - y)) + p * (1 - p - q) * ((x - z) * (x - z))
        + q * (1 - p - q) * ((y - z) * (y - z)) := by grind
  have n1 := Rat.mul_nonneg (Rat.mul_nonneg hp hq) (Interval.rat_sq_nonneg (x - y))
  have n2 := Rat.mul_nonneg (Rat.mul_nonneg hp hr) (Interval.rat_sq_nonneg (x - z))
  have n3 := Rat.mul_nonneg (Rat.mul_nonneg hq hr) (Interval.rat_sq_nonneg (y - z))
  grind

/-- The step in characteristic variables. -/
theorem rusanovStep_char {m : Nat} {A R Rinv : Mat} {lam : Vec} (h : IsEigenSystem m A R Rinv lam)
    (a ν : Rat) (n : Nat) (U : Nat → Vec) (i k : Nat) (hk : k < m) :
    mulVec m Rinv (rusanovStep m A a ν n U i) k
      = (1 - ν * a) * mulVec m Rinv (U i) k
        + ν / 2 * (a - lam k) * mulVec m Rinv (U (nextCell n i)) k
        + ν / 2 * (a + lam k) * mulVec m Rinv (U (prevCell n i)) k := by
  have e1 : rusanovStep m A a ν n U i
      = fun c => (1 - ν * a) * U i c + ν * a / 2 * U (nextCell n i) c + ν * a / 2 * U (prevCell n i) c
          + -(ν / 2) * mulVec m A (fun j => U (nextCell n i) j - U (prevCell n i) j) c :=
    funext (fun c => by simp only [rusanovStep]; grind)
  have e2 : (fun j => U (nextCell n i) j - U (prevCell n i) j)
      = fun j => 1 * U (nextCell n i) j + -1 * U (prevCell n i) j := funext (fun j => by grind)
  rw [e1, mulVec_lin4, h.char_flux _ k hk, e2, mulVec_lin]
  grind

/-- **Energy decay, one step.** Under the CFL condition `0 ≤ ν`, `ν·a ≤ 1` with `|λ_k| ≤ a`, and
for non-negative weights, the discrete energy does not grow. -/
theorem rusanov_energy_step {m : Nat} {A R Rinv : Mat} {lam : Vec} (h : IsEigenSystem m A R Rinv lam)
    (w : Vec) (hw : ∀ k, k < m → 0 ≤ w k) (a ν : Rat) (hν : 0 ≤ ν) (hcfl : ν * a ≤ 1)
    (ha : ∀ k, k < m → -a ≤ lam k ∧ lam k ≤ a) (n : Nat) (U : Nat → Vec) :
    gridEnergy m w Rinv n (rusanovStep m A a ν n U) ≤ gridEnergy m w Rinv n U := by
  simp only [gridEnergy, charForm]
  have step1 : sumTo n (fun i => sumTo m (fun k =>
        w k * (mulVec m Rinv (rusanovStep m A a ν n U i) k * mulVec m Rinv (rusanovStep m A a ν n U i) k)))
      ≤ sumTo n (fun i => sumTo m (fun k =>
        w k * (1 - ν * a) * (mulVec m Rinv (U i) k * mulVec m Rinv (U i) k)
        + w k * (ν / 2 * (a - lam k)) * (mulVec m Rinv (U (nextCell n i)) k * mulVec m Rinv (U (nextCell n i)) k)
        + w k * (ν / 2 * (a + lam k)) * (mulVec m Rinv (U (prevCell n i)) k * mulVec m Rinv (U (prevCell n i)) k))) := by
    refine sumTo_le (fun i _ => sumTo_le (fun k hk => ?_))
    rw [rusanovStep_char h a ν n U i k hk]
    have hq : 0 ≤ ν / 2 * (a - lam k) := Rat.mul_nonneg (by grind) (by have := (ha k hk).2; grind)
    have hr : 0 ≤ ν / 2 * (a + lam k) := Rat.mul_nonneg (by grind) (by have := (ha k hk).1; grind)
    have hj := convex_sq (1 - ν * a) (ν / 2 * (a - lam k)) (ν / 2 * (a + lam k))
      (mulVec m Rinv (U i) k) (mulVec m Rinv (U (nextCell n i)) k) (mulVec m Rinv (U (prevCell n i)) k)
      (by grind) hq hr (by grind)
    have := Rat.mul_le_mul_of_nonneg_left hj (hw k hk)
    grind
  refine Rat.le_trans step1 (rat_le_of_eq ?_)
  rw [sumTo_comm, sumTo_comm n m]
  refine sumTo_congr (fun k _ => ?_)
  rw [sumTo_shift3 n (w k * (1 - ν * a)) (w k * (ν / 2 * (a - lam k))) (w k * (ν / 2 * (a + lam k)))
    (fun i => mulVec m Rinv (U i) k * mulVec m Rinv (U i) k), ← sumTo_mul_left]
  have : w k * (1 - ν * a) + w k * (ν / 2 * (a - lam k)) + w k * (ν / 2 * (a + lam k)) = w k := by grind
  rw [this]

/-- `N` steps of the scheme. -/
def rusanovRun (m : Nat) (A : Mat) (a ν : Rat) (n : Nat) : Nat → (Nat → Vec) → (Nat → Vec)
  | 0, U => U
  | N + 1, U => rusanovRun m A a ν n N (rusanovStep m A a ν n U)

/-- **Energy decay over any number of steps**: `E(Uᴺ) ≤ E(U⁰)`. -/
theorem rusanov_energy_run {m : Nat} {A R Rinv : Mat} {lam : Vec} (h : IsEigenSystem m A R Rinv lam)
    (w : Vec) (hw : ∀ k, k < m → 0 ≤ w k) (a ν : Rat) (hν : 0 ≤ ν) (hcfl : ν * a ≤ 1)
    (ha : ∀ k, k < m → -a ≤ lam k ∧ lam k ≤ a) (n : Nat) : ∀ (N : Nat) (U : Nat → Vec),
    gridEnergy m w Rinv n (rusanovRun m A a ν n N U) ≤ gridEnergy m w Rinv n U
  | 0, _ => Rat.le_refl
  | N + 1, U =>
    Rat.le_trans (rusanov_energy_run h w hw a ν hν hcfl ha n N _)
      (rusanov_energy_step h w hw a ν hν hcfl ha n U)

/-! ## The certificate and its checker (`hyperbolic-fvm@1`) -/

/-- Entry `i` of a list, `d` past its end. -/
def getOr {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, i + 1, d => getOr xs i d

/-- `[f k, f (k+1), …]`, `n` entries. -/
def tabFrom {α : Type} (f : Nat → α) : Nat → Nat → List α
  | _, 0 => []
  | k, n + 1 => f k :: tabFrom f (k + 1) n

theorem getOr_tabFrom {α : Type} (f : Nat → α) (d : α) : ∀ (n k i : Nat), i < n → getOr (tabFrom f k n) i d = f (k + i)
  | 0, _, _, h => by omega
  | n + 1, k, 0, _ => rfl
  | n + 1, k, i + 1, h => by
    simp only [tabFrom, getOr]
    rw [getOr_tabFrom f d n (k + 1) i (by omega)]
    congr 1; omega

def matOf (rows : List (List Rat)) : Mat := fun i j => getOr (getOr rows i []) j 0
def vecOf (xs : List Rat) : Vec := fun i => getOr xs i 0

/-- The assignment of the listed values to the listed variables (`0` elsewhere). -/
def envOf : List String → List Rat → String → Rat
  | x :: xs, v :: vs, y => if y == x then v else envOf xs vs y
  | _, _, _ => 0

/-- A first-order system `∂_t U + ∂_x F(U) = 0` at a state, with the Riemann problem `(left, right)`
its conservation is checked on, the claimed bound `aMax` on its wave speeds and the scheme's
`cfl = Δt/Δx`. -/
structure HyperbolicSystem where
  /-- the conserved variables' names -/
  vars : List String
  /-- the flux components, expressions in the variables -/
  flux : List RealExpr
  /-- the state the system is linearized at -/
  state : List Rat
  left : List Rat
  right : List Rat
  aMax : Rat
  cfl : Rat

namespace HyperbolicSystem

def dim (o : HyperbolicSystem) : Nat := o.vars.length

/-- One flux, one state value and one left and right value per variable. -/
@[expose] def WellFormed (o : HyperbolicSystem) : Prop :=
  o.flux.length = o.vars.length ∧ o.state.length = o.vars.length ∧ o.left.length = o.vars.length ∧
    o.right.length = o.vars.length

instance (o : HyperbolicSystem) : Decidable o.WellFormed :=
  inferInstanceAs (Decidable (o.flux.length = o.vars.length ∧ o.state.length = o.vars.length ∧
    o.left.length = o.vars.length ∧ o.right.length = o.vars.length))

/-- **The Fréchet derivative of the flux at the state**, by forward-mode dual numbers: entry
`(i, j)` is `∂F_i/∂u_j`. No Jacobian is taken on trust; this is the one every check uses. -/
def jacobian (o : HyperbolicSystem) : Mat := fun i j =>
  (evalDualRat (envOf o.vars o.state) (getOr o.vars j "") (getOr o.flux i (.const 0))).der

/-- Flux component `i` at the listed values. -/
def fluxAt (o : HyperbolicSystem) (vals : List Rat) (i : Nat) : Rat :=
  evalExpr (envOf o.vars vals) (getOr o.flux i (.const 0))

/-- The jump of the Riemann problem. -/
def jump (o : HyperbolicSystem) : Vec := fun j => vecOf o.right j - vecOf o.left j

end HyperbolicSystem

/-- The certificate: the Jacobian the author claims, a real eigen-decomposition of it, and a
symmetrizer `sym = eigInvᵀ·diag(weights)·eigInv` with positive weights. -/
structure HyperbolicCert where
  jac : List (List Rat)
  /-- `R`: column `k` is the `k`-th right eigenvector -/
  eigVecs : List (List Rat)
  eigVals : List Rat
  /-- `R⁻¹` -/
  eigInv : List (List Rat)
  weights : List Rat
  sym : List (List Rat)

inductive Clause where
  /-- the system's lists have different lengths -/
  | shapeMismatch
  /-- `Δt/Δx` is negative or `Δt/Δx·aMax > 1` -/
  | cflViolation
  /-- `A·(right - left) ≠ F(right) - F(left)` in a component -/
  | conservationDefect
  /-- the claimed Jacobian differs from the dual-number derivative -/
  | jacobianMismatch
  /-- `A·R ≠ R·Λ` in an entry -/
  | eigenMismatch
  /-- `R⁻¹·R ≠ I` or `R·R⁻¹ ≠ I` in an entry -/
  | inverseMismatch
  /-- an eigenvalue of the verified decomposition exceeds `aMax` -/
  | speedExceedsBound
  /-- a symmetrizer weight is not positive -/
  | weightNotPositive
  /-- the claimed symmetrizer is not the weighted Gram matrix -/
  | symmetrizerMismatch
  deriving DecidableEq, Repr

/-- The least `i < n` at which `p` fails. -/
def firstBad : Nat → (Nat → Bool) → Option Nat
  | 0, _ => none
  | n + 1, p => match firstBad n p with
    | some i => some i
    | none => if p n then none else some n

theorem firstBad_none : ∀ (n : Nat) (p : Nat → Bool), firstBad n p = none ↔ ∀ i, i < n → p i = true
  | 0, _ => ⟨fun _ i hi => by omega, fun _ => rfl⟩
  | n + 1, p => by
    simp only [firstBad]
    cases h : firstBad n p with
    | some i =>
      simp only [reduceCtorEq, false_iff]
      intro hall
      have := (firstBad_none n p).mpr (fun i hi => hall i (by omega))
      rw [this] at h; cases h
    | none =>
      have ih := (firstBad_none n p).mp h
      by_cases hp : p n = true
      · simp only [hp, ↓reduceIte, true_iff]
        intro i hi
        by_cases hin : i = n
        · subst hin; exact hp
        · exact ih i (by omega)
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
        intro hall; exact hp (hall n (by omega))

theorem firstBad_some : ∀ (n : Nat) (p : Nat → Bool) (i : Nat), firstBad n p = some i → i < n ∧ p i = false
  | 0, _, _, h => by cases h
  | n + 1, p, i, h => by
    simp only [firstBad] at h
    cases h' : firstBad n p with
    | some j =>
      rw [h'] at h; simp only [Option.some.injEq] at h; subst h
      have := firstBad_some n p _ h'
      exact ⟨by omega, this.2⟩
    | none =>
      rw [h'] at h
      by_cases hp : p n = true
      · simp [hp] at h
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h; exact ⟨by omega, by simpa using hp⟩

/-- The first entry `(i, j)`, `i, j < m`, at which `p` fails. -/
def firstBad2 (m : Nat) (p : Nat → Nat → Bool) : Option (Nat × Nat) :=
  match firstBad m (fun i => (firstBad m (p i)).isNone) with
  | none => none
  | some i => some (i, (firstBad m (p i)).getD 0)

theorem firstBad2_none (m : Nat) (p : Nat → Nat → Bool) :
    firstBad2 m p = none ↔ ∀ i j, i < m → j < m → p i j = true := by
  simp only [firstBad2]
  constructor
  · intro h i j hi hj
    cases h' : firstBad m (fun i => (firstBad m (p i)).isNone) with
    | some k => rw [h'] at h; cases h
    | none =>
      have := (firstBad_none m _).mp h' i hi
      simp only [Option.isNone_iff_eq_none] at this
      exact (firstBad_none m (p i)).mp this j hj
  · intro h
    have : firstBad m (fun i => (firstBad m (p i)).isNone) = none :=
      (firstBad_none m _).mpr (fun i hi => by
        simp only [Option.isNone_iff_eq_none]
        exact (firstBad_none m (p i)).mpr (fun j hj => h i j hi hj))
    rw [this]

section Checks
variable (o : HyperbolicSystem) (c : HyperbolicCert)

def cflB : Bool := decide (0 ≤ o.cfl ∧ o.cfl * o.aMax ≤ 1)
def conservB (i : Nat) : Bool :=
  decide (mulVec o.dim o.jacobian o.jump i = o.fluxAt o.right i - o.fluxAt o.left i)
def jacB (i j : Nat) : Bool := decide (matOf c.jac i j = o.jacobian i j)
def eigB (i k : Nat) : Bool :=
  decide (sumTo o.dim (fun j => o.jacobian i j * matOf c.eigVecs j k) = vecOf c.eigVals k * matOf c.eigVecs i k)
def leftB (i j : Nat) : Bool :=
  decide (sumTo o.dim (fun k => matOf c.eigInv i k * matOf c.eigVecs k j) = if i = j then 1 else 0)
def rightB (i j : Nat) : Bool :=
  decide (sumTo o.dim (fun k => matOf c.eigVecs i k * matOf c.eigInv k j) = if i = j then 1 else 0)
def speedB (k : Nat) : Bool := decide (-o.aMax ≤ vecOf c.eigVals k ∧ vecOf c.eigVals k ≤ o.aMax)
def weightB (k : Nat) : Bool := decide (0 < vecOf c.weights k)
def symB (i j : Nat) : Bool :=
  decide (matOf c.sym i j = gram o.dim (vecOf c.weights) (matOf c.eigInv) i j)

end Checks

def guardB (b : Bool) (cl : Clause) (rest : Judge.Verdict Clause) : Judge.Verdict Clause :=
  if b then rest else .refused cl []
def guard1 (b : Option Nat) (cl : Clause) (rest : Judge.Verdict Clause) : Judge.Verdict Clause :=
  match b with
  | some i => .refused cl [i]
  | none => rest
def guard2 (b : Option (Nat × Nat)) (cl : Clause) (rest : Judge.Verdict Clause) : Judge.Verdict Clause :=
  match b with
  | some ij => .refused cl [ij.1, ij.2]
  | none => rest

/-- The checker. Object-level conditions first (shape, CFL, conservation of the Riemann problem under
the dual-number Jacobian), then the certificate: claimed Jacobian, eigen-decomposition, wave speeds
within `aMax`, positive weights, symmetrizer. A refusal's path is the failing index or entry. -/
def check (o : HyperbolicSystem) (c : HyperbolicCert) : Judge.Verdict Clause :=
  guardB (decide o.WellFormed) .shapeMismatch <|
  guardB (cflB o) .cflViolation <|
  guard1 (firstBad o.dim (conservB o)) .conservationDefect <|
  guard2 (firstBad2 o.dim (jacB o c)) .jacobianMismatch <|
  guard2 (firstBad2 o.dim (eigB o c)) .eigenMismatch <|
  guard2 (firstBad2 o.dim (leftB o c)) .inverseMismatch <|
  guard2 (firstBad2 o.dim (rightB o c)) .inverseMismatch <|
  guard1 (firstBad o.dim (speedB o c)) .speedExceedsBound <|
  guard1 (firstBad o.dim (weightB c)) .weightNotPositive <|
  guard2 (firstBad2 o.dim (symB o c)) .symmetrizerMismatch .ok

theorem guardB_cases (b : Bool) (cl : Clause) (rest v : Judge.Verdict Clause) (h : guardB b cl rest = v) :
    (b = false ∧ v = .refused cl []) ∨ (b = true ∧ rest = v) := by
  cases b
  · left; exact ⟨rfl, h.symm⟩
  · right; exact ⟨rfl, h⟩

theorem guard1_cases (b : Option Nat) (cl : Clause) (rest v : Judge.Verdict Clause) (h : guard1 b cl rest = v) :
    (∃ i, b = some i ∧ v = .refused cl [i]) ∨ (b = none ∧ rest = v) := by
  cases b with
  | some i => left; exact ⟨i, rfl, h.symm⟩
  | none => right; exact ⟨rfl, h⟩

theorem guard2_cases (b : Option (Nat × Nat)) (cl : Clause) (rest v : Judge.Verdict Clause)
    (h : guard2 b cl rest = v) :
    (∃ ij, b = some ij ∧ v = .refused cl [ij.1, ij.2]) ∨ (b = none ∧ rest = v) := by
  cases b with
  | some ij => left; exact ⟨ij, rfl, h.symm⟩
  | none => right; exact ⟨rfl, h⟩

/-! ## What acceptance means -/

/-- The discrete energy of a grid state under the certificate's symmetrizer. -/
def symEnergy (o : HyperbolicSystem) (c : HyperbolicCert) (n : Nat) (U : Nat → Vec) : Rat :=
  sumTo n (fun i => dot o.dim (U i) (mulVec o.dim (matOf c.sym) (U i)))

/-- **The meaning of an accepted certificate.** With `A` the dual-number Jacobian of the flux at the
state and `H` the certificate's symmetrizer: the system is well formed and its CFL number admissible;
the Riemann problem is conserved by `A`; the claimed Jacobian is `A`; `A` has the certificate's real
eigenstructure; `H` is symmetric positive definite with `H·A` symmetric (a Friedrichs symmetrizer);
the flux form is bounded by `aMax` times the energy; and the Rusanov scheme's energy never grows on
any periodic grid over any number of steps. -/
structure Certified (o : HyperbolicSystem) (c : HyperbolicCert) : Prop where
  wf : o.WellFormed
  cfl : 0 ≤ o.cfl ∧ o.cfl * o.aMax ≤ 1
  roe : ∀ i, i < o.dim → mulVec o.dim o.jacobian o.jump i = o.fluxAt o.right i - o.fluxAt o.left i
  jac : ∀ i j, i < o.dim → j < o.dim → matOf c.jac i j = o.jacobian i j
  eigen : IsEigenSystem o.dim o.jacobian (matOf c.eigVecs) (matOf c.eigInv) (vecOf c.eigVals)
  symm : ∀ u v : Vec, dot o.dim u (mulVec o.dim (matOf c.sym) v) = dot o.dim v (mulVec o.dim (matOf c.sym) u)
  spd : ∀ (v : Vec) (i : Nat), i < o.dim → v i ≠ 0 → 0 < dot o.dim v (mulVec o.dim (matOf c.sym) v)
  friedrichs : ∀ u v : Vec, dot o.dim u (mulVec o.dim (matOf c.sym) (mulVec o.dim o.jacobian v))
    = dot o.dim v (mulVec o.dim (matOf c.sym) (mulVec o.dim o.jacobian u))
  speed : ∀ v : Vec,
    -(o.aMax * dot o.dim v (mulVec o.dim (matOf c.sym) v))
      ≤ dot o.dim v (mulVec o.dim (matOf c.sym) (mulVec o.dim o.jacobian v)) ∧
    dot o.dim v (mulVec o.dim (matOf c.sym) (mulVec o.dim o.jacobian v))
      ≤ o.aMax * dot o.dim v (mulVec o.dim (matOf c.sym) v)
  energy : ∀ (n N : Nat) (U : Nat → Vec),
    symEnergy o c n (rusanovRun o.dim o.jacobian o.aMax o.cfl n N U) ≤ symEnergy o c n U

/-- Either a vector vanishes on its first `n` coordinates or one of them is not zero. -/
theorem zero_or_ne (v : Vec) : ∀ n : Nat, (∀ k, k < n → v k = 0) ∨ ∃ k, k < n ∧ v k ≠ 0
  | 0 => Or.inl (fun k hk => by omega)
  | n + 1 => by
    rcases zero_or_ne v n with hz | ⟨k, hk, hne⟩
    · by_cases hn0 : v n = 0
      · left; intro k hk
        by_cases hkn : k = n
        · subst hkn; exact hn0
        · exact hz k (by omega)
      · right; exact ⟨n, by omega, hn0⟩
    · right; exact ⟨k, by omega, hne⟩

/-- **Every eigenvalue is within the speed bound** (Rayleigh quotient under `H`): if `H` is positive
definite and the flux form is bounded by `a` times the energy, an eigenvalue `lam` of `A` with an
eigenvector that is not zero satisfies `|lam| ≤ a`. -/
theorem eigenvalue_le_of_forms (m : Nat) (A H : Mat) (a : Rat)
    (hspd : ∀ (v : Vec) (i : Nat), i < m → v i ≠ 0 → 0 < dot m v (mulVec m H v))
    (hspeed : ∀ v : Vec, -(a * dot m v (mulVec m H v)) ≤ dot m v (mulVec m H (mulVec m A v)) ∧
      dot m v (mulVec m H (mulVec m A v)) ≤ a * dot m v (mulVec m H v))
    (r : Vec) (lam : Rat) (hr : ∀ i, i < m → mulVec m A r i = lam * r i) (i : Nat) (hi : i < m)
    (hne : r i ≠ 0) : -a ≤ lam ∧ lam ≤ a := by
  have hq := hspd r i hi hne
  obtain ⟨s1, s2⟩ := hspeed r
  have e : dot m r (mulVec m H (mulVec m A r)) = lam * dot m r (mulVec m H r) := by
    simp only [dot]
    rw [← sumTo_mul_left]
    refine sumTo_congr (fun j _ => ?_)
    have e1 : mulVec m H (mulVec m A r) j = mulVec m H (fun i => lam * r i + 0 * r i) j :=
      mulVec_congr (fun _ _ => rfl) (fun i hi => by rw [hr i hi]; grind)
    rw [e1, mulVec_lin]; grind
  rw [e] at s1 s2
  generalize dot m r (mulVec m H r) = q at *
  constructor
  · by_cases h : -a ≤ lam
    · exact h
    · have := Rat.mul_lt_mul_of_pos_right (by grind : lam < -a) hq; grind
  · by_cases h : lam ≤ a
    · exact h
    · have := Rat.mul_lt_mul_of_pos_right (by grind : a < lam) hq; grind

/-- An eigenvector of an eigen-decomposition has a coordinate that is not zero. -/
theorem IsEigenSystem.eigenvector_ne {m : Nat} {A R Rinv : Mat} {lam : Vec} (h : IsEigenSystem m A R Rinv lam)
    (k : Nat) (hk : k < m) : ∃ i, i < m ∧ R i k ≠ 0 := by
  rcases zero_or_ne (fun j => R j k) m with hz | hex
  · have e := h.eigenvector_coord k hk
    have : mulVec m Rinv (fun j => R j k) k = sumTo m (fun _ => 0) :=
      sumTo_congr (fun j hj => by show Rinv k j * R j k = 0; rw [hz j hj]; grind)
    rw [this, sumTo_zero] at e
    exact absurd e (by decide)
  · exact hex

/-- The certificate's symmetrizer form is the weighted characteristic form. -/
theorem sym_form (o : HyperbolicSystem) (c : HyperbolicCert)
    (hsym : ∀ i j, i < o.dim → j < o.dim →
      matOf c.sym i j = gram o.dim (vecOf c.weights) (matOf c.eigInv) i j) (u v : Vec) :
    dot o.dim u (mulVec o.dim (matOf c.sym) v) = charForm o.dim (vecOf c.weights) (matOf c.eigInv) u v := by
  rw [← dot_gram]
  exact sumTo_congr (fun i hi => by
    rw [mulVec_congr (B := gram o.dim (vecOf c.weights) (matOf c.eigInv)) (fun j hj => hsym i j hi hj)
      (fun _ _ => rfl)])

/-- What the checker's stages establish, read off an acceptance. -/
theorem check_ok {o : HyperbolicSystem} {c : HyperbolicCert} (h : check o c = .ok) :
    o.WellFormed ∧ (0 ≤ o.cfl ∧ o.cfl * o.aMax ≤ 1) ∧
    (∀ i, i < o.dim → mulVec o.dim o.jacobian o.jump i = o.fluxAt o.right i - o.fluxAt o.left i) ∧
    (∀ i j, i < o.dim → j < o.dim → matOf c.jac i j = o.jacobian i j) ∧
    IsEigenSystem o.dim o.jacobian (matOf c.eigVecs) (matOf c.eigInv) (vecOf c.eigVals) ∧
    (∀ k, k < o.dim → -o.aMax ≤ vecOf c.eigVals k ∧ vecOf c.eigVals k ≤ o.aMax) ∧
    (∀ k, k < o.dim → 0 < vecOf c.weights k) ∧
    (∀ i j, i < o.dim → j < o.dim → matOf c.sym i j = gram o.dim (vecOf c.weights) (matOf c.eigInv) i j) := by
  unfold check at h
  rcases guardB_cases _ _ _ _ h with ⟨_, hv⟩ | ⟨h1, h⟩
  · cases hv
  rcases guardB_cases _ _ _ _ h with ⟨_, hv⟩ | ⟨h2, h⟩
  · cases hv
  rcases guard1_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h3, h⟩
  · cases hv
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h4, h⟩
  · cases hv
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h5, h⟩
  · cases hv
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h6, h⟩
  · cases hv
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h7, h⟩
  · cases hv
  rcases guard1_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h8, h⟩
  · cases hv
  rcases guard1_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h9, h⟩
  · cases hv
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h10, _⟩
  · cases hv
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2,
    fun i hi => of_decide_eq_true ((firstBad_none _ _).mp h3 i hi),
    fun i j hi hj => of_decide_eq_true ((firstBad2_none _ _).mp h4 i j hi hj),
    ⟨fun i k hi hk => of_decide_eq_true ((firstBad2_none _ _).mp h5 i k hi hk),
     fun i j hi hj => of_decide_eq_true ((firstBad2_none _ _).mp h6 i j hi hj),
     fun i j hi hj => of_decide_eq_true ((firstBad2_none _ _).mp h7 i j hi hj)⟩,
    fun k hk => of_decide_eq_true ((firstBad_none _ _).mp h8 k hk),
    fun k hk => of_decide_eq_true ((firstBad_none _ _).mp h9 k hk),
    fun i j hi hj => of_decide_eq_true ((firstBad2_none _ _).mp h10 i j hi hj)⟩

/-- **Soundness.** -/
theorem check_sound {o : HyperbolicSystem} {c : HyperbolicCert} (h : check o c = .ok) : Certified o c := by
  obtain ⟨hwf, hcfl, hroe, hjac, E, hsp, hw, hsym⟩ := check_ok h
  have hw0 : ∀ k, k < o.dim → 0 ≤ vecOf c.weights k := fun k hk => Rat.le_of_lt (hw k hk)
  have F := sym_form o c hsym
  refine ⟨hwf, hcfl, hroe, hjac, E, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v; rw [F, F]; exact charForm_symm _ _ _ _ _
  · intro v i hi hv; rw [F]; exact E.charForm_pos _ hw v i hi hv
  · intro u v
    rw [F, F, E.charForm_flux_symm, charForm_symm]
  · intro v; rw [F, F]; exact E.charForm_flux_le _ hw0 _ hsp v
  · intro n N U
    have e : ∀ V : Nat → Vec, symEnergy o c n V = gridEnergy o.dim (vecOf c.weights) (matOf c.eigInv) n V :=
      fun V => sumTo_congr (fun i _ => F _ _)
    rw [e, e]
    exact rusanov_energy_run E _ hw0 _ _ hcfl.1 hcfl.2 hsp n N U

/-- The clauses whose refusal no certificate can repair: they are facts about the system. -/
def refutes : Clause → Bool
  | .shapeMismatch => true
  | .cflViolation => true
  | .conservationDefect => true
  | .speedExceedsBound => true
  | _ => false

/-- **Refutation.** A refusal for the system's shape, its CFL number or its conservation defect is
independent of the certificate. A refusal for an eigenvalue beyond `aMax` comes after that eigenpair
was verified, and then no symmetrizer at all can bound the flux form by `aMax`
(`eigenvalue_le_of_forms`). In each case no certificate has the meaning. -/
theorem check_refuted {o : HyperbolicSystem} {c : HyperbolicCert} {k : Clause} {p : List Nat}
    (h : check o c = .refused k p) (hk : refutes k = true) (c' : HyperbolicCert) : ¬ Certified o c' := by
  intro hc
  unfold check at h
  rcases guardB_cases _ _ _ _ h with ⟨hb, _⟩ | ⟨_, h⟩
  · exact (of_decide_eq_false hb) hc.wf
  rcases guardB_cases _ _ _ _ h with ⟨hb, _⟩ | ⟨_, h⟩
  · exact (of_decide_eq_false hb) hc.cfl
  rcases guard1_cases _ _ _ _ h with ⟨i, hb, _⟩ | ⟨_, h⟩
  · obtain ⟨hi, hf⟩ := firstBad_some _ _ _ hb
    exact (of_decide_eq_false hf) (hc.roe i hi)
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨_, h⟩
  · cases hv; exact absurd hk (by decide)
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h5, h⟩
  · cases hv; exact absurd hk (by decide)
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h6, h⟩
  · cases hv; exact absurd hk (by decide)
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨h7, h⟩
  · cases hv; exact absurd hk (by decide)
  rcases guard1_cases _ _ _ _ h with ⟨j, hb, _⟩ | ⟨_, h⟩
  · obtain ⟨hj, hf⟩ := firstBad_some _ _ _ hb
    have E : IsEigenSystem o.dim o.jacobian (matOf c.eigVecs) (matOf c.eigInv) (vecOf c.eigVals) :=
      ⟨fun i k hi hk => of_decide_eq_true ((firstBad2_none _ _).mp h5 i k hi hk),
       fun i j hi hj => of_decide_eq_true ((firstBad2_none _ _).mp h6 i j hi hj),
       fun i j hi hj => of_decide_eq_true ((firstBad2_none _ _).mp h7 i j hi hj)⟩
    obtain ⟨i, hi, hne⟩ := E.eigenvector_ne j hj
    exact (of_decide_eq_false hf) (eigenvalue_le_of_forms o.dim o.jacobian (matOf c'.sym) o.aMax hc.spd hc.speed
      (fun i => matOf c.eigVecs i j) (vecOf c.eigVals j) (fun i hi => E.eigenvector j i hj hi) i hi hne)
  rcases guard1_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨_, h⟩
  · cases hv; exact absurd hk (by decide)
  rcases guard2_cases _ _ _ _ h with ⟨_, _, hv⟩ | ⟨_, h⟩
  · cases hv; exact absurd hk (by decide)
  cases h

/-- A certificate's eigen-decomposition with the canonical symmetrizer `R⁻ᵀ·R⁻¹` (unit weights). -/
def canonical (o : HyperbolicSystem) (c : HyperbolicCert) : HyperbolicCert where
  jac := c.jac
  eigVecs := c.eigVecs
  eigVals := c.eigVals
  eigInv := c.eigInv
  weights := tabFrom (fun _ => 1) 0 o.dim
  sym := tabFrom (fun i => tabFrom (fun j =>
    gram o.dim (vecOf (tabFrom (fun _ => 1) 0 o.dim)) (matOf c.eigInv) i j) 0 o.dim) 0 o.dim

/-- **Completeness.** Whenever some certificate has the meaning, the checker accepts one: the same
eigen-decomposition with the canonical symmetrizer. The checker asks nothing the meaning does not
give; in particular the eigenvalue bound it checks follows from the meaning's bound on the flux form. -/
theorem check_complete {o : HyperbolicSystem} {c : HyperbolicCert} (hc : Certified o c) :
    check o (canonical o c) = .ok := by
  have h1 : decide o.WellFormed = true := decide_eq_true hc.wf
  have h2 : cflB o = true := decide_eq_true hc.cfl
  have h3 : firstBad o.dim (conservB o) = none :=
    (firstBad_none _ _).mpr (fun i hi => decide_eq_true (hc.roe i hi))
  have h4 : firstBad2 o.dim (jacB o (canonical o c)) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => decide_eq_true (hc.jac i j hi hj))
  have h5 : firstBad2 o.dim (eigB o (canonical o c)) = none :=
    (firstBad2_none _ _).mpr (fun i k hi hk => decide_eq_true (hc.eigen.eig i k hi hk))
  have h6 : firstBad2 o.dim (leftB o (canonical o c)) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => decide_eq_true (hc.eigen.left i j hi hj))
  have h7 : firstBad2 o.dim (rightB o (canonical o c)) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => decide_eq_true (hc.eigen.right i j hi hj))
  have h8 : firstBad o.dim (speedB o (canonical o c)) = none :=
    (firstBad_none _ _).mpr (fun k hk => by
      obtain ⟨i, hi, hne⟩ := hc.eigen.eigenvector_ne k hk
      exact decide_eq_true (eigenvalue_le_of_forms o.dim o.jacobian (matOf c.sym) o.aMax hc.spd hc.speed
        (fun i => matOf c.eigVecs i k) (vecOf c.eigVals k) (fun i hi => hc.eigen.eigenvector k i hk hi) i hi hne))
  have h9 : firstBad o.dim (weightB (canonical o c)) = none :=
    (firstBad_none _ _).mpr (fun k hk => by
      have e : vecOf (canonical o c).weights k = 1 := by
        show getOr (tabFrom (fun _ => (1 : Rat)) 0 o.dim) k 0 = 1
        rw [getOr_tabFrom _ _ _ _ _ hk]
      simp only [weightB, e]; decide)
  have h10 : firstBad2 o.dim (symB o (canonical o c)) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => by
      have e : matOf (canonical o c).sym i j
          = gram o.dim (vecOf (canonical o c).weights) (matOf (canonical o c).eigInv) i j := by
        show getOr (getOr (tabFrom (fun i => tabFrom (fun j =>
          gram o.dim (vecOf (tabFrom (fun _ => 1) 0 o.dim)) (matOf c.eigInv) i j) 0 o.dim) 0 o.dim) i []) j 0 = _
        rw [getOr_tabFrom _ _ _ _ _ hi, getOr_tabFrom _ _ _ _ _ hj, Nat.zero_add, Nat.zero_add]; rfl
      exact decide_eq_true e)
  unfold check
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; rfl

/-- The certificate format's name. -/
def formatName : String := "hyperbolic-fvm@1"

/-- **The judge of `hyperbolic-fvm@1`.** The checker does not use the grade. -/
instance hyperbolicPdeJudge : Judge HyperbolicSystem HyperbolicCert where
  Clause := Clause
  Meaning := Certified
  check := fun _ o c => check o c
  sound := fun h => check_sound h
  refutes := refutes
  refuted := fun h hk c' => check_refuted h hk c'
  Fragment := HyperbolicSystem.WellFormed
  complete := fun _ ⟨c, hc⟩ => ⟨canonical _ c, 0, check_complete hc⟩
  mono := fun _ _ => rfl

/-! ## Consequences of a certificate -/

/-- **Conservation of the wave-fluctuation splitting**: for the system's Riemann problem,
`A⁻Δ + A⁺Δ = F(U_R) - F(U_L)`. -/
theorem Certified.fluctuation {o : HyperbolicSystem} {c : HyperbolicCert} (hc : Certified o c) (i : Nat)
    (hi : i < o.dim) :
    amdq o.dim (matOf c.eigVecs) (matOf c.eigInv) (vecOf c.eigVals) o.jump i
      + apdq o.dim (matOf c.eigVecs) (matOf c.eigInv) (vecOf c.eigVals) o.jump i
      = o.fluxAt o.right i - o.fluxAt o.left i := by
  rw [fluctuation_sum hc.eigen _ i hi]; exact hc.roe i hi

/-- **Real, bounded wave speeds**: every rational eigenvalue of the Jacobian, the certificate's or
any other, is within `aMax`. -/
theorem Certified.eigenvalue_le {o : HyperbolicSystem} {c : HyperbolicCert} (hc : Certified o c) (r : Vec)
    (lam : Rat) (hr : ∀ i, i < o.dim → mulVec o.dim o.jacobian r i = lam * r i) (i : Nat) (hi : i < o.dim)
    (hne : r i ≠ 0) : -o.aMax ≤ lam ∧ lam ≤ o.aMax :=
  eigenvalue_le_of_forms o.dim o.jacobian (matOf c.sym) o.aMax hc.spd hc.speed r lam hr i hi hne

theorem dot_flux_eigen (m : Nat) (A H : Mat) (u r : Vec) (lam : Rat)
    (hr : ∀ i, i < m → mulVec m A r i = lam * r i) :
    dot m u (mulVec m H (mulVec m A r)) = lam * dot m u (mulVec m H r) := by
  simp only [dot]
  rw [← sumTo_mul_left]
  refine sumTo_congr (fun j _ => ?_)
  have e1 : mulVec m H (mulVec m A r) j = mulVec m H (fun i => lam * r i + 0 * r i) j :=
    mulVec_congr (fun _ _ => rfl) (fun i hi => by rw [hr i hi]; grind)
  rw [e1, mulVec_lin]; grind

/-- **Eigenvectors of different speeds are `H`-orthogonal.** -/
theorem Certified.orthogonal {o : HyperbolicSystem} {c : HyperbolicCert} (hc : Certified o c) (j k : Nat)
    (hj : j < o.dim) (hk : k < o.dim) (hne : vecOf c.eigVals j ≠ vecOf c.eigVals k) :
    dot o.dim (fun i => matOf c.eigVecs i j) (mulVec o.dim (matOf c.sym) (fun i => matOf c.eigVecs i k)) = 0 := by
  have f := hc.friedrichs (fun i => matOf c.eigVecs i j) (fun i => matOf c.eigVecs i k)
  rw [dot_flux_eigen _ _ _ _ _ _ (fun i hi => hc.eigen.eigenvector k i hk hi),
    dot_flux_eigen _ _ _ _ _ _ (fun i hi => hc.eigen.eigenvector j i hj hi),
    hc.symm (fun i => matOf c.eigVecs i k) (fun i => matOf c.eigVecs i j)] at f
  generalize dot o.dim (fun i => matOf c.eigVecs i j) (mulVec o.dim (matOf c.sym) (fun i => matOf c.eigVecs i k)) = x at *
  have hz : (vecOf c.eigVals k - vecOf c.eigVals j) * x = 0 := by grind
  rcases Rat.mul_eq_zero.mp hz with h | h
  · exact absurd (by grind : vecOf c.eigVals j = vecOf c.eigVals k) hne
  · exact h

/-! ## Certified systems -/

/-- Maxwell's equations in one dimension, `∂_t E_y + c²·∂_x B_z = 0`, `∂_t B_z + ∂_x E_y = 0`, with
`c = 3/2` and CFL number `ν·c = 1`. -/
def maxwellSystem : HyperbolicSystem where
  vars := ["Ey", "Bz"]
  flux := [.mul (.const (9 / 4)) (.var "Bz"), .var "Ey"]
  state := [1, 2]
  left := [1, 1 / 2]
  right := [3, -1]
  aMax := 3 / 2
  cfl := 2 / 3

/-- Its eigenvectors `(±c, 1)` with speeds `±c`, and the electromagnetic energy `E_y² + c²·B_z²`. -/
def maxwellCert : HyperbolicCert where
  jac := [[0, 9 / 4], [1, 0]]
  eigVecs := [[3 / 2, -(3 / 2)], [1, 1]]
  eigVals := [3 / 2, -(3 / 2)]
  eigInv := [[1 / 3, 1 / 2], [-(1 / 3), 1 / 2]]
  weights := [9 / 2, 9 / 2]
  sym := [[1, 0], [0, 9 / 4]]

example : check maxwellSystem maxwellCert = .ok := by decide +kernel

/-- The longitudinal part of Munz's perfectly hyperbolic Maxwell system (`E_x, B_x` with the
divergence-cleaning potentials `φ, ψ`): `∂_t E_x + χ·c²·∂_x φ = 0`, `∂_t B_x + γ·∂_x ψ = 0`,
`∂_t φ + χ·∂_x E_x = 0`, `∂_t ψ + γ·c²·∂_x B_x = 0`, with `c = 2`, `χ = 3/2`, `γ = 5/4`: the
divergence errors leave at `χ·c = 3` and `γ·c = 5/2`. -/
def phmSystem : HyperbolicSystem where
  vars := ["Ex", "Bx", "phi", "psi"]
  flux := [.mul (.const 6) (.var "phi"), .mul (.const (5 / 4)) (.var "psi"),
    .mul (.const (3 / 2)) (.var "Ex"), .mul (.const 5) (.var "Bx")]
  state := [1, 2, 3, 4]
  left := [0, 0, 0, 0]
  right := [1, -1, 2, 1 / 2]
  aMax := 3
  cfl := 1 / 3

/-- Its four waves and the energy `E_x² + c²·B_x² + c²·φ² + ψ²`. -/
def phmCert : HyperbolicCert where
  jac := [[0, 0, 6, 0], [0, 0, 0, 5 / 4], [3 / 2, 0, 0, 0], [0, 5, 0, 0]]
  eigVecs := [[2, -2, 0, 0], [0, 0, 1, -1], [1, 1, 0, 0], [0, 0, 2, 2]]
  eigVals := [3, -3, 5 / 2, -(5 / 2)]
  eigInv := [[1 / 4, 0, 1 / 2, 0], [-(1 / 4), 0, 1 / 2, 0], [0, 1 / 2, 0, 1 / 4], [0, -(1 / 2), 0, 1 / 4]]
  weights := [8, 8, 8, 8]
  sym := [[1, 0, 0, 0], [0, 4, 0, 0], [0, 0, 4, 0], [0, 0, 0, 1]]

example : check phmSystem phmCert = .ok := by decide +kernel

/-- Burgers' equation `∂_t u + ∂_x (u²/2) = 0` linearized at `u = 1`, the Roe average of the
Riemann problem `(0, 2)`: the one state at which the frozen Jacobian conserves the jump. -/
def burgersSystem : HyperbolicSystem where
  vars := ["u"]
  flux := [.mul (.const (1 / 2)) (.sqr (.var "u"))]
  state := [1]
  left := [0]
  right := [2]
  aMax := 1
  cfl := 1

def burgersCert : HyperbolicCert where
  jac := [[1]]
  eigVecs := [[1]]
  eigVals := [1]
  eigInv := [[1]]
  weights := [1]
  sym := [[1]]

example : check burgersSystem burgersCert = .ok := by decide +kernel

/-! Refusals, each naming its clause and the failing entry. -/

example : check maxwellSystem { maxwellCert with jac := [[0, 2], [1, 0]] }
    = .refused .jacobianMismatch [0, 1] := by decide +kernel
example : check maxwellSystem { maxwellCert with weights := [9 / 2, 0] }
    = .refused .weightNotPositive [1] := by decide +kernel
example : check maxwellSystem { maxwellCert with sym := [[1, 1], [1, 9 / 4]] }
    = .refused .symmetrizerMismatch [0, 1] := by decide +kernel
example : check maxwellSystem { maxwellCert with eigVals := [3 / 2, 3 / 2] }
    = .refused .eigenMismatch [0, 1] := by decide +kernel
example : check { maxwellSystem with cfl := 1 } maxwellCert = .refused .cflViolation [] := by decide +kernel
example : check { maxwellSystem with aMax := 1 } maxwellCert = .refused .speedExceedsBound [0] := by
  decide +kernel
example : check { burgersSystem with state := [2], aMax := 2, cfl := 1 / 2 } burgersCert
    = .refused .conservationDefect [0] := by decide +kernel

/-- A refuting refusal at work: no certificate whatever makes Maxwell's equations with `c = 3/2`
respect a speed bound of `1`. -/
theorem maxwell_speed_one_refuted (c : HyperbolicCert) : ¬ Certified { maxwellSystem with aMax := 1 } c :=
  check_refuted (c := maxwellCert) (k := .speedExceedsBound) (p := [0]) (by decide +kernel) rfl c

/-- The electromagnetic energy of the one-dimensional Maxwell scheme never grows. -/
theorem maxwell_energy_decay (n N : Nat) (U : Nat → Vec) :
    symEnergy maxwellSystem maxwellCert n
        (rusanovRun maxwellSystem.dim maxwellSystem.jacobian (3 / 2) (2 / 3) n N U)
      ≤ symEnergy maxwellSystem maxwellCert n U :=
  (check_sound (by decide +kernel : check maxwellSystem maxwellCert = .ok)).energy n N U

/-- The same for the perfectly hyperbolic system's energy `E_x² + c²·B_x² + c²·φ² + ψ²`. -/
theorem phm_energy_decay (n N : Nat) (U : Nat → Vec) :
    symEnergy phmSystem phmCert n (rusanovRun phmSystem.dim phmSystem.jacobian 3 (1 / 3) n N U)
      ≤ symEnergy phmSystem phmCert n U :=
  (check_sound (by decide +kernel : check phmSystem phmCert = .ok)).energy n N U

end Obend.Analysis.HyperbolicPde
end
