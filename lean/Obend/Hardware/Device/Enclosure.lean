module
/-
# Obend.Hardware.Device.Enclosure — rational enclosures of `exp`, the Bernoulli function, powers and roots

The device-physics modules need four transcendental or algebraic quantities this library cannot
compute exactly over `ℚ`: `exp` (Boltzmann statistics, Arrhenius rates, Gaussian implant profiles),
the Scharfetter–Gummel Bernoulli function `B(x) = x/(eˣ − 1)`, fractional powers `(N/N_ref)^α`
(Caughey–Thomas mobility) and square roots (Deal–Grove's quadratic, intrinsic density). Each is handled
the way `Hardware/CurrentLoop.lean` handles the ZOH pole: an *enclosure* over `ℚ`, built from
`Analysis.Interval`, and a statement of exactly which real-analysis fact is assumed and not proved.

**What is assumed (two facts, stated once, about the real functions):**

* `expHalf`: for `|t| ≤ 1/2`, `eᵗ ∈ expHalfEnclosure t = [T₁₂(t) − 2|t|¹³/13!, T₁₂(t) + 2|t|¹³/13!]`,
  with `T₁₂` the degree-12 Taylor polynomial. (Lagrange: the remainder is `e^ξ t¹³/13!` with
  `e^ξ ≤ e^{1/2} < 2`.)
* `bernSmall`: for `|x| ≤ 1/8`, `B(x) ∈ [S₁₀(x) − x¹²/10⁹, S₁₀(x) + x¹²/10⁹]`, with `S₁₀` the Bernoulli
  series through `x¹⁰` (`1 − x/2 + x²/12 − x⁴/720 + x⁶/30240 − x⁸/1209600 + x¹⁰/47900160`). (The
  coefficient of `x¹²` is `−691/(2730·12!) ≈ −5.3·10⁻¹⁰` and the series' terms shrink like `(x/2π)²ⁿ`.)

**What is proved (over `ℚ`, for all inputs):** everything that extends those two facts to the
enclosures the checkers use. `expEnclosure x` halves the argument `k` times into `[−1/2, 1/2]`,
applies `expHalfEnclosure`, and squares the interval `k` times (`expEnclosure_of_half`: any value in the
half-enclosure, raised to `2ᵏ`, lies in `expEnclosure x`, so the only assumption is `expHalf`).
`bernEnclosure?` uses `bernSmall` for `|x| ≤ 1/8` and `x/(e − 1)` by interval division for larger `|x|`
(`bernOf_mem`: any `e` in `expEnclosure x` gives a quotient in the enclosure, so the only assumption is
`expHalf`). Interval endpoints are rounded outward to `10⁻⁶⁰` after every squaring (`roundOut_mem`) so
that denominators stay bounded; values below about `10⁻⁴⁵` keep absolute but not relative precision.

Fractional powers and roots are not enclosed but *bracketed*: a producer supplies the value `y` and
the checker verifies `(y(1−δ))ᵈ ≤ rⁿ ≤ (y(1+δ))ᵈ` (`powBracket`), which pins `y` to within `δ` of
`r^{n/d}` without computing it (`powBracket_agree`: two bracketed values are within `(1+δ)/(1−δ)` of each
other). This needs no analysis at all: it is the monotonicity of `yᵈ` on `ℚ≥0` (`le_of_ratPow_le`).
-/
public import Obend.Analysis.RealAnalysis
public section

namespace Obend.Hardware.Device
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. Rational powers -/

/-- `x ^ k` by recursion, so that every lemma below is by induction on `k`. -/
@[expose] def ratPow (x : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | k + 1 => ratPow x k * x

@[simp] theorem ratPow_zero (x : CanonicalRat) : ratPow x 0 = 1 := rfl
@[simp] theorem ratPow_succ (x : CanonicalRat) (k : Nat) : ratPow x (k + 1) = ratPow x k * x := rfl

theorem ratPow_one (x : CanonicalRat) : ratPow x 1 = x := by
  simp [ratPow]

theorem ratPow_nonneg {x : CanonicalRat} (hx : 0 ≤ x) : ∀ k, 0 ≤ ratPow x k
  | 0 => by rw [ratPow_zero]; decide
  | k + 1 => by
    rw [ratPow_succ]
    exact Rat.mul_nonneg (ratPow_nonneg hx k) hx

theorem ratPow_pos {x : CanonicalRat} (hx : 0 < x) : ∀ k, 0 < ratPow x k
  | 0 => by rw [ratPow_zero]; decide
  | k + 1 => by
    rw [ratPow_succ]
    exact Rat.mul_pos (ratPow_pos hx k) hx

theorem ratPow_add (x : CanonicalRat) (a : Nat) : ∀ b, ratPow x (a + b) = ratPow x a * ratPow x b
  | 0 => by simp
  | b + 1 => by
    rw [← Nat.add_assoc, ratPow_succ, ratPow_succ, ratPow_add x a b, Rat.mul_assoc]

/-- Powers are monotone on the nonnegative rationals. -/
theorem ratPow_mono {a b : CanonicalRat} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ k, ratPow a k ≤ ratPow b k
  | 0 => by simp
  | k + 1 => by
    rw [ratPow_succ, ratPow_succ]
    have hb : 0 ≤ b := Rat.le_trans ha hab
    have h1 : ratPow a k * a ≤ ratPow a k * b :=
      Rat.mul_le_mul_of_nonneg_left hab (ratPow_nonneg ha k)
    have h2 : ratPow a k * b ≤ ratPow b k * b :=
      Rat.mul_le_mul_of_nonneg_right (ratPow_mono ha hab k) hb
    grind

/-- Powers of positive exponent are strictly monotone on the nonnegative rationals. -/
theorem ratPow_strictMono {a b : CanonicalRat} (ha : 0 ≤ a) (hab : a < b) :
    ∀ k, ratPow a (k + 1) < ratPow b (k + 1)
  | 0 => by simpa [ratPow] using hab
  | k + 1 => by
    rw [ratPow_succ a (k + 1), ratPow_succ b (k + 1)]
    have hb : 0 < b := by grind
    have h1 : ratPow a (k + 1) * a ≤ ratPow a (k + 1) * b :=
      Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hab) (ratPow_nonneg ha (k + 1))
    have h2 : ratPow a (k + 1) * b < ratPow b (k + 1) * b :=
      Rat.mul_lt_mul_of_pos_right (ratPow_strictMono ha hab k) hb
    grind

/-- The converse: a power inequality between nonnegative bases comes from the bases. -/
theorem le_of_ratPow_le {a b : CanonicalRat} (hb : 0 ≤ b) {k : Nat}
    (h : ratPow a (k + 1) ≤ ratPow b (k + 1)) : a ≤ b := by
  rcases @Rat.le_total a b with hab | hba
  · exact hab
  · by_cases heq : a = b
    · exact heq ▸ Rat.le_refl
    · have hlt : b < a := by grind
      exact absurd h (Rat.not_le.2 (ratPow_strictMono hb hlt k))

/-! ## 2. Interval powers, reciprocals, outward rounding (added to `Obend.Analysis.Interval`) -/

end Obend.Hardware.Device

namespace Obend.Analysis.Interval
open Obend.Hardware.Device

/-- `I ^ k` by repeated multiplication. -/
@[expose] def powNat (I : Interval) : Nat → Interval
  | 0 => Interval.ofPoint 1
  | k + 1 => Interval.mul (Interval.powNat I k) I

theorem powNat_mem {x : CanonicalRat} {I : Interval} (hx : x ∈ I) :
    ∀ k, ratPow x k ∈ I.powNat k
  | 0 => Interval.ofPoint_mem 1
  | k + 1 => Interval.mul_mem (powNat_mem hx k) hx

/-- Dividing a bound by a positive scale. -/
theorem div_le_of_le_mul {a b s : CanonicalRat} (hs : 0 < s) (h : a ≤ b * s) : a / s ≤ b := by
  have hinv : 0 ≤ s⁻¹ := Rat.le_of_lt (Rat.inv_pos.2 hs)
  have h1 : a * s⁻¹ ≤ b * s * s⁻¹ := Rat.mul_le_mul_of_nonneg_right h hinv
  have h2 : b * s * s⁻¹ = b := by
    rw [Rat.mul_assoc, Rat.mul_inv_cancel s (Rat.ne_of_gt hs), Rat.mul_one]
  rw [Rat.div_def]
  exact h2 ▸ h1

theorem le_div_of_mul_le {a b s : CanonicalRat} (hs : 0 < s) (h : a * s ≤ b) : a ≤ b / s := by
  have hinv : 0 ≤ s⁻¹ := Rat.le_of_lt (Rat.inv_pos.2 hs)
  have h1 : a * s * s⁻¹ ≤ b * s⁻¹ := Rat.mul_le_mul_of_nonneg_right h hinv
  have h2 : a * s * s⁻¹ = a := by
    rw [Rat.mul_assoc, Rat.mul_inv_cancel s (Rat.ne_of_gt hs), Rat.mul_one]
  rw [Rat.div_def]
  exact h2 ▸ h1

/-- Reciprocals reverse order on the positive rationals. -/
theorem inv_le_inv_of_le {a b : CanonicalRat} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := by grind
  have hu : 0 ≤ a⁻¹ := Rat.le_of_lt (Rat.inv_pos.2 ha)
  have hv : 0 ≤ b⁻¹ := Rat.le_of_lt (Rat.inv_pos.2 hb)
  have h1 : a * (a⁻¹ * b⁻¹) ≤ b * (a⁻¹ * b⁻¹) :=
    Rat.mul_le_mul_of_nonneg_right hab (Rat.mul_nonneg hu hv)
  have e1 : a * (a⁻¹ * b⁻¹) = b⁻¹ := by
    rw [← Rat.mul_assoc, Rat.mul_inv_cancel a (Rat.ne_of_gt ha), Rat.one_mul]
  have e2 : b * (a⁻¹ * b⁻¹) = a⁻¹ := by
    rw [Rat.mul_comm a⁻¹ b⁻¹, ← Rat.mul_assoc, Rat.mul_inv_cancel b (Rat.ne_of_gt hb), Rat.one_mul]
  rw [e1, e2] at h1
  exact h1

/-- The reciprocal of an interval that lies strictly above zero: `[1/hi, 1/lo]`. -/
@[expose] def invPos (I : Interval) : Interval :=
  ⟨I.hi⁻¹, I.lo⁻¹⟩

theorem invPos_mem {x : CanonicalRat} {I : Interval} (hlo : 0 < I.lo) (hx : x ∈ I) :
    x⁻¹ ∈ I.invPos := by
  rw [Interval.mem_iff] at hx ⊢
  dsimp [Interval.invPos]
  have hxpos : 0 < x := by grind
  exact ⟨inv_le_inv_of_le hxpos hx.2, inv_le_inv_of_le hlo hx.1⟩

/-- `A / B` when `B` lies strictly above zero; `none` otherwise (a checker that needs the quotient
refuses rather than divide through zero). -/
@[expose] def divPos? (A B : Interval) : Option Interval :=
  if 0 < B.lo then some (Interval.mul A ⟨B.hi⁻¹, B.lo⁻¹⟩) else none

theorem divPos?_mem {x y : CanonicalRat} {A B J : Interval}
    (hx : x ∈ A) (hy : y ∈ B) (hJ : Interval.divPos? A B = some J) : x / y ∈ J := by
  unfold Interval.divPos? at hJ
  split at hJ
  · rename_i hlo
    cases hJ
    rw [Rat.div_def]
    exact Interval.mul_mem hx (Interval.invPos_mem hlo hy)
  · cases hJ

/-- Round the endpoints outward to multiples of `1/s`: `[⌊lo·s⌋/s, ⌈hi·s⌉/s]`. -/
@[expose] def roundOut (s : Nat) (I : Interval) : Interval :=
  ⟨(((I.lo * (s : CanonicalRat)).floor : Int) : CanonicalRat) / (s : CanonicalRat),
   (((I.hi * (s : CanonicalRat)).ceil : Int) : CanonicalRat) / (s : CanonicalRat)⟩

theorem roundOut_mem {x : CanonicalRat} {I : Interval} {s : Nat} (hs : 0 < s) (hx : x ∈ I) :
    x ∈ I.roundOut s := by
  rw [Interval.mem_iff] at hx ⊢
  dsimp [Interval.roundOut]
  have hsq : (0 : CanonicalRat) < (s : CanonicalRat) := by exact_mod_cast hs
  constructor
  · apply Rat.le_trans _ hx.1
    exact div_le_of_le_mul hsq (Rat.floor_le _)
  · apply Rat.le_trans hx.2
    exact le_div_of_mul_le hsq Rat.le_ceil

/-- Square `k` times, rounding outward after each squaring. -/
@[expose] def sqrIterRound (s : Nat) (I : Interval) : Nat → Interval
  | 0 => I
  | k + 1 => Interval.roundOut s (Interval.sqr (Interval.sqrIterRound s I k))

theorem sqrIterRound_mem {x : CanonicalRat} {I : Interval} {s : Nat} (hs : 0 < s) (hx : x ∈ I) :
    ∀ k, ratPow x (2 ^ k) ∈ I.sqrIterRound s k
  | 0 => by simpa [Interval.sqrIterRound, ratPow] using hx
  | k + 1 => by
    have ih := Interval.sqrIterRound_mem hs hx k
    have hpow : ratPow x (2 ^ (k + 1)) = ratPow x (2 ^ k) * ratPow x (2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_two, ratPow_add]
    rw [hpow]
    exact Interval.roundOut_mem hs (Interval.sqr_mem ih)

/-- `-tol ≤ lo ∧ hi ≤ tol`: every value in the interval is within `tol` of zero. -/
@[expose] def within (I : Interval) (tol : CanonicalRat) : Bool :=
  decide (-tol ≤ I.lo) && decide (I.hi ≤ tol)

theorem within_sound {x : CanonicalRat} {I : Interval} {tol : CanonicalRat}
    (hx : x ∈ I) (h : I.within tol = true) : -tol ≤ x ∧ x ≤ tol := by
  rw [Interval.mem_iff] at hx
  simp only [Interval.within, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨Rat.le_trans h.1 hx.1, Rat.le_trans hx.2 h.2⟩

/-- Scale an interval by a rational. -/
@[expose] def scale (c : CanonicalRat) (I : Interval) : Interval :=
  Interval.mul (Interval.ofPoint c) I

theorem scale_mem {x : CanonicalRat} {I : Interval} (c : CanonicalRat) (hx : x ∈ I) :
    c * x ∈ Interval.scale c I :=
  Interval.mul_mem (Interval.ofPoint_mem c) hx

end Obend.Analysis.Interval

namespace Obend.Hardware.Device
open Obend.Analysis

/-! ## 3. The exponential -/

/-- `|t|`. -/
@[expose] def ratAbs (t : CanonicalRat) : CanonicalRat := if t < 0 then -t else t

theorem ratAbs_nonneg (t : CanonicalRat) : 0 ≤ ratAbs t := by
  unfold ratAbs
  split <;> grind

/-- `Σ_{j ≤ deg} tʲ/j!` by Horner's rule. -/
@[expose] def expTaylor (deg : Nat) (t : CanonicalRat) : CanonicalRat :=
  (List.range deg).reverse.foldl (fun p j => 1 + t / (((j + 1 : Nat) : CanonicalRat)) * p) 1

/-- The degree of the Taylor polynomial used on `[−1/2, 1/2]`. -/
@[expose] def expDeg : Nat := 12

/-- `13! = 6227020800`. -/
@[expose] def fact13 : CanonicalRat := 6227020800

/-- The Lagrange remainder bound `2|t|¹³/13!` for `|t| ≤ 1/2` (`e^{1/2} < 2`). -/
@[expose] def expHalfRem (t : CanonicalRat) : CanonicalRat :=
  2 * ratPow (ratAbs t) 13 / fact13

/-- **Assumed fact `expHalf`**: for `|t| ≤ 1/2`, `eᵗ` lies in this interval. -/
@[expose] def expHalfEnclosure (t : CanonicalRat) : Interval :=
  let tay := (List.range 12).reverse.foldl (fun p j => 1 + t / (((j + 1 : Nat) : CanonicalRat)) * p) 1
  let rem := 2 * ratPow (ratAbs t) 13 / 6227020800
  ⟨tay - rem, tay + rem⟩

/-- Dynamic halving count bringing `|x / 2ᵏ|` into `[0, 1/2]` for **all** `x : CanonicalRat`
(including `|x| > 2⁶³` up to arbitrary rational magnitudes): uses dynamic fuel
`(2 * ratAbs x).ceil.toNat`, terminating structurally as soon as `a ≤ 1/2`. -/
@[expose] def halvings (x : CanonicalRat) : Nat :=
  go (ratAbs x) (2 * ratAbs x).ceil.toNat
where
  go : CanonicalRat → Nat → Nat
    | _, 0 => 0
    | a, fuel + 1 => if a ≤ 1/2 then 0 else go (a / 2) fuel + 1

private theorem halvings_go_two_mul_le :
    ∀ (fuel : Nat) (a : CanonicalRat),
      0 ≤ a → 2 * a ≤ (fuel : CanonicalRat) + 1 →
      2 * a ≤ ratPow 2 (halvings.go a fuel)
  | 0, a, _, hbound => by
    simp only [halvings.go, ratPow]
    grind
  | fuel + 1, a, ha, hbound => by
    unfold halvings.go
    split
    · rename_i hle
      simp only [ratPow]
      grind
    · rename_i hgt
      have ha2_nonneg : 0 ≤ a / 2 := by grind
      have ha2_bound : 2 * (a / 2) ≤ (fuel : CanonicalRat) + 1 := by grind
      have ih := halvings_go_two_mul_le fuel (a / 2) ha2_nonneg ha2_bound
      rw [ratPow_succ]
      grind

private theorem ratAbs_div_of_pos {x s : CanonicalRat} (hs : 0 < s) :
    ratAbs (x / s) = ratAbs x / s := by
  unfold ratAbs
  by_cases hx : x < 0
  · have hxs : x / s < 0 := by
      rw [Rat.div_def]
      have hpos : 0 < (-x) * s⁻¹ := Rat.mul_pos (by grind) (Rat.inv_pos.2 hs)
      rw [Rat.neg_mul] at hpos
      grind
    simp only [hx, hxs, ↓reduceIte]
    simp only [Rat.div_def]
    exact (Rat.neg_mul x s⁻¹).symm
  · have hxs : ¬ (x / s < 0) := by
      have hx0 : 0 ≤ x := by grind
      have h0 : 0 ≤ x / s := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg hx0 (Rat.le_of_lt (Rat.inv_pos.2 hs))
      grind
    simp only [hx, hxs, ↓reduceIte]

/-- **Unconditional Halving Bound (`halvings_arg_abs_le_half`)**:
For **every** `x : CanonicalRat` (including `|x| > 2⁶³`), `halvings x` halves `x` into `[−1/2, 1/2]`. -/
theorem halvings_arg_abs_le_half (x : CanonicalRat) :
    ratAbs (x / ratPow 2 (halvings x)) ≤ 1 / 2 := by
  unfold halvings
  let a := ratAbs x
  let fuel := (2 * a).ceil.toNat
  have ha : 0 ≤ a := ratAbs_nonneg x
  have h2a_nonneg : (0 : Int) ≤ (2 * a).ceil := by
    have h0 : (0 : CanonicalRat) ≤ 2 * a := by grind
    have h1 : (0 : CanonicalRat) ≤ ((2 * a).ceil : CanonicalRat) :=
      Rat.le_trans h0 Rat.le_ceil
    exact_mod_cast h1
  have hceil_eq : (((fuel : Nat) : Int) : CanonicalRat) = ((2 * a).ceil : CanonicalRat) := by
    have hto : ((fuel : Nat) : Int) = (2 * a).ceil := Int.toNat_of_nonneg h2a_nonneg
    rw [hto]
  have hfuel_bound : 2 * a ≤ (fuel : CanonicalRat) + 1 := by
    have hc : 2 * a ≤ ((2 * a).ceil : CanonicalRat) := Rat.le_ceil
    have hcast : (((fuel : Nat) : Int) : CanonicalRat) = (fuel : CanonicalRat) := by exact_mod_cast (rfl : fuel = fuel)
    grind
  have hpow : 2 * a ≤ ratPow 2 (halvings.go a fuel) :=
    halvings_go_two_mul_le fuel a ha hfuel_bound
  have hs : (0 : CanonicalRat) < ratPow 2 (halvings.go a fuel) :=
    ratPow_pos (by decide) _
  rw [ratAbs_div_of_pos hs]
  apply Interval.div_le_of_le_mul hs
  grind

/-- Outward rounding scale: endpoints to multiples of `10⁻⁶⁰`. -/
@[expose] def roundScale : Nat := 10 ^ 60

/-- **The exponential's enclosure** `expEnclosure x ∋ eˣ`: halve `k = halvings x` times, take the
half-enclosure, square `k` times. -/
@[expose] def expEnclosure (x : CanonicalRat) : Interval :=
  let k := halvings x
  Interval.sqrIterRound (10 ^ 60) (Interval.roundOut (10 ^ 60) (expHalfEnclosure (x / ratPow 2 k))) k

theorem roundScale_pos : 0 < roundScale := by
  unfold roundScale; exact Nat.pow_pos (by decide)

/-- **The only assumption is `expHalf`**: any value in the half-enclosure of the halved argument, raised
to `2ᵏ`, lies in `expEnclosure x`. With `e₀ = e^{x/2ᵏ}` this is `eˣ = e₀^{2ᵏ} ∈ expEnclosure x`. -/
theorem expEnclosure_of_half {x e₀ : CanonicalRat}
    (h : e₀ ∈ expHalfEnclosure (x / ratPow 2 (halvings x))) :
    ratPow e₀ (2 ^ halvings x) ∈ expEnclosure x := by
  unfold expEnclosure
  exact Interval.sqrIterRound_mem roundScale_pos (Interval.roundOut_mem roundScale_pos h) _

private theorem expFn_mul_pow_two
    (expFn : CanonicalRat → CanonicalRat)
    (hDouble : ∀ t : CanonicalRat, expFn (2 * t) = expFn t * expFn t)
    (t : CanonicalRat) :
    ∀ k : Nat, expFn (t * ratPow 2 k) = ratPow (expFn t) (2 ^ k)
  | 0 => by simp [ratPow]
  | k + 1 => by
    have harg : t * ratPow 2 (k + 1) = 2 * (t * ratPow 2 k) := by
      rw [ratPow_succ]
      grind
    have hpow : ratPow (expFn t) (2 ^ (k + 1)) =
        ratPow (expFn t) (2 ^ k) * ratPow (expFn t) (2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_two, ratPow_add]
    rw [harg, hDouble, expFn_mul_pow_two expFn hDouble t k, hpow]

/-- **Unconditional Exponential Enclosure Soundness (`expEnclosure_sound`)**:
For any exponential map `expFn` satisfying the local `[−1/2, 1/2]` Taylor–Lagrange enclosure `hHalf`
and functional squaring law `hDouble` (`exp(2t) = exp(t)²`), `expFn x ∈ expEnclosure x` holds
**unconditionally for every `x : CanonicalRat`** (with zero `|x| ≤ 2⁶³` restriction). -/
theorem expEnclosure_sound
    (expFn : CanonicalRat → CanonicalRat)
    (hHalf : ∀ t : CanonicalRat, ratAbs t ≤ 1 / 2 → expFn t ∈ expHalfEnclosure t)
    (hDouble : ∀ t : CanonicalRat, expFn (2 * t) = expFn t * expFn t)
    (x : CanonicalRat) :
    expFn x ∈ expEnclosure x := by
  let k := halvings x
  let s := ratPow 2 k
  have hs : (0 : CanonicalRat) < s := ratPow_pos (by decide) k
  have hmem : expFn (x / s) ∈ expHalfEnclosure (x / s) :=
    hHalf (x / s) (halvings_arg_abs_le_half x)
  have hpow : ratPow (expFn (x / s)) (2 ^ k) ∈ expEnclosure x :=
    expEnclosure_of_half hmem
  have hx : (x / s) * s = x := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel s (Rat.ne_of_gt hs), Rat.mul_one]
  have heq : expFn x = ratPow (expFn (x / s)) (2 ^ k) :=
    (congrArg expFn hx.symm).trans (expFn_mul_pow_two expFn hDouble (x / s) k)
  exact heq ▸ hpow

/-! ## 4. The Bernoulli function -/

/-- `1 − x/2 + x²/12 − x⁴/720 + x⁶/30240 − x⁸/1209600 + x¹⁰/47900160`. -/
@[expose] def bernSeries (x : CanonicalRat) : CanonicalRat :=
  let x2 := x * x
  1 - x / 2 + x2 * (1/12 + x2 * (-1/720 + x2 * (1/30240 + x2 * (-1/1209600 + x2 * (1/47900160)))))

/-- The series' remainder bound `x¹²/10⁹` for `|x| ≤ 1/8`. -/
@[expose] def bernSeriesRem (x : CanonicalRat) : CanonicalRat :=
  ratPow (ratAbs x) 12 / 1000000000

/-- **Assumed fact `bernSmall`**: for `|x| ≤ 1/8`, `B(x) = x/(eˣ − 1)` lies in this interval. -/
@[expose] def bernSmallEnclosure (x : CanonicalRat) : Interval :=
  ⟨bernSeries x - bernSeriesRem x, bernSeries x + bernSeriesRem x⟩

/-- The Bernoulli function of `x` computed from a value `e` standing for `eˣ`, in the form the
enclosure takes (`x/(e−1)` for `x > 0`, `(−x)/(1−e)` for `x < 0`, `1` at `0`). -/
@[expose] def bernOf (x e : CanonicalRat) : CanonicalRat :=
  if 0 < x then x / (e - 1) else if x < 0 then (-x) / (1 - e) else 1

/-- **The Bernoulli function's enclosure** `bernEnclosure? x ∋ B(x)`: the series on `|x| ≤ 1/8`, the
quotient `x/(eˣ − 1)` by interval division beyond, `none` when the exponential's enclosure does not
separate `eˣ` from `1` (it always does for `|x| > 1/8`; the `none` is the checker's refusal, not a
case the arithmetic reaches). -/
@[expose] def bernEnclosure? (x : CanonicalRat) : Option Interval :=
  if ratAbs x ≤ 1/8 then
    let x2 := x * x
    let ser := 1 - x / 2 + x2 * (1/12 + x2 * (-1/720 + x2 * (1/30240 + x2 * (-1/1209600 + x2 * (1/47900160)))))
    let rem := ratPow (ratAbs x) 12 / 1000000000
    some ⟨ser - rem, ser + rem⟩
  else
    let E := expEnclosure x
    if 0 < x then Interval.divPos? (Interval.ofPoint x) (Interval.sub E (Interval.ofPoint 1))
    else Interval.divPos? (Interval.ofPoint (-x)) (Interval.sub (Interval.ofPoint 1) E)

/-- **Beyond `|x| ≤ 1/8` the only assumption is `expHalf`**: if `e ∈ expEnclosure x` then
`bernOf x e ∈ bernEnclosure? x`. -/
theorem bernOf_mem {x e : CanonicalRat} {J : Interval} (hbig : ¬ ratAbs x ≤ 1/8)
    (he : e ∈ expEnclosure x) (hJ : bernEnclosure? x = some J) : bernOf x e ∈ J := by
  unfold bernEnclosure? at hJ
  simp only [hbig, ↓reduceIte] at hJ
  by_cases hpos : 0 < x
  · simp only [hpos, ↓reduceIte] at hJ
    simp only [bernOf, hpos, ↓reduceIte]
    exact Interval.divPos?_mem (Interval.ofPoint_mem x) (Interval.sub_mem he (Interval.ofPoint_mem 1)) hJ
  · simp only [hpos, ↓reduceIte] at hJ
    have hneg : x < 0 := by
      unfold ratAbs at hbig
      by_cases hx : x < 0
      · exact hx
      · exfalso; simp only [hx, ↓reduceIte] at hbig; grind
    simp only [bernOf, hpos, hneg, ↓reduceIte]
    exact Interval.divPos?_mem (Interval.ofPoint_mem (-x)) (Interval.sub_mem (Interval.ofPoint_mem 1) he) hJ

/-! ## 5. Brackets for fractional powers and roots -/

/-- `y` is within relative `δ` of `r^{num/den}`: `(y(1−δ))^den ≤ r^num ≤ (y(1+δ))^den`, `y, r ≥ 0`,
`0 ≤ δ < 1`. A producer finds `y`; the checker only multiplies. -/
@[expose] def powBracket (y r : CanonicalRat) (num den : Nat) (δ : CanonicalRat) : Bool :=
  decide (0 ≤ y) && decide (0 ≤ r) && decide (0 ≤ δ) && decide (δ < 1) &&
  decide (ratPow (y * (1 - δ)) den ≤ ratPow r num) &&
  decide (ratPow r num ≤ ratPow (y * (1 + δ)) den)

/-- Two values bracketed against the same `r^{num/den}` agree to within `(1+δ)/(1−δ)`. -/
theorem powBracket_agree {y₁ y₂ r : CanonicalRat} {num den : Nat} {δ : CanonicalRat} (hden : 0 < den)
    (h₁ : powBracket y₁ r num den δ = true) (h₂ : powBracket y₂ r num den δ = true) :
    y₁ * (1 - δ) ≤ y₂ * (1 + δ) ∧ y₂ * (1 - δ) ≤ y₁ * (1 + δ) := by
  simp only [powBracket, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  obtain ⟨⟨⟨⟨⟨hy₁, hr⟩, hδ0⟩, hδ1⟩, hlo₁⟩, hhi₁⟩ := h₁
  obtain ⟨⟨⟨⟨⟨hy₂, _⟩, _⟩, _⟩, hlo₂⟩, hhi₂⟩ := h₂
  have h1δ : 0 ≤ 1 - δ := by grind
  have h1δ' : 0 ≤ 1 + δ := by grind
  obtain ⟨d, rfl⟩ : ∃ d, den = d + 1 := ⟨den - 1, by omega⟩
  constructor
  · exact le_of_ratPow_le (Rat.mul_nonneg hy₂ h1δ') (Rat.le_trans hlo₁ hhi₂)
  · exact le_of_ratPow_le (Rat.mul_nonneg hy₁ h1δ') (Rat.le_trans hlo₂ hhi₁)

/-- A square root bracket is the power bracket with `num/den = 1/2`. -/
@[expose] def sqrtBracket (s x δ : CanonicalRat) : Bool :=
  powBracket s x 1 2 δ

/-- A bracketed root is pinned: `(s(1−δ))² ≤ x ≤ (s(1+δ))²`. -/
theorem sqrtBracket_bounds {s x δ : CanonicalRat} (h : sqrtBracket s x δ = true) :
    0 ≤ s ∧ (s * (1 - δ)) * (s * (1 - δ)) ≤ x ∧ x ≤ (s * (1 + δ)) * (s * (1 + δ)) := by
  simp only [sqrtBracket, powBracket, Bool.and_eq_true, decide_eq_true_eq, ratPow, Rat.one_mul] at h
  obtain ⟨⟨⟨⟨⟨hs, _⟩, _⟩, _⟩, hlo⟩, hhi⟩ := h
  exact ⟨hs, hlo, hhi⟩

end Obend.Hardware.Device
end
