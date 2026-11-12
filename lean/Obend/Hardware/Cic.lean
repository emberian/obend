module
/-!
# Obend.Hardware.Cic — Hogenauer's cascaded integrator-comb decimator

A CIC decimator (Hogenauer 1981) is `N` integrators at the input rate, a decimation by `R`, and
`N` combs with differential delay `M` at the output rate. This file proves, for every `R ≥ 1`,
`M` and `N`:

* `cicOut_eq_movingSum`: the decimated output is the `N`-fold moving sum of length `R·M` of the
  input, sampled every `R` samples (the impulse response is the `N`-fold convolution of a box of
  length `R·M`, so the DC gain is `(R·M)^N`);
* `cicOut_bounds`: an input in `[lo, hi]` (with `lo ≤ 0 ≤ hi`) gives an output in
  `[(R·M)^N·lo, (R·M)^N·hi]`;
* `cic_register_width`: with `R·M = 2^k` and a two's-complement input of `b + 1` bits, every
  register `B = N·k + b + 1` bits wide suffices. The integrators do wrap (an integrator of a
  constant input grows without bound); what Hogenauer's bound says, and what is proved here, is
  that any datapath whose output is congruent to the exact output modulo `2^B` (an adder/subtracter
  datapath that wraps modulo `2^B` in every register is one, `Congr`) reads, as a `B`-bit signed
  number, exactly the true output.

Signals are causal: `x : Nat → Int`, zero before time `0`. `Obend.Apps.SdrFt8Cic` instantiates this
for the SDR's `R = 64, M = 1, N = 3`, 16-bit input, 34-bit `RtlModule`.
-/
@[expose] public section

namespace Obend.Hardware.Cic

set_option autoImplicit false

/-- A causal integer signal: sample `n` at time `n = 0, 1, …`. -/
abbrev Signal := Nat → Int

/-- Integrator: `cum x n = x 0 + ⋯ + x (n - 1)`, the accumulator's value after `n` samples. -/
def cum (x : Signal) : Signal
  | 0 => 0
  | n + 1 => cum x n + x n

/-- Comb with lag `D` and zero history: `y n - y (n - D)`, with `y` zero before time `0`. -/
def comb (D : Nat) (y : Signal) : Signal :=
  fun n => if D ≤ n then y n - y (n - D) else y n

/-- `N` cascaded copies of a stage. -/
def stages (f : Signal → Signal) : Nat → Signal → Signal
  | 0, x => x
  | n + 1, x => f (stages f n x)

/-- Moving sum of the last `D` samples: a comb after an integrator. -/
def movingSum (D : Nat) (x : Signal) : Signal :=
  comb D (cum x)

/-- The exact output of the CIC decimator, at output index `m`: `N` integrators at the input rate,
the integrator output sampled at times `m·R`, then `N` combs of delay `M` at the output rate. -/
def cicOut (R M N : Nat) (x : Signal) : Signal :=
  stages (comb M) N (fun m => stages cum N x (m * R))

@[simp] theorem cum_zero (x : Signal) : cum x 0 = 0 := rfl
@[simp] theorem cum_succ (x : Signal) (n : Nat) : cum x (n + 1) = cum x n + x n := rfl
@[simp] theorem stages_zero (f : Signal → Signal) (x : Signal) : stages f 0 x = x := rfl
@[simp] theorem stages_succ (f : Signal → Signal) (n : Nat) (x : Signal) :
    stages f (n + 1) x = f (stages f n x) := rfl

/-! ## The impulse response -/

/-- Combs and integrators commute (both are linear and time-invariant on causal signals). -/
theorem comb_cum (D : Nat) (y : Signal) : comb D (cum y) = cum (comb D y) := by
  funext n
  induction n with
  | zero => simp [comb]
  | succ n ih =>
    rw [cum_succ, ← ih]
    simp only [comb]
    by_cases hD : D ≤ n
    · have h1 : D ≤ n + 1 := by omega
      have h2 : n + 1 - D = (n - D) + 1 := by omega
      rw [ite_eq_left h1, ite_eq_left hD, ite_eq_left hD, h2, cum_succ, cum_succ]
      omega
    · by_cases hD1 : D = n + 1
      · subst hD1
        rw [ite_eq_left (Nat.le_refl _), ite_eq_right hD, ite_eq_right hD, Nat.sub_self, cum_zero, cum_succ]
        omega
      · have h1 : ¬ D ≤ n + 1 := by omega
        rw [ite_eq_right h1, ite_eq_right hD, ite_eq_right hD, cum_succ]

theorem stages_comb_cum (D N : Nat) (y : Signal) :
    stages (comb D) N (cum y) = cum (stages (comb D) N y) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [stages_succ, stages_succ, ih, comb_cum]

/-- `N` combs after `N` integrators is `N` moving sums. -/
theorem stages_comb_stages_cum (D N : Nat) (x : Signal) :
    stages (comb D) N (stages cum N x) = stages (movingSum D) N x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [stages_succ, stages_succ cum, stages_comb_cum, stages_succ, ih]
    rfl

/-- A comb of delay `M` at the output rate is a comb of delay `M·R` at the input rate, sampled. -/
theorem stages_comb_decimate (R M N : Nat) (hR : 0 < R) (y : Signal) :
    stages (comb M) N (fun m => y (m * R)) = fun m => stages (comb (M * R)) N y (m * R) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [stages_succ, ih]
    funext m
    simp only [stages_succ, comb]
    by_cases hM : M ≤ m
    · have h1 : M * R ≤ m * R := Nat.mul_le_mul_right R hM
      rw [ite_eq_left hM, ite_eq_left h1, Nat.sub_mul]
    · have h1 : ¬ M * R ≤ m * R := fun h => hM ((Nat.mul_le_mul_right_iff hR).mp h)
      rw [ite_eq_right hM, ite_eq_right h1]

/-- **The CIC's impulse response.** The decimated output is the `N`-fold moving sum of length
`R·M` of the input, sampled every `R` input samples. -/
theorem cicOut_eq_movingSum (R M N : Nat) (hR : 0 < R) (x : Signal) (m : Nat) :
    cicOut R M N x m = stages (movingSum (M * R)) N x (m * R) := by
  unfold cicOut
  rw [stages_comb_decimate R M N hR, stages_comb_stages_cum]

/-! ## Gain -/

theorem cum_window_bounds (x : Signal) (lo hi : Int) (hx : ∀ n, lo ≤ x n ∧ x n ≤ hi) (m : Nat) :
    ∀ k : Nat, (k : Int) * lo ≤ cum x (m + k) - cum x m ∧ cum x (m + k) - cum x m ≤ (k : Int) * hi := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hxk := hx (m + k)
    rw [← Nat.add_assoc, cum_succ]
    have e1 : ((k + 1 : Nat) : Int) * lo = (k : Int) * lo + lo := by push_cast; rw [Int.add_mul, Int.one_mul]
    have e2 : ((k + 1 : Nat) : Int) * hi = (k : Int) * hi + hi := by push_cast; rw [Int.add_mul, Int.one_mul]
    rw [e1, e2]
    omega

/-- A moving sum of length `D` of a signal in `[lo, hi]` lies in `[D·lo, D·hi]` (`lo ≤ 0 ≤ hi`:
the first `D - 1` outputs sum fewer than `D` samples). -/
theorem movingSum_bounds (D : Nat) (x : Signal) (lo hi : Int) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hx : ∀ n, lo ≤ x n ∧ x n ≤ hi) (n : Nat) :
    (D : Int) * lo ≤ movingSum D x n ∧ movingSum D x n ≤ (D : Int) * hi := by
  unfold movingSum comb
  by_cases hD : D ≤ n
  · rw [ite_eq_left hD]
    have h := cum_window_bounds x lo hi hx (n - D) D
    rw [Nat.sub_add_cancel hD] at h
    exact h
  · rw [ite_eq_right hD]
    have h := cum_window_bounds x lo hi hx 0 n
    rw [Nat.zero_add, cum_zero, Int.sub_zero] at h
    have hnD : (n : Int) ≤ (D : Int) := by omega
    have a1 : (D : Int) * lo ≤ (n : Int) * lo := Int.mul_le_mul_of_nonpos_right hnD hlo
    have a2 : (n : Int) * hi ≤ (D : Int) * hi := Int.mul_le_mul_of_nonneg_right hnD hhi
    omega

theorem stages_movingSum_bounds (D N : Nat) (x : Signal) (lo hi : Int) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hx : ∀ n, lo ≤ x n ∧ x n ≤ hi) (n : Nat) :
    (D : Int) ^ N * lo ≤ stages (movingSum D) N x n ∧ stages (movingSum D) N x n ≤ (D : Int) ^ N * hi := by
  induction N generalizing n with
  | zero => simp [stages, Int.pow_zero, Int.one_mul, hx n]
  | succ N ih =>
    have hpow : (0 : Int) ≤ (D : Int) ^ N := Int.pow_nonneg (Int.natCast_nonneg D)
    have hlo' : (D : Int) ^ N * lo ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hpow hlo
    have hhi' : 0 ≤ (D : Int) ^ N * hi := Int.mul_nonneg hpow hhi
    have h := movingSum_bounds D (stages (movingSum D) N x) _ _ hlo' hhi' ih n
    rw [stages_succ, Int.pow_succ, Int.mul_comm ((D : Int) ^ N) (D : Int), Int.mul_assoc, Int.mul_assoc]
    exact h

/-- **The CIC's gain.** An input in `[lo, hi]` (`lo ≤ 0 ≤ hi`) gives an output in
`[(R·M)^N·lo, (R·M)^N·hi]`. -/
theorem cicOut_bounds (R M N : Nat) (hR : 0 < R) (x : Signal) (lo hi : Int) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hx : ∀ n, lo ≤ x n ∧ x n ≤ hi) (m : Nat) :
    ((M * R : Nat) : Int) ^ N * lo ≤ cicOut R M N x m ∧ cicOut R M N x m ≤ ((M * R : Nat) : Int) ^ N * hi := by
  rw [cicOut_eq_movingSum R M N hR]
  exact stages_movingSum_bounds (M * R) N x lo hi hlo hhi hx (m * R)

/-! ## Register width -/

/-- Two signals agree modulo `2^B` at every sample. -/
def Congr (B : Nat) (y z : Signal) : Prop :=
  ∀ n, y n % (2 : Int) ^ B = z n % (2 : Int) ^ B

theorem Congr.refl (B : Nat) (y : Signal) : Congr B y y := fun _ => rfl

theorem Congr.cum {B : Nat} {y z : Signal} (h : Congr B y z) : Congr B (cum y) (cum z) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [cum_succ, cum_succ, Int.add_emod, ih, h n, ← Int.add_emod]

theorem Congr.comb {B : Nat} (D : Nat) {y z : Signal} (h : Congr B y z) : Congr B (comb D y) (comb D z) := by
  intro n
  simp only [Obend.Hardware.Cic.comb]
  split
  · rw [Int.sub_emod, h n, h (n - D), ← Int.sub_emod]
  · exact h n

theorem Congr.stages {B : Nat} (f : Signal → Signal) (hf : ∀ y z, Congr B y z → Congr B (f y) (f z))
    (N : Nat) {y z : Signal} (h : Congr B y z) : Congr B (stages f N y) (stages f N z) := by
  induction N with
  | zero => exact h
  | succ N ih => exact hf _ _ ih

theorem Congr.sample {B : Nat} (R : Nat) {y z : Signal} (h : Congr B y z) :
    Congr B (fun m => y (m * R)) (fun m => z (m * R)) := fun m => h (m * R)

/-- A value in `[-2^(B-1), 2^(B-1))` is its own `B`-bit signed reading. -/
theorem bmod_two_pow_of_range (B : Nat) (v : Int) (hlo : -(2 : Int) ^ B ≤ v) (hhi : v < (2 : Int) ^ B) :
    Int.bmod v (2 ^ (B + 1)) = v := by
  apply Int.bmod_eq_of_le
  · have : ((2 ^ (B + 1) : Nat) : Int) / 2 = (2 : Int) ^ B := by
      rw [Int.natCast_pow, Int.pow_succ]; push_cast; exact Int.mul_ediv_cancel _ (by decide)
    rw [this]; exact hlo
  · have : (((2 ^ (B + 1) : Nat) : Int) + 1) / 2 = (2 : Int) ^ B := by
      rw [Int.natCast_pow, Int.pow_succ]; push_cast; omega
    rw [this]; exact hhi

/-- **Hogenauer's register width.** Let `R·M = 2^k` and let the input be a two's-complement
`(b+1)`-bit signal (`-2^b ≤ x n < 2^b`). Then the exact output lies in `[-2^(N·k+b), 2^(N·k+b))`,
and any datapath output `w` congruent to it modulo `2^B`, `B = N·k + b + 1` (a datapath whose
registers wrap modulo `2^B`), read as a `B`-bit signed number (`Int.bmod`), is the exact output. -/
theorem cic_register_width (R M N k b : Nat) (hR : 0 < R) (hRM : M * R = 2 ^ k)
    (x : Signal) (hx : ∀ n, -(2 : Int) ^ b ≤ x n ∧ x n < (2 : Int) ^ b)
    (w : Signal) (hw : Congr (N * k + b + 1) w (cicOut R M N x)) (m : Nat) :
    (-(2 : Int) ^ (N * k + b) ≤ cicOut R M N x m ∧ cicOut R M N x m < (2 : Int) ^ (N * k + b)) ∧
    Int.bmod (w m) (2 ^ (N * k + b + 1)) = cicOut R M N x m := by
  have hb : (0 : Int) < (2 : Int) ^ b := Int.pow_pos (by decide)
  have hx' : ∀ n, -(2 : Int) ^ b ≤ x n ∧ x n ≤ (2 : Int) ^ b - 1 := fun n => ⟨(hx n).1, by have := (hx n).2; omega⟩
  have hbnd := cicOut_bounds R M N hR x (-(2 : Int) ^ b) ((2 : Int) ^ b - 1) (by omega) (by omega) hx' m
  have hG : ((M * R : Nat) : Int) ^ N = (2 : Int) ^ (N * k) := by
    rw [hRM, Int.natCast_pow, ← Int.pow_mul, Nat.mul_comm k N]; rfl
  rw [hG] at hbnd
  have hGpos : (0 : Int) < (2 : Int) ^ (N * k) := Int.pow_pos (by decide)
  have hsplit : (2 : Int) ^ (N * k + b) = (2 : Int) ^ (N * k) * (2 : Int) ^ b := Int.pow_add _ _ _
  have hrange : -(2 : Int) ^ (N * k + b) ≤ cicOut R M N x m ∧ cicOut R M N x m < (2 : Int) ^ (N * k + b) := by
    rw [hsplit]
    refine ⟨?_, ?_⟩
    · have := hbnd.1; rw [Int.mul_neg] at this; exact this
    · have h1 := hbnd.2
      rw [Int.mul_sub, Int.mul_one] at h1
      omega
  refine ⟨hrange, ?_⟩
  have hcast : ((2 ^ (N * k + b + 1) : Nat) : Int) = (2 : Int) ^ (N * k + b + 1) := by
    rw [Int.natCast_pow]; rfl
  rw [← Int.emod_bmod, hcast, hw m, ← hcast, Int.emod_bmod]
  exact bmod_two_pow_of_range (N * k + b) _ hrange.1 hrange.2

end Obend.Hardware.Cic
