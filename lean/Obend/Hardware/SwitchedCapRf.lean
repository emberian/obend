module
public import Obend.Analysis.TaylorModel
/-!
# The switched-capacitor front end and the vectoring CORDIC (`Obend.Hardware.SwitchedCapRf`)

The analog side of the FT8 receiver of `Obend.Apps.SdrFt8Rx` and the one digital block whose error
that file took as given, over the rationals and the integers.

* **Tayloe detector.** Four hold capacitors commutated at the LO (Tayloe, US 6,230,000; for the
  switched-RC analysis see Soer, Klumperink, de Boer, van Vliet and Nauta, "Unified frequency-domain
  analysis of switched-series-RC passive mixers and samplers", IEEE TCAS-I 57(10), 2010).
  `tayloe_monodromy_contractive`: the
  retention factor `α = exp(-T_LO/(4·R_s·C_H))` is enclosed in `(0, 1)` for all component values and
  every `AnalyticModel` of `exp`, and the period map contracts, stays bounded and keeps `I` and `Q`
  apart. `tayloe_odd_harmonic_alias_envelope`: even harmonics cancel in the differential outputs;
  the `(2m+1)`-th harmonic folds with relative amplitude exactly `1/(2m+1)` (`chebU_even`,
  `gateU_quarter`: Chebyshev's `U_{2m}` at `cos² φ = 1/2`).
* **Preselector.** `cauer_lc_ladder_scattering_passive`: any ladder of series and shunt branches,
  including the series and shunt LC traps of an elliptic (Cauer) section, between resistive
  terminations has `|S₁₁|² + |S₂₁|² ≤ 1` at every frequency, with equality when it is reactive;
  `tayloe_cauer_composite_alias_bound` composes it with the detector.
* **CORDIC.** `cordicAtan2` is the discriminator's 12-stage integer vectoring CORDIC.
  `cordic_residual_cone` is its convergence theorem with every shift's truncation: the input,
  turned back by the exact rational rotation `∏ (2^i + σ_i·j)` the run's signs define, lies within
  `atan (303/100000)` of the real axis, for every input with `|x| + |y| ≥ 2^13`.
  `cordicAtan2_arg` restates it in radians, `cordicAtan2_error_lt_4000_urad` in the budget the
  slicer leaves. The convergence invariant is the classical one (Volder 1959, Walther 1971); for
  the standard treatment of the truncation error see Hu, "The quantization effects of the CORDIC
  algorithm", IEEE Trans. Signal Processing 40(4), 1992. The bound here is this file's own.

This tree has no real numbers. The cone theorem is exact integer algebra; "radians" enter through
`ArgIn`, a derivation calculus whose two generating rules are theorems of real analysis (see there).
-/

public section

namespace Obend.Hardware.SwitchedCapRf

open Obend.Analysis

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The Tayloe detector

Four hold capacitors `C_H`, each connected to the antenna (source resistance `R_s`) for one quarter
`τ = T_LO/4` of the LO period by a non-overlapping commutator. While capacitor `k` is connected its
voltage follows `C_H·dv/dt = (u - v)/R_s`, so over its aperture `v ↦ α·v + (1 - α)·w` with
`α = exp(-τ/(R_s·C_H))` and `w` the exponentially weighted mean of the source over the aperture
(the source itself when it is constant). The other three quarters it holds. One LO period is one
such step on each capacitor: the Poincaré map of the periodically switched network is affine with
linear part `α·I`. `I = v₀ - v₂` and `Q = v₁ - v₃` are the baseband outputs. -/

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind
theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

/-- `2^k` as a rational. -/
def pow2 : Nat → Rat
  | 0 => 1
  | k + 1 => 2 * pow2 k

theorem pow2_pos : ∀ k, 0 < pow2 k
  | 0 => by decide
  | k + 1 => by have := pow2_pos k; simp only [pow2]; grind

/-- `e^(2^k)` by `k` squarings. -/
def sqIter : Nat → Rat → Rat
  | 0, e => e
  | k + 1, e => sqIter k (e * e)

theorem sqIter_mono : ∀ (k : Nat) (a b : Rat), 0 < a → a ≤ b → 0 < sqIter k a ∧ sqIter k a ≤ sqIter k b
  | 0, _, _, ha, hab => ⟨ha, hab⟩
  | k + 1, a, b, ha, hab => by
    have h1 := Rat.mul_le_mul_of_nonneg_left hab (Rat.le_of_lt ha)
    have h2 := Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans (Rat.le_of_lt ha) hab)
    exact sqIter_mono k (a * a) (b * b) (Rat.mul_pos ha ha) (Rat.le_trans h1 h2)

theorem sqIter_lt_one : ∀ (k : Nat) (a : Rat), 0 < a → a < 1 → sqIter k a < 1
  | 0, _, _, h => h
  | k + 1, a, ha, h => by
    have h1 := Rat.mul_lt_mul_of_pos_left h ha
    exact sqIter_lt_one k (a * a) (Rat.mul_pos ha ha) (by grind)

/-- The front end's components, with the depth `k` of the argument reduction
`exp(-x) = exp(-x/2^k)^(2^k)` that brings the exponent into the exponential's enclosure domain. -/
structure TayloeFrontEndSpec where
  /-- source resistance, Ω -/
  rs : Rat
  /-- hold capacitance, F -/
  ch : Rat
  /-- LO period, s -/
  tlo : Rat
  /-- halvings of the exponent -/
  k : Nat
  rs_pos : 0 < rs
  ch_pos : 0 < ch
  tlo_pos : 0 < tlo
  reduced : tlo / (4 * rs * ch) ≤ pow2 k

namespace TayloeFrontEndSpec

/-- The aperture in time constants, `x = T_LO / (4·R_s·C_H)`. -/
def exponent (s : TayloeFrontEndSpec) : Rat := s.tlo / (4 * s.rs * s.ch)

/-- The reduced argument `-x/2^k ∈ [-1, 0)`. -/
def reducedArg (s : TayloeFrontEndSpec) : Rat := -(s.exponent / pow2 s.k)

theorem exponent_pos (s : TayloeFrontEndSpec) : 0 < s.exponent := by
  have h4 : (0 : Rat) < 4 * s.rs * s.ch :=
    Rat.mul_pos (Rat.mul_pos (by decide) s.rs_pos) s.ch_pos
  have hne : s.tlo / (4 * s.rs * s.ch) ≠ 0 := by
    intro e
    have := Rat.div_mul_cancel (a := s.tlo) (Rat.ne_of_gt h4)
    rw [e] at this
    have := s.tlo_pos
    grind
  have := rat_div_nonneg (Rat.le_of_lt s.tlo_pos) h4
  unfold exponent
  grind

theorem reducedArg_mem (s : TayloeFrontEndSpec) : -1 ≤ s.reducedArg ∧ s.reducedArg < 0 := by
  have hp := pow2_pos s.k
  have hx := s.exponent_pos
  have h1 : s.exponent / pow2 s.k ≤ 1 := rat_div_le_of_mul_le hp (by have := s.reduced; unfold exponent; grind)
  have h0 := rat_div_nonneg (Rat.le_of_lt hx) hp
  have hne : s.exponent / pow2 s.k ≠ 0 := by
    intro e
    have := Rat.div_mul_cancel (a := s.exponent) (Rat.ne_of_gt hp)
    rw [e] at this; grind
  unfold reducedArg
  constructor <;> grind

/-- The degree-4 Maclaurin polynomial of `exp` less its Lagrange remainder bound on `[-1, 0]`. -/
def expLo (y : Rat) : Rat := 1 + y + y * y / 2 + y * y * y / 6 + y * y * y * y / 24 + y * y * y * y * y / 40
/-- The same polynomial plus the remainder bound. -/
def expHi (y : Rat) : Rat := 1 + y + y * y / 2 + y * y * y / 6 + y * y * y * y / 24 - y * y * y * y * y / 40

/-- The retention factor `α = exp(-T_LO/(4·R_s·C_H))` of one aperture, in an analytic model. -/
def retention (R : Type) [M : AnalyticModel R] (s : TayloeFrontEndSpec) : Rat :=
  sqIter s.k (M.expFn s.reducedArg)

/-- The rational enclosure of the retention factor. -/
def retentionLo (s : TayloeFrontEndSpec) : Rat := sqIter s.k (expLo s.reducedArg)
def retentionHi (s : TayloeFrontEndSpec) : Rat := sqIter s.k (expHi s.reducedArg)

/-- On `[-1, 0)` the two polynomials are in `(0, 1)`. -/
theorem exp_poly_bounds (y : Rat) (h1 : -1 ≤ y) (h0 : y < 0) : 0 < expLo y ∧ expHi y < 1 ∧ expLo y ≤ expHi y := by
  -- u = -y ∈ (0, 1]
  have hu0 : (0 : Rat) < -y := by grind
  have hu1 : -y ≤ 1 := by grind
  have p2 : 0 < y * y := by have := Rat.mul_pos hu0 hu0; grind
  have q2 : y * y ≤ -y := by have := Rat.mul_le_mul_of_nonneg_left hu1 (Rat.le_of_lt hu0); grind
  have q3 : -(y * y * y) ≤ y * y := by
    have := Rat.mul_le_mul_of_nonneg_left hu1 (Rat.le_of_lt p2); grind
  have p3 : 0 ≤ -(y * y * y) := by have := Rat.mul_nonneg (Rat.le_of_lt p2) (Rat.le_of_lt hu0); grind
  have p4 : 0 ≤ y * y * y * y := by have := Rat.mul_nonneg p3 (Rat.le_of_lt hu0); grind
  have q4 : y * y * y * y ≤ -(y * y * y) := by
    have := Rat.mul_le_mul_of_nonneg_left hu1 p3; grind
  have p5 : 0 ≤ -(y * y * y * y * y) := by have := Rat.mul_nonneg p4 (Rat.le_of_lt hu0); grind
  have q5 : -(y * y * y * y * y) ≤ y * y * y * y := by
    have := Rat.mul_le_mul_of_nonneg_left hu1 p4; grind
  unfold expLo expHi
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- **The retention factor is enclosed strictly inside `(0, 1)`**, for every component choice and
every analytic model of `exp`: `0 < α_lo ≤ α ≤ α_hi < 1`. -/
theorem retention_enclosure (R : Type) [M : AnalyticModel R] (s : TayloeFrontEndSpec) :
    0 < s.retentionLo ∧ s.retentionLo ≤ s.retention R ∧ s.retention R ≤ s.retentionHi ∧
      s.retentionHi < 1 := by
  unfold retentionLo retention retentionHi
  obtain ⟨h1, h0⟩ := s.reducedArg_mem
  obtain ⟨b0, b1, b2⟩ := exp_poly_bounds _ h1 h0
  obtain ⟨c, hc, he⟩ := M.exp_lagrange4 expValidDomain (by decide +kernel) s.reducedArg
    (by show (-1 : Rat) ≤ s.reducedArg ∧ s.reducedArg ≤ 1; constructor <;> grind)
  have hc' : CanonicalRat.mk (-1) 40 ≤ c ∧ c ≤ CanonicalRat.mk 1 40 := hc
  have e1 : CanonicalRat.mk (-1) 40 = -(1 / 40 : Rat) := by decide +kernel
  have e2 : CanonicalRat.mk 1 40 = (1 / 40 : Rat) := by decide +kernel
  rw [e1, e2] at hc'
  simp only [evalTaylorPolyAt, powRat] at he
  have e3 : CanonicalRat.mk 1 2 = (1 / 2 : Rat) := by decide +kernel
  have e4 : CanonicalRat.mk 1 6 = (1 / 6 : Rat) := by decide +kernel
  have e5 : CanonicalRat.mk 1 24 = (1 / 24 : Rat) := by decide +kernel
  rw [e3, e4, e5] at he
  generalize s.reducedArg = y at *
  -- y⁵ ≤ 0, so c·y⁵ is between y⁵/40 and -y⁵/40
  have hu0 : (0 : Rat) < -y := by grind
  have p2 : 0 < y * y := by have := Rat.mul_pos hu0 hu0; grind
  have p4 : 0 < y * y * y * y := by have := Rat.mul_pos p2 p2; grind
  have p5 : 0 < -(y * y * y * y * y) := by have := Rat.mul_pos p4 hu0; grind
  have m1 := Rat.mul_le_mul_of_nonneg_right hc'.1 (Rat.le_of_lt p5)
  have m2 := Rat.mul_le_mul_of_nonneg_right hc'.2 (Rat.le_of_lt p5)
  have hlo : expLo y ≤ M.expFn y := by unfold expLo; grind
  have hhi : M.expFn y ≤ expHi y := by unfold expHi; grind
  have s1 := sqIter_mono s.k _ _ b0 hlo
  have s2 := sqIter_mono s.k _ _ (rat_lt_of_lt_of_le b0 hlo) hhi
  exact ⟨s1.1, s1.2, s2.2, sqIter_lt_one s.k _ (rat_lt_of_lt_of_le b0 b2) b1⟩

theorem nat_le_pow2 : ∀ n : Nat, (n : Rat) ≤ pow2 n
  | 0 => by decide
  | n + 1 => by
    have h := nat_le_pow2 n
    have hp := pow2_pos n
    have h1 : (1 : Rat) ≤ pow2 n := by
      cases n with
      | zero => decide
      | succ m => have := pow2_pos m; simp only [pow2]; have := nat_le_pow2 m; simp only [pow2] at h; grind
    rw [Rat.natCast_add]; simp only [pow2]
    have : ((1 : Nat) : Rat) = 1 := rfl
    grind

/-- Every positive `R_s`, `C_H`, `T_LO` is a front end: some reduction depth always exists. -/
theorem exists_for (rs ch tlo : Rat) (h1 : 0 < rs) (h2 : 0 < ch) (h3 : 0 < tlo) :
    ∃ s : TayloeFrontEndSpec, s.rs = rs ∧ s.ch = ch ∧ s.tlo = tlo := by
  have hc := Rat.le_ceil (x := tlo / (4 * rs * ch))
  have hn : ((tlo / (4 * rs * ch)).ceil : Rat) ≤ (((tlo / (4 * rs * ch)).ceil.toNat : Nat) : Rat) := by
    rw [← Rat.intCast_natCast]; exact Rat.intCast_le_intCast.mpr (Int.self_le_toNat _)
  exact ⟨⟨rs, ch, tlo, (tlo / (4 * rs * ch)).ceil.toNat, h1, h2, h3,
    Rat.le_trans hc (Rat.le_trans hn (nat_le_pow2 _))⟩, rfl, rfl, rfl⟩

end TayloeFrontEndSpec

/-- The four hold capacitors' voltages. -/
structure TayloeState where
  v0 : Rat
  v1 : Rat
  v2 : Rat
  v3 : Rat

/-- One LO period of drive: the aperture mean of the source seen by each capacitor. -/
abbrev TayloeDrive := TayloeState

namespace TayloeState

/-- One LO period: each capacitor shares charge with the source for its aperture, retention `α`. -/
def cycle (α : Rat) (v : TayloeState) (w : TayloeDrive) : TayloeState :=
  ⟨α * v.v0 + (1 - α) * w.v0, α * v.v1 + (1 - α) * w.v1, α * v.v2 + (1 - α) * w.v2,
   α * v.v3 + (1 - α) * w.v3⟩

/-- Any number of periods under a drive sequence. -/
def run (α : Rat) : List TayloeDrive → TayloeState → TayloeState
  | [], v => v
  | w :: ws, v => run α ws (cycle α v w)

/-- The differential baseband outputs: `I = v₀ - v₂` (`chan false`), `Q = v₁ - v₃` (`chan true`). -/
def chan (q : Bool) (v : TayloeState) : Rat := if q then v.v1 - v.v3 else v.v0 - v.v2
abbrev iOut (v : TayloeState) : Rat := chan false v
abbrev qOut (v : TayloeState) : Rat := chan true v

/-- The energy of the difference of two capacitor states, in units of `C_H/2`. -/
def energyDiff (v v' : TayloeState) : Rat :=
  (v.v0 - v'.v0) * (v.v0 - v'.v0) + (v.v1 - v'.v1) * (v.v1 - v'.v1)
    + (v.v2 - v'.v2) * (v.v2 - v'.v2) + (v.v3 - v'.v3) * (v.v3 - v'.v3)

/-- Every capacitor voltage is within `B` in magnitude. -/
def Bounded (B : Rat) (v : TayloeState) : Prop :=
  (-B ≤ v.v0 ∧ v.v0 ≤ B) ∧ (-B ≤ v.v1 ∧ v.v1 ≤ B) ∧ (-B ≤ v.v2 ∧ v.v2 ≤ B) ∧ (-B ≤ v.v3 ∧ v.v3 ≤ B)

theorem energyDiff_nonneg (v v' : TayloeState) : 0 ≤ energyDiff v v' := by
  have h0 := Interval.rat_sq_nonneg (v.v0 - v'.v0)
  have h1 := Interval.rat_sq_nonneg (v.v1 - v'.v1)
  have h2 := Interval.rat_sq_nonneg (v.v2 - v'.v2)
  have h3 := Interval.rat_sq_nonneg (v.v3 - v'.v3)
  unfold energyDiff; grind

/-- One period scales the difference of two trajectories by `α` on every capacitor: the monodromy
is `α·I`, and the difference energy is multiplied by exactly `α²`. -/
theorem cycle_energyDiff (α : Rat) (v v' : TayloeState) (w : TayloeDrive) :
    energyDiff (cycle α v w) (cycle α v' w) = α * α * energyDiff v v' := by
  simp only [energyDiff, cycle]; grind

theorem run_energyDiff (α : Rat) : ∀ (ws : List TayloeDrive) (v v' : TayloeState),
    energyDiff (run α ws v) (run α ws v') = (α * α) ^ ws.length * energyDiff v v'
  | [], v, v' => by simp [run]
  | w :: ws, v, v' => by
    simp only [run, List.length_cons]
    rw [run_energyDiff α ws, cycle_energyDiff, Rat.pow_succ]; grind

theorem pow_le_one (a : Rat) (h0 : 0 ≤ a) (h1 : a ≤ 1) : ∀ n : Nat, 0 ≤ a ^ n ∧ a ^ n ≤ 1
  | 0 => by rw [Rat.pow_zero]; exact ⟨by decide, Rat.le_refl⟩
  | n + 1 => by
    obtain ⟨i0, i1⟩ := pow_le_one a h0 h1 n
    rw [Rat.pow_succ]
    have := Rat.mul_le_mul_of_nonneg_left h1 i0
    exact ⟨Rat.mul_nonneg i0 h0, by grind⟩

theorem cycle_bounded (α B : Rat) (h0 : 0 ≤ α) (h1 : α ≤ 1) (v : TayloeState) (w : TayloeDrive)
    (hv : Bounded B v) (hw : Bounded B w) : Bounded B (cycle α v w) := by
  have key : ∀ a b : Rat, -B ≤ a ∧ a ≤ B → -B ≤ b ∧ b ≤ B →
      -B ≤ α * a + (1 - α) * b ∧ α * a + (1 - α) * b ≤ B := by
    intro a b ha hb
    have m1 := Rat.mul_le_mul_of_nonneg_left ha.1 h0
    have m2 := Rat.mul_le_mul_of_nonneg_left ha.2 h0
    have m3 := Rat.mul_le_mul_of_nonneg_left hb.1 (by grind : (0 : Rat) ≤ 1 - α)
    have m4 := Rat.mul_le_mul_of_nonneg_left hb.2 (by grind : (0 : Rat) ≤ 1 - α)
    constructor <;> grind
  exact ⟨key _ _ hv.1 hw.1, key _ _ hv.2.1 hw.2.1, key _ _ hv.2.2.1 hw.2.2.1, key _ _ hv.2.2.2 hw.2.2.2⟩

theorem run_bounded (α B : Rat) (h0 : 0 ≤ α) (h1 : α ≤ 1) : ∀ (ws : List TayloeDrive) (v : TayloeState),
    Bounded B v → (∀ w ∈ ws, Bounded B w) → Bounded B (run α ws v)
  | [], _, hv, _ => hv
  | w :: ws, v, hv, hw =>
    run_bounded α B h0 h1 ws _ (cycle_bounded α B h0 h1 v w hv (hw w (List.mem_cons_self)))
      (fun w' h => hw w' (List.mem_cons_of_mem _ h))

/-- Two drive sequences of the same length agree, period by period, in the component `f`. -/
def DrivesAgree (f : TayloeState → Rat) : List TayloeDrive → List TayloeDrive → Prop
  | [], [] => True
  | w :: ws, w' :: ws' => f w = f w' ∧ DrivesAgree f ws ws'
  | _, _ => False

/-- A channel's output after a run depends only on its own initial value and its own component
of the drives: whatever the other channel's capacitors and drive do, it is the same. -/
theorem run_chan_isolated (α : Rat) (q : Bool) : ∀ (ws ws' : List TayloeDrive) (v v' : TayloeState),
    chan q v = chan q v' → DrivesAgree (chan q) ws ws' → chan q (run α ws v) = chan q (run α ws' v')
  | [], [], v, v', hv, _ => hv
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | w :: ws, w' :: ws', v, v', hv, h => by
    obtain ⟨hw, hrest⟩ := h
    simp only [run]
    refine run_chan_isolated α q ws ws' _ _ ?_ hrest
    cases q <;> simp only [chan, cycle] at hv hw ⊢ <;> grind

/-- **Even harmonics cancel.** An input that repeats after half an LO period (DC and every even
harmonic of the LO) gives opposite capacitors the same aperture mean, `w₀ = w₂` and `w₁ = w₃`;
under any such drive sequence the differential outputs only decay, `I ↦ α^n·I`, `Q ↦ α^n·Q`:
nothing of the input reaches them. -/
theorem run_even_harmonic_cancels (α : Rat) : ∀ (ws : List TayloeDrive) (v : TayloeState),
    (∀ w ∈ ws, w.v0 = w.v2 ∧ w.v1 = w.v3) →
    iOut (run α ws v) = α ^ ws.length * iOut v ∧ qOut (run α ws v) = α ^ ws.length * qOut v
  | [], v, _ => by simp [run]
  | w :: ws, v, hw => by
    obtain ⟨e0, e1⟩ := hw w (List.mem_cons_self)
    obtain ⟨hi, hq⟩ := run_even_harmonic_cancels α ws (cycle α v w) (fun w' h => hw w' (List.mem_cons_of_mem _ h))
    simp only [run, List.length_cons]
    rw [hi, hq, Rat.pow_succ]
    simp only [chan, cycle, e0, e1]
    constructor <;> grind

end TayloeState

open TayloeState in
/-- **The Tayloe detector's Poincaré map is a strict contraction.** For every `R_s, C_H, T_LO > 0`
and every analytic model of `exp`: the retention factor `α` is enclosed in `[α_lo, α_hi] ⊂ (0, 1)`;
over any drive sequence two trajectories' difference energy is multiplied by `α^(2n)`, so it never
grows; capacitor voltages stay within any bound that holds for the initial state and the drive; and
the `I` and `Q` channels do not interact. -/
theorem tayloe_monodromy_contractive (R : Type) [M : AnalyticModel R] (s : TayloeFrontEndSpec) :
    (0 < s.retentionLo ∧ s.retentionLo ≤ s.retention R ∧ s.retention R ≤ s.retentionHi ∧
      s.retentionHi < 1) ∧
    (∀ (ws : List TayloeDrive) (v v' : TayloeState),
      energyDiff (run (s.retention R) ws v) (run (s.retention R) ws v')
        = (s.retention R * s.retention R) ^ ws.length * energyDiff v v' ∧
      energyDiff (run (s.retention R) ws v) (run (s.retention R) ws v') ≤ energyDiff v v') ∧
    (∀ (B : Rat) (ws : List TayloeDrive) (v : TayloeState), Bounded B v → (∀ w ∈ ws, Bounded B w) →
      Bounded B (run (s.retention R) ws v)) ∧
    (∀ (q : Bool) (ws ws' : List TayloeDrive) (v v' : TayloeState), chan q v = chan q v' →
      DrivesAgree (chan q) ws ws' →
      chan q (run (s.retention R) ws v) = chan q (run (s.retention R) ws' v')) := by
  have he := s.retention_enclosure R
  have h0 : 0 < s.retention R := rat_lt_of_lt_of_le he.1 he.2.1
  have h1 : s.retention R < 1 := rat_lt_of_le_of_lt he.2.2.1 he.2.2.2
  refine ⟨he, ?_, ?_, run_chan_isolated _⟩
  · intro ws v v'
    refine ⟨run_energyDiff _ ws v v', ?_⟩
    rw [run_energyDiff]
    have hsq : s.retention R * s.retention R ≤ 1 := by
      have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h1) (Rat.le_of_lt h0); grind
    have hp := pow_le_one _ (Rat.le_of_lt (Rat.mul_pos h0 h0)) hsq ws.length
    have := Rat.mul_le_mul_of_nonneg_right hp.2 (energyDiff_nonneg v v')
    grind
  · intro B ws v hv hw
    exact run_bounded _ B (Rat.le_of_lt h0) (Rat.le_of_lt h1) ws v hv hw

/-! ### Odd harmonics: the gate's Chebyshev envelope

A capacitor's aperture is a rectangular gate of half-width `φ` in LO phase (`φ = π/4` at 25 %
duty). The gate's response to the `n`-th harmonic of the LO relative to its response to the
fundamental is `sin(nφ)/(n·sin φ) = U_{n-1}(cos φ)/n`, `U` the Chebyshev polynomials of the second
kind (the Dirichlet kernel). `chebU c` is their recurrence; for odd `n = 2m + 1` the value is a
polynomial in `q = cos² φ`, `gateU q m`, and at `q = 1/2` it is `±1`: the envelope is `1/(2m+1)`. -/

/-- Chebyshev polynomials of the second kind at `c`: `U₀ = 1`, `U₁ = 2c`, `U_{n+2} = 2c·U_{n+1} - U_n`. -/
def chebU (c : Rat) : Nat → Rat
  | 0 => 1
  | 1 => 2 * c
  | n + 2 => 2 * c * chebU c (n + 1) - chebU c n

/-- `U_{2m}` as a polynomial in `q = c²`. -/
def gateU (q : Rat) : Nat → Rat
  | 0 => 1
  | 1 => 4 * q - 1
  | m + 2 => (4 * q - 2) * gateU q (m + 1) - gateU q m

theorem chebU_even (c : Rat) : ∀ m : Nat, chebU c (2 * m) = gateU (c * c) m ∧
    chebU c (2 * m + 1) = 2 * c * gateU (c * c) m - chebU c (2 * m - 1) * (if m = 0 then 0 else 1)
  | 0 => by simp [chebU, gateU]; grind
  | 1 => by simp [chebU, gateU]; grind
  | m + 2 => by
    obtain ⟨a1, a2⟩ := chebU_even c (m + 1)
    obtain ⟨b1, b2⟩ := chebU_even c m
    have e1 : 2 * (m + 2) = (2 * (m + 1) + 1) + 1 := by omega
    have e2 : 2 * (m + 2) + 1 = (2 * (m + 1) + 1) + 2 := by omega
    have e3 : 2 * (m + 1) + 1 = 2 * (m + 1) - 1 + 2 := by omega
    have e4 : 2 * (m + 1) = 2 * m + 2 := by omega
    have e5 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have e6 : 2 * (m + 2) - 1 = 2 * (m + 1) + 1 := by omega
    have c1 : chebU c (2 * (m + 2)) = 2 * c * chebU c (2 * (m + 1) + 1) - chebU c (2 * (m + 1)) := by
      rw [e1]; rfl
    have c2 : chebU c (2 * (m + 1) + 1) = 2 * c * chebU c (2 * (m + 1)) - chebU c (2 * m + 1) := by
      rw [e4]; rfl
    have c3 : chebU c (2 * (m + 1)) = 2 * c * chebU c (2 * m + 1) - chebU c (2 * m) := by
      rw [e4]; rfl
    have g : gateU (c * c) (m + 2) = (4 * (c * c) - 2) * gateU (c * c) (m + 1) - gateU (c * c) m := rfl
    refine ⟨?_, ?_⟩
    · rw [c1, g, ← a1, ← b1]; grind
    · rw [e6]
      have hm : ¬ (m + 2 = 0) := by omega
      simp only [hm, ↓reduceIte]
      have : chebU c (2 * (m + 2) + 1) = 2 * c * chebU c (2 * (m + 2)) - chebU c (2 * (m + 1) + 1) := by
        rw [e2]; rfl
      rw [this, c1, g, ← a1, ← b1]; grind

/-- At 25 % duty (`cos² φ = 1/2`) the odd-harmonic factor has period 4 in `m`: `1, 1, -1, -1, …`. -/
theorem gateU_quarter : ∀ m : Nat, gateU (1 / 2) (m + 2) = -gateU (1 / 2) m ∧
    gateU (1 / 2) m * gateU (1 / 2) m = 1
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | m + 2 => by
    obtain ⟨_, h2⟩ := gateU_quarter m
    obtain ⟨_, h3⟩ := gateU_quarter (m + 1)
    have g : gateU (1 / 2) (m + 2 + 2) = (4 * (1 / 2) - 2) * gateU (1 / 2) (m + 2 + 1) - gateU (1 / 2) (m + 2) := rfl
    have g2 : gateU (1 / 2) (m + 2) = (4 * (1 / 2) - 2) * gateU (1 / 2) (m + 1) - gateU (1 / 2) m := rfl
    have z : (4 * (1 / 2) - 2 : Rat) = 0 := by decide +kernel
    rw [z] at g g2
    constructor
    · rw [g]; grind
    · rw [g2]; grind

/-- The Tayloe gate's response to the `(2m+1)`-th LO harmonic, relative to the fundamental. -/
def oddHarmonicGain (m : Nat) : Rat := gateU (1 / 2) m / ((2 * m + 1 : Nat) : Rat)

/-- Its square, the relative alias power. -/
theorem oddHarmonicGain_sq (m : Nat) :
    oddHarmonicGain m * oddHarmonicGain m = 1 / (((2 * m + 1 : Nat) : Rat) * ((2 * m + 1 : Nat) : Rat)) := by
  have h := (gateU_quarter m).2
  have hn : (0 : Rat) < ((2 * m + 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  unfold oddHarmonicGain
  generalize ((2 * m + 1 : Nat) : Rat) = n at *
  generalize gateU (1 / 2) m = u at *
  have hnn : n * n ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hn hn)
  have ex := Rat.div_mul_cancel (a := u) (Rat.ne_of_gt hn)
  have ey := Rat.div_mul_cancel (a := 1) hnn
  generalize u / n = x at *
  generalize 1 / (n * n) = y at *
  have hz : (x * x - y) * (n * n) = 0 := by rw [← ex] at h; grind
  rcases Rat.mul_eq_zero.mp hz with hz | hz
  · grind
  · exact absurd hz hnn

/-- **The odd-harmonic alias envelope.** A signal at the `(2m+1)`-th harmonic of the LO folds to
baseband with amplitude exactly `1/(2m+1)` of the fundamental's (`1/3` at `3·f_LO`, `1/5` at
`5·f_LO`), strictly less with every higher harmonic, while under every drive that repeats after
half a period (the even harmonics and DC) the differential outputs receive nothing. -/
theorem tayloe_odd_harmonic_alias_envelope :
    (∀ m : Nat, oddHarmonicGain m * oddHarmonicGain m
        = 1 / (((2 * m + 1 : Nat) : Rat) * ((2 * m + 1 : Nat) : Rat))) ∧
    (∀ m : Nat, oddHarmonicGain (m + 1) * oddHarmonicGain (m + 1) < oddHarmonicGain m * oddHarmonicGain m) ∧
    oddHarmonicGain 1 = 1 / 3 ∧ oddHarmonicGain 2 = -(1 / 5) ∧
    (∀ (α : Rat) (ws : List TayloeDrive) (v : TayloeState), (∀ w ∈ ws, w.v0 = w.v2 ∧ w.v1 = w.v3) →
      (TayloeState.run α ws v).iOut = α ^ ws.length * v.iOut ∧
      (TayloeState.run α ws v).qOut = α ^ ws.length * v.qOut) := by
  refine ⟨oddHarmonicGain_sq, ?_, by decide +kernel, by decide +kernel,
    fun α ws v h => TayloeState.run_even_harmonic_cancels α ws v h⟩
  intro m
  rw [oddHarmonicGain_sq, oddHarmonicGain_sq]
  have h1 : (0 : Rat) < ((2 * m + 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have h2 : ((2 * m + 1 : Nat) : Rat) < ((2 * (m + 1) + 1 : Nat) : Rat) := Rat.natCast_lt_natCast.mpr (by omega)
  generalize ((2 * m + 1 : Nat) : Rat) = a at *
  generalize ((2 * (m + 1) + 1 : Nat) : Rat) = b at *
  have hb : 0 < b := by grind
  have haa : 0 < a * a := Rat.mul_pos h1 h1
  have hab : a * a < b * b := by
    have x1 := Rat.mul_lt_mul_of_pos_left h2 h1
    have x2 := Rat.mul_lt_mul_of_pos_left h2 hb
    grind
  -- 1/(b·b) < 1/(a·a)
  have hbb : 0 < b * b := Rat.mul_pos hb hb
  have ia : 0 < 1 / (a * a) := by rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr haa
  have ib : 0 < 1 / (b * b) := by rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr hbb
  have ea := Rat.div_mul_cancel (a := 1) (Rat.ne_of_gt haa)
  have eb := Rat.div_mul_cancel (a := 1) (Rat.ne_of_gt hbb)
  generalize 1 / (a * a) = x at *
  generalize 1 / (b * b) = y at *
  by_cases hxy : y < x
  · exact hxy
  · have hle : x ≤ y := by grind
    have m1 := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt haa)
    have m2 := Rat.mul_lt_mul_of_pos_left hab ib
    grind

/-! ## The preselector: a Cauer LC ladder between resistive terminations

At angular frequency `ω` every branch of the ladder is a complex impedance or admittance with
rational real and imaginary parts, so the port phasors are Gaussian rationals and the scattering
parameters' squared magnitudes are rational. A ladder is the list of its branches from the load
towards the source. The elliptic (Cauer) sections are the two traps, whose reactance has a pole at
`ω²·L·C = 1`: their chain relation is kept multiplied through by `δ = 1 - ω²·L·C`, and the port
state carries the accumulated factor `κ`, so the pole is an ordinary point (`κ = 0`, a transmission
zero) instead of a division by zero. -/

/-- A ladder branch. Component values are in Ω, H, S, F. -/
inductive LadderElem where
  /-- series branch `R + jωL` -/
  | seriesRL (r l : Rat)
  /-- shunt branch `G + jωC` -/
  | shuntGC (g c : Rat)
  /-- series branch of `L` and `C` in parallel: impedance `jωL/(1 - ω²LC)` -/
  | seriesTrap (l c : Rat)
  /-- shunt branch of `L` and `C` in series: admittance `jωC/(1 - ω²LC)` -/
  | shuntTrap (l c : Rat)

/-- Voltage and current phasors at a port, each scaled by the real factor `k`. -/
structure PortState where
  vr : Rat
  vi : Rat
  ir : Rat
  ii : Rat
  k : Rat

namespace LadderElem

/-- Every component value is non-negative. -/
def Passive : LadderElem → Prop
  | seriesRL r l => 0 ≤ r ∧ 0 ≤ l
  | shuntGC g c => 0 ≤ g ∧ 0 ≤ c
  | seriesTrap l c => 0 ≤ l ∧ 0 ≤ c
  | shuntTrap l c => 0 ≤ l ∧ 0 ≤ c

/-- No resistance and no conductance: a purely reactive branch. -/
def Lossless : LadderElem → Prop
  | seriesRL r _ => r = 0
  | shuntGC g _ => g = 0
  | seriesTrap _ _ => True
  | shuntTrap _ _ => True

/-- The factor a branch multiplies the port scale by: `1 - ω²LC` for a trap, `1` otherwise. -/
def gain (ω : Rat) : LadderElem → Rat
  | seriesRL _ _ => 1
  | shuntGC _ _ => 1
  | seriesTrap l c => 1 - ω * ω * l * c
  | shuntTrap l c => 1 - ω * ω * l * c

/-- The port on the source side of a branch from the port on its load side (Kirchhoff's laws). -/
def act (ω : Rat) : LadderElem → PortState → PortState
  | seriesRL r l, s =>
    ⟨s.vr + r * s.ir - ω * l * s.ii, s.vi + r * s.ii + ω * l * s.ir, s.ir, s.ii, s.k⟩
  | shuntGC g c, s =>
    ⟨s.vr, s.vi, s.ir + g * s.vr - ω * c * s.vi, s.ii + g * s.vi + ω * c * s.vr, s.k⟩
  | seriesTrap l c, s =>
    ⟨(1 - ω * ω * l * c) * s.vr - ω * l * s.ii, (1 - ω * ω * l * c) * s.vi + ω * l * s.ir,
     (1 - ω * ω * l * c) * s.ir, (1 - ω * ω * l * c) * s.ii, (1 - ω * ω * l * c) * s.k⟩
  | shuntTrap l c, s =>
    ⟨(1 - ω * ω * l * c) * s.vr, (1 - ω * ω * l * c) * s.vi,
     (1 - ω * ω * l * c) * s.ir - ω * c * s.vi, (1 - ω * ω * l * c) * s.ii + ω * c * s.vr,
     (1 - ω * ω * l * c) * s.k⟩

end LadderElem

namespace PortState

/-- The real power flowing through the port towards the load, `Re (V·conj I)`, scaled by `k²`. -/
def power (s : PortState) : Rat := s.vr * s.ir + s.vi * s.ii

end PortState

open LadderElem PortState

theorem act_scale (ω : Rat) (e : LadderElem) (s : PortState) : (e.act ω s).k = e.gain ω * s.k := by
  cases e <;> simp [act, gain]

/-- **A passive branch absorbs power**: what enters on the source side is at least what leaves on
the load side (both in the port's scaled units). -/
theorem act_power_ge (ω : Rat) (e : LadderElem) (s : PortState) (he : e.Passive) :
    e.gain ω * e.gain ω * s.power ≤ (e.act ω s).power := by
  cases e with
  | seriesRL r l =>
    have h := Rat.mul_nonneg he.1 (Rat.add_nonneg (Interval.rat_sq_nonneg s.ir) (Interval.rat_sq_nonneg s.ii))
    simp only [act, gain, power]; grind
  | shuntGC g c =>
    have h := Rat.mul_nonneg he.1 (Rat.add_nonneg (Interval.rat_sq_nonneg s.vr) (Interval.rat_sq_nonneg s.vi))
    simp only [act, gain, power]; grind
  | seriesTrap l c => simp only [act, gain, power]; grind
  | shuntTrap l c => simp only [act, gain, power]; grind

/-- **A reactive branch absorbs none.** -/
theorem act_power_eq (ω : Rat) (e : LadderElem) (s : PortState) (he : e.Lossless) :
    (e.act ω s).power = e.gain ω * e.gain ω * s.power := by
  cases e with
  | seriesRL r l => simp only [Lossless] at he; subst he; simp only [act, gain, power]; grind
  | shuntGC g c => simp only [Lossless] at he; subst he; simp only [act, gain, power]; grind
  | seriesTrap l c => simp only [act, gain, power]; grind
  | shuntTrap l c => simp only [act, gain, power]; grind

/-- The ladder's port on the source side, from the port at the load. -/
def ladderAct (ω : Rat) : List LadderElem → PortState → PortState
  | [], s => s
  | e :: es, s => ladderAct ω es (e.act ω s)

/-- The load end: a resistance `r2` carrying unit current. -/
def loadPort (r2 : Rat) : PortState := ⟨r2, 0, 1, 0, 1⟩

theorem ladder_power_ge (ω r2 : Rat) (hr : 0 ≤ r2) : ∀ (es : List LadderElem) (s : PortState),
    (∀ e ∈ es, e.Passive) → s.k * s.k * r2 ≤ s.power →
    (ladderAct ω es s).k * (ladderAct ω es s).k * r2 ≤ (ladderAct ω es s).power
  | [], _, _, h => h
  | e :: es, s, hp, h => by
    refine ladder_power_ge ω r2 hr es (e.act ω s) (fun e' he' => hp e' (List.mem_cons_of_mem _ he')) ?_
    have h1 := act_power_ge ω e s (hp e (List.mem_cons_self))
    have h2 := Rat.mul_le_mul_of_nonneg_left h (Interval.rat_sq_nonneg (e.gain ω))
    rw [act_scale]; grind

theorem ladder_power_eq (ω r2 : Rat) : ∀ (es : List LadderElem) (s : PortState),
    (∀ e ∈ es, e.Lossless) → s.power = s.k * s.k * r2 →
    (ladderAct ω es s).power = (ladderAct ω es s).k * (ladderAct ω es s).k * r2
  | [], _, _, h => h
  | e :: es, s, hp, h => by
    refine ladder_power_eq ω r2 es (e.act ω s) (fun e' he' => hp e' (List.mem_cons_of_mem _ he')) ?_
    rw [act_power_eq ω e s (hp e (List.mem_cons_self)), act_scale, h]; grind

/-- A branch with zero gain anywhere in the ladder leaves the source port with zero scale. -/
theorem ladder_scale_zero (ω : Rat) : ∀ (es : List LadderElem) (s : PortState),
    (s.k = 0 ∨ ∃ e ∈ es, e.gain ω = 0) → (ladderAct ω es s).k = 0
  | [], s, h => by
    rcases h with h | ⟨e, he, _⟩
    · exact h
    · cases he
  | e :: es, s, h => by
    refine ladder_scale_zero ω es (e.act ω s) ?_
    rw [act_scale]
    rcases h with h | ⟨e', he', hg⟩
    · left; rw [h]; grind
    · rcases List.mem_cons.mp he' with he' | he'
      · left; subst he'; rw [hg]; grind
      · right; exact ⟨e', he', hg⟩

/-- `|V + r1·I|²` at the source port: the squared magnitude of the common denominator of the
scattering parameters. -/
def denSq (ω r1 r2 : Rat) (es : List LadderElem) : Rat :=
  let s := ladderAct ω es (loadPort r2)
  (s.vr + r1 * s.ir) * (s.vr + r1 * s.ir) + (s.vi + r1 * s.ii) * (s.vi + r1 * s.ii)

/-- `|S₁₁|²`, the reflected fraction of the available power: `|V - r1·I|² / |V + r1·I|²`. -/
def s11Sq (ω r1 r2 : Rat) (es : List LadderElem) : Rat :=
  let s := ladderAct ω es (loadPort r2)
  ((s.vr - r1 * s.ir) * (s.vr - r1 * s.ir) + (s.vi - r1 * s.ii) * (s.vi - r1 * s.ii)) / denSq ω r1 r2 es

/-- `|S₂₁|²`, the transmitted fraction: `4·r1·r2·κ² / |V + r1·I|²`. -/
def s21Sq (ω r1 r2 : Rat) (es : List LadderElem) : Rat :=
  let s := ladderAct ω es (loadPort r2)
  4 * r1 * r2 * (s.k * s.k) / denSq ω r1 r2 es

theorem div_nonneg_of_nonneg (a d : Rat) (ha : 0 ≤ a) (hd : 0 ≤ d) : 0 ≤ a / d := by
  by_cases h0 : d = 0
  · subst h0; rw [Rat.div_def]; simp
  · exact rat_div_nonneg ha (by grind)

theorem div_add_div_le_one (a b d : Rat) (hd : 0 ≤ d) (h : a + b ≤ d) :
    a / d + b / d ≤ 1 := by
  by_cases h0 : d = 0
  · subst h0; rw [Rat.div_def, Rat.div_def]; simp; grind
  · have hd' : 0 < d := by grind
    have e1 := Rat.div_mul_cancel (a := a) h0
    have e2 := Rat.div_mul_cancel (a := b) h0
    generalize a / d = x at *
    generalize b / d = y at *
    by_cases hxy : x + y ≤ 1
    · exact hxy
    · have := Rat.mul_lt_mul_of_pos_right (by grind : 1 < x + y) hd'
      grind

/-- **Scattering passivity of the ladder.** Between a source resistance `r1` and a load `r2`, at
every frequency, a ladder of non-negative components reflects and transmits at most the available
power, `|S₁₁|² + |S₂₁|² ≤ 1`; a purely reactive ladder reflects exactly what it does not transmit,
`|S₁₁|² + |S₂₁|² = 1` (wherever the source port is not degenerate, `|V + r1·I|² ≠ 0`). -/
theorem cauer_lc_ladder_scattering_passive (ω r1 r2 : Rat) (es : List LadderElem)
    (h1 : 0 < r1) (h2 : 0 < r2) :
    ((∀ e ∈ es, e.Passive) → s11Sq ω r1 r2 es + s21Sq ω r1 r2 es ≤ 1) ∧
    ((∀ e ∈ es, e.Lossless) → denSq ω r1 r2 es ≠ 0 → s11Sq ω r1 r2 es + s21Sq ω r1 r2 es = 1) := by
  have key : ∀ s : PortState,
      (s.vr + r1 * s.ir) * (s.vr + r1 * s.ir) + (s.vi + r1 * s.ii) * (s.vi + r1 * s.ii)
        = (s.vr - r1 * s.ir) * (s.vr - r1 * s.ir) + (s.vi - r1 * s.ii) * (s.vi - r1 * s.ii)
          + 4 * r1 * s.power := by
    intro s; simp only [power]; grind
  constructor
  · intro hp
    have hpow := ladder_power_ge ω r2 (Rat.le_of_lt h2) es (loadPort r2) hp (by simp [loadPort, power]; grind)
    have hk := key (ladderAct ω es (loadPort r2))
    simp only [s11Sq, s21Sq, denSq]
    generalize ladderAct ω es (loadPort r2) = s at *
    have n0 := Rat.add_nonneg (Interval.rat_sq_nonneg (s.vr - r1 * s.ir)) (Interval.rat_sq_nonneg (s.vi - r1 * s.ii))
    have d0 := Rat.add_nonneg (Interval.rat_sq_nonneg (s.vr + r1 * s.ir)) (Interval.rat_sq_nonneg (s.vi + r1 * s.ii))
    have t0 : 0 ≤ 4 * r1 * r2 * (s.k * s.k) :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt h1)) (Rat.le_of_lt h2))
        (Interval.rat_sq_nonneg s.k)
    have m := Rat.mul_le_mul_of_nonneg_left hpow (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 4) (Rat.le_of_lt h1))
    exact div_add_div_le_one _ _ _ d0 (by grind)
  · intro hl hd
    have hpow := ladder_power_eq ω r2 es (loadPort r2) hl (by simp [loadPort, power]; grind)
    have hk := key (ladderAct ω es (loadPort r2))
    simp only [s11Sq, s21Sq, denSq] at hd ⊢
    generalize ladderAct ω es (loadPort r2) = s at *
    have e1 := Rat.div_mul_cancel
      (a := (s.vr - r1 * s.ir) * (s.vr - r1 * s.ir) + (s.vi - r1 * s.ii) * (s.vi - r1 * s.ii)) hd
    have e2 := Rat.div_mul_cancel (a := 4 * r1 * r2 * (s.k * s.k)) hd
    generalize ((s.vr - r1 * s.ir) * (s.vr - r1 * s.ir) + (s.vi - r1 * s.ii) * (s.vi - r1 * s.ii)) /
      ((s.vr + r1 * s.ir) * (s.vr + r1 * s.ir) + (s.vi + r1 * s.ii) * (s.vi + r1 * s.ii)) = x at *
    generalize 4 * r1 * r2 * (s.k * s.k) /
      ((s.vr + r1 * s.ir) * (s.vr + r1 * s.ir) + (s.vi + r1 * s.ii) * (s.vi + r1 * s.ii)) = y at *
    generalize hD : (s.vr + r1 * s.ir) * (s.vr + r1 * s.ir) + (s.vi + r1 * s.ii) * (s.vi + r1 * s.ii) = D at *
    have hz : (x + y - 1) * D = 0 := by grind
    rcases Rat.mul_eq_zero.mp hz with hz | hz
    · grind
    · exact absurd hz hd

/-- A trap tuned to `ω` is a transmission zero: nothing reaches the load. -/
theorem s21Sq_trap_zero (ω r1 r2 : Rat) (es : List LadderElem) (h : ∃ e ∈ es, e.gain ω = 0) :
    s21Sq ω r1 r2 es = 0 := by
  have hk := ladder_scale_zero ω es (loadPort r2) (Or.inr h)
  simp only [s21Sq, hk]; rw [Rat.div_def]; simp

theorem s21Sq_le_one (ω r1 r2 : Rat) (es : List LadderElem) (h1 : 0 < r1) (h2 : 0 < r2)
    (hp : ∀ e ∈ es, e.Passive) : 0 ≤ s21Sq ω r1 r2 es ∧ s21Sq ω r1 r2 es ≤ 1 := by
  have h := (cauer_lc_ladder_scattering_passive ω r1 r2 es h1 h2).1 hp
  have d0 : 0 ≤ denSq ω r1 r2 es := by
    simp only [denSq]; exact Rat.add_nonneg (Interval.rat_sq_nonneg _) (Interval.rat_sq_nonneg _)
  have a0 : 0 ≤ s11Sq ω r1 r2 es := by
    simp only [s11Sq]
    exact div_nonneg_of_nonneg _ _ (Rat.add_nonneg (Interval.rat_sq_nonneg _) (Interval.rat_sq_nonneg _)) d0
  have b0 : 0 ≤ s21Sq ω r1 r2 es := by
    simp only [s21Sq]
    exact div_nonneg_of_nonneg _ _ (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt h1))
      (Rat.le_of_lt h2)) (Interval.rat_sq_nonneg _)) d0
  exact ⟨b0, by grind⟩

/-- The power an interferer at the `(2m+1)`-th LO harmonic delivers to the baseband output through
the preselector and the detector, relative to an equal signal at the fundamental through an ideal
preselector. `ω` is the LO's angular frequency. -/
def compositeAliasPower (ω r1 r2 : Rat) (es : List LadderElem) (m : Nat) : Rat :=
  s21Sq (((2 * m + 1 : Nat) : Rat) * ω) r1 r2 es * (oddHarmonicGain m * oddHarmonicGain m)

/-- **Preselector and detector together.** Any passive ladder leaves the detector's `1/(2m+1)²`
alias power or less, and a trap tuned to the `(2m+1)`-th harmonic removes that alias entirely. -/
theorem tayloe_cauer_composite_alias_bound (ω r1 r2 : Rat) (es : List LadderElem) (m : Nat)
    (h1 : 0 < r1) (h2 : 0 < r2) (hp : ∀ e ∈ es, e.Passive) :
    compositeAliasPower ω r1 r2 es m ≤ 1 / (((2 * m + 1 : Nat) : Rat) * ((2 * m + 1 : Nat) : Rat)) ∧
    ((∃ e ∈ es, e.gain (((2 * m + 1 : Nat) : Rat) * ω) = 0) → compositeAliasPower ω r1 r2 es m = 0) := by
  have hs := s21Sq_le_one (((2 * m + 1 : Nat) : Rat) * ω) r1 r2 es h1 h2 hp
  have hg := oddHarmonicGain_sq m
  have hn : (0 : Rat) < ((2 * m + 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have hpos : 0 ≤ 1 / (((2 * m + 1 : Nat) : Rat) * ((2 * m + 1 : Nat) : Rat)) :=
    rat_div_nonneg (by decide) (Rat.mul_pos hn hn)
  unfold compositeAliasPower
  constructor
  · rw [hg]
    have := Rat.mul_le_mul_of_nonneg_right hs.2 hpos
    grind
  · intro ht
    rw [s21Sq_trap_zero _ r1 r2 es ht]; grind

/-! ## The vectoring CORDIC -/

/-- `atan(2^-i)` in µrad, `i = 0..11`: the angle table of the discriminator's CORDIC. -/
@[expose] def cordicLutUrad : List Int :=
  [785398, 463648, 244979, 124355, 62419, 31240, 15624, 7812, 3906, 1953, 977, 488]

/-- `π` in µrad, as the quadrant fold adds it. -/
@[expose] def cordicPiUrad : Int := 3141593

/-- The vectoring iteration from stage `i` over the remaining angle table: each stage turns the
vector towards the positive real axis by `atan(2^-i)` (arithmetic shifts, so floor division) and
accumulates the angle it turned by. -/
@[expose] def cordicIter : Nat → List Int → Int → Int → Int → Int × Int × Int
  | _, [], x, y, z => (x, y, z)
  | i, a :: as, x, y, z =>
    if y < 0 then cordicIter (i + 1) as (x - y / 2 ^ i) (y + x / 2 ^ i) (z - a)
    else cordicIter (i + 1) as (x + y / 2 ^ i) (y - x / 2 ^ i) (z + a)

/-- The quadrant fold: a vector in the left half plane is negated and the angle starts at `±π`. -/
@[expose] def cordicFold (x y : Int) : Int × Int × Int :=
  if x < 0 then (-x, -y, if y < 0 then -cordicPiUrad else cordicPiUrad) else (x, y, 0)

/-- The angle of `x + j·y` in µrad as the 12-stage integer CORDIC computes it. -/
@[expose] def cordicAtan2 (x y : Int) : Int :=
  (cordicIter 0 cordicLutUrad (cordicFold x y).1 (cordicFold x y).2.1 (cordicFold x y).2.2).2.2

/-- The exact rotation the run performs: the Gaussian integer `∏ (2^i + σ_i·j)` over the stages,
`σ_i` the direction stage `i` turned. Its argument is `Σ σ_i·atan(2^-i)`. -/
def cordicGauss : Nat → List Int → Int → Int → Int × Int
  | _, [], _, _ => (1, 0)
  | i, _ :: as, x, y =>
    if y < 0 then
      ((2 : Int) ^ i * (cordicGauss (i + 1) as (x - y / 2 ^ i) (y + x / 2 ^ i)).1
          + (cordicGauss (i + 1) as (x - y / 2 ^ i) (y + x / 2 ^ i)).2,
       (2 : Int) ^ i * (cordicGauss (i + 1) as (x - y / 2 ^ i) (y + x / 2 ^ i)).2
          - (cordicGauss (i + 1) as (x - y / 2 ^ i) (y + x / 2 ^ i)).1)
    else
      ((2 : Int) ^ i * (cordicGauss (i + 1) as (x + y / 2 ^ i) (y - x / 2 ^ i)).1
          - (cordicGauss (i + 1) as (x + y / 2 ^ i) (y - x / 2 ^ i)).2,
       (2 : Int) ^ i * (cordicGauss (i + 1) as (x + y / 2 ^ i) (y - x / 2 ^ i)).2
          + (cordicGauss (i + 1) as (x + y / 2 ^ i) (y - x / 2 ^ i)).1)

/-- The scale of the run, `∏ 2^i`. -/
def cordicScale : Nat → List Int → Int
  | _, [] => 1
  | i, _ :: as => 2 ^ i * cordicScale (i + 1) as

/-- Bounds on the real and imaginary parts of `cordicGauss`, whatever the directions. -/
def cordicGaussBound : Nat → List Int → Int × Int
  | _, [] => (1, 0)
  | i, _ :: as =>
    (2 ^ i * (cordicGaussBound (i + 1) as).1 + (cordicGaussBound (i + 1) as).2,
     2 ^ i * (cordicGaussBound (i + 1) as).2 + (cordicGaussBound (i + 1) as).1)

/-- The accumulated truncation error of the run, in units of the final scale: each stage drops
less than one unit from each coordinate, and the later stages rotate and scale what it dropped. -/
def cordicErrBound : Nat → List Int → Int
  | _, [] => 0
  | i, _ :: as =>
    2 ^ i * cordicErrBound (i + 1) as
      + (2 ^ i - 1) * ((cordicGaussBound (i + 1) as).1 + (cordicGaussBound (i + 1) as).2)

/-- The slack of the convergence invariant `2^i·|y| ≤ 2·x + S` after the run. -/
def cordicSlack : Nat → List Int → Int → Int
  | _, [], S => S
  | i, _ :: as, S => cordicSlack (i + 1) as (2 * S + 2 * 2 ^ i - 2)

theorem two_pow_pos (i : Nat) : (0 : Int) < 2 ^ i := Int.pow_pos (by decide)

/-- Floor division by a positive `d`: the remainder is in `0 .. d - 1`. -/
theorem ediv_bounds (a d : Int) (hd : 0 < d) : d * (a / d) ≤ a ∧ a ≤ d * (a / d) + d - 1 := by
  have h1 := Int.emod_nonneg a (Int.ne_of_gt hd)
  have h2 := Int.emod_lt_of_pos a hd
  have h3 := Int.emod_def a d
  omega

theorem ediv_nonpos (a d : Int) (ha : a ≤ 0) (hd : 0 < d) : a / d ≤ 0 := by
  have h := ediv_bounds a d hd
  by_cases hq : 0 < a / d
  · have : d * 1 ≤ d * (a / d) := Int.mul_le_mul_of_nonneg_left hq (Int.le_of_lt hd)
    omega
  · omega

/-- `0 ≤ r ≤ e` and `|g| ≤ G` give `|r·g| ≤ e·G`. -/
theorem mul_bound (r e g G : Int) (h0 : 0 ≤ r) (h1 : r ≤ e) (hg1 : -G ≤ g) (hg2 : g ≤ G) :
    -(e * G) ≤ r * g ∧ r * g ≤ e * G := by
  have hG : 0 ≤ G := by omega
  have a1 : r * g ≤ r * G := Int.mul_le_mul_of_nonneg_left hg2 h0
  have a2 : r * (-G) ≤ r * g := Int.mul_le_mul_of_nonneg_left hg1 h0
  have a3 : r * G ≤ e * G := Int.mul_le_mul_of_nonneg_right h1 hG
  have a4 : r * (-G) = -(r * G) := Int.mul_neg r G
  omega

theorem cordicGaussBound_nonneg (as : List Int) : ∀ i : Nat,
    0 ≤ (cordicGaussBound i as).1 ∧ 0 ≤ (cordicGaussBound i as).2 := by
  induction as with
  | nil => intro i; simp [cordicGaussBound]
  | cons a as ih =>
    intro i
    have h := ih (i + 1)
    have hd := two_pow_pos i
    simp only [cordicGaussBound]
    have p1 := Int.mul_nonneg (Int.le_of_lt hd) h.1
    have p2 := Int.mul_nonneg (Int.le_of_lt hd) h.2
    omega

/-- The rotation's real and imaginary parts are within `cordicGaussBound`. -/
theorem cordicGauss_bound (as : List Int) : ∀ (i : Nat) (x y : Int),
    -(cordicGaussBound i as).1 ≤ (cordicGauss i as x y).1 ∧
    (cordicGauss i as x y).1 ≤ (cordicGaussBound i as).1 ∧
    -(cordicGaussBound i as).2 ≤ (cordicGauss i as x y).2 ∧
    (cordicGauss i as x y).2 ≤ (cordicGaussBound i as).2 := by
  induction as with
  | nil => intro i x y; simp [cordicGauss, cordicGaussBound]
  | cons a as ih =>
    intro i x y
    have hd := two_pow_pos i
    simp only [cordicGauss, cordicGaussBound]
    split
    · obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (x - y / 2 ^ i) (y + x / 2 ^ i)
      have m1 := Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt hd)
      have m2 := Int.mul_le_mul_of_nonneg_left h2 (Int.le_of_lt hd)
      have m3 := Int.mul_le_mul_of_nonneg_left h3 (Int.le_of_lt hd)
      have m4 := Int.mul_le_mul_of_nonneg_left h4 (Int.le_of_lt hd)
      rw [Int.mul_neg] at m1 m3
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (x + y / 2 ^ i) (y - x / 2 ^ i)
      have m1 := Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt hd)
      have m2 := Int.mul_le_mul_of_nonneg_left h2 (Int.le_of_lt hd)
      have m3 := Int.mul_le_mul_of_nonneg_left h3 (Int.le_of_lt hd)
      have m4 := Int.mul_le_mul_of_nonneg_left h4 (Int.le_of_lt hd)
      rw [Int.mul_neg] at m1 m3
      omega

/-- One stage of the convergence invariant, both directions at once: `yh` is `|y|`'s successor
`|y| - ⌊x/d⌋` up to sign, `x1 ≥ x`. -/
theorem stage_invariant (d x S Y qx x1 : Int) (hd : 0 < d) (hY : 0 ≤ Y) (hinv : d * Y ≤ 2 * x + S)
    (hS : 0 ≤ S) (hq1 : d * qx ≤ x) (hq2 : x ≤ d * qx + d - 1) (hx1 : x ≤ x1) :
    2 * d * (Y - qx) ≤ 2 * x1 + (2 * S + 2 * d - 2) ∧
    -(2 * d * (Y - qx)) ≤ 2 * x1 + (2 * S + 2 * d - 2) := by
  have e : 2 * d * (Y - qx) = 2 * (d * Y) - 2 * (d * qx) := by grind
  have hdY : 0 ≤ d * Y := Int.mul_nonneg (Int.le_of_lt hd) hY
  rw [e]
  omega

/-- A stage's contribution to the truncation error: `d` times the error of the later stages plus
the two products of this stage's remainders with the later rotation. -/
theorem err_combine (d u B1 t1 t2 E1 E2 : Int) (hd : 0 < d) (hu1 : -B1 ≤ u) (hu2 : u ≤ B1)
    (h1 : -E1 ≤ t1 ∧ t1 ≤ E1) (h2 : -E2 ≤ t2 ∧ t2 ≤ E2) :
    -(d * B1 + (E1 + E2)) ≤ d * u + t1 + t2 ∧ d * u + t1 + t2 ≤ d * B1 + (E1 + E2) := by
  have a1 := Int.mul_le_mul_of_nonneg_left hu1 (Int.le_of_lt hd)
  have a2 := Int.mul_le_mul_of_nonneg_left hu2 (Int.le_of_lt hd)
  rw [Int.mul_neg] at a1
  omega

/-- **The run against its exact rotation.** From a state with `2^i·|y| ≤ 2·x + S`, the run over the
remaining stages ends in `(x', y')` with `x ≤ x'` and `2^(i+n)·|y'| ≤ 2·x' + cordicSlack`, and the
start vector turned back by the exact rotation `cordicGauss` (`w = (x + j·y)·conj g`) is
`cordicScale·(x' + j·y')` up to `cordicErrBound` in each coordinate. -/
theorem cordicIter_residual (as : List Int) : ∀ (i : Nat) (x y z S : Int),
    0 ≤ x → 0 ≤ S → 2 ^ i * y ≤ 2 * x + S → -(2 ^ i * y) ≤ 2 * x + S →
    x ≤ (cordicIter i as x y z).1 ∧
    2 ^ (i + as.length) * (cordicIter i as x y z).2.1
      ≤ 2 * (cordicIter i as x y z).1 + cordicSlack i as S ∧
    -(2 ^ (i + as.length) * (cordicIter i as x y z).2.1)
      ≤ 2 * (cordicIter i as x y z).1 + cordicSlack i as S ∧
    -(cordicErrBound i as) ≤ (x * (cordicGauss i as x y).1 + y * (cordicGauss i as x y).2)
      - cordicScale i as * (cordicIter i as x y z).1 ∧
    (x * (cordicGauss i as x y).1 + y * (cordicGauss i as x y).2)
      - cordicScale i as * (cordicIter i as x y z).1 ≤ cordicErrBound i as ∧
    -(cordicErrBound i as) ≤ (y * (cordicGauss i as x y).1 - x * (cordicGauss i as x y).2)
      - cordicScale i as * (cordicIter i as x y z).2.1 ∧
    (y * (cordicGauss i as x y).1 - x * (cordicGauss i as x y).2)
      - cordicScale i as * (cordicIter i as x y z).2.1 ≤ cordicErrBound i as := by
  induction as with
  | nil =>
    intro i x y z S hx hS h1 h2
    simp only [cordicIter, cordicGauss, cordicScale, cordicErrBound, cordicSlack, List.length_nil,
      Nat.add_zero]
    refine ⟨Int.le_refl _, h1, h2, ?_, ?_, ?_, ?_⟩ <;> omega
  | cons a as ih =>
    intro i x y z S hx hS hinv1 hinv2
    have hd := two_pow_pos i
    have el : i + (a :: as).length = i + 1 + as.length := by simp only [List.length_cons]; omega
    have ep : (2 : Int) ^ (i + 1) = 2 * 2 ^ i := by rw [Int.pow_succ]; omega
    obtain ⟨hG1, hG2, hG3, hG4⟩ := cordicGauss_bound as (i + 1)
      (if y < 0 then x - y / 2 ^ i else x + y / 2 ^ i) (if y < 0 then y + x / 2 ^ i else y - x / 2 ^ i)
    have hqx := ediv_bounds x (2 ^ i) hd
    have hqy := ediv_bounds y (2 ^ i) hd
    rw [el]
    simp only [cordicIter, cordicGauss, cordicScale, cordicErrBound, cordicSlack]
    by_cases hy : y < 0
    · simp only [hy, ↓reduceIte] at hG1 hG2 hG3 hG4 ⊢
      have hqy0 : y / 2 ^ i ≤ 0 := ediv_nonpos y _ (Int.le_of_lt hy) hd
      generalize x / 2 ^ i = qx at *
      generalize y / 2 ^ i = qy at *
      generalize (2 : Int) ^ i = d at *
      have hsi := stage_invariant d x S (-y) qx (x - qy) hd (by omega)
        (by rw [Int.mul_neg]; exact hinv2) hS hqx.1 hqx.2 (by omega)
      have e2 : 2 * d * (-y - qx) = -(2 * d * (y + qx)) := by grind
      rw [e2] at hsi
      obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := ih (i + 1) (x - qy) (y + qx) (z - a) (2 * S + 2 * d - 2)
        (by omega) (by omega) (by rw [ep]; omega) (by rw [ep]; omega)
      generalize (cordicIter (i + 1) as (x - qy) (y + qx) (z - a)).1 = X' at *; generalize (cordicIter (i + 1) as (x - qy) (y + qx) (z - a)).2.1 = Y' at *
      generalize (cordicGauss (i + 1) as (x - qy) (y + qx)).1 = gr at *; generalize (cordicGauss (i + 1) as (x - qy) (y + qx)).2 = gi at *
      generalize cordicScale (i + 1) as = P1 at *; generalize cordicErrBound (i + 1) as = B1 at *
      generalize (cordicGaussBound (i + 1) as).1 = Gr at *; generalize (cordicGaussBound (i + 1) as).2 = Gi at *
      have mry_r := mul_bound (y - d * qy) (d - 1) gr Gr (by omega) (by omega) hG1 hG2
      have mrx_i := mul_bound (x - d * qx) (d - 1) gi Gi (by omega) (by omega) hG3 hG4
      have mrx_r := mul_bound (x - d * qx) (d - 1) gr Gr (by omega) (by omega) hG1 hG2
      have mry_i := mul_bound (y - d * qy) (d - 1) gi Gi (by omega) (by omega) hG3 hG4
      have hdist : (d - 1) * (Gr + Gi) = (d - 1) * Gr + (d - 1) * Gi := Int.mul_add _ _ _
      have id1 : x * (d * gr + gi) + y * (d * gi - gr) - d * P1 * X'
          = d * ((x - qy) * gr + (y + qx) * gi - P1 * X') + (-((y - d * qy) * gr)) + (x - d * qx) * gi := by
        grind
      have id2 : y * (d * gr + gi) - x * (d * gi - gr) - d * P1 * Y'
          = d * ((y + qx) * gr - (x - qy) * gi - P1 * Y') + (x - d * qx) * gr + (y - d * qy) * gi := by
        grind
      have c1 := err_combine d _ B1 (-((y - d * qy) * gr)) ((x - d * qx) * gi) ((d - 1) * Gr)
        ((d - 1) * Gi) hd k4 k5 ⟨by omega, by omega⟩ mrx_i
      have c2 := err_combine d _ B1 ((x - d * qx) * gr) ((y - d * qy) * gi) _ _ hd k6 k7 mrx_r mry_i
      rw [id1, id2, hdist]
      refine ⟨by omega, k2, k3, c1.1, c1.2, c2.1, c2.2⟩
    · simp only [hy, ↓reduceIte] at hG1 hG2 hG3 hG4 ⊢
      have hy0 : 0 ≤ y := by omega
      have hqy0 : 0 ≤ y / 2 ^ i := Int.ediv_nonneg hy0 (Int.le_of_lt hd)
      generalize x / 2 ^ i = qx at *
      generalize y / 2 ^ i = qy at *
      generalize (2 : Int) ^ i = d at *
      have hsi := stage_invariant d x S y qx (x + qy) hd hy0 hinv1 hS hqx.1 hqx.2 (by omega)
      obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := ih (i + 1) (x + qy) (y - qx) (z + a) (2 * S + 2 * d - 2)
        (by omega) (by omega) (by rw [ep]; omega) (by rw [ep]; omega)
      generalize (cordicIter (i + 1) as (x + qy) (y - qx) (z + a)).1 = X' at *; generalize (cordicIter (i + 1) as (x + qy) (y - qx) (z + a)).2.1 = Y' at *
      generalize (cordicGauss (i + 1) as (x + qy) (y - qx)).1 = gr at *; generalize (cordicGauss (i + 1) as (x + qy) (y - qx)).2 = gi at *
      generalize cordicScale (i + 1) as = P1 at *; generalize cordicErrBound (i + 1) as = B1 at *
      generalize (cordicGaussBound (i + 1) as).1 = Gr at *; generalize (cordicGaussBound (i + 1) as).2 = Gi at *
      have mry_r := mul_bound (y - d * qy) (d - 1) gr Gr (by omega) (by omega) hG1 hG2
      have mrx_i := mul_bound (x - d * qx) (d - 1) gi Gi (by omega) (by omega) hG3 hG4
      have mrx_r := mul_bound (x - d * qx) (d - 1) gr Gr (by omega) (by omega) hG1 hG2
      have mry_i := mul_bound (y - d * qy) (d - 1) gi Gi (by omega) (by omega) hG3 hG4
      have hdist : (d - 1) * (Gr + Gi) = (d - 1) * Gr + (d - 1) * Gi := Int.mul_add _ _ _
      have id1 : x * (d * gr - gi) + y * (d * gi + gr) - d * P1 * X'
          = d * ((x + qy) * gr + (y - qx) * gi - P1 * X') + (y - d * qy) * gr + (-((x - d * qx) * gi)) := by
        grind
      have id2 : y * (d * gr - gi) - x * (d * gi + gr) - d * P1 * Y'
          = d * ((y - qx) * gr - (x + qy) * gi - P1 * Y') + (-((x - d * qx) * gr)) + (-((y - d * qy) * gi)) := by
        grind
      have c1 := err_combine d _ B1 ((y - d * qy) * gr) (-((x - d * qx) * gi)) ((d - 1) * Gr)
        ((d - 1) * Gi) hd k4 k5 mry_r ⟨by omega, by omega⟩
      have c2 := err_combine d _ B1 (-((x - d * qx) * gr)) (-((y - d * qy) * gi)) ((d - 1) * Gr)
        ((d - 1) * Gi) hd k6 k7 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      rw [id1, id2, hdist]
      refine ⟨by omega, k2, k3, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ### The folded run: stage 0 is exact, stages 1..11 are the residual theorem -/

theorem cordicIter_stage0 (a : Int) (as : List Int) (x y z : Int) :
    cordicIter 0 (a :: as) x y z =
      if y < 0 then cordicIter 1 as (x - y) (y + x) (z - a) else cordicIter 1 as (x + y) (y - x) (z + a) := by
  rw [cordicIter]; simp only [Int.pow_zero, Int.ediv_one, Nat.zero_add]

theorem cordicGauss_stage0 (a : Int) (as : List Int) (x y : Int) :
    cordicGauss 0 (a :: as) x y =
      if y < 0 then
        ((cordicGauss 1 as (x - y) (y + x)).1 + (cordicGauss 1 as (x - y) (y + x)).2,
         (cordicGauss 1 as (x - y) (y + x)).2 - (cordicGauss 1 as (x - y) (y + x)).1)
      else
        ((cordicGauss 1 as (x + y) (y - x)).1 - (cordicGauss 1 as (x + y) (y - x)).2,
         (cordicGauss 1 as (x + y) (y - x)).2 + (cordicGauss 1 as (x + y) (y - x)).1) := by
  rw [cordicGauss]; simp only [Int.pow_zero, Int.ediv_one, Int.one_mul, Nat.zero_add]

/-- Stages `1..11` of the angle table. -/
def cordicLutTail : List Int := [463648, 244979, 124355, 62419, 31240, 15624, 7812, 3906, 1953, 977, 488]

/-- The folded input turned back by the run's exact rotation: `(x + j·y)·conj (cordicGauss …)`. -/
def cordicBack (x y : Int) : Int × Int :=
  (x * (cordicGauss 0 cordicLutUrad x y).1 + y * (cordicGauss 0 cordicLutUrad x y).2,
   y * (cordicGauss 0 cordicLutUrad x y).1 - x * (cordicGauss 0 cordicLutUrad x y).2)

/-- **CORDIC convergence, with the truncation of every shift.** For a vector in the closed right
half plane with `|x| + |y| ≥ 2^13`, the run's sign choices `σ` define the exact rotation
`g = ∏ (2^i + σ_i·j)`, and the input turned back by it lies within `atan (303/100000)` (under
3030 µrad) of the positive real axis. So the direction of the input is the direction of `g` up to
that cone: no transcendental function appears, only the run's own rational rotation. -/
theorem cordic_residual_cone (x y : Int) (hx : 0 ≤ x) (hR : 8192 ≤ x.natAbs + y.natAbs) :
    0 < (cordicBack x y).1 ∧
    100000 * (cordicBack x y).2 ≤ 303 * (cordicBack x y).1 ∧
    -(100000 * (cordicBack x y).2) ≤ 303 * (cordicBack x y).1 := by
  have hP : cordicScale 1 cordicLutTail = 73786976294838206464 := by decide
  have hB : cordicErrBound 1 cordicLutTail = 791635260843988926635 := by decide
  have hS : cordicSlack 1 cordicLutTail 0 = 40962 := by decide
  have hpow : (2 : Int) ^ (1 + cordicLutTail.length) = 4096 := by decide
  have hl : cordicLutUrad = 785398 :: cordicLutTail := rfl
  simp only [cordicBack, hl, cordicGauss_stage0]
  by_cases hy : y < 0
  · simp only [hy, ↓reduceIte]
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := cordicIter_residual cordicLutTail 1 (x - y) (y + x) 0 0
      (by omega) (by omega) (by omega) (by omega)
    rw [hP, hB] at k4 k5 k6 k7
    rw [hS, hpow] at k2 k3
    generalize (cordicIter 1 _ (x - y) (y + x) 0).1 = X' at *; generalize (cordicIter 1 _ (x - y) (y + x) 0).2.1 = Y' at *
    generalize (cordicGauss 1 _ (x - y) (y + x)).1 = gr at *; generalize (cordicGauss 1 _ (x - y) (y + x)).2 = gi at *
    have e1 : x * (gr + gi) + y * (gi - gr) = (x - y) * gr + (y + x) * gi := by grind
    have e2 : y * (gr + gi) - x * (gi - gr) = (y + x) * gr - (x - y) * gi := by grind
    rw [e1, e2]
    omega
  · simp only [hy, ↓reduceIte]
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := cordicIter_residual cordicLutTail 1 (x + y) (y - x) 0 0
      (by omega) (by omega) (by omega) (by omega)
    rw [hP, hB] at k4 k5 k6 k7
    rw [hS, hpow] at k2 k3
    generalize (cordicIter 1 _ (x + y) (y - x) 0).1 = X' at *; generalize (cordicIter 1 _ (x + y) (y - x) 0).2.1 = Y' at *
    generalize (cordicGauss 1 _ (x + y) (y - x)).1 = gr at *; generalize (cordicGauss 1 _ (x + y) (y - x)).2 = gi at *
    have e1 : x * (gr - gi) + y * (gi + gr) = (x + y) * gr + (y - x) * gi := by grind
    have e2 : y * (gr - gi) - x * (gi + gr) = (y - x) * gr - (x + y) * gi := by grind
    rw [e1, e2]
    omega

/-! ### The angle output as a function of the sign choices -/

theorem cordicIter_z (as : List Int) : ∀ (i : Nat) (x y z : Int),
    (cordicIter i as x y z).2.2 = z + (cordicIter i as x y 0).2.2 := by
  induction as with
  | nil => intro i x y z; simp [cordicIter]
  | cons a as ih =>
    intro i x y z
    simp only [cordicIter]
    split
    · rw [ih (i + 1) _ _ (z - a), ih (i + 1) _ _ (0 - a)]; omega
    · rw [ih (i + 1) _ _ (z + a), ih (i + 1) _ _ (0 + a)]; omega

/-- Both directions of one stage, for every leaf of the later stages. -/
@[expose] def cordicLeavesStep (d a : Int) : List ((Int × Int) × Int) → List ((Int × Int) × Int)
  | [] => []
  | l :: ls =>
    ((d * l.1.1 - l.1.2, d * l.1.2 + l.1.1), l.2 + a) ::
    ((d * l.1.1 + l.1.2, d * l.1.2 - l.1.1), l.2 - a) :: cordicLeavesStep d a ls

/-- Every sign choice of the stages: the rotation `∏ (2^i + σ_i·j)` with the angle `Σ σ_i·a_i`
the run would report for it. -/
@[expose] def cordicLeaves : Nat → List Int → List ((Int × Int) × Int)
  | _, [] => [((1, 0), 0)]
  | i, a :: as => cordicLeavesStep (2 ^ i) a (cordicLeaves (i + 1) as)

theorem mem_cordicLeavesStep (d a : Int) (l : (Int × Int) × Int) :
    ∀ ls : List ((Int × Int) × Int), l ∈ ls →
      ((d * l.1.1 - l.1.2, d * l.1.2 + l.1.1), l.2 + a) ∈ cordicLeavesStep d a ls ∧
      ((d * l.1.1 + l.1.2, d * l.1.2 - l.1.1), l.2 - a) ∈ cordicLeavesStep d a ls := by
  intro ls
  induction ls with
  | nil => intro h; cases h
  | cons m ms ih =>
    intro h
    simp only [cordicLeavesStep, List.mem_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨Or.inr (Or.inr (ih h).1), Or.inr (Or.inr (ih h).2)⟩

/-- The run's rotation and reported angle are one of the leaves. -/
theorem cordic_mem_leaves (as : List Int) : ∀ (i : Nat) (x y : Int),
    (cordicGauss i as x y, (cordicIter i as x y 0).2.2) ∈ cordicLeaves i as := by
  induction as with
  | nil => intro i x y; simp [cordicGauss, cordicIter, cordicLeaves]
  | cons a as ih =>
    intro i x y
    simp only [cordicGauss, cordicIter, cordicLeaves]
    split
    · have h := (mem_cordicLeavesStep (2 ^ i) a _ _ (ih (i + 1) (x - y / 2 ^ i) (y + x / 2 ^ i))).2
      rw [cordicIter_z as (i + 1) _ _ (0 - a)]
      have e : 0 - a + (cordicIter (i + 1) as (x - y / 2 ^ i) (y + x / 2 ^ i) 0).2.2
          = (cordicIter (i + 1) as (x - y / 2 ^ i) (y + x / 2 ^ i) 0).2.2 - a := by omega
      rw [e]; exact h
    · have h := (mem_cordicLeavesStep (2 ^ i) a _ _ (ih (i + 1) (x + y / 2 ^ i) (y - x / 2 ^ i))).1
      rw [cordicIter_z as (i + 1) _ _ (0 + a)]
      have e : 0 + a + (cordicIter (i + 1) as (x + y / 2 ^ i) (y - x / 2 ^ i) 0).2.2
          = (cordicIter (i + 1) as (x + y / 2 ^ i) (y - x / 2 ^ i) 0).2.2 + a := by omega
      rw [e]; exact h

/-- The CORDIC's angle is the fold's offset plus the folded run's. -/
theorem cordicAtan2_fold (x y : Int) :
    cordicAtan2 x y =
      if x < 0 then (if y < 0 then -cordicPiUrad else cordicPiUrad)
        + (cordicIter 0 cordicLutUrad (-x) (-y) 0).2.2
      else (cordicIter 0 cordicLutUrad x y 0).2.2 := by
  unfold cordicAtan2 cordicFold
  split
  · exact cordicIter_z _ _ _ _ _
  · rfl

theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (by omega : 0 ≤ -a) (by omega : 0 ≤ -a)
    rwa [Int.neg_mul_neg] at this

/-- The norm of the run's rotation is positive, and the turned-back products are the input's
products scaled by it. -/
theorem cordicBack_products (p : Int × Int) (x y : Int) (hx : 0 ≤ x) (hR : 8192 ≤ x.natAbs + y.natAbs) :
    let g := cordicGauss 0 cordicLutUrad x y
    let N := g.1 * g.1 + g.2 * g.2
    0 < N ∧
    (p.1 * g.1 + p.2 * g.2) * (cordicBack x y).2 - (p.2 * g.1 - p.1 * g.2) * (cordicBack x y).1
      = N * (p.1 * y - p.2 * x) ∧
    (p.1 * g.1 + p.2 * g.2) * (cordicBack x y).1 + (p.2 * g.1 - p.1 * g.2) * (cordicBack x y).2
      = N * (p.1 * x + p.2 * y) := by
  intro g N
  have hw := (cordic_residual_cone x y hx hR).1
  simp only [cordicBack] at hw ⊢
  have hg : cordicGauss 0 cordicLutUrad x y = g := rfl
  rw [hg] at hw ⊢
  refine ⟨?_, by grind, by grind⟩
  have h1 := mul_self_nonneg g.1
  have h2 := mul_self_nonneg g.2
  show 0 < g.1 * g.1 + g.2 * g.2
  by_cases h0 : 0 < g.1 * g.1 + g.2 * g.2
  · exact h0
  · have hz1 : g.1 * g.1 = 0 := by omega
    have hz2 : g.2 * g.2 = 0 := by omega
    have z1 : g.1 = 0 := by
      rcases Int.mul_eq_zero.mp hz1 with h | h <;> exact h
    have z2 : g.2 = 0 := by
      rcases Int.mul_eq_zero.mp hz2 with h | h <;> exact h
    rw [z1, z2] at hw
    omega

/-! ### Angles in radians: the argument-enclosure calculus

This tree has no real numbers, so "the argument of `x + j·y` lies in `[lo, hi]` radians" is stated
as derivability in a calculus with two generating facts of real analysis and two structural rules:

* `gregory`: for `0 ≤ t ≤ 1`, `atan t` lies between consecutive partial sums of Gregory's series
  `t - t³/3 + t⁵/5 - …` (the Leibniz bound for an alternating series with decreasing terms);
* `mul`: arguments add under multiplication of complex numbers;
* `conj`: conjugation negates the argument; `weaken`: an enclosure may be widened.

`ArgIn re im lo hi` reads "some lift of the argument of `re + j·im` to the real line lies in
`[lo, hi]`"; each rule is sound for that reading. A derivation is a certificate a reader checks
against those two facts; nothing in Lean interprets it, and the cone theorems above do not use it. -/

/-- Gregory's series, `n` terms from index `k`: `p` is the signed odd power `(-1)^k·t^(2k+1)`. -/
def gregoryAux (t2 : Rat) : Nat → Nat → Rat → Rat → Rat
  | 0, _, _, acc => acc
  | n + 1, k, p, acc => gregoryAux t2 n (k + 1) (-(p * t2)) (acc + p / ((2 * k + 1 : Nat) : Rat))

/-- The partial sum `Σ_{k<n} (-1)^k·t^(2k+1)/(2k+1)` of Gregory's series for `atan t`. -/
def gregorySum (t : Rat) (n : Nat) : Rat := gregoryAux (t * t) n 0 t 0

inductive ArgIn : Rat → Rat → Rat → Rat → Prop
  | gregory (n : Nat) (re im : Rat) : 0 < re → 0 ≤ im → im ≤ re →
      ArgIn re im (gregorySum (im / re) (2 * n + 2)) (gregorySum (im / re) (2 * n + 1))
  | mul {a b c d lo₁ hi₁ lo₂ hi₂ : Rat} : ArgIn a b lo₁ hi₁ → ArgIn c d lo₂ hi₂ →
      ArgIn (a * c - b * d) (a * d + b * c) (lo₁ + lo₂) (hi₁ + hi₂)
  | conj {a b lo hi : Rat} : ArgIn a b lo hi → ArgIn a (-b) (-hi) (-lo)
  | weaken {a b lo hi lo' hi' : Rat} : ArgIn a b lo hi → lo' ≤ lo → hi ≤ hi' → ArgIn a b lo' hi'

namespace ArgIn

theorem cast {a b lo hi a' b' lo' hi' : Rat} (h : ArgIn a b lo hi) (ea : a = a') (eb : b = b')
    (el : lo = lo') (eh : hi = hi') : ArgIn a' b' lo' hi' := by
  subst ea; subst eb; subst el; subst eh; exact h

/-- The calculus derives no argument for `0`. -/
theorem nonzero {a b lo hi : Rat} (h : ArgIn a b lo hi) : a ≠ 0 ∨ b ≠ 0 := by
  induction h with
  | gregory n re im h1 h2 h3 => left; grind
  | mul h1 h2 ih1 ih2 =>
    rename_i a b c d _ _ _ _
    -- |(a + jb)(c + jd)|² = (a² + b²)(c² + d²)
    have key : (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c)
        = (a * a + b * b) * (c * c + d * d) := by grind
    have p1 : 0 < a * a + b * b := by
      have h1 := Interval.rat_sq_nonneg a
      have h2 := Interval.rat_sq_nonneg b
      rcases ih1 with h | h
      · have : a * a ≠ 0 := by intro e; exact h (by rcases Rat.mul_eq_zero.mp e with e | e <;> exact e)
        grind
      · have : b * b ≠ 0 := by intro e; exact h (by rcases Rat.mul_eq_zero.mp e with e | e <;> exact e)
        grind
    have p2 : 0 < c * c + d * d := by
      have h1 := Interval.rat_sq_nonneg c
      have h2 := Interval.rat_sq_nonneg d
      rcases ih2 with h | h
      · have : c * c ≠ 0 := by intro e; exact h (by rcases Rat.mul_eq_zero.mp e with e | e <;> exact e)
        grind
      · have : d * d ≠ 0 := by intro e; exact h (by rcases Rat.mul_eq_zero.mp e with e | e <;> exact e)
        grind
    have p3 := Rat.mul_pos p1 p2
    by_cases hz : a * c - b * d = 0
    · right; intro hz2; rw [hz, hz2] at key; grind
    · left; exact hz
  | conj h ih => rcases ih with h | h
                 · left; exact h
                 · right; grind
  | weaken h _ _ ih => exact ih

theorem gregorySum_one (t : Rat) : gregorySum t 1 = t := by
  simp [gregorySum, gregoryAux]; grind

theorem gregorySum_two (t : Rat) : gregorySum t 2 = t - t * (t * t) / 3 := by
  simp [gregorySum, gregoryAux]; grind

/-- A positive real has argument `0`. -/
theorem pos_real (c : Rat) (hc : 0 < c) : ArgIn c 0 0 0 := by
  have h := ArgIn.gregory 0 c 0 hc (Rat.le_refl) (Rat.le_of_lt hc)
  have e : (0 : Rat) / c = 0 := by grind
  rw [e] at h
  exact h.cast rfl rfl (by decide +kernel) (by decide +kernel)

/-- Scaling by a positive real keeps the argument. -/
theorem scale {a b lo hi : Rat} (c : Rat) (hc : 0 < c) (h : ArgIn a b lo hi) :
    ArgIn (c * a) (c * b) lo hi :=
  ((pos_real c hc).mul h).cast (by grind) (by grind) (by grind) (by grind)

/-- A vector within tangent `T ≤ 1` of the positive real axis has argument in `[-T, T]`:
`0 ≤ atan t ≤ t` for `0 ≤ t ≤ 1`, the first two partial sums. -/
theorem of_tan_le (re im T : Rat) (hre : 0 < re) (h1 : im ≤ T * re) (h2 : -(T * re) ≤ im)
    (hT : T ≤ 1) : ArgIn re im (-T) T := by
  have key : ∀ im' : Rat, 0 ≤ im' → im' ≤ T * re → ArgIn re im' (-T) T := by
    intro im' h0 hle
    have hTre : T * re ≤ re := by
      have := Rat.mul_le_mul_of_nonneg_right hT (Rat.le_of_lt hre); grind
    have ht0 : 0 ≤ im' / re := rat_div_nonneg h0 hre
    have htT : im' / re ≤ T := rat_div_le_of_mul_le hre hle
    have ht1 : im' / re ≤ 1 := by grind
    have h := ArgIn.gregory 0 re im' hre h0 (by grind)
    rw [gregorySum_one, gregorySum_two] at h
    generalize im' / re = t at *
    have s1 : t * t ≤ t := by
      have := Rat.mul_le_mul_of_nonneg_left ht1 ht0; grind
    have s2 : t * (t * t) ≤ t := by
      have := Rat.mul_le_mul_of_nonneg_left s1 ht0; grind
    exact h.weaken (by grind) htT
  by_cases h0 : 0 ≤ im
  · exact key im h0 h1
  · exact (key (-im) (by grind) (by grind)).conj.cast rfl (by grind) rfl (by grind)

end ArgIn

/-- `atan (1/2) + atan (1/3)`: the argument of `1 + j` to eight places. -/
theorem argIn_one_one : ArgIn 1 1 (78539816 / 100000000) (78539817 / 100000000) := by
  have h2 := ArgIn.gregory 6 2 1 (by decide) (by decide) (by decide)
  have h3 := ArgIn.gregory 6 3 1 (by decide) (by decide) (by decide)
  have h := ((h2.mul h3).scale (1 / 5) (by decide +kernel)).weaken
    (lo' := 78539816 / 100000000) (hi' := 78539817 / 100000000) (by decide +kernel) (by decide +kernel)
  exact h.cast (by decide +kernel) (by decide +kernel) rfl rfl

/-- `π` to seven places, as the argument of `-1 = (1 + j)⁴ / 4`. -/
theorem argIn_neg_one : ArgIn (-1) 0 (314159264 / 100000000) (314159268 / 100000000) := by
  have h2 := argIn_one_one.mul argIn_one_one
  have h4 := ((h2.mul h2).scale (1 / 4) (by decide +kernel))
  exact h4.cast (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The angle table against Gregory's series: entry `a` of stage `i ≥ 1` is within half a µrad of
`atan (2^-i)`, checked with `2n + 1` and `2n + 2` terms. -/
def lutCheck (n : Nat) : Nat → List Int → Bool
  | _, [] => true
  | i, a :: as =>
    decide (((2 * a - 1 : Int) : Rat) / 2000000 ≤ gregorySum (1 / (((2 : Int) ^ i : Int) : Rat)) (2 * n + 2)) &&
    decide (gregorySum (1 / (((2 : Int) ^ i : Int) : Rat)) (2 * n + 1) ≤ ((2 * a + 1 : Int) : Rat) / 2000000) &&
    lutCheck n (i + 1) as

/-- The run's exact rotation has the angle the run reports, up to half a µrad per stage. -/
theorem cordicGauss_arg (n : Nat) (as : List Int) : ∀ (i : Nat) (x y : Int), lutCheck n i as = true →
    ArgIn (cordicGauss i as x y).1 (cordicGauss i as x y).2
      (((2 * (cordicIter i as x y 0).2.2 - as.length : Int) : Rat) / 2000000)
      (((2 * (cordicIter i as x y 0).2.2 + as.length : Int) : Rat) / 2000000) := by
  induction as with
  | nil =>
    intro i x y _
    simp only [cordicGauss, cordicIter, List.length_nil]
    exact (ArgIn.pos_real 1 (by decide)).cast (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  | cons a as ih =>
    intro i x y hchk
    simp only [lutCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨c1, c2⟩, c3⟩ := hchk
    have hd : (1 : Int) ≤ 2 ^ i := by have := two_pow_pos i; omega
    have hdq : (1 : Rat) ≤ (((2 : Int) ^ i : Int) : Rat) := by exact_mod_cast hd
    have hstage := (ArgIn.gregory n (((2 : Int) ^ i : Int) : Rat) 1 (by grind) (by decide) hdq).weaken c1 c2
    simp only [cordicGauss, cordicIter, List.length_cons]
    split
    · have h := hstage.conj.mul (ih (i + 1) (x - y / 2 ^ i) (y + x / 2 ^ i) c3)
      rw [cordicIter_z as (i + 1) _ _ (0 - a)]
      refine h.cast ?_ ?_ ?_ ?_ <;> push_cast <;> grind
    · have h := hstage.mul (ih (i + 1) (x + y / 2 ^ i) (y - x / 2 ^ i) c3)
      rw [cordicIter_z as (i + 1) _ _ (0 + a)]
      refine h.cast ?_ ?_ ?_ ?_ <;> push_cast <;> grind

/-- The whole table: the rotation of any run is within 6 µrad of the angle the run reports. -/
theorem cordicRun_arg (x y : Int) :
    ArgIn (cordicGauss 0 cordicLutUrad x y).1 (cordicGauss 0 cordicLutUrad x y).2
      (((cordicIter 0 cordicLutUrad x y 0).2.2 - 6 : Int) / 1000000)
      (((cordicIter 0 cordicLutUrad x y 0).2.2 + 6 : Int) / 1000000) := by
  have hchk : lutCheck 6 1 cordicLutTail = true := by decide +kernel
  have hl : cordicLutUrad = 785398 :: cordicLutTail := rfl
  have h45 := argIn_one_one.weaken (lo' := ((2 * 785398 - 1 : Int) : Rat) / 2000000)
    (hi' := ((2 * 785398 + 1 : Int) : Rat) / 2000000) (by decide +kernel) (by decide +kernel)
  simp only [hl, cordicGauss_stage0, cordicIter_stage0]
  split
  · have h := h45.conj.mul (cordicGauss_arg 6 _ 1 (x - y) (y + x) hchk)
    rw [cordicIter_z _ 1 _ _ (0 - 785398)]
    refine (h.weaken (lo' := _) (hi' := _) ?_ ?_).cast ?_ ?_ rfl rfl
    all_goals (simp only [cordicLutTail, List.length_cons, List.length_nil]; push_cast; grind)
  · have h := h45.mul (cordicGauss_arg 6 _ 1 (x + y) (y - x) hchk)
    rw [cordicIter_z _ 1 _ _ (0 + 785398)]
    refine (h.weaken (lo' := _) (hi' := _) ?_ ?_).cast ?_ ?_ rfl rfl
    all_goals (simp only [cordicLutTail, List.length_cons, List.length_nil]; push_cast; grind)

/-- The folded run in radians: the input's argument is within 3036 µrad of the reported angle
(3030 of residual cone, 6 of table rounding). -/
theorem cordic_folded_arg (x y : Int) (hx : 0 ≤ x) (hR : 8192 ≤ x.natAbs + y.natAbs) :
    ArgIn x y (((cordicIter 0 cordicLutUrad x y 0).2.2 - 3036 : Int) / 1000000)
      (((cordicIter 0 cordicLutUrad x y 0).2.2 + 3036 : Int) / 1000000) := by
  obtain ⟨w0, w1, w2⟩ := cordic_residual_cone x y hx hR
  obtain ⟨hN, -, -⟩ := cordicBack_products (0, 0) x y hx hR
  have hg := cordicRun_arg x y
  simp only [cordicBack] at w0 w1 w2
  generalize (cordicGauss 0 cordicLutUrad x y).1 = gr at *
  generalize (cordicGauss 0 cordicLutUrad x y).2 = gi at *
  generalize (cordicIter 0 cordicLutUrad x y 0).2.2 = Z at *
  have q0 : (0 : Rat) < ((x * gr + y * gi : Int) : Rat) := Rat.intCast_pos.mpr w0
  have q1 := Rat.intCast_le_intCast.mpr w1
  have q2 := Rat.intCast_le_intCast.mpr w2
  rw [Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_ofNat, Rat.intCast_ofNat] at q1
  rw [Rat.intCast_neg, Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_ofNat, Rat.intCast_ofNat] at q2
  have qN : (0 : Rat) < ((gr * gr + gi * gi : Int) : Rat) := Rat.intCast_pos.mpr hN
  have hw := ArgIn.of_tan_le ((x * gr + y * gi : Int) : Rat) ((y * gr - x * gi : Int) : Rat)
    (303 / 100000) q0 (by grind) (by grind) (by decide +kernel)
  have hinv : (0 : Rat) < 1 / ((gr * gr + gi * gi : Int) : Rat) := by
    have := rat_div_nonneg (a := 1) (by decide) qN
    by_cases hz : 1 / ((gr * gr + gi * gi : Int) : Rat) = 0
    · have : (1 : Rat) = 0 := by
        have e := Rat.div_mul_cancel (a := 1) (Rat.ne_of_gt qN)
        rw [hz] at e; grind
      exact absurd this (by decide)
    · grind
  have h := (hw.mul hg).scale _ hinv
  refine h.cast ?_ ?_ ?_ ?_
  · have e := Rat.div_mul_cancel (a := 1) (Rat.ne_of_gt qN)
    simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat] at e ⊢
    generalize (1 : Rat) / ((gr : Rat) * gr + gi * gi) = r at *
    have : r * (((x : Rat) * gr + y * gi) * gr - (y * gr - x * gi) * gi) = (r * (gr * gr + gi * gi)) * x := by grind
    rw [this, e]; grind
  · have e := Rat.div_mul_cancel (a := 1) (Rat.ne_of_gt qN)
    simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat] at e ⊢
    generalize (1 : Rat) / ((gr : Rat) * gr + gi * gi) = r at *
    have : r * (((x : Rat) * gr + y * gi) * gi + (y * gr - x * gi) * gr) = (r * (gr * gr + gi * gi)) * y := by grind
    rw [this, e]; grind
  · simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat]; grind
  · simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat]; grind

/-- **The CORDIC's angle error in radians.** For every input with `|x| + |y| ≥ 2^13`, the argument
of `x + j·y` (a lift of it: the output wraps at `±π`) is within 3037 µrad of `cordicAtan2 x y`:
3030 µrad of convergence and shift truncation (`cordic_residual_cone`), 6 of table rounding, and
the rounding of `π`. -/
theorem cordicAtan2_arg (x y : Int) (hR : 8192 ≤ x.natAbs + y.natAbs) :
    ArgIn x y ((cordicAtan2 x y - 3037 : Int) / 1000000) ((cordicAtan2 x y + 3037 : Int) / 1000000) := by
  rw [cordicAtan2_fold]
  by_cases hx : x < 0
  · simp only [hx, ↓reduceIte]
    have h := cordic_folded_arg (-x) (-y) (by omega) (by omega)
    generalize (cordicIter 0 cordicLutUrad (-x) (-y) 0).2.2 = Z at *
    by_cases hy : y < 0
    · simp only [hy, ↓reduceIte, cordicPiUrad]
      refine ((argIn_neg_one.conj.mul h).weaken (lo' := _) (hi' := _) ?_ ?_).cast ?_ ?_ rfl rfl
      all_goals (simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat]; grind)
    · simp only [hy, ↓reduceIte, cordicPiUrad]
      refine ((argIn_neg_one.mul h).weaken (lo' := _) (hi' := _) ?_ ?_).cast ?_ ?_ rfl rfl
      all_goals (simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat]; grind)
  · simp only [hx, ↓reduceIte]
    have h := cordic_folded_arg x y (by omega) hR
    generalize (cordicIter 0 cordicLutUrad x y 0).2.2 = Z at *
    exact h.weaken (by simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat]; grind) (by simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat]; grind)

/-- **`|cordicAtan2 x y - 10^6·arg (x + j·y)| < 4000` µrad**, against the 209438 µrad the FT8
slicer allows: the enclosure of `cordicAtan2_arg`, widened to the budget the slicer weld uses. -/
theorem cordicAtan2_error_lt_4000_urad (x y : Int) (hR : 8192 ≤ x.natAbs + y.natAbs) :
    ∃ lo hi : Rat, ArgIn x y lo hi ∧
      ((cordicAtan2 x y : Int) : Rat) - 4000 < 1000000 * lo ∧ 1000000 * hi < ((cordicAtan2 x y : Int) : Rat) + 4000 := by
  refine ⟨_, _, cordicAtan2_arg x y hR, ?_, ?_⟩ <;> simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_ofNat] <;> grind


/-- Carry the passive RF alias envelope into an additive receiver-error power budget.
`incident` is the interferer's input power; the coupling bound is a measured/modelled
front-end contract, not a consequence of calibration alone. -/
theorem rf_frontEnd_error_power (ω r1 r2 incident errorPower : Rat) (es : List LadderElem) (m : Nat)
    (h1 : 0 < r1) (h2 : 0 < r2) (hp : ∀ e ∈ es, e.Passive) (hi : 0 ≤ incident)
    (he : errorPower ≤ compositeAliasPower ω r1 r2 es m * incident) :
    errorPower ≤ (1 / (((2*m+1 : Nat) : Rat) * ((2*m+1 : Nat) : Rat))) * incident := by
  exact Rat.le_trans he (Rat.mul_le_mul_of_nonneg_right
    (tayloe_cauer_composite_alias_bound ω r1 r2 es m h1 h2 hp).1 hi)

/-- Strict non-trivial harmonic alias attenuation (`1 ≤ m` gives at least `9×` power rejection `≤ incident / 9`). -/
theorem rf_harmonic_alias_attenuation_ge_9x (ω r1 r2 incident errorPower : Rat) (es : List LadderElem) (m : Nat)
    (hm : 1 ≤ m) (h1 : 0 < r1) (h2 : 0 < r2) (hp : ∀ e ∈ es, e.Passive) (hi : 0 ≤ incident)
    (he : errorPower ≤ compositeAliasPower ω r1 r2 es m * incident) :
    errorPower ≤ (1 / 9) * incident := by
  have hBase := rf_frontEnd_error_power ω r1 r2 incident errorPower es m h1 h2 hp hi he
  have h3Nat : 3 ≤ 2 * m + 1 := by omega
  have h3 : (3 : Rat) ≤ ((2 * m + 1 : Nat) : Rat) := by exact_mod_cast h3Nat
  let D : Rat := ((2 * m + 1 : Nat) : Rat) * ((2 * m + 1 : Nat) : Rat)
  have h9 : (9 : Rat) ≤ D := by
    have a := Rat.mul_le_mul_of_nonneg_left h3 (by decide : (0 : Rat) ≤ 3)
    have b := Rat.mul_le_mul_of_nonneg_right h3 (by grind : (0 : Rat) ≤ ((2 * m + 1 : Nat) : Rat))
    dsimp [D]; grind
  have hDpos : (0 : Rat) < D := by grind
  have hRecip : 1 / D ≤ (1 / 9 : Rat) := by
    have hMul : 9 * (1 / D) ≤ D * (1 / D) :=
      Rat.mul_le_mul_of_nonneg_right h9 (rat_div_nonneg (by decide) hDpos)
    have hCan : D * (1 / D) = 1 := by
      rw [Rat.mul_comm]; exact Rat.div_mul_cancel (Rat.ne_of_gt hDpos)
    rw [hCan] at hMul; grind
  exact Rat.le_trans hBase (Rat.mul_le_mul_of_nonneg_right hRecip hi)

end Obend.Hardware.SwitchedCapRf
end
