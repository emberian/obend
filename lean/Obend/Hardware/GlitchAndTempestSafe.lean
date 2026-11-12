module
/-
# Obend.Hardware.GlitchAndTempestSafe — Power-Glitch-Immune Dual-Rail CPU & High-Frequency PCB TEMPEST Safety
1. **Adversarial Voltage/Clock Glitch Physics, PDN RLC Droop & Single-Rail Auth-Skip (`§1`)**:
   - Couples a passive 2-state on-die PDN RLC MNA DAE (`Obend.Hardware.CircuitDae`) with the CMOS
     alpha-power propagation-delay law $\tau(V_{\text{DD}}) = \frac{k_{\text{path}}}{(V_{\text{DD}} - V_{\text{th}})^2}$
     under $V_{\text{DD}}(t) = V_{\text{nom}} - \Delta V_{\text{PDN}}(t) - v_{\text{glitch}}(t)$
     (`cmos_alpha_delay_monotone_and_diverges`).
   - Proves **`singleRail_powerGlitch_skips_auth_check`**: on an explicit inhabited `BEQ`-guarded
     actuation/secret-store sequence on `Obend.Hardware.PipelinedRiscCore`, a concrete brownout
     $V_{\text{glitch}} \in (V_{\text{ret}}, V_{\text{nom}})$ lets the fast `PC + 4` adder meet setup
     timing while the critical 64-bit `BEQ` zero-compare misses `T_clk - t_setup`, committing an
     unauthorized architectural state provably unreachable by `PipelinedRisc.stepIsaN` at any step!
2. **Dual-Rail Null-Convention / WDDL CPU, Windowed Crowbar Monitor & Verified RTL (`§2`)**:
   - Formalizes 4-state 2-wire `DualRailBit` (`00` spacer, `01` valid `0`, `10` valid `1`, `11` fault),
     positive-monotonic WDDL `AND`/`OR`/`XOR` gates, 64-bit completion tree (`allWordsValid`),
     synthesizable `Obend.Hardware.HDL.RtlModule` (`dualRailWddlGuardRtlModule`,
     `dualRailAluSliceRtlModule`, `checkRtlModuleW = true`), and sticky `.glitchQuarantine` clamping.
   - Proves **`power_glitch_immunity_multi_turn_sound`**: across ANY multi-turn adversarial voltage/clock
     glitch waveform trace with subset bit arrival `{00} → {00, 01, 10}` and cross-rail `11` overdrive,
     every cycle either advances to exact `PipelinedRisc.stepIsa` or latches sticky `.glitchQuarantine`
     with `0#64` external outputs until an authenticated cold zeroization reset wipes secrets first.
3. **Multi-GHz Coupled-PCB TEMPEST Non-Interference & Thermal-Noise Envelope (`§3`)**:
   - Models multi-GHz edge slews driving the $2\times 2$ coupled PCB capacitance matrix
     $\mathbf{C} = \begin{bmatrix} C_0 + \Delta C_1 & -C_m \\ -C_m & C_0 + \Delta C_2 \end{bmatrix}$
     and dipole radiation $\propto f_{\text{clk}}^2 (L_{\text{trace}} |I_{\text{CM}}| + A_{\text{diff}} |I_{\text{DM}}|)$.
   - Proves **`balanced_wddl_zero_secret_dependent_power_and_cm`**,
     **`masked_dualRail_exact_mutual_info_zero`** (exact zero statistical distance / mutual information
     at any GHz frequency and any PCB asymmetry under PRNG `railSwap`), and
     **`imperfect_pcb_tempest_snr_below_noise_floor`** (`SNR < snrMaxMilli / 1000 < 1` via stripline +
     $\lambda_{\min}/20$ stitching-via Faraday fence + DFM skew/etch bounds, refusing ground slots).
4. **Total `Obend.Judge` & `"tempest-glitch-emc@1"` `Judge.Format` (`§4`)**:
   - Packages PDN DAE passivity, RTL guard validity, glitch timing closure, and PCB TEMPEST safety into
     `tempestGlitchEmcJudge` and `tempestGlitchEmcFormat` (`"tempest-glitch-emc@1"`).
-/
public import Obend.Hardware.PipelinedRiscCore
public import Obend.Hardware.HDL
public import Obend.Hardware.CircuitDae
public import Obend.Judge.Class
import all Obend.Hardware.PipelinedRiscCore
import all Obend.Hardware.HDL
import all Obend.Hardware.CircuitDae
public section
namespace Obend.Hardware.GlitchAndTempestSafe
open Obend
open Obend.Analysis
open Obend.Hardware.HDL
open Obend.Hardware.PipelinedRisc
open Obend.Hardware.CircuitDae
set_option autoImplicit false
/-! ## 1. Adversarial Voltage/Clock Glitch Physics, PDN RLC Droop & Single-Rail Auth-Skip -/
/-- Two-state on-die PDN decap + package inductance RLC MNA specification (`dim = 2`, `inputDim = 1`): -/
def pdnDecapRlcSpec (cDecap gBleed lPkg rPkg : CanonicalRat) : MnaCircuitSpec :=
  ⟨2, 1, [[cDecap, 0], [0, lPkg]], [[gBleed, -1], [1, rPkg]], [[1], [0]], []⟩
/-- Rank-1 Gram passivity certificate for `pdnDecapRlcSpec`. -/
def pdnDecapRlcCert (cDecap gBleed lPkg rPkg : CanonicalRat) : MnaDaeCert :=
  ⟨[⟨cDecap, [1, 0]⟩, ⟨lPkg, [0, 1]⟩], [⟨2 * gBleed, [1, 0]⟩, ⟨2 * rPkg, [0, 1]⟩]⟩
/-- **PDN RLC Passivity & Stored-Energy Non-Negativity (`pdnDecapRlc_passive_and_dissipative`)**: -/
theorem pdnDecapRlc_passive_and_dissipative
    (cDecap gBleed lPkg rPkg : CanonicalRat)
    (hC : 0 ≤ cDecap) (hG : 0 ≤ gBleed) (hL : 0 ≤ lPkg) (hR : 0 ≤ rPkg) :
    let spec := pdnDecapRlcSpec cDecap gBleed lPkg rPkg
    (∀ x, 0 ≤ mnaStoredEnergy 2 spec.matC x) ∧ (∀ x, 0 ≤ quadFormN 2 spec.matG x x) := by
  intro spec
  have hCapE : ∀ i j, i < 2 → j < 2 →
      matEntry spec.matC i j = gramEntry (pdnDecapRlcCert cDecap gBleed lPkg rPkg).capGramFactors i j := by
    intro i j hi hj
    match i, j with
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 => dsimp [spec, pdnDecapRlcSpec, pdnDecapRlcCert, matEntry, gramEntry, vecEntry]; grind
    | n + 2, _ => omega | _, n + 2 => omega
  have hCapW : ∀ f, f ∈ (pdnDecapRlcCert cDecap gBleed lPkg rPkg).capGramFactors → 0 ≤ f.weight := by
    intro f hf; simp [pdnDecapRlcCert] at hf; rcases hf with rfl | rfl <;> simpa
  have hCondE : ∀ i j, i < 2 → j < 2 →
      matEntry spec.matG i j + matEntry spec.matG j i =
        gramEntry (pdnDecapRlcCert cDecap gBleed lPkg rPkg).condSymGramFactors i j := by
    intro i j hi hj
    match i, j with
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 => dsimp [spec, pdnDecapRlcSpec, pdnDecapRlcCert, matEntry, gramEntry, vecEntry]; grind
    | n + 2, _ => omega | _, n + 2 => omega
  have hCondW : ∀ f, f ∈ (pdnDecapRlcCert cDecap gBleed lPkg rPkg).condSymGramFactors → 0 ≤ f.weight := by
    intro f hf; simp [pdnDecapRlcCert] at hf; rcases hf with rfl | rfl <;> dsimp <;> grind
  obtain ⟨_, _, hPsdC⟩ := gramCongruence_symm_and_psd 2 spec.matC _ hCapE hCapW
  exact ⟨fun x => Rat.mul_nonneg (show (0 : CanonicalRat) ≤ 1 / 2 by decide +kernel) (hPsdC x),
         quadFormN_nonneg_of_symSum_gram 2 spec.matG _ hCondE hCondW⟩
/-- Instantaneous rail voltage $V_{\text{DD}}(t) = V_{\text{nom}} - \Delta V_{\text{PDN}}(t) - v_{\text{glitch}}(t)$. -/
def effectiveSupplyVoltage (vNom dvPdn vGlitch : CanonicalRat) : CanonicalRat := vNom - dvPdn - vGlitch
/-- Physical Sakurai–Newton CMOS alpha-power ($\alpha = 2$) combinational path delay -/
def cmosAlphaDelay (kPath vTh vDd : CanonicalRat) : CanonicalRat := kPath / ((vDd - vTh) * (vDd - vTh))
private theorem rat_div_nonneg {a b : CanonicalRat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  have hInv : 0 ≤ b⁻¹ := Decidable.byContradiction fun hN => by
    have hM := (Rat.mul_lt_mul_left hb).mpr (show b⁻¹ < 0 by grind)
    rw [Rat.mul_inv_cancel _ (by grind)] at hM; grind
  rw [Rat.div_def]; exact Rat.mul_nonneg ha hInv
private theorem rat_div_mono_left {a1 a2 b : CanonicalRat} (ha : a1 ≤ a2) (hb : 0 < b) : a1 / b ≤ a2 / b := by
  have hDiff : 0 ≤ (a2 - a1) / b := rat_div_nonneg (show 0 ≤ a2 - a1 by grind) hb
  have hEq : (a2 - a1) / b = a2 / b - a1 / b := by rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
  grind
private theorem rat_div_le_div_of_pos_le {k a b : CanonicalRat}
    (hk : 0 ≤ k) (ha : 0 < a) (hab : a ≤ b) : k / b ≤ k / a := by
  have hb : 0 < b := by grind
  have habPos : 0 < a * b := Rat.mul_pos ha hb
  have h1 : (k / b) * (a * b) = k * a := by
    rw [Rat.div_def, show k * b⁻¹ * (a * b) = k * a * (b * b⁻¹) by grind, Rat.mul_inv_cancel b (by grind)]; grind
  have h2 : (k / a) * (a * b) = k * b := by
    rw [Rat.div_def, show k * a⁻¹ * (a * b) = k * b * (a * a⁻¹) by grind, Rat.mul_inv_cancel a (by grind)]; grind
  have hLeMul : (k / b) * (a * b) ≤ (k / a) * (a * b) := by
    rw [h1, h2]; exact Rat.mul_le_mul_of_nonneg_left hab hk
  exact Decidable.byContradiction fun hNot => by
    have hGtMul := (Rat.mul_lt_mul_right habPos).mpr (show k / a < k / b by grind)
    grind
private theorem rat_div_lt_div_of_pos_lt {k a b : CanonicalRat}
    (hk : 0 < k) (ha : 0 < a) (hab : a < b) : k / b < k / a := by
  have hb : 0 < b := by grind
  have h1 : (k / b) * (a * b) = k * a := by
    rw [Rat.div_def, show k * b⁻¹ * (a * b) = k * a * (b * b⁻¹) by grind, Rat.mul_inv_cancel b (by grind)]; grind
  have h2 : (k / a) * (a * b) = k * b := by
    rw [Rat.div_def, show k * a⁻¹ * (a * b) = k * b * (a * a⁻¹) by grind, Rat.mul_inv_cancel a (by grind)]; grind
  have hLtMul : (k / b) * (a * b) < (k / a) * (a * b) := by
    rw [h1, h2]; exact (Rat.mul_lt_mul_left hk).mpr hab
  exact Decidable.byContradiction fun hNot => by
    have hGeMul := Rat.mul_le_mul_of_nonneg_right (show k / a ≤ k / b by grind)
      (show 0 ≤ a * b by have := Rat.mul_pos ha hb; grind)
    grind
/-- **CMOS Alpha-Power Delay Monotonicity & Near-Threshold Divergence (`cmos_alpha_delay_monotone_and_diverges`)**. -/
theorem cmos_alpha_delay_monotone_and_diverges (kPath vTh : CanonicalRat) (hk : 0 < kPath) :
    (∀ v1 v2 : CanonicalRat, vTh < v1 → v1 ≤ v2 → cmosAlphaDelay kPath vTh v2 ≤ cmosAlphaDelay kPath vTh v1) ∧
    (∀ v1 v2 : CanonicalRat, vTh < v1 → v1 < v2 → cmosAlphaDelay kPath vTh v2 < cmosAlphaDelay kPath vTh v1) ∧
    (∀ tBound : CanonicalRat, 0 < tBound → ∃ vDd : CanonicalRat, vTh < vDd ∧ tBound < cmosAlphaDelay kPath vTh vDd) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v1 v2 hv1 hle; unfold cmosAlphaDelay
    have hd1 : 0 < v1 - vTh := by grind
    have hA := Rat.mul_le_mul_of_nonneg_left (show v1 - vTh ≤ v2 - vTh by grind) (show 0 ≤ v1 - vTh by grind)
    have hB := Rat.mul_le_mul_of_nonneg_right (show v1 - vTh ≤ v2 - vTh by grind) (show 0 ≤ v2 - vTh by grind)
    exact rat_div_le_div_of_pos_le (show 0 ≤ kPath by grind) (Rat.mul_pos hd1 hd1)
      (show (v1 - vTh) * (v1 - vTh) ≤ (v2 - vTh) * (v2 - vTh) by grind)
  · intro v1 v2 hv1 hlt; unfold cmosAlphaDelay
    have hd1 : 0 < v1 - vTh := by grind
    have hd2 : 0 < v2 - vTh := by grind
    have hA := (Rat.mul_lt_mul_left hd1).mpr (show v1 - vTh < v2 - vTh by grind)
    have hB := (Rat.mul_lt_mul_right hd2).mpr (show v1 - vTh < v2 - vTh by grind)
    exact rat_div_lt_div_of_pos_lt hk (Rat.mul_pos hd1 hd1)
      (show (v1 - vTh) * (v1 - vTh) < (v2 - vTh) * (v2 - vTh) by grind)
  · intro tBound ht
    let eps := if kPath ≤ tBound + 1 then kPath / (tBound + 1) else 1
    have hEpsPos : 0 < eps := by
      dsimp [eps]; split
      · have hNN := rat_div_nonneg (show 0 ≤ kPath by grind) (show 0 < tBound + 1 by grind)
        have hNe : kPath / (tBound + 1) ≠ 0 := fun hZ => by
          have hM : (kPath / (tBound + 1)) * (tBound + 1) = kPath := by
            rw [Rat.div_def, show kPath * (tBound + 1)⁻¹ * (tBound + 1) = kPath * ((tBound + 1) * (tBound + 1)⁻¹) by grind,
                Rat.mul_inv_cancel _ (by grind)]; grind
          rw [hZ] at hM; grind
        grind
      · decide +kernel
    have hEpsLe1 : eps ≤ 1 := by
      dsimp [eps]; split
      · rename_i hLe
        have h1 : (tBound + 1) / (tBound + 1) = 1 := by rw [Rat.div_def, Rat.mul_inv_cancel _ (by grind)]
        exact Rat.le_trans (rat_div_mono_left hLe (show 0 < tBound + 1 by grind)) (by grind)
      · grind
    have hEpsSqLeEps : eps * eps ≤ eps := by
      have := Rat.mul_le_mul_of_nonneg_left hEpsLe1 (show 0 ≤ eps by grind); grind
    have hEpsLtRatio : eps * (tBound + 1) ≤ kPath := by
      dsimp [eps]; split
      · rw [Rat.div_def, show kPath * (tBound + 1)⁻¹ * (tBound + 1) = kPath * ((tBound + 1) * (tBound + 1)⁻¹) by grind,
            Rat.mul_inv_cancel _ (by grind)]; grind
      · grind
    refine ⟨vTh + eps, by grind, ?_⟩
    unfold cmosAlphaDelay; rw [show (vTh + eps) - vTh = eps by grind]
    have hSqBound : (eps * eps) * tBound < kPath := by
      have h1 := Rat.mul_le_mul_of_nonneg_right hEpsSqLeEps (show 0 ≤ tBound by grind)
      have h2 := (Rat.mul_lt_mul_left hEpsPos).mpr (show tBound < tBound + 1 by grind)
      grind
    exact Decidable.byContradiction fun hNot => by
      have hMul := Rat.mul_le_mul_of_nonneg_right (show kPath / (eps * eps) ≤ tBound by grind)
        (show 0 ≤ eps * eps by have := Rat.mul_pos hEpsPos hEpsPos; grind)
      have hCancel : (kPath / (eps * eps)) * (eps * eps) = kPath := by
        rw [Rat.div_def, show kPath * (eps * eps)⁻¹ * (eps * eps) = kPath * ((eps * eps) * (eps * eps)⁻¹) by grind,
            Rat.mul_inv_cancel _ (by have := Rat.mul_pos hEpsPos hEpsPos; grind)]; grind
      rw [hCancel, show tBound * (eps * eps) = (eps * eps) * tBound by grind] at hMul; grind
/-- Single-rail timing parameters (`kFastPc` = short `PC + 4` carry chain, `kCritAlu` = 64-bit branch/ALU path). -/
structure SingleRailTimingSpec where
  (vNom vRet vTh tClkNom tSetup kFastPc kCritAlu : CanonicalRat)
  deriving DecidableEq, Repr
/-- Single-rail synchronous cycle semantics under supply `vDd` and clock period `tClk`: -/
def stepSingleRailGlitched
    (timing : SingleRailTimingSpec) (imem : InstrMem) (vDd tClk : CanonicalRat) (s : IsaState) : IsaState :=
  if decide (vDd ≤ timing.vTh) then
    { pc := 0#64, regs := RegFile.empty, dmem := s.dmem }
  else
    let budget := tClk - timing.tSetup
    let pcArrives   := decide (cmosAlphaDelay timing.kFastPc timing.vTh vDd ≤ budget)
    let critArrives := decide (cmosAlphaDelay timing.kCritAlu timing.vTh vDd ≤ budget)
    if critArrives && pcArrives then stepIsa imem s
    else if pcArrives then { pc := s.pc + 4#64, regs := s.regs, dmem := s.dmem }
    else s
theorem stepSingleRailGlitched_nominal_eq_stepIsa
    (timing : SingleRailTimingSpec) (imem : InstrMem) (vDd tClk : CanonicalRat) (s : IsaState)
    (hV : timing.vTh < vDd)
    (hFast : cmosAlphaDelay timing.kFastPc timing.vTh vDd ≤ tClk - timing.tSetup)
    (hCrit : cmosAlphaDelay timing.kCritAlu timing.vTh vDd ≤ tClk - timing.tSetup) :
    stepSingleRailGlitched timing imem vDd tClk s = stepIsa imem s := by
  unfold stepSingleRailGlitched; have hNotLe : ¬ (vDd ≤ timing.vTh) := by grind
  simp [hNotLe, hFast, hCrit]
/-- Privilege-guarded actuation program on `PipelinedRiscCore`: -/
def authGuardProg : Array IsaInstr := #[ .BEQ r1 r0 8#64, .ST r3 r4 0#64, .BEQ r0 r0 0#64 ]
/-- Unauthenticated initial `IsaState` (`r1 = 0`, `r3 = 0x1000`, `r4 = 0xCAFEBABEDEADBEEF`, `dmem = empty`). -/
def unauthInitIsaState : IsaState :=
  { pc := 0#64, regs := (RegFile.empty.write r3 0x1000#64).write r4 0xCAFEBABEDEADBEEF#64, dmem := DataMem.empty }
/-- Concrete 1 GHz CMOS timing parameters (`V_nom = 1.0 V`, `V_ret = 0.6 V`, `V_th = 0.4 V`, `T_clk = 1.0 ns`). -/
def nominal1GhzTiming : SingleRailTimingSpec :=
  ⟨1, CanonicalRat.mk 3 5, CanonicalRat.mk 2 5, 1, CanonicalRat.mk 1 10, CanonicalRat.mk 1 20, CanonicalRat.mk 1 5⟩
/-! ## 2. Dual-Rail Null-Convention / WDDL Logic, Verified `RtlModule` & Multi-Turn Glitch Immunity -/
/-- Two-wire 4-state Dual-Rail bit (`00` = spacer/null, `01` = valid `0`, `10` = valid `1`, `11` = fault/alarm). -/
structure DualRailBit where
  (t f : Bool)
  deriving DecidableEq, Repr, Inhabited
namespace DualRailBit
def spacer    : DualRailBit := ⟨false, false⟩
def validZero : DualRailBit := ⟨false, true⟩
def validOne  : DualRailBit := ⟨true,  false⟩
def alarm     : DualRailBit := ⟨true,  true⟩
def encode (b : Bool) : DualRailBit := ⟨b, !b⟩
def isSpacer (x : DualRailBit) : Bool := !x.t && !x.f
def isValid  (x : DualRailBit) : Bool := xor x.t x.f
def isAlarm  (x : DualRailBit) : Bool := x.t && x.f
def delayLe (a b : DualRailBit) : Prop := (a.t = true → b.t = true) ∧ (a.f = true → b.f = true)
def wddlNot (a : DualRailBit) : DualRailBit := ⟨a.f, a.t⟩
def wddlAnd (a b : DualRailBit) : DualRailBit := ⟨a.t && b.t, a.f || b.f⟩
def wddlOr  (a b : DualRailBit) : DualRailBit := ⟨a.t || b.t, a.f && b.f⟩
def wddlXor (a b : DualRailBit) : DualRailBit := ⟨(a.t && b.f) || (a.f && b.t), (a.t && b.t) || (a.f && b.f)⟩
end DualRailBit
/-- Fixed-width synthesizable 64-bit Dual-Rail word (`tRail` = `b_t[63:0]`, `fRail` = `b_f[63:0]`). -/
structure DualRailWord64 where
  (tRail fRail : BitVec 64)
  deriving DecidableEq, Repr, Inhabited
def DualRailWord64.spacer : DualRailWord64 := ⟨0#64, 0#64⟩
def DualRailWord64.encode (v : BitVec 64) : DualRailWord64 := ⟨v, ~~~v⟩
def wordAllValid (w : DualRailWord64) : Bool := (w.tRail ^^^ w.fRail == BitVec.allOnes 64) && ((w.tRail &&& w.fRail) == 0#64)
def wordIsSpacer (w : DualRailWord64) : Bool := (w.tRail == 0#64) && (w.fRail == 0#64)
def wordHasAlarm (w : DualRailWord64) : Bool := (w.tRail &&& w.fRail) != 0#64
def allWordsValid (words : List DualRailWord64) : Bool := words.all wordAllValid && !words.any wordHasAlarm
def allWordsSpacer (words : List DualRailWord64) : Bool := words.all wordIsSpacer
/-- Glitch-delayed Dual-Rail arrival (`{00} → {00, 01, 10}` via `maskT, maskF` + cross-rail `overdrive11`). -/
def applyGlitchArrivalMask (v maskT maskF overdrive11 : BitVec 64) : DualRailWord64 :=
  ⟨(v &&& maskT) ||| overdrive11, (~~~v &&& maskF) ||| overdrive11⟩
/-- **Fundamental Dual-Rail Completion Theorem (`subset_arrival_valid_implies_exact`)**: -/
theorem subset_arrival_valid_implies_exact
    (v maskT maskF overdrive11 : BitVec 64)
    (hValid : wordAllValid (applyGlitchArrivalMask v maskT maskF overdrive11) = true) :
    overdrive11 = 0#64 ∧ applyGlitchArrivalMask v maskT maskF overdrive11 = DualRailWord64.encode v := by
  unfold wordAllValid applyGlitchArrivalMask at hValid
  simp only [Bool.and_eq_true, beq_iff_eq] at hValid
  obtain ⟨hXor, hNo11⟩ := hValid
  have hOvZero : overdrive11 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i _
    have hBit := congrArg (fun x : BitVec 64 => x.getLsbD i) hNo11
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hBit
    cases hO : overdrive11.getLsbD i <;> simp_all
  subst hOvZero; refine ⟨rfl, ?_⟩; unfold DualRailWord64.encode
  have hT : (v &&& maskT) ||| 0#64 = v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hX := congrArg (fun x : BitVec 64 => x.getLsbD i) hXor
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, hi, Bool.or_false] at hX ⊢
    cases hv : v.getLsbD i <;> cases hmt : maskT.getLsbD i <;> cases hmf : maskF.getLsbD i <;> simp_all
  have hF : (~~~v &&& maskF) ||| 0#64 = ~~~v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hX := congrArg (fun x : BitVec 64 => x.getLsbD i) hXor
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, hi, Bool.or_false] at hX ⊢
    cases hv : v.getLsbD i <;> cases hmt : maskT.getLsbD i <;> cases hmf : maskF.getLsbD i <;> simp_all
  unfold applyGlitchArrivalMask; rw [hT, hF]
/-- Synthesizable Dual-Rail WDDL ALU + Completion Tree + Sticky Quarantine Guard (`Obend.Hardware.HDL.RtlModule`). -/
def dualRailWddlGuardRtlModule : RtlModule :=
  let (aT, aF, bT, bF) := (RtlExpr.inputPort 0, RtlExpr.inputPort 1, RtlExpr.inputPort 2, RtlExpr.inputPort 3)
  let (winOk, actCmd, keyIn) := (RtlExpr.inputPort 4, RtlExpr.inputPort 5, RtlExpr.inputPort 6)
  let (ones64, zero64, one64) := (RtlExpr.const (BitVec.allOnes 64), RtlExpr.const 0#64, RtlExpr.const 1#64)
  { name       := "dual_rail_wddl_guard"
    inputNames := ["a_t", "a_f", "b_t", "b_f", "rail_window_ok", "actuation_cmd", "secret_key_in"]
    wires      :=
      [ { wireIdx := 0,  name := "and_t", expr := .alu .bitAnd aT bT }
      , { wireIdx := 1,  name := "and_f", expr := .alu .bitOr  aF bF }
      , { wireIdx := 2,  name := "or_t",  expr := .alu .bitOr  aT bT }
      , { wireIdx := 3,  name := "or_f",  expr := .alu .bitAnd aF bF }
      , { wireIdx := 4,  name := "xor_t", expr := .alu .bitOr (.alu .bitAnd aT bF) (.alu .bitAnd aF bT) }
      , { wireIdx := 5,  name := "xor_f", expr := .alu .bitOr (.wireRef 0) (.wireRef 3) }
      , { wireIdx := 6,  name := "alarm_11_bits",
          expr := .alu .bitOr (.alu .bitOr (.alu .bitAnd aT aF) (.alu .bitAnd bT bF)) (.alu .bitAnd (.wireRef 4) (.wireRef 5)) }
      , { wireIdx := 7,  name := "completion_valid",
          expr := .alu .bitAnd
                    (.alu .bitAnd (.alu .eq (.alu .bitXor aT aF) ones64) (.alu .eq (.alu .bitXor bT bF) ones64))
                    (.alu .bitAnd (.alu .eq (.alu .bitXor (.wireRef 4) (.wireRef 5)) ones64) (.alu .eq (.wireRef 6) zero64)) }
      , { wireIdx := 8,  name := "fault_trip",
          expr := .mux (.alu .eq winOk zero64) one64 (.mux (.alu .eq (.wireRef 6) zero64) zero64 one64) }
      , { wireIdx := 9,  name := "quarantine_next",   expr := .mux (.regRead 0) one64 (.wireRef 8) }
      , { wireIdx := 10, name := "safe_commit_en",    expr := .mux (.wireRef 9) zero64 (.wireRef 7) }
      , { wireIdx := 11, name := "actuation_clamped", expr := .mux (.wireRef 10) actCmd zero64 }
      , { wireIdx := 12, name := "secret_key_clamped", expr := .mux (.wireRef 9) zero64 keyIn } ]
    regs :=
      [ { regIdx := 0, name := "quarantine_q", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 9 }
      , { regIdx := 1, name := "wave_phase_q", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef 9) (.regRead 1) (.alu .bitXor (.regRead 1) one64) } ]
    outputs :=
      [ { name := "xor_t", expr := .wireRef 4 }, { name := "xor_f", expr := .wireRef 5 }
      , { name := "and_t", expr := .wireRef 0 }, { name := "and_f", expr := .wireRef 1 }
      , { name := "or_t",  expr := .wireRef 2 }, { name := "or_f",  expr := .wireRef 3 }
      , { name := "completion_valid",  expr := .wireRef 7  }
      , { name := "quarantine_active", expr := .wireRef 9  }
      , { name := "actuation_out",     expr := .wireRef 11 }
      , { name := "secret_key_out",    expr := .wireRef 12 } ] }
abbrev dualRailAluSliceRtlModule : RtlModule := dualRailWddlGuardRtlModule
theorem dualRailWddlGuardRtl_sticky_quarantine_clamps_outputs
    (inputs regState : Nat → BitVec 64) (hQuar : regState 0 != 0#64) :
    let outs := evalModuleOutputs dualRailWddlGuardRtlModule inputs regState
    outs.lookup "actuation_out" = some 0#64 ∧
    outs.lookup "secret_key_out" = some 0#64 ∧
    stepModuleRegs dualRailWddlGuardRtlModule false inputs regState 0 = 1#64 := by
  simp [evalModuleOutputs, stepModuleRegs, dualRailWddlGuardRtlModule,
    evalWireTable, evalRtlExpr, List.lookup, hQuar]
/-- Analog / TDC windowed rail-voltage and clock-period monitor thresholds. -/
structure RailClockWindowSpec where
  (vTh vRet vMinTiming vMaxOv tClkMin tSetup kWddlCrit : CanonicalRat)
  deriving DecidableEq, Repr
def checkRailClockWindow (spec : RailClockWindowSpec) (vDdMinInCycle vDdMaxInCycle tClk : CanonicalRat) : Bool :=
  decide (spec.vMinTiming ≤ vDdMinInCycle) && decide (vDdMinInCycle ≤ vDdMaxInCycle) &&
  decide (vDdMaxInCycle ≤ spec.vMaxOv) && decide (spec.tClkMin ≤ tClk)
inductive WavePhase | spacerPhase | evalPhase deriving DecidableEq, Repr, Inhabited
inductive CpuExecMode | normal (phase : WavePhase) | glitchQuarantine deriving DecidableEq, Repr, Inhabited
/-- 4-word 64-bit Dual-Rail datapath bundle driving architectural `IsaState` commit. -/
structure DualRailIsaBundle where
  (nextPcDr wbValDr memAddrDr storeValDr : DualRailWord64)
  deriving DecidableEq, Repr, Inhabited
def DualRailIsaBundle.spacer : DualRailIsaBundle := ⟨.spacer, .spacer, .spacer, .spacer⟩
def bundleWords (b : DualRailIsaBundle) : List DualRailWord64 := [b.nextPcDr, b.wbValDr, b.memAddrDr, b.storeValDr]
def encodeIsaStepBundle (imem : InstrMem) (s : IsaState) : DualRailIsaBundle :=
  let instr  := imem s.pc
  let v1     := s.regs.read (instrRs1 instr)
  let v2     := s.regs.read (instrRs2 instr)
  let aluOut := exAluResult s.pc instr v1 v2
  let nextPc := if evalBranchCond instr v1 v2 then exBranchTarget s.pc instr else s.pc + 4#64
  let wbVal  := if instrIsLoad instr then s.dmem.read aluOut else aluOut
  ⟨.encode nextPc, .encode wbVal, .encode aluOut, .encode v2⟩
def commitIsaFromDualRailBundle (imem : InstrMem) (s : IsaState) (b : DualRailIsaBundle) : IsaState :=
  let instr := imem s.pc
  { pc   := b.nextPcDr.tRail
    regs := if instrWritesReg instr then s.regs.write (instrRd instr) b.wbValDr.tRail else s.regs
    dmem := if instrIsStore instr then s.dmem.write b.memAddrDr.tRail b.storeValDr.tRail else s.dmem }
theorem commitIsaFromDualRailBundle_encode_eq_stepIsa (imem : InstrMem) (s : IsaState) :
    commitIsaFromDualRailBundle imem s (encodeIsaStepBundle imem s) = stepIsa imem s := by rfl
structure GlitchProtectedCpuState where
  mode         : CpuExecMode
  isa          : IsaState
  secretKeyReg : BitVec 64
  actuationReg : BitVec 64
  busLatch     : DualRailIsaBundle
  deriving DecidableEq, Repr, Inhabited
def initGlitchProtectedCpu (s0 : IsaState) (secretKey actuation : BitVec 64) : GlitchProtectedCpuState :=
  ⟨.normal .spacerPhase, s0, secretKey, actuation, .spacer⟩
def externalActuationOut (st : GlitchProtectedCpuState) : BitVec 64 :=
  match st.mode with | .glitchQuarantine => 0#64 | .normal _ => st.actuationReg
def externalKeyBusOut (st : GlitchProtectedCpuState) : BitVec 64 :=
  match st.mode with | .glitchQuarantine => 0#64 | .normal _ => st.secretKeyReg
structure GlitchCycleFault where
  (vNom dvPdn vGlitchDrop vGlitchSpike tClk : CanonicalRat)
  (pcMaskT pcMaskF wbMaskT wbMaskF addrMaskT addrMaskF stMaskT stMaskF : BitVec 64)
  (overdrivePc overdriveWb overdriveAddr overdriveSt : BitVec 64)
  (spacerResidue : DualRailIsaBundle)
  deriving DecidableEq, Repr
inductive DualRailCpuTurn where
  | clockCycle (fault : GlitchCycleFault)
  | coldZeroizeReset (authTokenValid : Bool) (bootPc : BitVec 64)
  deriving DecidableEq, Repr
def arriveGlitchedEvalBundle (imem : InstrMem) (s : IsaState) (f : GlitchCycleFault) : DualRailIsaBundle :=
  let ex := encodeIsaStepBundle imem s
  ⟨applyGlitchArrivalMask ex.nextPcDr.tRail   f.pcMaskT   f.pcMaskF   f.overdrivePc,
   applyGlitchArrivalMask ex.wbValDr.tRail    f.wbMaskT   f.wbMaskF   f.overdriveWb,
   applyGlitchArrivalMask ex.memAddrDr.tRail  f.addrMaskT f.addrMaskF f.overdriveAddr,
   applyGlitchArrivalMask ex.storeValDr.tRail f.stMaskT   f.stMaskF   f.overdriveSt⟩
def stepGlitchProtectedCpu
    (winSpec : RailClockWindowSpec) (imem : InstrMem)
    (turn : DualRailCpuTurn) (st : GlitchProtectedCpuState) : GlitchProtectedCpuState :=
  match turn with
  | .coldZeroizeReset authOk bootPc =>
    if authOk then ⟨.normal .spacerPhase, ⟨bootPc, RegFile.empty, DataMem.empty⟩, 0#64, 0#64, .spacer⟩
    else st
  | .clockCycle f =>
    match st.mode with
    | .glitchQuarantine => st
    | .normal .spacerPhase =>
      let vMin := effectiveSupplyVoltage f.vNom f.dvPdn f.vGlitchDrop
      let vMax := effectiveSupplyVoltage f.vNom 0 (-f.vGlitchSpike)
      if checkRailClockWindow winSpec vMin vMax f.tClk && allWordsSpacer (bundleWords f.spacerResidue) then
        { st with mode := .normal .evalPhase, busLatch := .spacer }
      else { st with mode := .glitchQuarantine }
    | .normal .evalPhase =>
      let vMin := effectiveSupplyVoltage f.vNom f.dvPdn f.vGlitchDrop
      let vMax := effectiveSupplyVoltage f.vNom 0 (-f.vGlitchSpike)
      let arrived := arriveGlitchedEvalBundle imem st.isa f
      if checkRailClockWindow winSpec vMin vMax f.tClk && allWordsValid (bundleWords arrived) then
        { st with mode := .normal .spacerPhase, isa := commitIsaFromDualRailBundle imem st.isa arrived, busLatch := arrived }
      else { st with mode := .glitchQuarantine, busLatch := arrived }
def runGlitchProtectedCpuTrace
    (winSpec : RailClockWindowSpec) (imem : InstrMem)
    (turns : List DualRailCpuTurn) (st0 : GlitchProtectedCpuState) : GlitchProtectedCpuState :=
  turns.foldl (fun st turn => stepGlitchProtectedCpu winSpec imem turn st) st0
def isUnresetTurn : DualRailCpuTurn → Bool
  | .clockCycle _ => true | .coldZeroizeReset authOk _ => !authOk
def mkCleanGlitchCycleFault (vNom tClk : CanonicalRat) : GlitchCycleFault :=
  let ones := BitVec.allOnes 64
  ⟨vNom, 0, 0, 0, tClk, ones, ones, ones, ones, ones, ones, ones, ones, 0#64, 0#64, 0#64, 0#64, .spacer⟩
private theorem mkBundle_eq {a1 a2 b1 b2 c1 c2 d1 d2 : DualRailWord64}
    (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
    DualRailIsaBundle.mk a1 b1 c1 d1 = DualRailIsaBundle.mk a2 b2 c2 d2 := by
  subst ha hb hc hd; rfl
/-- **Main Multi-Turn Power-Glitch Immunity Theorem (`power_glitch_immunity_multi_turn_sound`)**: -/
theorem power_glitch_immunity_multi_turn_sound (winSpec : RailClockWindowSpec) (imem : InstrMem) :
    (∀ (f : GlitchCycleFault) (st : GlitchProtectedCpuState),
      let st' := stepGlitchProtectedCpu winSpec imem (.clockCycle f) st
      (st'.mode = .glitchQuarantine ∧ externalActuationOut st' = 0#64 ∧ externalKeyBusOut st' = 0#64) ∨
      (st'.isa = st.isa) ∨ (st'.isa = stepIsa imem st.isa)) ∧
    (∀ (turns : List DualRailCpuTurn) (s0 : IsaState) (key0 act0 : BitVec 64),
      turns.all isUnresetTurn = true →
      let stFinal := runGlitchProtectedCpuTrace winSpec imem turns (initGlitchProtectedCpu s0 key0 act0)
      (stFinal.mode = .glitchQuarantine ∧ externalActuationOut stFinal = 0#64 ∧ externalKeyBusOut stFinal = 0#64) ∨
      (∃ m : Nat, m ≤ turns.length ∧ stFinal.isa = stepIsaN imem m s0)) ∧
    (∀ (turns : List DualRailCpuTurn) (st : GlitchProtectedCpuState),
      st.mode = .glitchQuarantine → turns.all isUnresetTurn = true →
      let stFinal := runGlitchProtectedCpuTrace winSpec imem turns st
      stFinal.mode = .glitchQuarantine ∧ externalActuationOut stFinal = 0#64 ∧ externalKeyBusOut stFinal = 0#64) ∧
    (∀ (bootPc : BitVec 64) (st : GlitchProtectedCpuState),
      let stReset := stepGlitchProtectedCpu winSpec imem (.coldZeroizeReset true bootPc) st
      stReset.secretKeyReg = 0#64 ∧ stReset.actuationReg = 0#64 ∧ stReset.isa.dmem = DataMem.empty) := by
  have hStep : ∀ (f : GlitchCycleFault) (st : GlitchProtectedCpuState),
      let st' := stepGlitchProtectedCpu winSpec imem (.clockCycle f) st
      (st'.mode = .glitchQuarantine ∧ externalActuationOut st' = 0#64 ∧ externalKeyBusOut st' = 0#64) ∨
      (st'.isa = st.isa) ∨ (st'.isa = stepIsa imem st.isa) := by
    intro f st; unfold stepGlitchProtectedCpu
    cases hMode : st.mode with
    | glitchQuarantine => left; simp [hMode, externalActuationOut, externalKeyBusOut]
    | normal ph =>
      cases ph with
      | spacerPhase => dsimp only; split; · { right; left; rfl }; · { left; simp [externalActuationOut, externalKeyBusOut] }
      | evalPhase =>
        dsimp only; split
        · rename_i hBoth; simp only [Bool.and_eq_true] at hBoth
          have hAllV := hBoth.2
          unfold allWordsValid bundleWords arriveGlitchedEvalBundle at hAllV
          simp only [Bool.and_eq_true, List.all_cons, List.all_nil] at hAllV
          obtain ⟨⟨hPcV, hWbV, hAdV, hStV, _⟩, _⟩ := hAllV
          have hPcEx := (subset_arrival_valid_implies_exact _ _ _ _ hPcV).2
          have hWbEx := (subset_arrival_valid_implies_exact _ _ _ _ hWbV).2
          have hAdEx := (subset_arrival_valid_implies_exact _ _ _ _ hAdV).2
          have hStEx := (subset_arrival_valid_implies_exact _ _ _ _ hStV).2
          have hEq : arriveGlitchedEvalBundle imem st.isa f = encodeIsaStepBundle imem st.isa := by
            unfold arriveGlitchedEvalBundle encodeIsaStepBundle at *
            simp only [DualRailWord64.encode] at hPcEx hWbEx hAdEx hStEx
            exact mkBundle_eq hPcEx hWbEx hAdEx hStEx
          right; right; dsimp only; rw [hEq]; rfl
        · left; simp [externalActuationOut, externalKeyBusOut]
  have hAbsorb : ∀ (turns : List DualRailCpuTurn) (st : GlitchProtectedCpuState),
      st.mode = .glitchQuarantine → turns.all isUnresetTurn = true →
      let stFinal := runGlitchProtectedCpuTrace winSpec imem turns st
      stFinal.mode = .glitchQuarantine ∧ externalActuationOut stFinal = 0#64 ∧ externalKeyBusOut stFinal = 0#64 := by
    intro turns; induction turns with
    | nil => intro st hQ _; simp [runGlitchProtectedCpuTrace, hQ, externalActuationOut, externalKeyBusOut]
    | cons turn rest ih =>
      intro st hQ hAll; simp only [List.all_cons, Bool.and_eq_true] at hAll
      have hStepQ : (stepGlitchProtectedCpu winSpec imem turn st).mode = .glitchQuarantine := by
        cases turn with
        | clockCycle _ => simp [stepGlitchProtectedCpu, hQ]
        | coldZeroizeReset authOk _ =>
          cases authOk
          · simp [stepGlitchProtectedCpu, hQ]
          · exfalso; exact Bool.false_ne_true hAll.1
      exact ih _ hStepQ hAll.2
  refine ⟨hStep, ?_, hAbsorb, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  intro turns s0 key0 act0 hAll
  suffices ∀ (tr : List DualRailCpuTurn) (st : GlitchProtectedCpuState) (m : Nat),
      tr.all isUnresetTurn = true → ((st.mode = .glitchQuarantine) ∨ (st.isa = stepIsaN imem m s0)) →
      let stF := runGlitchProtectedCpuTrace winSpec imem tr st
      (stF.mode = .glitchQuarantine ∧ externalActuationOut stF = 0#64 ∧ externalKeyBusOut stF = 0#64) ∨
      (∃ k : Nat, k ≤ m + tr.length ∧ stF.isa = stepIsaN imem k s0) by
    rcases this turns (initGlitchProtectedCpu s0 key0 act0) 0 hAll (Or.inr rfl) with hQ | ⟨k, hk, hIsa⟩
    · exact Or.inl hQ
    · exact Or.inr ⟨k, by omega, hIsa⟩
  intro tr; induction tr with
  | nil =>
    intro st m _ hInv; rcases hInv with hQ | hIsa
    · left; simp [runGlitchProtectedCpuTrace, hQ, externalActuationOut, externalKeyBusOut]
    · right; exact ⟨m, by omega, hIsa⟩
  | cons turn rest ih =>
    intro st m hTr hInv; simp only [List.all_cons, Bool.and_eq_true] at hTr
    rcases hInv with hQ | hIsa
    · left; exact hAbsorb (turn :: rest) st hQ (by simp [hTr.1, hTr.2])
    · cases turn with
      | coldZeroizeReset authOk bootPc =>
        cases authOk
        · simp only [runGlitchProtectedCpuTrace, List.foldl_cons, stepGlitchProtectedCpu]
          rcases ih st m hTr.2 (Or.inr hIsa) with hQ | ⟨k, hk, hkIsa⟩
          · exact Or.inl hQ
          · exact Or.inr ⟨k, by simp; omega, hkIsa⟩
        · exfalso; exact Bool.false_ne_true hTr.1
      | clockCycle f =>
        rcases hStep f st with ⟨hQ', _, _⟩ | hHold | hAdv
        · left; simp only [runGlitchProtectedCpuTrace, List.foldl_cons]; exact hAbsorb rest _ hQ' hTr.2
        · simp only [runGlitchProtectedCpuTrace, List.foldl_cons]
          rcases ih _ m hTr.2 (Or.inr (hHold.trans hIsa)) with hQ | ⟨k, hk, hkIsa⟩
          · exact Or.inl hQ
          · exact Or.inr ⟨k, by simp; omega, hkIsa⟩
        · simp only [runGlitchProtectedCpuTrace, List.foldl_cons]
          have hNextIsa : (stepGlitchProtectedCpu winSpec imem (.clockCycle f) st).isa = stepIsaN imem (m + 1) s0 := by
            rw [hAdv, hIsa, stepIsaN_add, stepIsaN_one]
          rcases ih _ (m + 1) hTr.2 (Or.inr hNextIsa) with hQ | ⟨k, hk, hkIsa⟩
          · exact Or.inl hQ
          · exact Or.inr ⟨k, by simp; omega, hkIsa⟩
/-- **Environment Completeness & Clean Wave-Pipelined Progress (`dualRail_clean_2cycle_executes_stepIsa`)**. -/
theorem dualRail_clean_2cycle_executes_stepIsa
    (winSpec : RailClockWindowSpec) (imem : InstrMem) (vNom tClk : CanonicalRat)
    (hWin : checkRailClockWindow winSpec vNom vNom tClk = true)
    (s0 : IsaState) (key0 act0 : BitVec 64) :
    let f := mkCleanGlitchCycleFault vNom tClk
    let st2 := runGlitchProtectedCpuTrace winSpec imem [.clockCycle f, .clockCycle f] (initGlitchProtectedCpu s0 key0 act0)
    st2.mode = .normal .spacerPhase ∧ st2.isa = stepIsa imem s0 := by
  have hAndOnes : ∀ x : BitVec 64, (x &&& BitVec.allOnes 64) ||| 0#64 = x := fun x => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, BitVec.getLsbD_zero]
    simp [hi]
  have hSub0 : effectiveSupplyVoltage vNom 0 0 = vNom := by unfold effectiveSupplyVoltage; grind
  have hSubNeg0 : effectiveSupplyVoltage vNom 0 (-0) = vNom := by unfold effectiveSupplyVoltage; grind
  have hSp : allWordsSpacer (bundleWords DualRailIsaBundle.spacer) = true := by decide +kernel
  have hStep1 : stepGlitchProtectedCpu winSpec imem (.clockCycle (mkCleanGlitchCycleFault vNom tClk))
      (initGlitchProtectedCpu s0 key0 act0) =
      { initGlitchProtectedCpu s0 key0 act0 with mode := .normal .evalPhase, busLatch := .spacer } := by
    unfold stepGlitchProtectedCpu initGlitchProtectedCpu mkCleanGlitchCycleFault
    dsimp only; rw [hSub0, hSubNeg0, hWin, hSp]; rfl
  have hBundleId : arriveGlitchedEvalBundle imem s0 (mkCleanGlitchCycleFault vNom tClk) = encodeIsaStepBundle imem s0 := by
    unfold arriveGlitchedEvalBundle encodeIsaStepBundle mkCleanGlitchCycleFault applyGlitchArrivalMask DualRailWord64.encode
    simp only [hAndOnes]
  have hWordEnc : ∀ w : BitVec 64, wordAllValid (DualRailWord64.encode w) = true ∧ wordHasAlarm (DualRailWord64.encode w) = false := by
    intro w; unfold wordAllValid wordHasAlarm DualRailWord64.encode
    have hX : (w ^^^ ~~~w) = BitVec.allOnes 64 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes]
      cases w.getLsbD i <;> simp [hi]
    have hA : (w &&& ~~~w) = 0#64 := by apply BitVec.eq_of_getLsbD_eq; intro i _; simp
    simp [hX, hA]
  have hAllV : allWordsValid (bundleWords (encodeIsaStepBundle imem s0)) = true := by
    unfold allWordsValid bundleWords encodeIsaStepBundle; simp [(hWordEnc _).1, (hWordEnc _).2]
  dsimp only [runGlitchProtectedCpuTrace, List.foldl]
  rw [hStep1]
  unfold stepGlitchProtectedCpu
  dsimp only
  have hIsa0 : (initGlitchProtectedCpu s0 key0 act0).isa = s0 := rfl
  have hVMin : effectiveSupplyVoltage (mkCleanGlitchCycleFault vNom tClk).vNom
      (mkCleanGlitchCycleFault vNom tClk).dvPdn (mkCleanGlitchCycleFault vNom tClk).vGlitchDrop = vNom := hSub0
  have hVMax : effectiveSupplyVoltage (mkCleanGlitchCycleFault vNom tClk).vNom
      0 (-(mkCleanGlitchCycleFault vNom tClk).vGlitchSpike) = vNom := hSubNeg0
  have hTClk : (mkCleanGlitchCycleFault vNom tClk).tClk = tClk := rfl
  rw [hIsa0, hVMin, hVMax, hTClk, hWin, hBundleId, hAllV]
  simp [commitIsaFromDualRailBundle_encode_eq_stepIsa]
/-! ## 3. Multi-GHz Coupled-PCB TEMPEST Non-Interference & Imperfect-PCB Thermal-Noise Safety -/
/-- Coupled differential PCB trace pair with $2\times 2$ Maxwell capacitance matrix -/
structure CoupledPcbPairSpec where
  (c0 dc1 dc2 cm lTraceM aDiffM2 : CanonicalRat)
  deriving DecidableEq, Repr
def pcbCapMatrix (pcb : CoupledPcbPairSpec) : List (List CanonicalRat) :=
  [[pcb.c0 + pcb.dc1, -pcb.cm], [-pcb.cm, pcb.c0 + pcb.dc2]]
structure HighSpeedEdgeSpec where
  (fClkHz vSwing tRiseSec dtSkewSec : CanonicalRat)
  deriving DecidableEq, Repr
def pcbTraceCurrents (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) :
    CanonicalRat × CanonicalRat :=
  let pol : CanonicalRat := if xor s isSpacer then 1 else -1
  let slew := edge.vSwing / edge.tRiseSec
  let skewSlew := edge.vSwing * edge.dtSkewSec / (edge.tRiseSec * edge.tRiseSec)
  let iVec := matVecMulN 2 (pcbCapMatrix pcb) [pol * slew, -pol * slew + skewSlew]
  (vecEntry iVec 0, vecEntry iVec 1)
def pcbCommonModeCurrent (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) : CanonicalRat :=
  let (i1, i2) := pcbTraceCurrents pcb edge isSpacer s; i1 + i2
def pcbDiffModeCurrent (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) : CanonicalRat :=
  let (i1, i2) := pcbTraceCurrents pcb edge isSpacer s; (i1 - i2) / 2
def pcbPdnSupplyCurrent (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) : CanonicalRat :=
  let (i1, i2) := pcbTraceCurrents pcb edge isSpacer s; if xor s isSpacer then i1 else i2
def wddlTransitionWeights (isSpacer s : Bool) : Nat × Nat :=
  let d := DualRailBit.encode (xor s isSpacer)
  ((if d.t then 1 else 0) + (if !d.f then 0 else 1), (if !d.t then 1 else 0) + (if d.f then 0 else 1))
private theorem pcbTraceCurrents_closed_form
    (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) :
    let pol : CanonicalRat := if xor s isSpacer then 1 else -1
    let slew := edge.vSwing / edge.tRiseSec
    let skewSlew := edge.vSwing * edge.dtSkewSec / (edge.tRiseSec * edge.tRiseSec)
    pcbTraceCurrents pcb edge isSpacer s =
      ((pcb.c0 + pcb.dc1) * (pol * slew) + (-pcb.cm) * (-pol * slew + skewSlew),
       (-pcb.cm) * (pol * slew) + (pcb.c0 + pcb.dc2) * (-pol * slew + skewSlew)) := by
  dsimp [pcbTraceCurrents, pcbCapMatrix, matVecMulN, mkVec, mkVecFrom, sumUpTo, matEntry, vecEntry]; grind
/-- **Theorem 1 — Ideal Symmetry (`balanced_wddl_zero_secret_dependent_power_and_cm`)**: -/
theorem balanced_wddl_zero_secret_dependent_power_and_cm
    (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
    (hSymCap : pcb.dc1 = pcb.dc2) (hZeroSkew : edge.dtSkewSec = 0) :
    (∀ isSpacer s : Bool, wddlTransitionWeights isSpacer s = (1, 1)) ∧
    (∀ isSpacer : Bool, pcbPdnSupplyCurrent pcb edge isSpacer false = pcbPdnSupplyCurrent pcb edge isSpacer true) ∧
    (∀ isSpacer s : Bool,
      pcbCommonModeCurrent pcb edge isSpacer s = 0 ∧
      edge.fClkHz * edge.fClkHz * pcb.lTraceM * pcbCommonModeCurrent pcb edge isSpacer s = 0) := by
  refine ⟨fun isSpacer s => by cases isSpacer <;> cases s <;> rfl, ?_, ?_⟩
  · intro isSpacer; unfold pcbPdnSupplyCurrent
    rw [pcbTraceCurrents_closed_form pcb edge isSpacer false, pcbTraceCurrents_closed_form pcb edge isSpacer true]
    cases isSpacer <;> simp [hSymCap, hZeroSkew] <;> grind
  · intro isSpacer s
    have hCm0 : pcbCommonModeCurrent pcb edge isSpacer s = 0 := by
      unfold pcbCommonModeCurrent; rw [pcbTraceCurrents_closed_form pcb edge isSpacer s]
      cases xor s isSpacer <;> simp [hSymCap, hZeroSkew] <;> grind
    exact ⟨hCm0, by rw [hCm0]; grind⟩
/-- On-die PRNG Boolean rail-swapper (`mask = true` swaps which physical PCB trace carries `b_t` vs `b_f`). -/
def railSwap (w : DualRailBit) (mask : Bool) : DualRailBit := if mask then ⟨w.f, w.t⟩ else w
theorem railSwap_encode (s mask : Bool) :
    railSwap (DualRailBit.encode s) mask = DualRailBit.encode (xor s mask) := by cases s <;> cases mask <;> rfl
structure RadiatedEmObservation where
  (iTrace1 iTrace2 iCommonMode iDiffMode iPdnSupply eFieldCm hFieldDm : CanonicalRat)
  deriving DecidableEq, Repr
def observeMaskedEm (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s mask : Bool) :
    RadiatedEmObservation :=
  let physBit := (railSwap (DualRailBit.encode s) mask).t
  let (i1, i2) := pcbTraceCurrents pcb edge isSpacer physBit
  let iCm := pcbCommonModeCurrent pcb edge isSpacer physBit
  let iDm := pcbDiffModeCurrent pcb edge isSpacer physBit
  ⟨i1, i2, iCm, iDm, pcbPdnSupplyCurrent pcb edge isSpacer physBit,
   edge.fClkHz * edge.fClkHz * pcb.lTraceM * iCm, edge.fClkHz * edge.fClkHz * pcb.aDiffM2 * iDm⟩
def allBoolVecs : Nat → List (List Bool)
  | 0 => [[]] | k + 1 => (allBoolVecs k).map (false :: ·) ++ (allBoolVecs k).map (true :: ·)
def sumOverBoolVecs (k : Nat) (f : List Bool → CanonicalRat) : CanonicalRat :=
  (allBoolVecs k).foldr (fun m acc => f m + acc) 0
def uniformMaskExpectation (k : Nat) (f : List Bool → CanonicalRat) : CanonicalRat :=
  sumOverBoolVecs k f / CanonicalRat.ofNat (2 ^ k)
def observeMaskedEmTrace (envSeq : Nat → CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool) :
    Nat → List Bool → List Bool → List RadiatedEmObservation
  | _, [], _ | _, _, [] => []
  | idx, s :: ss, m :: ms =>
    let (pcb, edge, isSpacer) := envSeq idx
    observeMaskedEm pcb edge isSpacer s m :: observeMaskedEmTrace envSeq (idx + 1) ss ms
private theorem foldr_add_map {α β : Type} (g : α → β) (f : β → CanonicalRat) :
    ∀ (xs : List α) (init : CanonicalRat),
      (xs.map g).foldr (fun y acc => f y + acc) init = xs.foldr (fun x acc => f (g x) + acc) init
  | [], _ => rfl | _ :: xs, init => by simp [foldr_add_map g f xs init]
private theorem foldr_add_append {α : Type} (f : α → CanonicalRat) :
    ∀ (xs ys : List α),
      (xs ++ ys).foldr (fun x acc => f x + acc) 0 = xs.foldr (fun x acc => f x + acc) 0 + ys.foldr (fun x acc => f x + acc) 0
  | [], _ => by simp; grind | _ :: xs, ys => by simp [foldr_add_append f xs ys]; grind
private theorem sumOverBoolVecs_xor_invariant :
    ∀ (k : Nat) (delta : List Bool), delta.length = k →
      ∀ (f : List Bool → CanonicalRat), sumOverBoolVecs k (fun m => f (List.zipWith xor delta m)) = sumOverBoolVecs k f
  | 0, [], _, _ => rfl
  | k + 1, d :: ds, hLen, f => by
    have hDs : ds.length = k := by simp at hLen; exact hLen
    unfold sumOverBoolVecs allBoolVecs
    rw [foldr_add_append, foldr_add_append, foldr_add_map, foldr_add_map, foldr_add_map, foldr_add_map]
    have ihF := sumOverBoolVecs_xor_invariant k ds hDs (fun m => f (false :: m))
    have ihT := sumOverBoolVecs_xor_invariant k ds hDs (fun m => f (true :: m))
    unfold sumOverBoolVecs at ihF ihT
    cases d
    · have hFF : ∀ m, List.zipWith xor (false :: ds) (false :: m) = false :: List.zipWith xor ds m := fun _ => rfl
      have hFT : ∀ m, List.zipWith xor (false :: ds) (true :: m) = true :: List.zipWith xor ds m := fun _ => rfl
      simp only [hFF, hFT]; rw [ihF, ihT]
    · have hTF : ∀ m, List.zipWith xor (true :: ds) (false :: m) = true :: List.zipWith xor ds m := fun _ => rfl
      have hTT : ∀ m, List.zipWith xor (true :: ds) (true :: m) = false :: List.zipWith xor ds m := fun _ => rfl
      simp only [hTF, hTT]; rw [ihT, ihF]; grind
private theorem observeMaskedEmTrace_depends_only_on_xor
    (envSeq : Nat → CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
    (idx : Nat) (ss ms : List Bool) (hLen : ss.length = ms.length) :
    observeMaskedEmTrace envSeq idx ss ms =
      observeMaskedEmTrace envSeq idx (List.replicate ss.length false) (List.zipWith xor ss ms) := by
  induction ss generalizing idx ms with
  | nil =>
    cases ms with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons s ss ih =>
    cases ms with
    | nil => cases hLen
    | cons m ms =>
      have hSub : ss.length = ms.length := by simp at hLen; exact hLen
      have hHead : observeMaskedEm (envSeq idx).1 (envSeq idx).2.1 (envSeq idx).2.2 s m =
          observeMaskedEm (envSeq idx).1 (envSeq idx).2.1 (envSeq idx).2.2 false (xor s m) := by
        unfold observeMaskedEm; rw [railSwap_encode, railSwap_encode]; cases s <;> cases m <;> rfl
      simp only [observeMaskedEmTrace, List.length_cons, List.replicate_succ, List.zipWith_cons_cons]
      rw [hHead, ih (idx + 1) ms hSub]
private theorem allBoolVecs_mem_length : ∀ (k : Nat) (m : List Bool), m ∈ allBoolVecs k → m.length = k
  | 0, m, hm => by simp [allBoolVecs] at hm; subst hm; rfl
  | k + 1, m, hm => by
    simp only [allBoolVecs, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [allBoolVecs_mem_length k u hu]
private theorem foldr_congr_mem {α : Type} (xs : List α) (f g : α → CanonicalRat) (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldr (fun x acc => f x + acc) 0 = xs.foldr (fun x acc => g x + acc) 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.foldr_cons]; rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
/-- **Theorem 2a — Masked Dual-Rail Exact Zero Mutual Information (`masked_dualRail_exact_mutual_info_zero`)**: -/
theorem masked_dualRail_exact_mutual_info_zero
    (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer : Bool) (obs : RadiatedEmObservation)
    (k : Nat) (envSeq : Nat → CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
    (s0 s1 : List Bool) (h0 : s0.length = k) (h1 : s1.length = k)
    (distinguisher : List RadiatedEmObservation → CanonicalRat) :
    (((if observeMaskedEm pcb edge isSpacer false false = obs then (1 : CanonicalRat) else 0) +
      (if observeMaskedEm pcb edge isSpacer false true  = obs then 1 else 0)) / 2 =
     ((if observeMaskedEm pcb edge isSpacer true  false = obs then (1 : CanonicalRat) else 0) +
      (if observeMaskedEm pcb edge isSpacer true  true  = obs then 1 else 0)) / 2) ∧
    (uniformMaskExpectation k (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s0 m)) =
     uniformMaskExpectation k (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s1 m))) := by
  refine ⟨?_, ?_⟩
  · have h00 : observeMaskedEm pcb edge isSpacer false false = observeMaskedEm pcb edge isSpacer true true := by
      unfold observeMaskedEm; rw [railSwap_encode, railSwap_encode]; rfl
    have h01 : observeMaskedEm pcb edge isSpacer false true = observeMaskedEm pcb edge isSpacer true false := by
      unfold observeMaskedEm; rw [railSwap_encode, railSwap_encode]; rfl
    rw [h00, h01]; grind
  · unfold uniformMaskExpectation; congr 1
    let baseF : List Bool → CanonicalRat := fun u => distinguisher (observeMaskedEmTrace envSeq 0 (List.replicate k false) u)
    have hRew0 : sumOverBoolVecs k (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s0 m)) =
        sumOverBoolVecs k (fun m => baseF (List.zipWith xor s0 m)) :=
      foldr_congr_mem _ _ _ (fun m hm => by
        have := allBoolVecs_mem_length k m hm; dsimp [baseF]
        rw [← h0, observeMaskedEmTrace_depends_only_on_xor envSeq 0 s0 m (by omega)])
    have hRew1 : sumOverBoolVecs k (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s1 m)) =
        sumOverBoolVecs k (fun m => baseF (List.zipWith xor s1 m)) :=
      foldr_congr_mem _ _ _ (fun m hm => by
        have := allBoolVecs_mem_length k m hm; dsimp [baseF]
        rw [← h1, observeMaskedEmTrace_depends_only_on_xor envSeq 0 s1 m (by omega)])
    rw [hRew0, hRew1, sumOverBoolVecs_xor_invariant k s0 h0 baseF, sumOverBoolVecs_xor_invariant k s1 h1 baseF]
/-- High-speed PCB TEMPEST / EMC physical stackup, stitching-via Faraday fence, and thermal-noise envelope. -/
structure TempestPcbEnvelope where
  (c0 cm deltaCapMax vSwing tRiseSec deltaSkewMax fClkHz lTraceM aDiffM2 : CanonicalRat)
  (hasSolidDualGroundPlanes hasGroundSlot : Bool)
  (viaPitchUm lambdaMinUm : Nat)
  (planeShieldFactor kRadOhmM2 aRxApertureM2 rMinM kBTBWatts rxNoiseFigure : CanonicalRat)
  (nAvgTraces snrMaxMilli : Nat)
  deriving DecidableEq, Repr
def stitchingViaAttenuation (env : TempestPcbEnvelope) : CanonicalRat :=
  if env.hasSolidDualGroundPlanes && !env.hasGroundSlot &&
     decide (0 < env.viaPitchUm) && decide (20 * env.viaPitchUm ≤ env.lambdaMinUm) then
    let ratio := CanonicalRat.ofNat env.lambdaMinUm / CanonicalRat.ofNat (20 * env.viaPitchUm)
    env.planeShieldFactor * (ratio * ratio)
  else 0
def receiverNoiseFloor (env : TempestPcbEnvelope) : CanonicalRat := env.kBTBWatts * env.rxNoiseFigure
def cmLeakageBound (env : TempestPcbEnvelope) : CanonicalRat :=
  env.deltaCapMax * (env.vSwing / env.tRiseSec) + env.c0 * env.vSwing * env.deltaSkewMax / (env.tRiseSec * env.tRiseSec)
def dmPeakCurrentBound (env : TempestPcbEnvelope) : CanonicalRat :=
  (env.c0 + env.cm + env.deltaCapMax) * (env.vSwing / env.tRiseSec) +
  (env.c0 + env.cm) * env.vSwing * env.deltaSkewMax / (env.tRiseSec * env.tRiseSec)
def worstCaseRxPowerAtRMin (env : TempestPcbEnvelope) : CanonicalRat :=
  let maxMoment := env.fClkHz * env.fClkHz * (env.lTraceM * cmLeakageBound env + env.aDiffM2 * dmPeakCurrentBound env)
  (env.kRadOhmM2 * (maxMoment * maxMoment) * env.aRxApertureM2) / (env.rMinM * env.rMinM * stitchingViaAttenuation env)
def interceptedRxPower
    (env : TempestPcbEnvelope) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
    (isSpacer s : Bool) (rDistM : CanonicalRat) : CanonicalRat :=
  let moment := env.fClkHz * env.fClkHz *
    (env.lTraceM * ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) +
     env.aDiffM2 * ratAbs (pcbDiffModeCurrent pcb edge isSpacer s))
  (env.kRadOhmM2 * (moment * moment) * env.aRxApertureM2) / (rDistM * rDistM * stitchingViaAttenuation env)
def interceptedSnr
    (env : TempestPcbEnvelope) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
    (isSpacer s : Bool) (rDistM : CanonicalRat) : CanonicalRat :=
  (CanonicalRat.ofNat env.nAvgTraces * interceptedRxPower env pcb edge isSpacer s rDistM) / receiverNoiseFloor env
def checkTempestEmcEnvelope (env : TempestPcbEnvelope) : Bool :=
  env.hasSolidDualGroundPlanes && !env.hasGroundSlot &&
  decide (0 < env.viaPitchUm) && decide (20 * env.viaPitchUm ≤ env.lambdaMinUm) &&
  decide (1 ≤ env.planeShieldFactor) && decide (0 ≤ env.deltaCapMax) &&
  decide (env.deltaCapMax ≤ env.cm) && decide (env.cm + env.deltaCapMax ≤ env.c0) &&
  decide (0 < env.vSwing) && decide (0 < env.tRiseSec) && decide (0 ≤ env.deltaSkewMax) &&
  decide (0 ≤ env.fClkHz) && decide (0 ≤ env.lTraceM) && decide (0 ≤ env.aDiffM2) &&
  decide (0 ≤ env.kRadOhmM2) && decide (0 ≤ env.aRxApertureM2) && decide (0 < env.rMinM) &&
  decide (0 < env.kBTBWatts) && decide (1 ≤ env.rxNoiseFigure) && decide (1 ≤ env.nAvgTraces) &&
  decide (0 < env.snrMaxMilli) && decide (env.snrMaxMilli < 1000) &&
  decide (1000 * CanonicalRat.ofNat env.nAvgTraces * worstCaseRxPowerAtRMin env <
          CanonicalRat.ofNat env.snrMaxMilli * receiverNoiseFloor env)
def RealizesPcbDfm (env : TempestPcbEnvelope) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) : Prop :=
  pcb.c0 = env.c0 ∧ pcb.cm = env.cm ∧ pcb.lTraceM = env.lTraceM ∧ pcb.aDiffM2 = env.aDiffM2 ∧
  edge.fClkHz = env.fClkHz ∧ edge.vSwing = env.vSwing ∧ edge.tRiseSec = env.tRiseSec ∧
  ratAbs (pcb.dc1 - pcb.dc2) ≤ env.deltaCapMax ∧ ratAbs pcb.dc1 ≤ env.deltaCapMax ∧
  ratAbs pcb.dc2 ≤ env.deltaCapMax ∧ ratAbs edge.dtSkewSec ≤ env.deltaSkewMax
private theorem ratAbs_add_le (a b : CanonicalRat) : ratAbs (a + b) ≤ ratAbs a + ratAbs b := by
  unfold ratAbs; split <;> split <;> split <;> grind
private theorem ratAbs_mul_nonneg_right (a b : CanonicalRat) (hb : 0 ≤ b) : ratAbs (a * b) = ratAbs a * b := by
  unfold ratAbs; split
  · split; · rfl
    · have := Rat.mul_le_mul_of_nonneg_right (show a ≤ 0 by grind) hb
      by_cases hb0 : b = 0; · { subst hb0; grind }
      · have := (Rat.mul_lt_mul_right (show 0 < b by grind)).mpr (show a < 0 by grind); grind
  · split; · { rename_i hA; have := Rat.mul_nonneg hA hb; grind }; · grind
/-- **Theorem 2b — Imperfect-PCB Multi-GHz TEMPEST Safety Below Thermal Noise (`imperfect_pcb_tempest_snr_below_noise_floor`)**. -/
theorem imperfect_pcb_tempest_snr_below_noise_floor (env : TempestPcbEnvelope) :
    (∀ (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
       (isSpacer s : Bool) (rDistM : CanonicalRat),
      checkTempestEmcEnvelope env = true → RealizesPcbDfm env pcb edge → env.rMinM ≤ rDistM →
      ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) ≤ cmLeakageBound env ∧
      interceptedSnr env pcb edge isSpacer s rDistM < CanonicalRat.ofNat env.snrMaxMilli / 1000 ∧
      CanonicalRat.ofNat env.snrMaxMilli / 1000 < 1) ∧
    ((env.hasGroundSlot = true ∨ env.hasSolidDualGroundPlanes = false ∨ env.lambdaMinUm < 20 * env.viaPitchUm) →
      checkTempestEmcEnvelope env = false) := by
  refine ⟨?_, ?_⟩
  · intro pcb edge isSpacer s rDistM hChk hDfm hRDist
    unfold checkTempestEmcEnvelope at hChk
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hChk
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPlanes, hNoSlot⟩, hViaPos⟩, hViaLambda⟩, hPlaneF⟩,
      hDcNonneg⟩, hDcLeCm⟩, hCmDcLeC0⟩, hVPos⟩, hTrPos⟩, hSkewNonneg⟩, hFClk⟩,
      hLTr⟩, hADiff⟩, hKRad⟩, hARx⟩, hRMinPos⟩, hKbPos⟩, hRxNf⟩, hNAvg⟩, hSnrPos⟩,
      hSnrLt1000⟩, hSnrStrict⟩ := hChk
    obtain ⟨hC0Eq, hCmEq, hLEq, hAEq, hFEq, hVEq, hTEq, hDcDiff, hDc1, hDc2, hSkewB⟩ := hDfm
    have hSlewPos : 0 ≤ env.vSwing / env.tRiseSec := rat_div_nonneg (show 0 ≤ env.vSwing by grind) hTrPos
    have hTrSqPos : 0 < env.tRiseSec * env.tRiseSec := Rat.mul_pos hTrPos hTrPos
    have hVInvTrSqPos : 0 ≤ env.vSwing / (env.tRiseSec * env.tRiseSec) := rat_div_nonneg (show 0 ≤ env.vSwing by grind) hTrSqPos
    have hCmBound : ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) ≤ cmLeakageBound env := by
      unfold pcbCommonModeCurrent cmLeakageBound
      rw [pcbTraceCurrents_closed_form pcb edge isSpacer s, hC0Eq, hCmEq, hVEq, hTEq]
      have hDc2Iv := (ratAbs_le_iff _ _).mp hDc2
      have hCoeffCmNonneg : 0 ≤ env.c0 - env.cm + pcb.dc2 := by grind
      have hCoeffCmLeC0 : env.c0 - env.cm + pcb.dc2 ≤ env.c0 := by grind
      let pol : CanonicalRat := if xor s isSpacer then 1 else -1
      let slew := env.vSwing / env.tRiseSec
      have hAlg :
          ((env.c0 + pcb.dc1) * (pol * slew) + -env.cm * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec))) +
          (-env.cm * (pol * slew) + (env.c0 + pcb.dc2) * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec))) =
          ((pcb.dc1 - pcb.dc2) * pol) * slew + ((env.c0 - env.cm + pcb.dc2) * edge.dtSkewSec) * (env.vSwing / (env.tRiseSec * env.tRiseSec)) := by
        rw [Rat.div_def (env.vSwing * edge.dtSkewSec), Rat.div_def env.vSwing (env.tRiseSec * env.tRiseSec)]; grind
      dsimp only; rw [hAlg]
      have hTri := ratAbs_add_le (((pcb.dc1 - pcb.dc2) * pol) * slew)
        (((env.c0 - env.cm + pcb.dc2) * edge.dtSkewSec) * (env.vSwing / (env.tRiseSec * env.tRiseSec)))
      rw [ratAbs_mul_nonneg_right _ _ hSlewPos, ratAbs_mul_nonneg_right _ _ hVInvTrSqPos] at hTri
      have hPolAbs : ratAbs ((pcb.dc1 - pcb.dc2) * pol) = ratAbs (pcb.dc1 - pcb.dc2) := by
        dsimp [pol]; cases xor s isSpacer <;> simp only [↓reduceIte, Bool.false_eq_true] <;>
          unfold ratAbs <;> split <;> split <;> grind
      rw [hPolAbs] at hTri
      have hT1 := Rat.mul_le_mul_of_nonneg_right hDcDiff hSlewPos
      have hProdSkew : ratAbs ((env.c0 - env.cm + pcb.dc2) * edge.dtSkewSec) ≤ env.c0 * env.deltaSkewMax := by
        rw [ratAbs_le_iff]; have hSkIv := (ratAbs_le_iff _ _).mp hSkewB
        have := Rat.mul_le_mul_of_nonneg_left hSkIv.1 hCoeffCmNonneg
        have := Rat.mul_le_mul_of_nonneg_left hSkIv.2 hCoeffCmNonneg
        have := Rat.mul_le_mul_of_nonneg_right hCoeffCmLeC0 hSkewNonneg; grind
      have hT2 := Rat.mul_le_mul_of_nonneg_right hProdSkew hVInvTrSqPos
      have hRhsEq : env.c0 * env.deltaSkewMax * (env.vSwing / (env.tRiseSec * env.tRiseSec)) =
          env.c0 * env.vSwing * env.deltaSkewMax / (env.tRiseSec * env.tRiseSec) := by rw [Rat.div_def, Rat.div_def]; grind
      grind
    have hDmBound : ratAbs (pcbDiffModeCurrent pcb edge isSpacer s) ≤ dmPeakCurrentBound env := by
      unfold pcbDiffModeCurrent dmPeakCurrentBound
      rw [pcbTraceCurrents_closed_form pcb edge isSpacer s, hC0Eq, hCmEq, hVEq, hTEq]
      have hDc1Iv := (ratAbs_le_iff _ _).mp hDc1
      have hDc2Iv := (ratAbs_le_iff _ _).mp hDc2
      let pol : CanonicalRat := if xor s isSpacer then 1 else -1
      let slew := env.vSwing / env.tRiseSec
      have hAlgDm :
          (((env.c0 + pcb.dc1) * (pol * slew) + -env.cm * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec))) -
           (-env.cm * (pol * slew) + (env.c0 + pcb.dc2) * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec)))) / 2 =
          ((env.c0 + env.cm + (pcb.dc1 + pcb.dc2) / 2) * pol) * slew +
          (-((env.c0 + env.cm + pcb.dc2) / 2) * edge.dtSkewSec) * (env.vSwing / (env.tRiseSec * env.tRiseSec)) := by
        rw [Rat.div_def (env.vSwing * edge.dtSkewSec), Rat.div_def env.vSwing (env.tRiseSec * env.tRiseSec)]; grind
      dsimp only; rw [hAlgDm]
      have hTri := ratAbs_add_le (((env.c0 + env.cm + (pcb.dc1 + pcb.dc2) / 2) * pol) * slew)
        ((-((env.c0 + env.cm + pcb.dc2) / 2) * edge.dtSkewSec) * (env.vSwing / (env.tRiseSec * env.tRiseSec)))
      rw [ratAbs_mul_nonneg_right _ _ hSlewPos, ratAbs_mul_nonneg_right _ _ hVInvTrSqPos] at hTri
      have hC1Abs : ratAbs ((env.c0 + env.cm + (pcb.dc1 + pcb.dc2) / 2) * pol) ≤ env.c0 + env.cm + env.deltaCapMax := by
        rw [ratAbs_le_iff]; dsimp [pol]; cases xor s isSpacer <;> grind
      have hC2Abs : ratAbs (-((env.c0 + env.cm + pcb.dc2) / 2) * edge.dtSkewSec) ≤ (env.c0 + env.cm) * env.deltaSkewMax := by
        rw [ratAbs_le_iff]; have hSkIv := (ratAbs_le_iff _ _).mp hSkewB
        have hHN : 0 ≤ (env.c0 + env.cm + pcb.dc2) / 2 := by grind
        have hHL : (env.c0 + env.cm + pcb.dc2) / 2 ≤ env.c0 + env.cm := by grind
        have := Rat.mul_le_mul_of_nonneg_left hSkIv.1 hHN
        have := Rat.mul_le_mul_of_nonneg_left hSkIv.2 hHN
        have := Rat.mul_le_mul_of_nonneg_right hHL hSkewNonneg; grind
      have hT1 := Rat.mul_le_mul_of_nonneg_right hC1Abs hSlewPos
      have hT2 := Rat.mul_le_mul_of_nonneg_right hC2Abs hVInvTrSqPos
      have hRhsEq : (env.c0 + env.cm) * env.deltaSkewMax * (env.vSwing / (env.tRiseSec * env.tRiseSec)) =
          (env.c0 + env.cm) * env.vSwing * env.deltaSkewMax / (env.tRiseSec * env.tRiseSec) := by rw [Rat.div_def, Rat.div_def]; grind
      grind
    have hStitchPos : 0 < stitchingViaAttenuation env := by
      unfold stitchingViaAttenuation
      simp only [hPlanes, hNoSlot, Bool.not_false, hViaPos, hViaLambda, decide_true, Bool.and_self, ↓reduceIte]
      have hDenPos : (0 : CanonicalRat) < CanonicalRat.ofNat (20 * env.viaPitchUm) := by
        change (0 : CanonicalRat) < ((20 * env.viaPitchUm : Nat) : CanonicalRat)
        exact_mod_cast (show 0 < 20 * env.viaPitchUm by omega)
      have hNumGe : CanonicalRat.ofNat (20 * env.viaPitchUm) ≤ CanonicalRat.ofNat env.lambdaMinUm := by
        change ((20 * env.viaPitchUm : Nat) : CanonicalRat) ≤ (env.lambdaMinUm : CanonicalRat)
        exact_mod_cast hViaLambda
      have hRatioGe1 : 1 ≤ CanonicalRat.ofNat env.lambdaMinUm / CanonicalRat.ofNat (20 * env.viaPitchUm) := by
        have hOne : CanonicalRat.ofNat (20 * env.viaPitchUm) / CanonicalRat.ofNat (20 * env.viaPitchUm) = 1 := by
          rw [Rat.div_def, Rat.mul_inv_cancel _ (by grind)]
        rw [← hOne]; exact rat_div_mono_left hNumGe hDenPos
      have hRatioSqGe1 : 1 ≤ (CanonicalRat.ofNat env.lambdaMinUm / CanonicalRat.ofNat (20 * env.viaPitchUm)) *
          (CanonicalRat.ofNat env.lambdaMinUm / CanonicalRat.ofNat (20 * env.viaPitchUm)) := by
        have := Rat.mul_le_mul_of_nonneg_left hRatioGe1
          (show 0 ≤ CanonicalRat.ofNat env.lambdaMinUm / CanonicalRat.ofNat (20 * env.viaPitchUm) by grind)
        grind
      have := Rat.mul_le_mul_of_nonneg_left hRatioSqGe1 (show 0 ≤ env.planeShieldFactor by grind); grind
    have hPowerLe : interceptedRxPower env pcb edge isSpacer s rDistM ≤ worstCaseRxPowerAtRMin env := by
      unfold interceptedRxPower worstCaseRxPowerAtRMin
      let mObs := env.fClkHz * env.fClkHz *
        (env.lTraceM * ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) + env.aDiffM2 * ratAbs (pcbDiffModeCurrent pcb edge isSpacer s))
      let mMax := env.fClkHz * env.fClkHz * (env.lTraceM * cmLeakageBound env + env.aDiffM2 * dmPeakCurrentBound env)
      have hFSq : 0 ≤ env.fClkHz * env.fClkHz := Interval.rat_sq_nonneg _
      have hmObsNonneg : 0 ≤ mObs := by
        dsimp [mObs]
        have := Rat.mul_nonneg hLTr (ratAbs_nonneg (pcbCommonModeCurrent pcb edge isSpacer s))
        have := Rat.mul_nonneg hADiff (ratAbs_nonneg (pcbDiffModeCurrent pcb edge isSpacer s))
        exact Rat.mul_nonneg hFSq (show 0 ≤ env.lTraceM * ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) +
          env.aDiffM2 * ratAbs (pcbDiffModeCurrent pcb edge isSpacer s) by grind)
      have hmLe : mObs ≤ mMax := by
        dsimp [mObs, mMax]; have := Rat.mul_le_mul_of_nonneg_left hCmBound hLTr
        have := Rat.mul_le_mul_of_nonneg_left hDmBound hADiff
        exact Rat.mul_le_mul_of_nonneg_left
          (show env.lTraceM * ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) +
            env.aDiffM2 * ratAbs (pcbDiffModeCurrent pcb edge isSpacer s) ≤
            env.lTraceM * cmLeakageBound env + env.aDiffM2 * dmPeakCurrentBound env by grind) hFSq
      have hmSqLe : mObs * mObs ≤ mMax * mMax := by
        have := Rat.mul_le_mul_of_nonneg_left hmLe hmObsNonneg
        have := Rat.mul_le_mul_of_nonneg_right hmLe (show 0 ≤ mMax by grind); grind
      have hNumLe : env.kRadOhmM2 * (mObs * mObs) * env.aRxApertureM2 ≤ env.kRadOhmM2 * (mMax * mMax) * env.aRxApertureM2 :=
        Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left hmSqLe hKRad) hARx
      have hNumMaxNonneg : 0 ≤ env.kRadOhmM2 * (mMax * mMax) * env.aRxApertureM2 :=
        Rat.mul_nonneg (Rat.mul_nonneg hKRad (Interval.rat_sq_nonneg _)) hARx
      have hDenMinPos : 0 < env.rMinM * env.rMinM * stitchingViaAttenuation env :=
        Rat.mul_pos (Rat.mul_pos hRMinPos hRMinPos) hStitchPos
      have hRSqLe : env.rMinM * env.rMinM ≤ rDistM * rDistM := by
        have := Rat.mul_le_mul_of_nonneg_left hRDist (show 0 ≤ env.rMinM by grind)
        have := Rat.mul_le_mul_of_nonneg_right hRDist (show 0 ≤ rDistM by grind); grind
      have hDenLe := Rat.mul_le_mul_of_nonneg_right hRSqLe (show 0 ≤ stitchingViaAttenuation env by grind)
      have hStep1 := rat_div_mono_left hNumLe (show 0 < rDistM * rDistM * stitchingViaAttenuation env by grind)
      have hStep2 := rat_div_le_div_of_pos_le hNumMaxNonneg hDenMinPos hDenLe
      grind
    have hNoisePos : 0 < receiverNoiseFloor env := Rat.mul_pos hKbPos (show 0 < env.rxNoiseFigure by grind)
    have hNAvgNonneg : 0 ≤ CanonicalRat.ofNat env.nAvgTraces := by
      change (0 : CanonicalRat) ≤ (env.nAvgTraces : CanonicalRat)
      exact_mod_cast (Nat.zero_le env.nAvgTraces)
    have hSnrBound : interceptedSnr env pcb edge isSpacer s rDistM < CanonicalRat.ofNat env.snrMaxMilli / 1000 := by
      unfold interceptedSnr
      have hMulLe := Rat.mul_le_mul_of_nonneg_left hPowerLe hNAvgNonneg
      have hScaled := Rat.mul_le_mul_of_nonneg_left hMulLe (show (0 : CanonicalRat) ≤ 1000 by decide +kernel)
      have hCrossPos : 0 < 1000 * receiverNoiseFloor env :=
        Rat.mul_pos (show (0 : CanonicalRat) < 1000 by decide +kernel) hNoisePos
      exact Decidable.byContradiction fun hNotLt => by
        have hGeMul := Rat.mul_le_mul_of_nonneg_right
          (show CanonicalRat.ofNat env.snrMaxMilli / 1000 ≤
            (CanonicalRat.ofNat env.nAvgTraces * interceptedRxPower env pcb edge isSpacer s rDistM) / receiverNoiseFloor env by grind)
          (show 0 ≤ 1000 * receiverNoiseFloor env by grind)
        have hLC : (CanonicalRat.ofNat env.snrMaxMilli / 1000) * (1000 * receiverNoiseFloor env) =
            CanonicalRat.ofNat env.snrMaxMilli * receiverNoiseFloor env := by
          rw [Rat.div_def, show CanonicalRat.ofNat env.snrMaxMilli * (1000 : CanonicalRat)⁻¹ * (1000 * receiverNoiseFloor env) =
              CanonicalRat.ofNat env.snrMaxMilli * receiverNoiseFloor env * ((1000 : CanonicalRat) * (1000 : CanonicalRat)⁻¹) by grind,
              Rat.mul_inv_cancel _ (by decide +kernel)]; grind
        have hRC : ((CanonicalRat.ofNat env.nAvgTraces * interceptedRxPower env pcb edge isSpacer s rDistM) / receiverNoiseFloor env) *
            (1000 * receiverNoiseFloor env) =
            1000 * (CanonicalRat.ofNat env.nAvgTraces * interceptedRxPower env pcb edge isSpacer s rDistM) := by
          rw [Rat.div_def, show (CanonicalRat.ofNat env.nAvgTraces * interceptedRxPower env pcb edge isSpacer s rDistM) *
              (receiverNoiseFloor env)⁻¹ * (1000 * receiverNoiseFloor env) =
              1000 * (CanonicalRat.ofNat env.nAvgTraces * interceptedRxPower env pcb edge isSpacer s rDistM) *
              (receiverNoiseFloor env * (receiverNoiseFloor env)⁻¹) by grind,
              Rat.mul_inv_cancel _ (by grind)]; grind
        rw [hLC, hRC] at hGeMul; grind
    have hSnrLtOne : CanonicalRat.ofNat env.snrMaxMilli / 1000 < 1 := by
      have hLt1000Rat : CanonicalRat.ofNat env.snrMaxMilli < 1000 := by
        change (env.snrMaxMilli : CanonicalRat) < (1000 : Nat)
        exact_mod_cast hSnrLt1000
      exact Decidable.byContradiction fun hNot => by
        have hMul := Rat.mul_le_mul_of_nonneg_right (show 1 ≤ CanonicalRat.ofNat env.snrMaxMilli / 1000 by grind)
          (show (0 : CanonicalRat) ≤ 1000 by decide +kernel)
        rw [Rat.div_def, show CanonicalRat.ofNat env.snrMaxMilli * (1000 : CanonicalRat)⁻¹ * 1000 =
            CanonicalRat.ofNat env.snrMaxMilli * ((1000 : CanonicalRat) * (1000 : CanonicalRat)⁻¹) by grind,
            Rat.mul_inv_cancel _ (by decide +kernel)] at hMul; grind
    exact ⟨hCmBound, hSnrBound, hSnrLtOne⟩
  · intro hBad; unfold checkTempestEmcEnvelope
    rcases hBad with hSlot | hNoPlanes | hVia
    · simp [hSlot]
    · simp [hNoPlanes]
    · have hNotLe : ¬ (20 * env.viaPitchUm ≤ env.lambdaMinUm) := by omega
      simp [hNotLe]
/-! ## 4. Total `Obend.Judge` Instance (`tempestGlitchEmcJudge`) & `"tempest-glitch-emc@1"` `Judge.Format` -/
@[expose] def tempestGlitchEmcWireTag : String := "tempest-glitch-emc@1"
structure TempestGlitchEmcProblem where
  pdnProblem : MnaDaeProblem
  guardRtl   : RtlModule
  railSpec   : RailClockWindowSpec
  pcbEnv     : TempestPcbEnvelope
  deriving DecidableEq, Repr
structure TempestGlitchEmcCert where
  pdnCert          : MnaDaeCert
  prngMaskSeedBits : Nat
  deriving DecidableEq, Repr
inductive TempestGlitchEmcClause where
  | pdnDaeViolation (sub : MnaDaeClause)
  | invalidDualRailGuardRtl
  | railWindowTimingViolation
  | groundSlotOrMissingGroundPlanes
  | sparseStitchingViaFence
  | tempestSnrExceedsNoiseFloor
  | insufficientPrngMaskEntropy
  deriving DecidableEq, Repr
def RailWindowTimingProp (r : RailClockWindowSpec) : Prop :=
  0 < r.kWddlCrit ∧ 0 < r.vTh ∧ r.vTh < r.vRet ∧ r.vRet < r.vMinTiming ∧ r.vMinTiming ≤ r.vMaxOv ∧
  0 < r.tSetup ∧ r.tSetup < r.tClkMin ∧ cmosAlphaDelay r.kWddlCrit r.vTh r.vMinTiming ≤ r.tClkMin - r.tSetup
def checkRailWindowTimingClosure (r : RailClockWindowSpec) : Bool :=
  decide (0 < r.kWddlCrit) && decide (0 < r.vTh) && decide (r.vTh < r.vRet) &&
  decide (r.vRet < r.vMinTiming) && decide (r.vMinTiming ≤ r.vMaxOv) &&
  decide (0 < r.tSetup) && decide (r.tSetup < r.tClkMin) &&
  decide (cmosAlphaDelay r.kWddlCrit r.vTh r.vMinTiming ≤ r.tClkMin - r.tSetup)
private theorem checkRailWindowTimingClosure_iff (r : RailClockWindowSpec) :
    checkRailWindowTimingClosure r = true ↔ RailWindowTimingProp r := by
  unfold checkRailWindowTimingClosure RailWindowTimingProp; simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩,
         fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩⟩
def TempestPcbEnvelopeProp (env : TempestPcbEnvelope) : Prop :=
  env.hasSolidDualGroundPlanes = true ∧ env.hasGroundSlot = false ∧
  0 < env.viaPitchUm ∧ 20 * env.viaPitchUm ≤ env.lambdaMinUm ∧ 1 ≤ env.planeShieldFactor ∧
  0 ≤ env.deltaCapMax ∧ env.deltaCapMax ≤ env.cm ∧ env.cm + env.deltaCapMax ≤ env.c0 ∧
  0 < env.vSwing ∧ 0 < env.tRiseSec ∧ 0 ≤ env.deltaSkewMax ∧
  0 ≤ env.fClkHz ∧ 0 ≤ env.lTraceM ∧ 0 ≤ env.aDiffM2 ∧ 0 ≤ env.kRadOhmM2 ∧ 0 ≤ env.aRxApertureM2 ∧
  0 < env.rMinM ∧ 0 < env.kBTBWatts ∧ 1 ≤ env.rxNoiseFigure ∧ 1 ≤ env.nAvgTraces ∧
  0 < env.snrMaxMilli ∧ env.snrMaxMilli < 1000 ∧
  1000 * CanonicalRat.ofNat env.nAvgTraces * worstCaseRxPowerAtRMin env <
    CanonicalRat.ofNat env.snrMaxMilli * receiverNoiseFloor env
private theorem checkTempestEmcEnvelope_iff (env : TempestPcbEnvelope) :
    checkTempestEmcEnvelope env = true ↔ TempestPcbEnvelopeProp env := by
  unfold checkTempestEmcEnvelope TempestPcbEnvelopeProp
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · intro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
      h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
      h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩
@[expose] def TempestGlitchEmcMeaning (prob : TempestGlitchEmcProblem) (cert : TempestGlitchEmcCert) : Prop :=
  MnaDaeMeaning prob.pdnProblem cert.pdnCert ∧
  checkRtlModuleW prob.guardRtl = true ∧
  RailWindowTimingProp prob.railSpec ∧
  TempestPcbEnvelopeProp prob.pcbEnv ∧
  128 ≤ cert.prngMaskSeedBits
def tempestGlitchClauseRefutes : TempestGlitchEmcClause → Bool
  | .pdnDaeViolation sub => mnaClauseRefutes sub
  | .invalidDualRailGuardRtl | .railWindowTimingViolation | .groundSlotOrMissingGroundPlanes
  | .sparseStitchingViaFence | .tempestSnrExceedsNoiseFloor => true
  | .insufficientPrngMaskEntropy => false
def checkTempestGlitchEmc
    (grade : Nat) (prob : TempestGlitchEmcProblem) (cert : TempestGlitchEmcCert) :
    Judge.Verdict TempestGlitchEmcClause :=
  match checkMnaDaeProblem grade prob.pdnProblem cert.pdnCert with
  | .uncovered => .uncovered
  | .refused k p => .refused (.pdnDaeViolation k) p
  | .ok =>
    if !checkRtlModuleW prob.guardRtl then .refused .invalidDualRailGuardRtl []
    else if !checkRailWindowTimingClosure prob.railSpec then .refused .railWindowTimingViolation []
    else if !prob.pcbEnv.hasSolidDualGroundPlanes || prob.pcbEnv.hasGroundSlot then
      .refused .groundSlotOrMissingGroundPlanes []
    else if !(decide (0 < prob.pcbEnv.viaPitchUm) && decide (20 * prob.pcbEnv.viaPitchUm ≤ prob.pcbEnv.lambdaMinUm)) then
      .refused .sparseStitchingViaFence []
    else if !checkTempestEmcEnvelope prob.pcbEnv then .refused .tempestSnrExceedsNoiseFloor []
    else if !decide (128 ≤ cert.prngMaskSeedBits) then .refused .insufficientPrngMaskEntropy []
    else .ok
theorem checkTempestGlitchEmc_sound {r : Nat} {prob : TempestGlitchEmcProblem} {cert : TempestGlitchEmcCert}
    (hOk : checkTempestGlitchEmc r prob cert = .ok) : TempestGlitchEmcMeaning prob cert := by
  unfold checkTempestGlitchEmc at hOk
  cases hPdn : checkMnaDaeProblem r prob.pdnProblem cert.pdnCert with
  | uncovered => rw [hPdn] at hOk; cases hOk
  | refused k p => rw [hPdn] at hOk; cases hOk
  | ok =>
    rw [hPdn] at hOk; dsimp only at hOk
    by_cases hRtl : checkRtlModuleW prob.guardRtl = true
    · simp only [hRtl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      by_cases hWin : checkRailWindowTimingClosure prob.railSpec = true
      · simp only [hWin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        by_cases hGnd : (!prob.pcbEnv.hasSolidDualGroundPlanes || prob.pcbEnv.hasGroundSlot) = true
        · simp [hGnd] at hOk
        · simp only [hGnd, Bool.false_eq_true, ↓reduceIte] at hOk
          by_cases hVia : (decide (0 < prob.pcbEnv.viaPitchUm) &&
              decide (20 * prob.pcbEnv.viaPitchUm ≤ prob.pcbEnv.lambdaMinUm)) = true
          · simp only [hVia, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
            by_cases hEnv : checkTempestEmcEnvelope prob.pcbEnv = true
            · simp only [hEnv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
              by_cases hSeed : decide (128 ≤ cert.prngMaskSeedBits) = true
              · exact ⟨checkMnaDaeProblem_sound hPdn, hRtl, (checkRailWindowTimingClosure_iff _).mp hWin,
                       (checkTempestEmcEnvelope_iff _).mp hEnv, of_decide_eq_true hSeed⟩
              · simp [hSeed] at hOk
            · simp [hEnv] at hOk
          · simp [hVia] at hOk
      · simp [hWin] at hOk
    · simp [hRtl] at hOk
theorem checkTempestGlitchEmc_refuted
    {r : Nat} {prob : TempestGlitchEmcProblem} {cert : TempestGlitchEmcCert}
    {k : TempestGlitchEmcClause} {p : List Nat}
    (hRef : checkTempestGlitchEmc r prob cert = .refused k p)
    (hRefutes : tempestGlitchClauseRefutes k = true) :
    ∀ c', ¬ TempestGlitchEmcMeaning prob c' := by
  intro c' ⟨hPdnM, hRtlM, hWinM, hEnvM, _⟩
  unfold checkTempestGlitchEmc at hRef
  cases hPdn : checkMnaDaeProblem r prob.pdnProblem cert.pdnCert with
  | uncovered => rw [hPdn] at hRef; cases hRef
  | refused sub _ =>
    rw [hPdn] at hRef; injection hRef with hk _; subst hk
    exact checkMnaDaeProblem_refuted hPdn hRefutes c'.pdnCert hPdnM
  | ok =>
    rw [hPdn] at hRef; dsimp only at hRef
    have hWinT := (checkRailWindowTimingClosure_iff _).mpr hWinM
    have hEnvT := (checkTempestEmcEnvelope_iff _).mpr hEnvM
    have hGndF : (!prob.pcbEnv.hasSolidDualGroundPlanes || prob.pcbEnv.hasGroundSlot) = false := by
      simp [hEnvM.1, hEnvM.2.1]
    have hViaT : (decide (0 < prob.pcbEnv.viaPitchUm) &&
        decide (20 * prob.pcbEnv.viaPitchUm ≤ prob.pcbEnv.lambdaMinUm)) = true := by
      simp [hEnvM.2.2.1, hEnvM.2.2.2.1]
    simp only [hRtlM, hWinT, hGndF, hViaT, hEnvT, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
    by_cases hSeed : decide (128 ≤ cert.prngMaskSeedBits) = true
    · simp [hSeed] at hRef
    · simp only [hSeed, Bool.not_false, ↓reduceIte] at hRef
      injection hRef with hk _; subst hk; cases hRefutes
theorem checkTempestGlitchEmc_complete {prob : TempestGlitchEmcProblem}
    (hEx : ∃ c, TempestGlitchEmcMeaning prob c) : ∃ c r, checkTempestGlitchEmc r prob c = .ok := by
  obtain ⟨c, hPdnM, hRtlM, hWinM, hEnvM, hSeedM⟩ := hEx
  obtain ⟨pdnC, r, hPdnOk⟩ := checkMnaDaeProblem_complete ⟨c.pdnCert, hPdnM⟩
  refine ⟨⟨pdnC, c.prngMaskSeedBits⟩, r, ?_⟩
  unfold checkTempestGlitchEmc; rw [hPdnOk]; dsimp only
  have hWinT := (checkRailWindowTimingClosure_iff _).mpr hWinM
  have hEnvT := (checkTempestEmcEnvelope_iff _).mpr hEnvM
  have hGndF : (!prob.pcbEnv.hasSolidDualGroundPlanes || prob.pcbEnv.hasGroundSlot) = false := by
    simp [hEnvM.1, hEnvM.2.1]
  have hViaT : (decide (0 < prob.pcbEnv.viaPitchUm) &&
      decide (20 * prob.pcbEnv.viaPitchUm ≤ prob.pcbEnv.lambdaMinUm)) = true := by
    simp [hEnvM.2.2.1, hEnvM.2.2.2.1]
  have hSeedT : decide (128 ≤ c.prngMaskSeedBits) = true := decide_eq_true hSeedM
  simp [hRtlM, hWinT, hGndF, hViaT, hEnvT, hSeedT]
/-- **Total Inhabited Power-Glitch + High-Speed PCB TEMPEST Judge (`tempestGlitchEmcJudge`)**. -/
instance tempestGlitchEmcJudge : Judge TempestGlitchEmcProblem TempestGlitchEmcCert where
  Clause   := TempestGlitchEmcClause
  Meaning  := TempestGlitchEmcMeaning
  check    := checkTempestGlitchEmc
  sound    := checkTempestGlitchEmc_sound
  refutes  := tempestGlitchClauseRefutes
  refuted  := checkTempestGlitchEmc_refuted
  Fragment := fun _ => True
  complete := fun _ hEx => checkTempestGlitchEmc_complete hEx
  mono     := by
    intro r r' o c hLe hNe; unfold checkTempestGlitchEmc at hNe ⊢
    have hPdnNe : checkMnaDaeProblem r o.pdnProblem c.pdnCert ≠ .uncovered := fun hU => by rw [hU] at hNe; exact hNe rfl
    have hPdnMono := mnaCircuitDaeJudge.mono (o := o.pdnProblem) (c := c.pdnCert) hLe hPdnNe
    dsimp [Judge.check] at hPdnMono; rw [hPdnMono]
/-- Certified 2.5 GHz (`f = 5/2 GHz`, `t_r = 2/25 ns = 80 ps`, `C_0 = 2/25 pF = 80 fF`, `C_m = 3/100 pF = 30 fF`, -/
def certified2p5GhzStriplineEnv : TempestPcbEnvelope :=
  { c0 := CanonicalRat.mk 2 25, cm := CanonicalRat.mk 3 100
    deltaCapMax := CanonicalRat.mk 1 1000, vSwing := CanonicalRat.mk 4 5
    tRiseSec := CanonicalRat.mk 2 25, deltaSkewMax := CanonicalRat.mk 1 500
    fClkHz := CanonicalRat.mk 5 2, lTraceM := CanonicalRat.mk 1 50, aDiffM2 := CanonicalRat.mk 1 50000
    hasSolidDualGroundPlanes := true, hasGroundSlot := false, viaPitchUm := 1000, lambdaMinUm := 60000
    planeShieldFactor := 1000, kRadOhmM2 := 10000
    aRxApertureM2 := CanonicalRat.mk 1 100, rMinM := 1
    kBTBWatts := 4, rxNoiseFigure := 2
    nAvgTraces := 1000, snrMaxMilli := 250 }
def certifiedDualRailWindow : RailClockWindowSpec :=
  ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 3 5, CanonicalRat.mk 17 20, CanonicalRat.mk 23 20,
   1, CanonicalRat.mk 1 10, CanonicalRat.mk 3 20⟩
def certifiedPdnDaeProblem : MnaDaeProblem :=
  ⟨pdnDecapRlcSpec 1 1 1 1, .backwardEuler,
    [⟨1, [0, 0], [CanonicalRat.mk 2 5, -(CanonicalRat.mk 1 5)], [1], [], [], 0⟩]⟩
def certifiedPdnDaeCert : MnaDaeCert := pdnDecapRlcCert 1 1 1 1
def certifiedTempestGlitchProblem : TempestGlitchEmcProblem :=
  ⟨certifiedPdnDaeProblem, dualRailWddlGuardRtlModule, certifiedDualRailWindow, certified2p5GhzStriplineEnv⟩
def certifiedTempestGlitchCert : TempestGlitchEmcCert := ⟨certifiedPdnDaeCert, 256⟩
def groundSlotBadTempestProblem : TempestGlitchEmcProblem :=
  { certifiedTempestGlitchProblem with pcbEnv := { certified2p5GhzStriplineEnv with hasGroundSlot := true } }
def cyclicBadGuardRtlModule : RtlModule :=
  { dualRailWddlGuardRtlModule with
      name  := "cyclic_bad_guard"
      wires := { wireIdx := 0, name := "loop0", expr := .wireRef 0 } :: dualRailWddlGuardRtlModule.wires.drop 1 }
theorem groundSlotBadTempest_refused (grade : Nat) :
    checkTempestGlitchEmc (grade + 1) groundSlotBadTempestProblem certifiedTempestGlitchCert =
      .refused .groundSlotOrMissingGroundPlanes [] := by
  have hPdnEq : groundSlotBadTempestProblem.pdnProblem = certifiedPdnDaeProblem := rfl
  have hRtlEq : groundSlotBadTempestProblem.guardRtl = dualRailWddlGuardRtlModule := rfl
  have hWinEq : groundSlotBadTempestProblem.railSpec = certifiedDualRailWindow := rfl
  have hPdnOk : checkMnaDaeProblem (grade + 1) certifiedPdnDaeProblem certifiedPdnDaeCert = .ok := by
    unfold checkMnaDaeProblem certifiedPdnDaeProblem; dsimp only [List.length]
    have hNotLt : ¬ (grade + 1 < 1) := by omega
    simp only [hNotLt, ↓reduceIte]; decide +kernel
  unfold checkTempestGlitchEmc
  rw [hPdnEq, hRtlEq, hWinEq, show certifiedTempestGlitchCert.pdnCert = certifiedPdnDaeCert from rfl, hPdnOk]
  dsimp only
  have hRtl : checkRtlModuleW dualRailWddlGuardRtlModule = true := by decide +kernel
  have hWin : checkRailWindowTimingClosure certifiedDualRailWindow = true := by decide +kernel
  have hGnd : (!groundSlotBadTempestProblem.pcbEnv.hasSolidDualGroundPlanes ||
      groundSlotBadTempestProblem.pcbEnv.hasGroundSlot) = true := rfl
  simp [hRtl, hWin, hGnd]
private def encodeBoolNat (b : Bool) : SosJson := .ofNat (if b then 1 else 0)
private def decodeBoolNat (j : SosJson) : Except String Bool := do pure ((← j.getNat?) != 0)
private def encodeRailWindowJson (r : RailClockWindowSpec) : SosJson :=
  SosJson.mkObj [ ("vTh", sosJsonEncodeRat r.vTh), ("vRet", sosJsonEncodeRat r.vRet)
    , ("vMinTiming", sosJsonEncodeRat r.vMinTiming), ("vMaxOv", sosJsonEncodeRat r.vMaxOv)
    , ("tClkMin", sosJsonEncodeRat r.tClkMin), ("tSetup", sosJsonEncodeRat r.tSetup)
    , ("kWddlCrit", sosJsonEncodeRat r.kWddlCrit) ]
private def decodeRailWindowJson (j : SosJson) : Except String RailClockWindowSpec := do
  pure ⟨← j.getObjVal? "vTh" >>= decodeRatJson, ← j.getObjVal? "vRet" >>= decodeRatJson,
        ← j.getObjVal? "vMinTiming" >>= decodeRatJson, ← j.getObjVal? "vMaxOv" >>= decodeRatJson,
        ← j.getObjVal? "tClkMin" >>= decodeRatJson, ← j.getObjVal? "tSetup" >>= decodeRatJson,
        ← j.getObjVal? "kWddlCrit" >>= decodeRatJson⟩
private def encodeTempestPcbJson (e : TempestPcbEnvelope) : SosJson :=
  SosJson.mkObj [ ("c0", sosJsonEncodeRat e.c0), ("cm", sosJsonEncodeRat e.cm)
    , ("deltaCapMax", sosJsonEncodeRat e.deltaCapMax), ("vSwing", sosJsonEncodeRat e.vSwing)
    , ("tRiseSec", sosJsonEncodeRat e.tRiseSec), ("deltaSkewMax", sosJsonEncodeRat e.deltaSkewMax)
    , ("fClkHz", sosJsonEncodeRat e.fClkHz), ("lTraceM", sosJsonEncodeRat e.lTraceM)
    , ("aDiffM2", sosJsonEncodeRat e.aDiffM2), ("solidPlanes", encodeBoolNat e.hasSolidDualGroundPlanes)
    , ("groundSlot", encodeBoolNat e.hasGroundSlot), ("viaPitchUm", .ofNat e.viaPitchUm)
    , ("lambdaMinUm", .ofNat e.lambdaMinUm), ("planeShieldFactor", sosJsonEncodeRat e.planeShieldFactor)
    , ("kRadOhmM2", sosJsonEncodeRat e.kRadOhmM2), ("aRxApertureM2", sosJsonEncodeRat e.aRxApertureM2)
    , ("rMinM", sosJsonEncodeRat e.rMinM), ("kBTBWatts", sosJsonEncodeRat e.kBTBWatts)
    , ("rxNoiseFigure", sosJsonEncodeRat e.rxNoiseFigure)
    , ("nAvgTraces", .ofNat e.nAvgTraces), ("snrMaxMilli", .ofNat e.snrMaxMilli) ]
private def decodeTempestPcbJson (j : SosJson) : Except String TempestPcbEnvelope := do
  pure ⟨← j.getObjVal? "c0" >>= decodeRatJson, ← j.getObjVal? "cm" >>= decodeRatJson,
        ← j.getObjVal? "deltaCapMax" >>= decodeRatJson, ← j.getObjVal? "vSwing" >>= decodeRatJson,
        ← j.getObjVal? "tRiseSec" >>= decodeRatJson, ← j.getObjVal? "deltaSkewMax" >>= decodeRatJson,
        ← j.getObjVal? "fClkHz" >>= decodeRatJson, ← j.getObjVal? "lTraceM" >>= decodeRatJson,
        ← j.getObjVal? "aDiffM2" >>= decodeRatJson, ← j.getObjVal? "solidPlanes" >>= decodeBoolNat,
        ← j.getObjVal? "groundSlot" >>= decodeBoolNat, ← j.getObjNat? "viaPitchUm",
        ← j.getObjNat? "lambdaMinUm", ← j.getObjVal? "planeShieldFactor" >>= decodeRatJson,
        ← j.getObjVal? "kRadOhmM2" >>= decodeRatJson, ← j.getObjVal? "aRxApertureM2" >>= decodeRatJson,
        ← j.getObjVal? "rMinM" >>= decodeRatJson, ← j.getObjVal? "kBTBWatts" >>= decodeRatJson,
        ← j.getObjVal? "rxNoiseFigure" >>= decodeRatJson,
        ← j.getObjNat? "nAvgTraces", ← j.getObjNat? "snrMaxMilli"⟩
def encodeTempestGlitchEmcProblem (prob : TempestGlitchEmcProblem) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("pdn", SosJson.mkObj [ ("dim", .ofNat prob.pdnProblem.spec.dim), ("inputDim", .ofNat prob.pdnProblem.spec.inputDim)
        , ("cDecap", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matC 0 0))
        , ("lPkg", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matC 1 1))
        , ("gBleed", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matG 0 0))
        , ("rPkg", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matG 1 1))
        , ("nSteps", .ofNat prob.pdnProblem.trace.length) ])
    , ("guardRtl", .str prob.guardRtl.name.toList), ("railSpec", encodeRailWindowJson prob.railSpec)
    , ("pcbEnv", encodeTempestPcbJson prob.pcbEnv) ]
def decodeTempestGlitchEmcProblem (wire : String) : Except String TempestGlitchEmcProblem := do
  let root ← sosJsonParse wire; let pdnJ ← root.getObjVal? "pdn"; let dim ← pdnJ.getObjNat? "dim"
  if dim != 2 then .error "expected 2-state PDN RLC MNA specification" else
  let cDecap ← pdnJ.getObjVal? "cDecap" >>= decodeRatJson; let lPkg ← pdnJ.getObjVal? "lPkg" >>= decodeRatJson
  let gBleed ← pdnJ.getObjVal? "gBleed" >>= decodeRatJson; let rPkg ← pdnJ.getObjVal? "rPkg" >>= decodeRatJson
  let nSteps ← pdnJ.getObjNat? "nSteps"
  let trace := if nSteps == 0 then [] else [⟨1, [0, 0], [CanonicalRat.mk 2 5, -(CanonicalRat.mk 1 5)], [1], [], [], 0⟩]
  let rtlName ← root.getObjStr? "guardRtl"
  let guardRtl ← if rtlName == "dual_rail_wddl_guard" then .ok dualRailWddlGuardRtlModule
    else if rtlName == "cyclic_bad_guard" then .ok cyclicBadGuardRtlModule
    else .error s!"unknown Dual-Rail guard RtlModule: {rtlName}"
  pure ⟨⟨pdnDecapRlcSpec cDecap gBleed lPkg rPkg, .backwardEuler, trace⟩, guardRtl,
        ← root.getObjVal? "railSpec" >>= decodeRailWindowJson, ← root.getObjVal? "pcbEnv" >>= decodeTempestPcbJson⟩
def encodeTempestGlitchEmcCert (cert : TempestGlitchEmcCert) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("cW0", sosJsonEncodeRat ((cert.pdnCert.capGramFactors.getD 0 ⟨0, []⟩).weight))
    , ("cW1", sosJsonEncodeRat ((cert.pdnCert.capGramFactors.getD 1 ⟨0, []⟩).weight))
    , ("gW0", sosJsonEncodeRat ((cert.pdnCert.condSymGramFactors.getD 0 ⟨0, []⟩).weight))
    , ("gW1", sosJsonEncodeRat ((cert.pdnCert.condSymGramFactors.getD 1 ⟨0, []⟩).weight))
    , ("prngMaskSeedBits", .ofNat cert.prngMaskSeedBits) ]
def decodeTempestGlitchEmcCert (wire : String) : Except String TempestGlitchEmcCert := do
  let root ← sosJsonParse wire
  let cW0 ← root.getObjVal? "cW0" >>= decodeRatJson; let cW1 ← root.getObjVal? "cW1" >>= decodeRatJson
  let gW0 ← root.getObjVal? "gW0" >>= decodeRatJson; let gW1 ← root.getObjVal? "gW1" >>= decodeRatJson
  pure ⟨⟨[⟨cW0, [1, 0]⟩, ⟨cW1, [0, 1]⟩], [⟨gW0, [1, 0]⟩, ⟨gW1, [0, 1]⟩]⟩, ← root.getObjNat? "prngMaskSeedBits"⟩
/-- Registered `"tempest-glitch-emc@1"` `Judge.Format`. -/
@[expose] def tempestGlitchEmcFormat : Judge.Format where
  name := "tempest-glitch-emc"; version := "1"; Obj := TempestGlitchEmcProblem; Cert := TempestGlitchEmcCert
  judge := tempestGlitchEmcJudge; decodeObj := decodeTempestGlitchEmcProblem; decodeCert := decodeTempestGlitchEmcCert
  trust := .kernel; regime := .decidable
  bad := (groundSlotBadTempestProblem, certifiedTempestGlitchCert); badGrade := 1
  bad_refused := ⟨.groundSlotOrMissingGroundPlanes, [], groundSlotBadTempest_refused 0⟩
/-- Per-aggressor coupling mismatch and bounded signed voltage excursion. -/
structure BusAggressor where
  cp : Rat
  cn : Rat
  tolerance : Rat
  swing : Rat
  deriving DecidableEq, Repr
structure BusTempestSpec where
  lanes : Nat
  groundInductance : Rat
  currentStep : Rat
  aggressors : Array BusAggressor
  xtalkMax : Rat
  deriving DecidableEq, Repr
def hammingTransitions : List Bool → List Bool → Nat
  | p :: ps, q :: qs => (if p == q then 0 else 1) + hammingTransitions ps qs
  | _, _ => 0
def singleRailBusSsn (s : BusTempestSpec) (prev next : List Bool) : Rat :=
  s.groundInductance * s.currentStep * (hammingTransitions prev next : Rat)
def wddlTransitions : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + (if !b then 1 else 0) + wddlTransitions bs
theorem wddlTransitions_eq_length (word : List Bool) : wddlTransitions word = word.length := by
  induction word with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [wddlTransitions, ih, Nat.add_comm]
def wddlBusSsnAndCrosstalk (s : BusTempestSpec) (word : List Bool) : Rat × Rat :=
  (s.groundInductance * s.currentStep * (wddlTransitions word : Rat),
   (s.aggressors.toList.map (fun a => a.tolerance*a.swing)).sum)
theorem balanced_wddl_bus_ssn_secret_independent (s : BusTempestSpec) (a b : List Bool)
    (ha : a.length = s.lanes) (hb : b.length = s.lanes) :
    (wddlBusSsnAndCrosstalk s a).1 = (s.lanes : Rat)*s.groundInductance*s.currentStep ∧
    (wddlBusSsnAndCrosstalk s a).1 = (wddlBusSsnAndCrosstalk s b).1 := by
  simp only [wddlBusSsnAndCrosstalk, wddlTransitions_eq_length, ha, hb]; constructor <;> grind
/-- Nonzero calibrated SSN uniquely reveals the CMOS Hamming transition count. -/
theorem singleRailBusSsn_leaks_count (s : BusTempestSpec) (p q r t : List Bool)
    (h : s.groundInductance*s.currentStep ≠ 0) :
    singleRailBusSsn s p q = singleRailBusSsn s r t ↔ hammingTransitions p q = hammingTransitions r t := by
  unfold singleRailBusSsn; constructor
  · intro he; have hc : (hammingTransitions p q : Rat) = (hammingTransitions r t : Rat) := by grind
    exact Rat.natCast_inj.mp hc
  · intro he; rw [he]
def checkBusTempestEmc (s : BusTempestSpec) : Bool :=
  decide (0 ≤ s.groundInductance ∧ 0 ≤ s.currentStep ∧
    (∀ a ∈ s.aggressors.toList, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp-a.cn) ≤ a.tolerance) ∧
    (s.aggressors.toList.map (fun a => a.tolerance*a.swing)).sum ≤ s.xtalkMax)
def busDifferentialVoltage (as : List BusAggressor) (signal : BusAggressor → Rat) : Rat :=
  (as.map (fun a => (a.cp-a.cn)*signal a)).sum
private theorem abs_mul (a b : Rat) : ratAbs (a*b) = ratAbs a*ratAbs b := by
  have negabs (q : Rat) : ratAbs (-q) = ratAbs q := by unfold ratAbs; split <;> split <;> grind
  by_cases hb : 0 ≤ b
  · rw [ratAbs_mul_nonneg_right a b hb]; simp [ratAbs, hb]
  · have hn : 0 ≤ -b := by grind
    have he : a*b = -(a*(-b)) := by grind
    rw [he, negabs, ratAbs_mul_nonneg_right a (-b) hn]
    simp [ratAbs, hb]
private theorem crosstalk_sum_bound (as : List BusAggressor) (signal : BusAggressor → Rat)
    (h : ∀ a ∈ as, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp-a.cn) ≤ a.tolerance)
    (hv : ∀ a ∈ as, ratAbs (signal a) ≤ a.swing) :
    ratAbs (busDifferentialVoltage as signal) ≤ (as.map (fun a => a.tolerance*a.swing)).sum := by
  induction as with
  | nil => simp [busDifferentialVoltage, ratAbs]
  | cons a as ih =>
    have ha := h a (by simp)
    have hs := hv a (by simp)
    have hi := ih (fun b hb => h b (by simp [hb])) (fun b hb => hv b (by simp [hb]))
    have hp := Rat.mul_le_mul_of_nonneg_right ha.2.2 (ratAbs_nonneg (signal a))
    have hq := Rat.mul_le_mul_of_nonneg_left hs ha.1
    have ht := ratAbs_add_le ((a.cp-a.cn)*signal a) (busDifferentialVoltage as signal)
    rw [abs_mul] at ht
    simp only [busDifferentialVoltage, List.map_cons, List.sum_cons] at *
    grind
theorem checkBusTempestEmc_sound (s : BusTempestSpec) (signal : BusAggressor → Rat)
    (h : checkBusTempestEmc s = true)
    (hv : ∀ a ∈ s.aggressors.toList, ratAbs (signal a) ≤ a.swing) :
    ratAbs (busDifferentialVoltage s.aggressors.toList signal) ≤ s.xtalkMax := by
  simp only [checkBusTempestEmc, decide_eq_true_eq] at h
  exact Rat.le_trans (crosstalk_sum_bound _ signal h.2.2.1 hv) h.2.2.2
/-- Bus EMC is an additional physical envelope paired with the existing device checker. -/
def checkTempestGlitchBus (grade : Nat) (p : TempestGlitchEmcProblem) (c : TempestGlitchEmcCert)
    (bus : BusTempestSpec) : Bool := (checkTempestGlitchEmc grade p c == .ok) && checkBusTempestEmc bus
theorem checkTempestGlitchBus_sound (grade : Nat) (p : TempestGlitchEmcProblem) (c : TempestGlitchEmcCert)
    (bus : BusTempestSpec) (signal : BusAggressor → Rat) (h : checkTempestGlitchBus grade p c bus = true)
    (hv : ∀ a ∈ bus.aggressors.toList, ratAbs (signal a) ≤ a.swing) :
    TempestGlitchEmcMeaning p c ∧ ratAbs (busDifferentialVoltage bus.aggressors.toList signal) ≤ bus.xtalkMax := by
  simp only [checkTempestGlitchBus, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨checkTempestGlitchEmc_sound h.1, checkBusTempestEmc_sound bus signal h.2 hv⟩
theorem checkBusTempestEmc_complete (s : BusTempestSpec)
    (hg : 0 ≤ s.groundInductance) (hc : 0 ≤ s.currentStep)
    (ha : ∀ a ∈ s.aggressors.toList, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp-a.cn) ≤ a.tolerance)
    (hx : (s.aggressors.toList.map (fun a => a.tolerance*a.swing)).sum ≤ s.xtalkMax) :
    checkBusTempestEmc s = true :=
  decide_eq_true ⟨hg, hc, ha, hx⟩
theorem checkTempestGlitchBus_complete {p : TempestGlitchEmcProblem} {bus : BusTempestSpec}
    (hEx : ∃ c, TempestGlitchEmcMeaning p c)
    (hg : 0 ≤ bus.groundInductance) (hc : 0 ≤ bus.currentStep)
    (ha : ∀ a ∈ bus.aggressors.toList, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp-a.cn) ≤ a.tolerance)
    (hx : (bus.aggressors.toList.map (fun a => a.tolerance*a.swing)).sum ≤ bus.xtalkMax) :
    ∃ c r, checkTempestGlitchBus r p c bus = true := by
  obtain ⟨c, r, hOk⟩ := checkTempestGlitchEmc_complete hEx
  exact ⟨c, r, by simp [checkTempestGlitchBus, hOk, checkBusTempestEmc_complete bus hg hc ha hx]⟩
theorem symmetric_bus_crosstalk_cancels (as : List BusAggressor) (signal : BusAggressor → Rat)
    (h : ∀ a ∈ as, a.cp = a.cn) : busDifferentialVoltage as signal = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun b hb => h b (by simp [hb]))
    simp only [busDifferentialVoltage, List.map_cons, List.sum_cons] at *
    rw [ha, Rat.sub_self, Rat.zero_mul, Rat.zero_add]; exact hi
end Obend.Hardware.GlitchAndTempestSafe
end
