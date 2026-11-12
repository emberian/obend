module
public import Obend.Hardware.HDL
public import Obend.Hardware.Cic
public import Obend.Hardware.SwitchedCapRf
public import Obend.Elab.AutoCertTaylorSound
public import Obend.Judge.RealAnalysis
/-!
# The SDR-FT8 receive chain as hardware, with its signoff (`Obend.Apps.SdrFt8Rx`)
Three `RtlModule`s, emitted by `obend-emit-sv` (`sdr-nco`, `sdr-cic`, `sdr-disc`) into
`apps/sdr-ft8/verilator/` and LEC'd against these definitions by `verify_sdr_ft8.sh`, which also runs
a public FT8 recording through them:
* `sdrNcoModule`: the tuning NCO (32-bit phase accumulator, octant fold, Q30 polynomial phasor,
  complex mix); `nco_phasor_error` bounds its phasor against `cos`/`sin` (`taylor-model@1`).
* `sdrCicModule`: Hogenauer's CIC decimator, `N = 3, R = 64, M = 1`, 34-bit registers;
  `sdrCic_output_exact` says its output is exact (`Obend.Hardware.Cic` is the general theory).
* `sdrFt8DiscModule`: the FT8 tone discriminator (lag-2 conjugate product per symbol, 12-stage CORDIC,
  slicer); `ft8_bin_of_tone`, `ft8_bin_range`, `binExpr_correct` are the slicer's theorems.
`sdr_irr_ge_63dB` is the front end's image rejection after calibration (`interval@1`, `taylor-model@1`).
The CORDIC's angle is no longer taken as given: `Obend.Hardware.SwitchedCapRf.cordic_residual_cone`
bounds the 12-stage integer CORDIC (the table and iteration the discriminator's wires instantiate),
and `ft8_iq_cordic_slicer_exact_tone` carries it through the slicer: a correlation phasor inside tone
`k`'s cone is decided `k`. `disc_angle_eq_cordicAtan2` says the discriminator's angle wire is that
integer function of the accumulator registers, so the weld holds of the RTL (`disc_tone_exact`).
`sdrFt8RxTopModule` is the whole chain on one clock, the discriminator enabled by the decimation
strobe: `sdrFt8RxTop_step_refines` and `top_disc_wires` relate it to the three modules, and
`top_tone_latch` is the weld in it.
-/
public section
namespace Obend.Apps.SdrFt8Rx
open Obend.Hardware.HDL
open Obend.Hardware.Cic
set_option autoImplicit false
def trunc34 (e : RtlExpr) : RtlExpr := .resize (.trunc 34) e
def cicReg (i : Nat) (n : String) (e : RtlExpr) : RegSpec :=
  { regIdx := i, name := n, domain := .coreClk, resetKind := .syncReset 0#64,
    isSynchronizer := false, nextExpr := e, width := 34 }
@[expose] def sdrCicModule : RtlModule where
  name := "sdr_cic3_r64"
  inputNames := ["x_in", "decim_strobe"]
  inputWidths := [16, 1]
  wires :=
    [ { wireIdx := 0, name := "x_sext", expr := .resize (.sext 16 34) (.inputPort 0), width := 34 }
    , { wireIdx := 1, name := "comb1", expr := trunc34 (.alu .sub (.regRead 2) (.regRead 3)), width := 34 }
    , { wireIdx := 2, name := "comb2", expr := trunc34 (.alu .sub (.wireRef 1) (.regRead 4)), width := 34 }
    , { wireIdx := 3, name := "comb3", expr := trunc34 (.alu .sub (.wireRef 2) (.regRead 5)), width := 34 } ]
  regs :=
    [ cicReg 0 "int1" (trunc34 (.alu .add (.regRead 0) (.wireRef 0)))
    , cicReg 1 "int2" (trunc34 (.alu .add (.regRead 1) (.regRead 0)))
    , cicReg 2 "int3" (trunc34 (.alu .add (.regRead 2) (.regRead 1)))
    , cicReg 3 "comb_d1" (.mux (.inputPort 1) (.regRead 2) (.regRead 3))
    , cicReg 4 "comb_d2" (.mux (.inputPort 1) (.wireRef 1) (.regRead 4))
    , cicReg 5 "comb_d3" (.mux (.inputPort 1) (.wireRef 2) (.regRead 5))
    , cicReg 6 "cic_out_q" (.mux (.inputPort 1) (.wireRef 3) (.regRead 6)) ]
  outputs := [{ name := "cic_out", expr := .regRead 6, width := 34 }]
example : checkRtlModuleW sdrCicModule = true := by decide +kernel
def sx (a : BitVec 64) : BitVec 64 := evalWidthOp (.sext 16 34) a
def sel (s a b : BitVec 64) : BitVec 64 := if s != 0#64 then a else b
theorem step_eq (inp st : Nat → BitVec 64) :
    let t := stepModuleRegs sdrCicModule false inp st
    let c1 := truncToWidth 34 (st 2 - st 3)
    let c2 := truncToWidth 34 (c1 - st 4)
    let c3 := truncToWidth 34 (c2 - st 5)
    t 0 = truncToWidth 34 (st 0 + sx (inp 0)) ∧
    t 1 = truncToWidth 34 (st 1 + st 0) ∧
    t 2 = truncToWidth 34 (st 2 + st 1) ∧
    t 3 = sel (inp 1) (st 2) (st 3) ∧
    t 4 = sel (inp 1) c1 (st 4) ∧
    t 5 = sel (inp 1) c2 (st 5) ∧
    t 6 = sel (inp 1) c3 (st 6) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
/-! ### Arithmetic of the 34-bit registers -/
abbrev M34 : Int := 2 ^ 34
theorem natCast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by
  rw [Int.natCast_pow]; rfl
theorem trunc_add_val (a b : BitVec 64) :
    ((truncToWidth 34 (a + b)).toNat : Int) = ((a.toNat : Int) + b.toNat) % M34 := by
  rw [truncToWidth_toNat 34 (by decide), BitVec.toNat_add,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 34 ∣ 2 ^ 64), Int.natCast_emod, natCast_two_pow]
  push_cast; rfl
theorem trunc_sub_val (a b : BitVec 64) :
    ((truncToWidth 34 (a - b)).toNat : Int) = ((a.toNat : Int) - b.toNat) % M34 := by
  rw [truncToWidth_toNat 34 (by decide), BitVec.toNat_sub,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 34 ∣ 2 ^ 64), Int.natCast_emod, natCast_two_pow]
  have hb := b.isLt
  have e : ((2 ^ 64 - b.toNat + a.toNat : Nat) : Int) = ((a.toNat : Int) - b.toNat) + M34 * 2 ^ 30 := by
    have : ((2 ^ 64 - b.toNat : Nat) : Int) = (2 : Int) ^ 64 - b.toNat := by
      rw [Int.ofNat_sub (Nat.le_of_lt hb), natCast_two_pow]
    push_cast [this]
    show (2 : Int) ^ 64 - (b.toNat : Int) + a.toNat = (a.toNat : Int) - b.toNat + (2 : Int) ^ 34 * (2 : Int) ^ 30
    rw [← Int.pow_add]; omega
  rw [e, Int.add_mul_emod_self_left]
theorem trunc_add_mod (a b : BitVec 64) (A B : Int) (ha : (a.toNat : Int) = A % M34)
    (hb : (b.toNat : Int) = B % M34) : ((truncToWidth 34 (a + b)).toNat : Int) = (A + B) % M34 := by
  rw [trunc_add_val, ha, hb, ← Int.add_emod]
theorem trunc_sub_mod (a b : BitVec 64) (A B : Int) (ha : (a.toNat : Int) = A % M34)
    (hb : (b.toNat : Int) = B % M34) : ((truncToWidth 34 (a - b)).toNat : Int) = (A - B) % M34 := by
  rw [trunc_sub_val, ha, hb, ← Int.sub_emod]
theorem val_mod_self (a : BitVec 64) (h : a.toNat < 2 ^ 34) : ((a.toNat : Int)) % M34 = a.toNat := by
  apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
  have : ((a.toNat : Nat) : Int) < ((2 ^ 34 : Nat) : Int) := Int.ofNat_lt.mpr h
  rw [natCast_two_pow] at this; exact this
/-- The sample input as the module sees it: the 16-bit two's-complement word, zero-extended to the
64-bit carrier. -/
def xin (v : Int) : BitVec 64 := (BitVec.ofInt 16 v).setWidth 64
theorem sx_xin_val (v : Int) (hv : -(2 : Int) ^ 15 ≤ v ∧ v < (2 : Int) ^ 15) :
    ((sx (xin v)).toNat : Int) = v % M34 := by
  show ((((BitVec.ofInt 16 v).setWidth 64).setWidth 16).signExtend 34 |>.setWidth 64).toNat = v % M34
  rw [BitVec.setWidth_setWidth (by omega), BitVec.setWidth_eq]
  let y : BitVec 34 := (BitVec.ofInt 16 v).signExtend 34
  have hy : y.toInt = v := by
    show ((BitVec.ofInt 16 v).signExtend 34).toInt = v
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le
    · have : ((2 ^ 16 : Nat) : Int) / 2 = (2 : Int) ^ 15 := by decide
      rw [this]; exact hv.1
    · have : (((2 ^ 16 : Nat) : Int) + 1) / 2 = (2 : Int) ^ 15 := by decide
      rw [this]; exact hv.2
  have hlt : y.toNat < 2 ^ 34 := y.isLt
  have h64 : (y.setWidth 64).toNat = y.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))
  show (((BitVec.ofInt 16 v).signExtend 34).setWidth 64).toNat = v % M34
  change ((y.setWidth 64).toNat : Int) = v % M34
  rw [h64, ← hy, BitVec.toInt_eq_toNat_bmod]
  have hm : M34 = ((2 ^ 34 : Nat) : Int) := (natCast_two_pow 34).symm
  rw [hm, Int.bmod_emod]
  have h0 : (0 : Int) ≤ y.toNat := Int.natCast_nonneg _
  have h1 : (y.toNat : Int) < ((2 ^ 34 : Nat) : Int) := Int.ofNat_lt.mpr hlt
  rw [Int.emod_eq_of_lt h0 h1]
/-! ### The run of the module on a sample stream -/
/-- The decimation strobe of `R = 64`: high on cycles `0, 64, 128, …`. -/
def strobe (n : Nat) : BitVec 64 := if n % 64 = 0 then 1#64 else 0#64
/-- The module's inputs at cycle `n`: sample `x n` on port 0, the strobe on port 1. -/
def cicInputs (x : Signal) (n : Nat) : Nat → BitVec 64 :=
  fun i => if i = 0 then xin (x n) else if i = 1 then strobe n else 0#64
/-- The register file after `n` clock edges from the reset state (every register's reset value is `0`). -/
def cicRun (x : Signal) : Nat → (Nat → BitVec 64)
  | 0 => fun _ => 0#64
  | n + 1 => stepModuleRegs sdrCicModule false (cicInputs x n) (cicRun x n)
/-- One reset edge from any state gives the state `cicRun` starts from. -/
theorem reset_state (inp st : Nat → BitVec 64) (i : Nat) (hi : i < 7) :
    stepModuleRegs sdrCicModule true inp st i = 0#64 := by
  match i, hi with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
/-- Delay by one decimated sample, zero history. -/
def lag (s : Signal) : Signal
  | 0 => 0
  | k + 1 => s k
theorem comb_one_eq_lag (s : Signal) (q : Nat) : comb 1 s q = s q - lag s q := by
  cases q with
  | zero => simp [comb, lag]
  | succ q => simp [comb, lag]
/-- The exact (unbounded) register values: the integrators `cum x`, `cum² x`, `cum³ x`, the
integrator sampled at the strobes `u`, and the comb outputs. -/
def u (x : Signal) : Signal := fun q => cum (cum (cum x)) (q * 64)
def c1 (x : Signal) : Signal := comb 1 (u x)
def c2 (x : Signal) : Signal := comb 1 (c1 x)
def c3 (x : Signal) : Signal := comb 1 (c2 x)
theorem c3_eq_cicOut (x : Signal) : c3 x = cicOut 64 1 3 x := by rfl
/-- Strobes seen before cycle `n`. -/
def cnt (n : Nat) : Nat := (n + 63) / 64
def val (st : Nat → BitVec 64) (i : Nat) : Int := ((st i).toNat : Int)
/-- **Every register holds its exact value modulo `2^34`.** The integrators wrap (their exact values
grow without bound); the comb delays and the output hold the exact comb values of the strobes seen. -/
def Inv (x : Signal) (n : Nat) (st : Nat → BitVec 64) : Prop :=
  val st 0 = cum x n % M34 ∧
  val st 1 = cum (cum x) n % M34 ∧
  val st 2 = cum (cum (cum x)) n % M34 ∧
  val st 3 = lag (u x) (cnt n) % M34 ∧
  val st 4 = lag (c1 x) (cnt n) % M34 ∧
  val st 5 = lag (c2 x) (cnt n) % M34 ∧
  val st 6 = lag (c3 x) (cnt n) % M34
theorem inv_zero (x : Signal) : Inv x 0 (cicRun x 0) := by
  simp [Inv, val, cicRun, cnt, lag]
theorem sel_one (a b : BitVec 64) : sel 1#64 a b = a := by rfl
theorem sel_zero (a b : BitVec 64) : sel 0#64 a b = b := by rfl
theorem inv_succ (x : Signal) (hx : ∀ n, -(2 : Int) ^ 15 ≤ x n ∧ x n < (2 : Int) ^ 15) (n : Nat)
    (h : Inv x n (cicRun x n)) : Inv x (n + 1) (cicRun x (n + 1)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := step_eq (cicInputs x n) (cicRun x n)
  have hin0 : cicInputs x n 0 = xin (x n) := rfl
  have hin1 : cicInputs x n 1 = strobe n := rfl
  simp only [cicRun] at *
  unfold val at h0 h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold val; rw [s0, trunc_add_val, h0, hin0, sx_xin_val _ (hx n), cum_succ, ← Int.add_emod]
  · unfold val; rw [s1, trunc_add_val, h1, h0, cum_succ, ← Int.add_emod]
  · unfold val; rw [s2, trunc_add_val, h2, h1, cum_succ, ← Int.add_emod]
  · rw [hin1] at s3 s4 s5 s6
    by_cases hs : n % 64 = 0
    · have hq : cnt (n + 1) = cnt n + 1 := by unfold cnt; omega
      have hn : cnt n * 64 = n := by unfold cnt; omega
      have hst : strobe n = 1#64 := by simp [strobe, hs]
      rw [hst, sel_one] at s3 s4 s5 s6
      have hu : u x (cnt n) = cum (cum (cum x)) n := by simp only [u, hn]
      have v1 : ((truncToWidth 34 (cicRun x n 2 - cicRun x n 3)).toNat : Int) = c1 x (cnt n) % M34 := by
        rw [trunc_sub_mod _ _ _ _ h2 h3, c1, comb_one_eq_lag, hu]
      have v2 : ((truncToWidth 34 (truncToWidth 34 (cicRun x n 2 - cicRun x n 3) - cicRun x n 4)).toNat : Int)
          = c2 x (cnt n) % M34 := by
        rw [trunc_sub_mod _ _ _ _ v1 h4, c2, comb_one_eq_lag]
      have v3 : ((truncToWidth 34 (truncToWidth 34 (truncToWidth 34 (cicRun x n 2 - cicRun x n 3) - cicRun x n 4)
          - cicRun x n 5)).toNat : Int) = c3 x (cnt n) % M34 := by
        rw [trunc_sub_mod _ _ _ _ v2 h5, c3, comb_one_eq_lag]
      unfold val
      rw [hq, s3, s4, s5, s6, v1, v2, v3, h2, ← hu]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have hq : cnt (n + 1) = cnt n := by unfold cnt; omega
      have hst : strobe n = 0#64 := by simp [strobe, hs]
      rw [hst, sel_zero] at s3 s4 s5 s6
      unfold val
      rw [hq, s3, s4, s5, s6]
      exact ⟨h3, h4, h5, h6⟩
theorem inv_all (x : Signal) (hx : ∀ n, -(2 : Int) ^ 15 ≤ x n ∧ x n < (2 : Int) ^ 15) :
    ∀ n, Inv x n (cicRun x n)
  | 0 => inv_zero x
  | n + 1 => inv_succ x hx n (inv_all x hx n)
/-- **The SDR's CIC decimator RTL computes Hogenauer's CIC exactly, in 34-bit registers.**
For every stream of 16-bit two's-complement samples `x` and every clock cycle `n`, after the edge
of cycle `n` the 34-bit output register `cic_out` of `sdrCicModule`, read as a signed 34-bit
number, is the exact output of the `N = 3, R = 64, M = 1` CIC for decimation index `⌊n / 64⌋`,
which is the triple moving sum of length 64 of the input sampled at `64·⌊n/64⌋` and lies in
`[-2^33, 2^33)`. No register is wider than 34 bits, and none needs to be: the integrators wrap
modulo `2^34` (`Inv`) and the output is still exact. -/
theorem sdrCic_output_exact (x : Signal) (hx : ∀ n, -(2 : Int) ^ 15 ≤ x n ∧ x n < (2 : Int) ^ 15) (n : Nat) :
    ((cicRun x (n + 1) 6).setWidth 34).toInt = cicOut 64 1 3 x (n / 64) ∧
    cicOut 64 1 3 x (n / 64) = stages (movingSum 64) 3 x (n / 64 * 64) ∧
    -(2 : Int) ^ 33 ≤ cicOut 64 1 3 x (n / 64) ∧ cicOut 64 1 3 x (n / 64) < (2 : Int) ^ 33 := by
  have hI := (inv_all x hx (n + 1)).2.2.2.2.2.2
  have hc : cnt (n + 1) = n / 64 + 1 := by unfold cnt; omega
  rw [hc] at hI
  simp only [lag] at hI
  have hw : Congr (3 * 6 + 15 + 1) (fun m => if m = n / 64 then val (cicRun x (n + 1)) 6 else cicOut 64 1 3 x m)
      (cicOut 64 1 3 x) := by
    intro m
    by_cases hm : m = n / 64
    · subst hm; simp only [↓reduceIte]; rw [hI, c3_eq_cicOut, Int.emod_emod]
    · simp only [hm, ↓reduceIte]
  have hR := cic_register_width 64 1 3 6 15 (by decide) (by decide) x hx _ hw (n / 64)
  simp only [↓reduceIte] at hR
  refine ⟨?_, cicOut_eq_movingSum 64 1 3 (by decide) x _, hR.1.1, hR.1.2⟩
  rw [BitVec.toInt_setWidth]
  exact hR.2
/-! ## The FT8 tone discriminator
At the CIC's output rate `12000 / 64 = 187.5` samples/s an FT8 symbol (160 ms) is exactly 30
samples, and with the receiver tuned so that tone 0 sits at 0 Hz, tone `k` (`k·6.25` Hz) turns the
phasor by `2π·k·6.25·2 / 187.5 = k·2π/15` radians across a lag of two samples. The discriminator
accumulates `P = Σ z[n]·conj(z[n-2])` over a symbol, takes `angle P` with a 12-stage vectoring
CORDIC (in µrad), and slices it against the seven midpoints `(2k-1)·π/15`. -/
/-- `atan(2^-i)` in µrad, `i = 0..11`: the table `cordicAtan2` is proved for. -/
def cordicAtanUrad : List Int := Obend.Hardware.SwitchedCapRf.cordicLutUrad
def piUrad : Int := Obend.Hardware.SwitchedCapRf.cordicPiUrad
/-- The slicer thresholds `(2k-1)·π/15` in µrad, `k = 1..7` (rounded to the nearest µrad). -/
def ft8Thresholds : List Int := [209440, 628319, 1047198, 1466077, 1884956, 2303835, 2722714]
/-- The tone the slicer decides for an angle `a` (µrad): the number of thresholds at or below `a`. -/
@[expose] def ft8Bin (a : Int) : Nat := (ft8Thresholds.filter (fun t => decide (t ≤ a))).length
/-- Out of band: more than half a tone spacing below tone 0. -/
@[expose] def ft8Oob (a : Int) : Bool := decide (a < -209440)
/-- Tone `k`'s angle over the lag, `k·2π/15` rad, in µrad (`2π/15 = 0.41887902…`). -/
def toneUrad (k : Nat) : Int := 418879 * k
def ci (v : Int) : RtlExpr := .const (BitVec.ofInt 64 v)
def slt (a b : RtlExpr) : RtlExpr := .alu .slt a b
def neg (a : RtlExpr) : RtlExpr := .alu .sub (ci 0) a
def addE (a b : RtlExpr) : RtlExpr := .alu .add a b
def subE (a b : RtlExpr) : RtlExpr := .alu .sub a b
def ashrE (a : RtlExpr) (k : Nat) : RtlExpr := .alu .ashr a (ci k)
def ge1 (a : RtlExpr) (t : Int) : RtlExpr := .alu .bitXor (slt a (ci t)) (ci 1)
/-- The slicer as hardware: the sum of the seven comparator bits `a ≥ T_k`. -/
def binExpr (a : RtlExpr) : RtlExpr :=
  .resize (.trunc 3)
    (addE (addE (addE (ge1 a 209440) (ge1 a 628319)) (addE (ge1 a 1047198) (ge1 a 1466077)))
      (addE (addE (ge1 a 1884956) (ge1 a 2303835)) (ge1 a 2722714)))
def oobExpr (a : RtlExpr) : RtlExpr := slt a (ci (-209440))
/-- One vectoring CORDIC stage on wires `x, y, z` (indices), shift `i`, angle `ai`. -/
def cordicStage (base x y z : Nat) (i : Nat) (ai : Int) : List WireAssign :=
  let yn := slt (.wireRef y) (ci 0)
  [ { wireIdx := base, name := s!"cx{i+1}",
      expr := .mux yn (subE (.wireRef x) (ashrE (.wireRef y) i)) (addE (.wireRef x) (ashrE (.wireRef y) i)) }
  , { wireIdx := base + 1, name := s!"cy{i+1}",
      expr := .mux yn (addE (.wireRef y) (ashrE (.wireRef x) i)) (subE (.wireRef y) (ashrE (.wireRef x) i)) }
  , { wireIdx := base + 2, name := s!"cz{i+1}",
      expr := .mux yn (subE (.wireRef z) (ci ai)) (addE (.wireRef z) (ci ai)) } ]
/-- The CORDIC stages; the last stage computes only the angle and the one before it no `x`
(nothing reads them). -/
def cordicWires : Nat → List Int → Nat → Nat → Nat → Nat → List WireAssign
  | _, [], _, _, _, _ => []
  | i, [a], base, _, y, z =>
    [ { wireIdx := base, name := s!"cz{i+1}",
        expr := .mux (slt (.wireRef y) (ci 0)) (subE (.wireRef z) (ci a)) (addE (.wireRef z) (ci a)) } ]
  | i, [a, b], base, x, y, z =>
    let yn := slt (.wireRef y) (ci 0)
    [ { wireIdx := base, name := s!"cy{i+1}",
        expr := .mux yn (addE (.wireRef y) (ashrE (.wireRef x) i)) (subE (.wireRef y) (ashrE (.wireRef x) i)) }
    , { wireIdx := base + 1, name := s!"cz{i+1}",
        expr := .mux yn (subE (.wireRef z) (ci a)) (addE (.wireRef z) (ci a)) } ]
    ++ cordicWires (i + 1) [b] (base + 2) 0 base (base + 1)
  | i, a :: as, base, x, y, z => cordicStage base x y z i a ++ cordicWires (i + 1) as (base + 3) base (base + 1) (base + 2)
def discReg (i : Nat) (n : String) (e : RtlExpr) (w : Nat := 64) : RegSpec :=
  { regIdx := i, name := n, domain := .coreClk, resetKind := .syncReset 0#64,
    isSynchronizer := false, nextExpr := e, width := w }
/-- Index of the CORDIC's final angle wire. -/
def angleWire : Nat := 9 + 3 * 10 + 2
@[expose] def sdrFt8DiscModule : RtlModule where
  name := "sdr_ft8_disc"
  inputNames := ["i_cic", "q_cic", "acc_clr", "acc_en", "sym_latch"]
  inputWidths := [34, 34, 1, 1, 1]
  wires :=
    [ { wireIdx := 0, name := "zi", expr := ashrE (.resize (.sext 34 64) (.inputPort 0)) 18 }
    , { wireIdx := 1, name := "zq", expr := ashrE (.resize (.sext 34 64) (.inputPort 1)) 18 }
    , { wireIdx := 2, name := "prod_re",
        expr := addE (.alu .mul (.wireRef 0) (.regRead 2)) (.alu .mul (.wireRef 1) (.regRead 3)) }
    , { wireIdx := 3, name := "prod_im",
        expr := subE (.alu .mul (.wireRef 1) (.regRead 2)) (.alu .mul (.wireRef 0) (.regRead 3)) }
    , { wireIdx := 4, name := "acc_re_next",
        expr := addE (.mux (.inputPort 2) (ci 0) (.regRead 4)) (.mux (.inputPort 3) (.wireRef 2) (ci 0)) }
    , { wireIdx := 5, name := "acc_im_next",
        expr := addE (.mux (.inputPort 2) (ci 0) (.regRead 5)) (.mux (.inputPort 3) (.wireRef 3) (ci 0)) }
    , { wireIdx := 6, name := "cx0",
        expr := .mux (slt (.regRead 4) (ci 0)) (neg (.regRead 4)) (.regRead 4) }
    , { wireIdx := 7, name := "cy0",
        expr := .mux (slt (.regRead 4) (ci 0)) (neg (.regRead 5)) (.regRead 5) }
    , { wireIdx := 8, name := "cz0",
        expr := .mux (slt (.regRead 4) (ci 0)) (.mux (slt (.regRead 5) (ci 0)) (ci (-piUrad)) (ci piUrad)) (ci 0) } ]
    ++ cordicWires 0 cordicAtanUrad 9 6 7 8
  regs :=
    [ discReg 0 "zi_d1" (.wireRef 0)
    , discReg 1 "zq_d1" (.wireRef 1)
    , discReg 2 "zi_d2" (.regRead 0)
    , discReg 3 "zq_d2" (.regRead 1)
    , discReg 4 "acc_re" (.wireRef 4)
    , discReg 5 "acc_im" (.wireRef 5)
    , discReg 6 "tone_bin_q" (.mux (.inputPort 4) (binExpr (.wireRef angleWire)) (.regRead 6)) 3
    , discReg 7 "tone_oob_q" (.mux (.inputPort 4) (oobExpr (.wireRef angleWire)) (.regRead 7)) 1
    , discReg 8 "angle_urad_q" (.mux (.inputPort 4) (.resize (.trunc 32) (.wireRef angleWire)) (.regRead 8)) 32 ]
  outputs :=
    [ { name := "tone_bin", expr := .regRead 6, width := 3 }
    , { name := "tone_oob", expr := .regRead 7, width := 1 }
    , { name := "angle_urad", expr := .regRead 8, width := 32 } ]
example : checkRtlModuleW sdrFt8DiscModule = true := by decide +kernel
/-! ### The slicer -/
theorem ft8Bin_eq (a : Int) :
    ft8Bin a = (if 209440 ≤ a then 1 else 0) + (if 628319 ≤ a then 1 else 0) + (if 1047198 ≤ a then 1 else 0) +
      (if 1466077 ≤ a then 1 else 0) + (if 1884956 ≤ a then 1 else 0) + (if 2303835 ≤ a then 1 else 0) +
      (if 2722714 ≤ a then 1 else 0) := by
  simp only [ft8Bin, ft8Thresholds, List.filter_cons, List.filter_nil, decide_eq_true_eq]
  split <;> split <;> split <;> split <;> split <;> split <;> split <;> simp_all <;> omega
/-- **Tone bins.** If the measured angle is within `209438` µrad (half a tone spacing, less the
rounding of the thresholds) of tone `k`'s angle `k·2π/15`, the slicer decides `k` and does not flag
the symbol out of band. -/
theorem ft8_bin_of_tone (k : Nat) (hk : k ≤ 7) (a : Int)
    (ha : toneUrad k - 209438 ≤ a ∧ a ≤ toneUrad k + 209438) :
    ft8Bin a = k ∧ ft8Oob a = false := by
  unfold toneUrad at ha
  rw [ft8Bin_eq]
  simp only [ft8Oob, decide_eq_false_iff_not]
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk' with h | h | h | h | h | h | h | h <;> subst h <;>
    (constructor; (repeat' split) <;> omega; omega)
/-- **Every angle lands in a bin `0..7`.** Out of band is exactly `a < -209440`; above the top
threshold every angle is tone 7. -/
theorem ft8_bin_range (a : Int) : ft8Bin a ≤ 7 ∧ (ft8Oob a = true ↔ a < -209440) := by
  refine ⟨?_, by simp [ft8Oob]⟩
  rw [ft8Bin_eq]; (repeat' split) <;> omega
/-- The tone spacing over the lag at the design's rates: `6.25 Hz · 2 samples / (12000 / 64 Hz) = 1/15`
of a turn, so tone `k` turns the lag-2 product by `k·2π/15`. -/
theorem ft8_tone_turn : (625 : Nat) * 2 * 64 * 15 = 12000 * 100 := by decide
theorem toInt_ofInt64 (v : Int) (h1 : -(2 : Int) ^ 63 ≤ v) (h2 : v < (2 : Int) ^ 63) :
    (BitVec.ofInt 64 v).toInt = v := by
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le
  · have : ((2 ^ 64 : Nat) : Int) / 2 = (2 : Int) ^ 63 := by decide
    rw [this]; exact h1
  · have : (((2 ^ 64 : Nat) : Int) + 1) / 2 = (2 : Int) ^ 63 := by decide
    rw [this]; exact h2
theorem eval_ge1 (inp w r : Nat → BitVec 64) (e : RtlExpr) (t : Int) (ht1 : -(2 : Int) ^ 63 ≤ t) (ht2 : t < (2 : Int) ^ 63) :
    evalRtlExpr inp w r (ge1 e t) = if t ≤ (evalRtlExpr inp w r e).toInt then 1#64 else 0#64 := by
  simp only [ge1, slt, ci, evalRtlExpr, evalAluOp]
  by_cases h : t ≤ (evalRtlExpr inp w r e).toInt
  · have : ¬ (BitVec.slt (evalRtlExpr inp w r e) (BitVec.ofInt 64 t) = true) := by
      rw [BitVec.slt_iff_toInt_lt, toInt_ofInt64 t ht1 ht2]; omega
    simp only [this, h, Bool.false_eq_true, ↓reduceIte]; decide
  · have : BitVec.slt (evalRtlExpr inp w r e) (BitVec.ofInt 64 t) = true := by
      rw [BitVec.slt_iff_toInt_lt, toInt_ofInt64 t ht1 ht2]; omega
    simp only [this, h, ↓reduceIte]; decide
/-- **The slicer hardware computes `ft8Bin`.** For any value `a` of its input (the CORDIC angle,
read as a signed 64-bit number), `binExpr` evaluates to `ft8Bin a` and `oobExpr` to `ft8Oob a`. -/
theorem binExpr_correct (inp w r : Nat → BitVec 64) (e : RtlExpr) :
    evalRtlExpr inp w r (binExpr e) = BitVec.ofNat 64 (ft8Bin (evalRtlExpr inp w r e).toInt) ∧
    evalRtlExpr inp w r (oobExpr e) = (if ft8Oob (evalRtlExpr inp w r e).toInt then 1#64 else 0#64) := by
  constructor
  · simp only [binExpr, addE, evalRtlExpr, evalWidthOp, evalAluOp]
    rw [eval_ge1 _ _ _ _ _ (by decide) (by decide), eval_ge1 _ _ _ _ _ (by decide) (by decide),
      eval_ge1 _ _ _ _ _ (by decide) (by decide), eval_ge1 _ _ _ _ _ (by decide) (by decide),
      eval_ge1 _ _ _ _ _ (by decide) (by decide), eval_ge1 _ _ _ _ _ (by decide) (by decide),
      eval_ge1 _ _ _ _ _ (by decide) (by decide), ft8Bin_eq]
    generalize (evalRtlExpr inp w r e).toInt = a
    (repeat' split) <;> first | omega | decide
  · simp only [oobExpr, slt, ci, evalRtlExpr, evalAluOp, ft8Oob]
    by_cases h : (evalRtlExpr inp w r e).toInt < -209440
    · have : BitVec.slt (evalRtlExpr inp w r e) (BitVec.ofInt 64 (-209440)) = true := by
        rw [BitVec.slt_iff_toInt_lt, toInt_ofInt64 _ (by decide) (by decide)]; exact h
      simp only [this, h, decide_true, ↓reduceIte]
    · have : ¬ BitVec.slt (evalRtlExpr inp w r e) (BitVec.ofInt 64 (-209440)) = true := by
        rw [BitVec.slt_iff_toInt_lt, toInt_ofInt64 _ (by decide) (by decide)]; exact h
      simp only [this, h, decide_false, Bool.false_eq_true, ↓reduceIte]
/-! ## The tuning NCO
A 32-bit phase accumulator; the phase word's top three bits are the octant and the next twelve
`t`, so the angle inside the octant is `δ = (t / 4096)·(π/4)`. Odd octants use `4096 - t`
(`π/4 - δ`), so the polynomial core only ever sees `θ = (tt / 4096)·(π/4)`, `tt ∈ 0..4096`, that
is `θ ∈ [0, π/4]`. The core evaluates `cos θ ≈ 1 - (θ²/2) + θ⁴/24` and
`sin θ ≈ θ - θ³/6 + θ⁵/120` in Q30 by Horner's rule in `s = tt/4096`; the octant swaps and
negates the pair, and the mixer multiplies the sample by `cos Θ - j sin Θ`. Each Horner step is its
own wire, so no emitted expression nests an arithmetic shift inside the operand of another: Verilator
5.050 evaluates `64'($signed(b * (c + 64'($signed(a) >>> k))) >>> j)` with the inner shift logical,
which `evalRtlExpr` (and IEEE 1800's cast rule) do not. -/
/-- Q30 coefficients of the core polynomials in `s = θ / (π_r/4)`, `π_r = 355/113`:
`A2 = 2^30·a²/2`, `A4 = 2^30·a⁴/24`, `B1 = 2^30·a`, `B3 = 2^30·a³/6`, `B5 = 2^30·a⁵/120`, `a = π_r/4`,
each rounded to the nearest integer. -/
def ncoA2 : Int := 331169026
def ncoA4 : Int := 17023478
def ncoB1 : Int := 843314928
def ncoB3 : Int := 86699856
def ncoB5 : Int := 2674042
def mulE (a b : RtlExpr) : RtlExpr := .alu .mul a b
/-- Q30 product: `(a·b) >>> 30`. -/
def q30 (a b : RtlExpr) : RtlExpr := ashrE (mulE a b) 30
def sliceE (hi lo : Nat) (a : RtlExpr) : RtlExpr := .resize (.slice hi lo) a
def ncoWire (i : Nat) (n : String) (e : RtlExpr) : WireAssign := { wireIdx := i, name := n, expr := e }
@[expose] def sdrNcoModule : RtlModule where
  name := "sdr_nco_mix"
  inputNames := ["i_in", "q_in", "phase_inc"]
  inputWidths := [16, 16, 32]
  wires :=
    [ ncoWire 0 "t" (sliceE 28 17 (.regRead 0))
    , ncoWire 1 "odd" (sliceE 29 29 (.regRead 0))
    , ncoWire 2 "tt" (.mux (.wireRef 1) (subE (ci 4096) (.wireRef 0)) (.wireRef 0))
    , ncoWire 3 "s" (.alu .shl (.wireRef 2) (ci 18))
    , ncoWire 4 "s2" (q30 (.wireRef 3) (.wireRef 3))
    , ncoWire 5 "cos_a" (q30 (.wireRef 4) (ci ncoA4))
    , ncoWire 6 "cos_b" (q30 (.wireRef 4) (addE (ci (-ncoA2)) (.wireRef 5)))
    , ncoWire 7 "core_cos" (addE (ci (2 ^ 30)) (.wireRef 6))
    , ncoWire 8 "sin_a" (q30 (.wireRef 4) (ci ncoB5))
    , ncoWire 9 "sin_b" (q30 (.wireRef 4) (addE (ci (-ncoB3)) (.wireRef 8)))
    , ncoWire 10 "core_sin" (q30 (.wireRef 3) (addE (ci ncoB1) (.wireRef 9)))
    , ncoWire 11 "swap" (.alu .bitXor (sliceE 29 29 (.regRead 0)) (sliceE 30 30 (.regRead 0)))
    , ncoWire 12 "negc" (.alu .bitXor (sliceE 30 30 (.regRead 0)) (sliceE 31 31 (.regRead 0)))
    , ncoWire 13 "negs" (sliceE 31 31 (.regRead 0))
    , ncoWire 14 "cx" (.mux (.wireRef 11) (.wireRef 10) (.wireRef 7))
    , ncoWire 15 "sy" (.mux (.wireRef 11) (.wireRef 7) (.wireRef 10))
    , ncoWire 16 "cos_t" (.mux (.wireRef 12) (neg (.wireRef 14)) (.wireRef 14))
    , ncoWire 17 "sin_t" (.mux (.wireRef 13) (neg (.wireRef 15)) (.wireRef 15))
    , ncoWire 18 "xi" (.resize (.sext 16 64) (.inputPort 0))
    , ncoWire 19 "xq" (.resize (.sext 16 64) (.inputPort 1))
    , ncoWire 20 "mix_i" (ashrE (addE (mulE (.wireRef 18) (.wireRef 16)) (mulE (.wireRef 19) (.wireRef 17))) 30)
    , ncoWire 21 "mix_q" (ashrE (subE (mulE (.wireRef 19) (.wireRef 16)) (mulE (.wireRef 18) (.wireRef 17))) 30) ]
  regs :=
    [ discReg 0 "phase" (.resize (.trunc 32) (addE (.regRead 0) (.inputPort 2))) 32
    , discReg 1 "out_i_q" (.resize (.trunc 16) (.wireRef 20)) 16
    , discReg 2 "out_q_q" (.resize (.trunc 16) (.wireRef 21)) 16 ]
  outputs :=
    [ { name := "out_i", expr := .regRead 1, width := 16 }
    , { name := "out_q", expr := .regRead 2, width := 16 } ]
example : checkRtlModuleW sdrNcoModule = true := by decide +kernel
/-! ### The phasor's error (`taylor-model@1`)
The core's argument is `θ = s·a`, `s = tt/4096 ∈ [0, 1]`, `a = π_r/4 = 355/452` (so `θ ∈ [0, π_r/4]`,
the whole range the core is used on). Its polynomials in `θ` are `ncoCosPoly`, `ncoSinPoly` with the
Q30 coefficients above. The `taylor-model@1` queries enclose `poly(θ) - cos θ` and `poly(θ) - sin θ`
over that range; the bounds are what the judge's evaluation computes, not typed numbers. -/
section Phasor
open Obend.Analysis Obend.Elab.AutoCert
def ncoA : CanonicalRat := CanonicalRat.mk 355 452
def ncoDom : Interval := ⟨0, ncoA⟩
def q30r (k : Int) : CanonicalRat := (k : CanonicalRat) / (2 ^ 30 : CanonicalRat)
/-- `s = θ / a` as a Taylor-model expression in `θ`. -/
def sExpr : TaylorModelExpr := .scale (1 / ncoA) .var
def ncoCosPolyExpr : TaylorModelExpr :=
  .add (.const 1)
    (.add (.scale (-(q30r ncoA2)) (.mul sExpr sExpr)) (.scale (q30r ncoA4) (.mul (.mul sExpr sExpr) (.mul sExpr sExpr))))
def ncoSinPolyExpr : TaylorModelExpr :=
  .add (.scale (q30r ncoB1) sExpr)
    (.add (.scale (-(q30r ncoB3)) (.mul sExpr (.mul sExpr sExpr)))
      (.scale (q30r ncoB5) (.mul sExpr (.mul (.mul sExpr sExpr) (.mul sExpr sExpr)))))
def ncoCosErrExpr : TaylorModelExpr := .sub ncoCosPolyExpr (.cos .var)
def ncoSinErrExpr : TaylorModelExpr := .sub ncoSinPolyExpr (.sin .var)
/-- The core polynomials as functions of `θ`. -/
def ncoCosPoly (θ : CanonicalRat) : CanonicalRat :=
  1 + (-(q30r ncoA2) * ((1 / ncoA * θ) * (1 / ncoA * θ)) +
    q30r ncoA4 * (((1 / ncoA * θ) * (1 / ncoA * θ)) * ((1 / ncoA * θ) * (1 / ncoA * θ))))
def ncoSinPoly (θ : CanonicalRat) : CanonicalRat :=
  q30r ncoB1 * (1 / ncoA * θ) +
    (-(q30r ncoB3) * ((1 / ncoA * θ) * ((1 / ncoA * θ) * (1 / ncoA * θ))) +
      q30r ncoB5 * ((1 / ncoA * θ) * (((1 / ncoA * θ) * (1 / ncoA * θ)) * ((1 / ncoA * θ) * (1 / ncoA * θ)))))
/-- The Taylor models the judge computes, and the error bounds they give. -/
def ncoCosTm : TaylorModel := (evalTaylorModelExpr ncoDom 0 4 ncoCosErrExpr).getD (invalidTaylorModel ncoDom)
def ncoSinTm : TaylorModel := (evalTaylorModelExpr ncoDom 0 5 ncoSinErrExpr).getD (invalidTaylorModel ncoDom)
def ncoCosErrBound : Interval := evalTaylorModelRange ncoCosTm
def ncoSinErrBound : Interval := evalTaylorModelRange ncoSinTm
def ncoCosQuery : TaylorModelQuery :=
  { expr := ncoCosErrExpr, domain := ncoDom, center := 0, degree := 4, claimedBound := ncoCosErrBound }
def ncoSinQuery : TaylorModelQuery :=
  { expr := ncoSinErrExpr, domain := ncoDom, center := 0, degree := 5, claimedBound := ncoSinErrBound }
/-- The judge accepts both certificates. -/
theorem ncoCos_judge_ok : checkTaylorModelJudge 0 ncoCosQuery ncoCosTm = .ok := by decide +kernel
theorem ncoSin_judge_ok : checkTaylorModelJudge 0 ncoSinQuery ncoSinTm = .ok := by decide +kernel
/-- The derived bounds, rounded out to six digits for reading: `|cos error| ≤ 0.002491`,
`|sin error| ≤ 0.000327` (`-52.1 dB` and `-69.7 dB`). -/
theorem nco_err_bounds_readable :
    Interval.subset ncoCosErrBound ⟨CanonicalRat.mk (-2491) 1000000, CanonicalRat.mk 2491 1000000⟩ = true ∧
    Interval.subset ncoSinErrBound ⟨CanonicalRat.mk (-327) 1000000, CanonicalRat.mk 327 1000000⟩ = true := by
  decide +kernel
/-- **The phasor core's polynomial error.** For any `AnalyticModel` (any `cos`, `sin` satisfying the
Taylor–Lagrange remainder bounds of the real functions) and every `θ ∈ [0, π_r/4]`, the core's
polynomials differ from `cos θ`, `sin θ` by an amount in the bounds the `taylor-model@1` judge computed. -/
theorem nco_poly_enclosure (R : Type) [M : AnalyticModel R] (θ : CanonicalRat) (hθ : θ ∈ ncoDom) :
    ncoCosPoly θ - M.cosFn θ ∈ ncoCosErrBound ∧ ncoSinPoly θ - M.sinFn θ ∈ ncoSinErrBound :=
  ⟨taylorModelJudge_semantic R 0 ncoCosQuery ncoCosTm rfl (by decide) ncoCos_judge_ok θ hθ,
   taylorModelJudge_semantic R 0 ncoSinQuery ncoSinTm rfl (by decide) ncoSin_judge_ok θ hθ⟩
end Phasor
open Obend.Analysis Obend.Elab.AutoCert
/-! ### The phasor core in hardware -/
/-- The core's `cos` output as a function of `tt` (wire 2), the expressions of wires 3–7. -/
def ncoCoreCos (tt : BitVec 64) : BitVec 64 :=
  let s := tt <<< 18
  let s2 := BitVec.sshiftRight (s * s) 30
  let ca := BitVec.sshiftRight (s2 * BitVec.ofInt 64 ncoA4) 30
  let cb := BitVec.sshiftRight (s2 * (BitVec.ofInt 64 (-ncoA2) + ca)) 30
  BitVec.ofInt 64 (2 ^ 30) + cb
/-- The core's `sin` output as a function of `tt`, the expressions of wires 3, 4, 8–10. -/
def ncoCoreSin (tt : BitVec 64) : BitVec 64 :=
  let s := tt <<< 18
  let s2 := BitVec.sshiftRight (s * s) 30
  let sa := BitVec.sshiftRight (s2 * BitVec.ofInt 64 ncoB5) 30
  let sb := BitVec.sshiftRight (s2 * (BitVec.ofInt 64 (-ncoB3) + sa)) 30
  BitVec.sshiftRight (s * (BitVec.ofInt 64 ncoB1 + sb)) 30
theorem nco_core_wires (inp regs : Nat → BitVec 64) :
    evalWireTable inp regs sdrNcoModule.wires 7 = ncoCoreCos (evalWireTable inp regs sdrNcoModule.wires 2) ∧
    evalWireTable inp regs sdrNcoModule.wires 10 = ncoCoreSin (evalWireTable inp regs sdrNcoModule.wires 2) :=
  ⟨rfl, rfl⟩
/-- `tt` (wire 2) is at most 4096 for every phase word. -/
theorem nco_tt_le (inp regs : Nat → BitVec 64) : (evalWireTable inp regs sdrNcoModule.wires 2).toNat ≤ 4096 := by
  show (if (truncToWidth 1 (regs 0 >>> 29)) != 0#64 then BitVec.ofInt 64 4096 - truncToWidth 12 (regs 0 >>> 17)
        else truncToWidth 12 (regs 0 >>> 17)).toNat ≤ 4096
  have h12 := truncToWidth_lt 12 (by decide) (regs 0 >>> 17)
  split
  · rw [BitVec.toNat_sub]
    have : (BitVec.ofInt 64 4096).toNat = 4096 := by decide
    rw [this]; omega
  · omega
def fixErrOk (tt : Nat) : Bool :=
  let x : CanonicalRat := (tt : CanonicalRat) / 4096
  let θ := x * ncoA
  let c := q30r (ncoCoreCos (BitVec.ofNat 64 tt)).toInt - ncoCosPoly θ
  let s := q30r (ncoCoreSin (BitVec.ofNat 64 tt)).toInt - ncoSinPoly θ
  decide (-(q30r 3) ≤ c ∧ c ≤ q30r 3 ∧ -(q30r 3) ≤ s ∧ s ≤ q30r 3)
/-- The fixed-point core is within 3 LSB (Q30) of the polynomials at every one of its 4097 inputs. -/
theorem nco_fixed_point_ok : (List.range 4097).all fixErrOk = true := by decide +kernel
/-- **The NCO's phasor error, in hardware.** For every phase word (any register state), the core's
outputs (wires 7 and 10, Q30) differ from `cos θ`, `sin θ` of the angle the core is evaluating,
`θ = (tt/4096)·π_r/4` with `tt` the folded octant offset (wire 2), by at most the `taylor-model@1`
bound plus 3 LSB of fixed-point rounding. The octant logic then only swaps and negates the pair. -/
theorem nco_phasor_error (R : Type) [M : AnalyticModel R] (inp regs : Nat → BitVec 64) :
    let tt := (evalWireTable inp regs sdrNcoModule.wires 2).toNat
    let θ : CanonicalRat := (tt : CanonicalRat) / 4096 * ncoA
    q30r (evalWireTable inp regs sdrNcoModule.wires 7).toInt - M.cosFn θ ∈
        Interval.add ⟨-(q30r 3), q30r 3⟩ ncoCosErrBound ∧
    q30r (evalWireTable inp regs sdrNcoModule.wires 10).toInt - M.sinFn θ ∈
        Interval.add ⟨-(q30r 3), q30r 3⟩ ncoSinErrBound := by
  intro tt θ
  have htt : tt ≤ 4096 := nco_tt_le inp regs
  have hfix : fixErrOk tt = true := List.all_eq_true.mp nco_fixed_point_ok tt (List.mem_range.mpr (by omega))
  have hw2 : evalWireTable inp regs sdrNcoModule.wires 2 = BitVec.ofNat 64 tt := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm
  obtain ⟨h7, h10⟩ := nco_core_wires inp regs
  rw [h7, h10, hw2]
  have hθ : θ ∈ ncoDom := by
    rw [Interval.mem_iff]
    have h0 : (0 : CanonicalRat) ≤ (tt : CanonicalRat) := by exact_mod_cast Nat.zero_le tt
    have h1 : (tt : CanonicalRat) ≤ 4096 := by exact_mod_cast htt
    show (0 : CanonicalRat) ≤ (tt : CanonicalRat) / 4096 * ncoA ∧ (tt : CanonicalRat) / 4096 * ncoA ≤ ncoA
    have ha : (0 : CanonicalRat) ≤ ncoA := by decide
    have hx0 : (0 : CanonicalRat) ≤ (tt : CanonicalRat) / 4096 := by grind
    have hx1 : (tt : CanonicalRat) / 4096 ≤ 1 := by grind
    refine ⟨Rat.mul_nonneg hx0 ha, ?_⟩
    have := Rat.mul_le_mul_of_nonneg_right hx1 ha
    rwa [Rat.one_mul] at this
  obtain ⟨hc, hs⟩ := nco_poly_enclosure R θ hθ
  simp only [fixErrOk, decide_eq_true_eq] at hfix
  obtain ⟨f1, f2, f3, f4⟩ := hfix
  constructor
  · have e : q30r (ncoCoreCos (BitVec.ofNat 64 tt)).toInt - M.cosFn θ =
        (q30r (ncoCoreCos (BitVec.ofNat 64 tt)).toInt - ncoCosPoly θ) + (ncoCosPoly θ - M.cosFn θ) := by grind
    rw [e]
    exact Interval.add_mem (by rw [Interval.mem_iff]; exact ⟨f1, f2⟩) hc
  · have e : q30r (ncoCoreSin (BitVec.ofNat 64 tt)).toInt - M.sinFn θ =
        (q30r (ncoCoreSin (BitVec.ofNat 64 tt)).toInt - ncoSinPoly θ) + (ncoSinPoly θ - M.sinFn θ) := by grind
    rw [e]
    exact Interval.add_mem (by rw [Interval.mem_iff]; exact ⟨f3, f4⟩) hs
/-! ## Image rejection (`interval@1`, `taylor-model@1`)
An I/Q pair with amplitude ratio `g` and phase error `φ` passes the wanted sideband with power
proportional to `1 + 2g·cos φ + g²` and the image with `1 - 2g·cos φ + g²`; their ratio is the image
rejection ratio. The Tayloe front end's calibration trims the I/Q gain in steps of `1/500` (the
`iqGainPermille` trim, `500` = unity) and the phase in steps of 2 mrad, so after calibration
`|g - 1| ≤ 1/1000` and `|φ| ≤ 1/1000` rad. -/
/-- The image rejection ratio (power), the standard formula. -/
def irrRatio (g c : CanonicalRat) : CanonicalRat := (1 + 2 * g * c + g * g) / (1 - 2 * g * c + g * g)
def irrPhaseDom : Interval := ⟨CanonicalRat.mk (-1) 1000, CanonicalRat.mk 1 1000⟩
def irrCosTm : TaylorModel := (evalTaylorModelExpr irrPhaseDom 0 4 (.cos .var)).getD (invalidTaylorModel irrPhaseDom)
/-- `cos φ` over the residual phase range, as the `taylor-model@1` judge encloses it. -/
def irrCosBound : Interval := evalTaylorModelRange irrCosTm
def irrCosQuery : TaylorModelQuery :=
  { expr := .cos .var, domain := irrPhaseDom, center := 0, degree := 4, claimedBound := irrCosBound }
theorem irrCos_judge_ok : checkTaylorModelJudge 0 irrCosQuery irrCosTm = .ok := by decide +kernel
/-- `10^6.3 < 1995263`: an image at most `1/1995263` of the wanted power is more than 63 dB down. -/
def irrK : CanonicalRat := 1995263
/-- The `interval@1` query: with `u = g - 1` and `v = 1 - cos φ`, `wanted - K·image` is
`(2+u)² - K·u² - 2(K+1)(1+u)·v`, over `u ∈ [-1/1000, 1/1000]` and `v` in `1 - irrCosBound`. -/
def irrExpr : RealExpr :=
  .sub (.sub (.sqr (.add (.const 2) (.var "u"))) (.mul (.const irrK) (.sqr (.var "u"))))
    (.mul (.const (2 * (irrK + 1))) (.mul (.add (.const 1) (.var "u")) (.var "v")))
def irrQuery : Obend.Judge.IntervalQuery :=
  { expr := irrExpr
    env := [("u", ⟨CanonicalRat.mk (-1) 1000, CanonicalRat.mk 1 1000⟩), ("v", ⟨1 - irrCosBound.hi, 1 - irrCosBound.lo⟩)]
    claimedBound := ⟨0, 10⟩ }
theorem irr_judge_ok : Obend.Judge.intervalCheck 0 irrQuery .direct = .ok := by decide +kernel
/-- **Image rejection after calibration: at least 63 dB.** For any `AnalyticModel` and every residual
gain ratio `g` and phase error `φ` inside the calibration's half-step box, the image's power times
`1995263` (`> 10^6.3`) is at most the wanted sideband's power. Against a 60 dB requirement (a signal
40 dB above the wanted one on the image frequency ends at least 20 dB below it) the margin is 3 dB. -/
theorem sdr_irr_ge_63dB (R : Type) [M : AnalyticModel R] (g φ : CanonicalRat)
    (hg : CanonicalRat.mk 999 1000 ≤ g ∧ g ≤ CanonicalRat.mk 1001 1000)
    (hφ : φ ∈ irrPhaseDom) :
    irrK * (1 - 2 * g * M.cosFn φ + g * g) ≤ 1 + 2 * g * M.cosFn φ + g * g := by
  have hc : M.cosFn φ ∈ irrCosBound := by
    have := taylorModelJudge_semantic R 0 irrCosQuery irrCosTm rfl (by decide) irrCos_judge_ok φ hφ
    exact this
  rw [Interval.mem_iff] at hc
  have hsem := Obend.Judge.intervalCheck_sound 0 irrQuery .direct irr_judge_ok
  let rho : String → CanonicalRat := fun x => if x = "u" then g - 1 else if x = "v" then 1 - M.cosFn φ else 0
  have henv : ∀ v iv, irrQuery.env.lookup v = some iv → rho v ∈ iv := by
    intro v iv h
    simp only [irrQuery, List.lookup] at h
    split at h
    · rename_i hv; simp only [beq_iff_eq] at hv; subst hv; simp only [Option.some.injEq] at h; subst h
      rw [Interval.mem_iff]; simp only [rho, ↓reduceIte]
      have e1 : CanonicalRat.mk (-1) 1000 = CanonicalRat.mk 999 1000 - 1 := by decide +kernel
      have e2 : CanonicalRat.mk 1 1000 = CanonicalRat.mk 1001 1000 - 1 := by decide +kernel
      rw [e1, e2]; constructor <;> grind
    · split at h
      · rename_i _ hv; simp only [beq_iff_eq] at hv; subst hv; simp only [Option.some.injEq] at h; subst h
        rw [Interval.mem_iff]; simp only [rho]; constructor <;> grind
      · contradiction
  have h := hsem rho henv
  rw [Interval.mem_iff] at h
  have h0 := h.1
  simp only [irrQuery, irrExpr, Obend.Analysis.evalExpr, rho] at h0
  simp only [↓reduceIte] at h0
  grind
/-! ## The CORDIC inside the slicer's bins
`Obend.Hardware.SwitchedCapRf.cordic_residual_cone` says where the input lies relative to the run's
own exact rotation. Against a reference direction `p` that becomes a bound on the reported angle,
checked once over the 4096 sign choices; the tone cones' boundaries are sixteen such references. -/
section Weld
open Obend.Hardware.SwitchedCapRf
/-! ### The CORDIC against a reference direction
`cordicLowerCheck p θ` runs over the 4096 sign choices: wherever the reference `p`, turned back by
the choice's rotation, could still be clockwise of the residual cone, the reported angle is at least
`θ`. With `cordic_residual_cone` this bounds the CORDIC's output on every input counterclockwise of
`p` (`cordic_lower_of_check`); the upper check is its mirror image. -/
def cordicLowerCheck (p : Int × Int) (θ : Int) : Bool :=
  (cordicLeaves 0 cordicLutUrad).all fun l =>
    !(decide (0 ≤ 303 * (p.1 * l.1.1 + p.2 * l.1.2) - 100000 * (p.2 * l.1.1 - p.1 * l.1.2)) &&
      decide (0 < 100000 * (p.1 * l.1.1 + p.2 * l.1.2) - 303 * (p.2 * l.1.1 - p.1 * l.1.2)))
    || decide (θ ≤ l.2)
def cordicUpperCheck (p : Int × Int) (θ : Int) : Bool :=
  (cordicLeaves 0 cordicLutUrad).all fun l =>
    !(decide (0 ≤ 303 * (p.1 * l.1.1 + p.2 * l.1.2) + 100000 * (p.2 * l.1.1 - p.1 * l.1.2)) &&
      decide (0 < 100000 * (p.1 * l.1.1 + p.2 * l.1.2) + 303 * (p.2 * l.1.1 - p.1 * l.1.2)))
    || decide (l.2 ≤ θ)
theorem nonneg_of_mul_nonneg (a b : Int) (ha : 0 < a) (h : 0 ≤ a * b) : 0 ≤ b := by
  by_cases hb : 0 ≤ b
  · exact hb
  · have := Int.mul_neg_of_pos_of_neg ha (by omega : b < 0); omega
theorem pos_of_mul_pos (a b : Int) (ha : 0 < a) (h : 0 < a * b) : 0 < b := by
  by_cases hb : 0 < b
  · exact hb
  · have := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt ha) (by omega : b ≤ 0); omega
/-- The cone algebra both checks rest on. `w` is in the residual cone, `(pr, pi)` is the reference
turned back by the same rotation, `c` and `t` are the cross and dot products of the reference with
the input, scaled by the rotation's norm `N`. -/
theorem cone_transfer (wr wi pr pi c t N : Int) (hw0 : 0 < wr)
    (hw1 : 100000 * wi ≤ 303 * wr) (hw2 : -(100000 * wi) ≤ 303 * wr)
    (hc : pr * wi - pi * wr = N * c) (ht : pr * wr + pi * wi = N * t)
    (hN : 0 < N) (hc0 : 0 ≤ c) (ht0 : 0 < t) :
    0 ≤ 303 * pr - 100000 * pi ∧ 0 < 100000 * pr - 303 * pi := by
  have hW : 0 < wr * wr + wi * wi := by
    have := Int.mul_pos hw0 hw0
    have := mul_self_nonneg wi
    omega
  have hNc : 0 ≤ N * c := Int.mul_nonneg (Int.le_of_lt hN) hc0
  have hNt : 0 < N * t := Int.mul_pos hN ht0
  have i1 : (wr * wr + wi * wi) * (303 * pr - 100000 * pi)
      = (100000 * wr + 303 * wi) * (N * c) + (303 * wr - 100000 * wi) * (N * t) := by
    rw [← hc, ← ht]; grind
  have i2 : (wr * wr + wi * wi) * (100000 * pr - 303 * pi)
      = (100000 * wr - 303 * wi) * (N * t) + (303 * wr + 100000 * wi) * (N * c) := by
    rw [← hc, ← ht]; grind
  have a1 : 0 ≤ (100000 * wr + 303 * wi) * (N * c) := Int.mul_nonneg (by omega) hNc
  have a2 : 0 ≤ (303 * wr - 100000 * wi) * (N * t) := Int.mul_nonneg (by omega) (Int.le_of_lt hNt)
  have a3 : 0 < (100000 * wr - 303 * wi) * (N * t) := Int.mul_pos (by omega) hNt
  have a4 : 0 ≤ (303 * wr + 100000 * wi) * (N * c) := Int.mul_nonneg (by omega) hNc
  exact ⟨nonneg_of_mul_nonneg _ _ hW (by omega), pos_of_mul_pos _ _ hW (by omega)⟩
/-- **Lower cone bound.** If the check holds for the reference direction `p` and label `θ`, then
every valid input in the closed right half plane that is counterclockwise of `p` (cross product
`≥ 0`) and within a quarter turn of it (dot product `> 0`) gets an angle of at least `θ`. -/
theorem cordic_lower_of_check (p : Int × Int) (θ : Int) (hchk : cordicLowerCheck p θ = true)
    (x y : Int) (hx : 0 ≤ x) (hR : 8192 ≤ x.natAbs + y.natAbs)
    (hc : 0 ≤ p.1 * y - p.2 * x) (ht : 0 < p.1 * x + p.2 * y) :
    θ ≤ (cordicIter 0 cordicLutUrad x y 0).2.2 := by
  obtain ⟨hN, e1, e2⟩ := cordicBack_products p x y hx hR
  obtain ⟨w0, w1, w2⟩ := cordic_residual_cone x y hx hR
  have hmem := cordic_mem_leaves cordicLutUrad 0 x y
  have hl := List.all_eq_true.mp hchk _ hmem
  have hct := cone_transfer _ _ _ _ _ _ _ w0 w1 w2 e1 e2 hN hc ht
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    decide_eq_true_eq] at hl
  omega
/-- **Upper cone bound**, the mirror image: an input clockwise of `p` and within a quarter turn
of it gets an angle of at most `θ`. -/
theorem cordic_upper_of_check (p : Int × Int) (θ : Int) (hchk : cordicUpperCheck p θ = true)
    (x y : Int) (hx : 0 ≤ x) (hR : 8192 ≤ x.natAbs + y.natAbs)
    (hc : 0 ≤ p.2 * x - p.1 * y) (ht : 0 < p.1 * x + p.2 * y) :
    (cordicIter 0 cordicLutUrad x y 0).2.2 ≤ θ := by
  obtain ⟨hN, e1, e2⟩ := cordicBack_products p x y hx hR
  obtain ⟨w0, w1, w2⟩ := cordic_residual_cone x y hx hR
  have hmem := cordic_mem_leaves cordicLutUrad 0 x y
  have hl := List.all_eq_true.mp hchk _ hmem
  -- mirror in the real axis: negate the imaginary parts
  have e1' : (p.1 * (cordicGauss 0 cordicLutUrad x y).1 + p.2 * (cordicGauss 0 cordicLutUrad x y).2)
        * (-(cordicBack x y).2)
      - (-(p.2 * (cordicGauss 0 cordicLutUrad x y).1 - p.1 * (cordicGauss 0 cordicLutUrad x y).2))
        * (cordicBack x y).1
      = ((cordicGauss 0 cordicLutUrad x y).1 * (cordicGauss 0 cordicLutUrad x y).1
        + (cordicGauss 0 cordicLutUrad x y).2 * (cordicGauss 0 cordicLutUrad x y).2) * (p.2 * x - p.1 * y) := by
    grind
  have e2' : (p.1 * (cordicGauss 0 cordicLutUrad x y).1 + p.2 * (cordicGauss 0 cordicLutUrad x y).2)
        * (cordicBack x y).1
      + (-(p.2 * (cordicGauss 0 cordicLutUrad x y).1 - p.1 * (cordicGauss 0 cordicLutUrad x y).2))
        * (-(cordicBack x y).2)
      = ((cordicGauss 0 cordicLutUrad x y).1 * (cordicGauss 0 cordicLutUrad x y).1
        + (cordicGauss 0 cordicLutUrad x y).2 * (cordicGauss 0 cordicLutUrad x y).2) * (p.1 * x + p.2 * y) := by
    grind
  have hct := cone_transfer _ (-(cordicBack x y).2) _ _ _ _ _ w0 (by omega) (by omega) e1' e2' hN hc ht
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    decide_eq_true_eq] at hl
  omega
/-- Both bounds through the quadrant fold: an input inside the cone from `lo` to `hi` (narrower
than a quarter turn), not in the open third quadrant, gets an angle in `[L, U]`. -/
theorem cordic_cone_bounds (lo hi : Int × Int) (L U : Int)
    (c1 : cordicLowerCheck lo L = true) (c2 : cordicUpperCheck hi U = true)
    (c3 : cordicLowerCheck (-lo.1, -lo.2) (L - cordicPiUrad) = true)
    (c4 : cordicUpperCheck (-hi.1, -hi.2) (U - cordicPiUrad) = true)
    (x y : Int) (hR : 8192 ≤ x.natAbs + y.natAbs)
    (h1 : 0 ≤ lo.1 * y - lo.2 * x) (h2 : 0 ≤ hi.2 * x - hi.1 * y)
    (h3 : 0 < lo.1 * x + lo.2 * y) (h4 : 0 < hi.1 * x + hi.2 * y) (hq : x < 0 → 0 ≤ y) :
    L ≤ cordicAtan2 x y ∧ cordicAtan2 x y ≤ U := by
  rw [cordicAtan2_fold]
  by_cases hx : x < 0
  · have hy : ¬ y < 0 := by have := hq hx; omega
    simp only [hx, hy, ↓reduceIte]
    have e1 : -lo.1 * -y - -lo.2 * -x = lo.1 * y - lo.2 * x := by grind
    have e2 : -lo.1 * -x + -lo.2 * -y = lo.1 * x + lo.2 * y := by grind
    have e3 : -hi.2 * -x - -hi.1 * -y = hi.2 * x - hi.1 * y := by grind
    have e4 : -hi.1 * -x + -hi.2 * -y = hi.1 * x + hi.2 * y := by grind
    have l := cordic_lower_of_check (-lo.1, -lo.2) _ c3 (-x) (-y) (by omega) (by omega)
      (by show 0 ≤ -lo.1 * -y - -lo.2 * -x; omega) (by show 0 < -lo.1 * -x + -lo.2 * -y; omega)
    have u := cordic_upper_of_check (-hi.1, -hi.2) _ c4 (-x) (-y) (by omega) (by omega)
      (by show 0 ≤ -hi.2 * -x - -hi.1 * -y; omega) (by show 0 < -hi.1 * -x + -hi.2 * -y; omega)
    omega
  · simp only [hx, ↓reduceIte]
    exact ⟨cordic_lower_of_check lo L c1 x y (by omega) hR h1 h3,
      cordic_upper_of_check hi U c2 x y (by omega) hR h2 h4⟩
/-- The clockwise boundary of tone `k`'s cone: the direction at `k·2π/15 - 205439` µrad, as an
integer vector of length `10^9`. -/
@[expose] def toneConeLo : Nat → Int × Int
  | 0 => (978971524, -203996948)
  | 1 => (977308027, 211823086)
  | 2 => (806659110, 591016988)
  | 3 => (496531518, 868018693)
  | 4 => (100549124, 994932095)
  | 5 => (-312819126, 949812716)
  | 6 => (-672098112, 740462105)
  | _ => (-915165239, 403078881)
/-- The counterclockwise boundary: the direction at `k·2π/15 + 205439` µrad. -/
@[expose] def toneConeHi : Nat → Int × Int
  | 0 => (978971524, 203996948)
  | 1 => (811361967, 584544060)
  | 2 => (503460569, 864018203)
  | 3 => (108506272, 994095764)
  | 4 => (-305209742, 952285153)
  | 5 => (-666152225, 745815804)
  | 6 => (-911910947, 410388139)
  | _ => (-999991997, 4000643)
/-- The phasor `x + j·y` lies in tone `k`'s cone: counterclockwise of `toneConeLo k`, clockwise of
`toneConeHi k`, within a quarter turn of both. The cone contains every direction within 205438 µrad
of `k·2π/15`, the slicer's half bin less the CORDIC's 4000 µrad. -/
@[expose] def InToneCone (k : Nat) (x y : Int) : Prop :=
  0 ≤ (toneConeLo k).1 * y - (toneConeLo k).2 * x ∧ 0 ≤ (toneConeHi k).2 * x - (toneConeHi k).1 * y ∧
  0 < (toneConeLo k).1 * x + (toneConeLo k).2 * y ∧ 0 < (toneConeHi k).1 * x + (toneConeHi k).2 * y
instance (k : Nat) (x y : Int) : Decidable (InToneCone k x y) :=
  inferInstanceAs (Decidable (
    0 ≤ (toneConeLo k).1 * y - (toneConeLo k).2 * x ∧ 0 ≤ (toneConeHi k).2 * x - (toneConeHi k).1 * y ∧
    0 < (toneConeLo k).1 * x + (toneConeLo k).2 * y ∧ 0 < (toneConeHi k).1 * x + (toneConeHi k).2 * y))
/-- The four reference checks of tone `k`: its two boundaries against the slicer's bin edges,
directly and through the quadrant fold. -/
def toneCheck (k : Nat) : Bool :=
  cordicLowerCheck (toneConeLo k) (toneUrad k - 209438) &&
  cordicUpperCheck (toneConeHi k) (toneUrad k + 209438) &&
  cordicLowerCheck (-(toneConeLo k).1, -(toneConeLo k).2) (toneUrad k - 209438 - cordicPiUrad) &&
  cordicUpperCheck (-(toneConeHi k).1, -(toneConeHi k).2) (toneUrad k + 209438 - cordicPiUrad)
set_option maxRecDepth 1000000 in
private theorem toneCheck_0 : toneCheck 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
private theorem toneCheck_1 : toneCheck 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
private theorem toneCheck_2 : toneCheck 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
private theorem toneCheck_3 : toneCheck 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
private theorem toneCheck_4 : toneCheck 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
private theorem toneCheck_5 : toneCheck 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
private theorem toneCheck_6 : toneCheck 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
private theorem toneCheck_7 : toneCheck 7 = true := by decide +kernel
theorem toneCheck_all : (toneCheck 0 && toneCheck 1 && toneCheck 2 && toneCheck 3 && toneCheck 4 &&
    toneCheck 5 && toneCheck 6 && toneCheck 7) = true := by
  rw [toneCheck_0, toneCheck_1, toneCheck_2, toneCheck_3, toneCheck_4, toneCheck_5, toneCheck_6, toneCheck_7]
  rfl
theorem toneCheck_le (k : Nat) (hk : k ≤ 7) : toneCheck k = true := by
  have h := toneCheck_all
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
/-- **From the correlation phasor to the tone, exactly.** For every tone `k ∈ 0..7` and every
phasor `x + j·y` with `|x| + |y| ≥ 2^13` inside tone `k`'s cone, the 12-stage integer CORDIC
followed by the slicer decides `k`, not out of band: the CORDIC's whole error (convergence, the
truncation of every shift, table and `π` rounding) fits between the cone and the bin edges. -/
theorem ft8_iq_cordic_slicer_exact_tone (k : Nat) (hk : k ≤ 7) (x y : Int)
    (hR : 8192 ≤ x.natAbs + y.natAbs) (hc : InToneCone k x y) :
    ft8Bin (cordicAtan2 x y) = k ∧ ft8Oob (cordicAtan2 x y) = false := by
  apply ft8_bin_of_tone k hk
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hchk := toneCheck_le k hk
  simp only [toneCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hchk
  refine cordic_cone_bounds (toneConeLo k) (toneConeHi k) _ _ c1 c2 c3 c4 x y hR h1 h2 h3 h4 ?_
  intro hx
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [toneConeLo, toneConeHi] at h1 h2 h3 h4 <;> omega
end Weld
/-! ## The whole receive chain on one clock
`sdrFt8RxTopModule` instantiates the NCO, a CIC decimator on each of `I` and `Q` and the
discriminator in one module with one clock. A 6-bit counter makes the decimation strobe; the CIC
comb registers and every discriminator register load only when it is high (a clock enable), so no
second clock exists. The sub-modules are embedded by `shiftExpr`: wire and register indices are
offset and each input port is replaced by the expression that drives it. -/
/-- An expression of a sub-module inside a larger one: wires and registers offset, input port `i`
replaced by `inMap i`. -/
def shiftExpr (wOff rOff : Nat) (inMap : Nat → RtlExpr) : RtlExpr → RtlExpr
  | .const v => .const v
  | .inputPort i => inMap i
  | .wireRef i => .wireRef (i + wOff)
  | .regRead i => .regRead (i + rOff)
  | .alu op a b => .alu op (shiftExpr wOff rOff inMap a) (shiftExpr wOff rOff inMap b)
  | .mux c t f => .mux (shiftExpr wOff rOff inMap c) (shiftExpr wOff rOff inMap t) (shiftExpr wOff rOff inMap f)
  | .bitNot a => .bitNot (shiftExpr wOff rOff inMap a)
  | .resize op a => .resize op (shiftExpr wOff rOff inMap a)
/-- **Embedding preserves evaluation**: the embedded expression, in the larger module's
environments, has the value of the original in the environments the embedding induces. -/
theorem shiftExpr_eval (wOff rOff : Nat) (inMap : Nat → RtlExpr) (inp W R : Nat → BitVec 64) :
    ∀ e : RtlExpr, evalRtlExpr inp W R (shiftExpr wOff rOff inMap e)
      = evalRtlExpr (fun i => evalRtlExpr inp W R (inMap i)) (fun i => W (i + wOff)) (fun i => R (i + rOff)) e
  | .const _ => rfl
  | .inputPort _ => rfl
  | .wireRef _ => rfl
  | .regRead _ => rfl
  | .alu op a b => by
    simp only [shiftExpr, evalRtlExpr, shiftExpr_eval wOff rOff inMap inp W R a,
      shiftExpr_eval wOff rOff inMap inp W R b]
  | .mux c t f => by
    simp only [shiftExpr, evalRtlExpr, shiftExpr_eval wOff rOff inMap inp W R c,
      shiftExpr_eval wOff rOff inMap inp W R t, shiftExpr_eval wOff rOff inMap inp W R f]
  | .bitNot a => by simp only [shiftExpr, evalRtlExpr, shiftExpr_eval wOff rOff inMap inp W R a]
  | .resize op a => by simp only [shiftExpr, evalRtlExpr, shiftExpr_eval wOff rOff inMap inp W R a]
/-- A sub-module's wire inside the larger module. -/
def shiftWire (pre : String) (wOff rOff : Nat) (inMap : Nat → RtlExpr) (a : WireAssign) : WireAssign :=
  { a with wireIdx := a.wireIdx + wOff, name := pre ++ a.name, expr := shiftExpr wOff rOff inMap a.expr }
def shiftWires (pre : String) (wOff rOff : Nat) (inMap : Nat → RtlExpr) : List WireAssign → List WireAssign
  | [] => []
  | a :: as => shiftWire pre wOff rOff inMap a :: shiftWires pre wOff rOff inMap as
/-- The embedded registers; with `gate`, each loads only when the gate is high and holds otherwise. -/
def shiftRegs (pre : String) (wOff rOff : Nat) (inMap : Nat → RtlExpr) (gate : Option RtlExpr) :
    List RegSpec → List RegSpec
  | [] => []
  | r :: rs =>
    { r with regIdx := r.regIdx + rOff, name := pre ++ r.name,
             nextExpr := match gate with
               | none => shiftExpr wOff rOff inMap r.nextExpr
               | some g => .mux g (shiftExpr wOff rOff inMap r.nextExpr) (.regRead (r.regIdx + rOff)) }
      :: shiftRegs pre wOff rOff inMap gate rs
/-- The decimation strobe's wire in the top module. -/
def strobeWire : Nat := 22
/-- What drives each sub-module's input ports in the top module. -/
def cicInI : Nat → RtlExpr := fun i => if i = 0 then .regRead 1 else .wireRef strobeWire
def cicInQ : Nat → RtlExpr := fun i => if i = 0 then .regRead 2 else .wireRef strobeWire
def discIn : Nat → RtlExpr := fun i =>
  if i = 0 then .regRead 10 else if i = 1 then .regRead 17 else .inputPort (i + 1)
/-- The top module's wires before the discriminator's: the NCO, the strobe, the two CICs. -/
def topPrefixWires : List WireAssign :=
  sdrNcoModule.wires ++
  [{ wireIdx := strobeWire, name := "decim_strobe", expr := .alu .eq (.regRead 3) (ci 0), width := 1 }] ++
  shiftWires "i_" 23 4 cicInI sdrCicModule.wires ++
  shiftWires "q_" 27 11 cicInQ sdrCicModule.wires
@[expose] def sdrFt8RxTopModule : RtlModule where
  name := "sdr_ft8_rx_top"
  inputNames := ["i_in", "q_in", "phase_inc", "acc_clr", "acc_en", "sym_latch"]
  inputWidths := [16, 16, 32, 1, 1, 1]
  wires := topPrefixWires ++ shiftWires "" 31 18 discIn sdrFt8DiscModule.wires
  regs :=
    sdrNcoModule.regs ++
    [discReg 3 "decim_cnt" (.resize (.trunc 6) (addE (.regRead 3) (ci 1))) 6] ++
    shiftRegs "i_" 23 4 cicInI none sdrCicModule.regs ++
    shiftRegs "q_" 27 11 cicInQ none sdrCicModule.regs ++
    shiftRegs "" 31 18 discIn (some (.wireRef strobeWire)) sdrFt8DiscModule.regs
  outputs :=
    [ { name := "tone_bin", expr := .regRead 24, width := 3 }
    , { name := "tone_oob", expr := .regRead 25, width := 1 }
    , { name := "angle_urad", expr := .regRead 26, width := 32 }
    , { name := "decim_strobe_o", expr := .wireRef strobeWire, width := 1 } ]
/-- The unified module passes the emission gate: wire DAG, one clock domain, port and signal widths. -/
theorem sdrFt8RxTopModule_checkRtlModuleW : checkRtlModuleW sdrFt8RxTopModule = true := by decide +kernel
/-- The strobe as the top module computes it from its counter (register 3). -/
def topStrobe (st : Nat → BitVec 64) : BitVec 64 := if st 3 == 0#64 then 1#64 else 0#64
/-- The discriminator's inputs inside the top module: the two CIC outputs and the control ports. -/
def topDiscInputs (inp st : Nat → BitVec 64) : Nat → BitVec 64 :=
  fun i => if i = 0 then st 10 else if i = 1 then st 17 else inp (i + 1)
set_option maxRecDepth 1000000 in
/-- **One clock edge of the top module is one edge of each stage** (NCO, counter, CICs). The NCO's
registers step as `sdrNcoModule`'s; the counter counts modulo 64; each CIC's registers step as
`sdrCicModule`'s on the NCO's output register and the strobe. So `nco_phasor_error` and
`sdrCic_output_exact` speak about the registers of the unified module. -/
theorem sdrFt8RxTop_step_refines (inp st : Nat → BitVec 64) :
    (∀ r, r < 3 → stepModuleRegs sdrFt8RxTopModule false inp st r = stepModuleRegs sdrNcoModule false inp st r) ∧
    stepModuleRegs sdrFt8RxTopModule false inp st 3 = truncToWidth 6 (st 3 + 1#64) ∧
    (∀ r, r < 7 → stepModuleRegs sdrFt8RxTopModule false inp st (4 + r)
      = stepModuleRegs sdrCicModule false (fun i => if i = 0 then st 1 else topStrobe st) (fun i => st (4 + i)) r) ∧
    (∀ r, r < 7 → stepModuleRegs sdrFt8RxTopModule false inp st (11 + r)
      = stepModuleRegs sdrCicModule false (fun i => if i = 0 then st 2 else topStrobe st) (fun i => st (11 + i)) r) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro r hr
    match r, hr with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
  · intro r hr
    match r, hr with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  · intro r hr
    match r, hr with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
section CordicWires
open Obend.Hardware.SwitchedCapRf
set_option linter.unusedSimpArgs false
/-! ## The discriminator's wires compute `cordicAtan2` -/
theorem bmod64 (v : Int) (h1 : -(2:Int)^63 ≤ v) (h2 : v < (2:Int)^63) : v.bmod (2^64) = v := by
  apply Int.bmod_eq_of_le
  · have : ((2 ^ 64 : Nat) : Int) / 2 = (2 : Int) ^ 63 := by decide
    rw [this]; exact h1
  · have : (((2 ^ 64 : Nat) : Int) + 1) / 2 = (2 : Int) ^ 63 := by decide
    rw [this]; exact h2
theorem ediv_within (Y d B : Int) (hd : 1 ≤ d) (h1 : -B ≤ Y) (h2 : Y ≤ B) : -B ≤ Y / d ∧ Y / d ≤ B := by
  have hb := ediv_bounds Y d (by omega)
  generalize Y / d = q at *
  constructor
  · by_cases hq : -B ≤ q
    · exact hq
    · have : (d - 1) * (q + 1) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      have e : (d - 1) * (q + 1) = d * q + d - q - 1 := by grind
      omega
  · by_cases hq : q ≤ B
    · exact hq
    · have : 0 ≤ (d - 1) * q := Int.mul_nonneg (by omega) (by omega)
      have e : (d - 1) * q = d * q - q := by grind
      omega
def bvStage (i : Nat) (a : Int) (x y z : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  if (if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64 then
    (x - BitVec.sshiftRight y ((BitVec.ofInt 64 (i : Int)).toNat % 64),
     y + BitVec.sshiftRight x ((BitVec.ofInt 64 (i : Int)).toNat % 64), z - BitVec.ofInt 64 a)
  else
    (x + BitVec.sshiftRight y ((BitVec.ofInt 64 (i : Int)).toNat % 64),
     y - BitVec.sshiftRight x ((BitVec.ofInt 64 (i : Int)).toNat % 64), z + BitVec.ofInt 64 a)
theorem bvStage_x (i : Nat) (a : Int) (x y z : BitVec 64) : (bvStage i a x y z).1 =
    if (if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64 then
      x - BitVec.sshiftRight y ((BitVec.ofInt 64 (i : Int)).toNat % 64)
    else x + BitVec.sshiftRight y ((BitVec.ofInt 64 (i : Int)).toNat % 64) := by
  unfold bvStage; cases ((if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64) <;> rfl
theorem bvStage_y (i : Nat) (a : Int) (x y z : BitVec 64) : (bvStage i a x y z).2.1 =
    if (if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64 then
      y + BitVec.sshiftRight x ((BitVec.ofInt 64 (i : Int)).toNat % 64)
    else y - BitVec.sshiftRight x ((BitVec.ofInt 64 (i : Int)).toNat % 64) := by
  unfold bvStage; cases ((if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64) <;> rfl
theorem bvStage_z (i : Nat) (a : Int) (x y z : BitVec 64) : (bvStage i a x y z).2.2 =
    if (if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64 then z - BitVec.ofInt 64 a
    else z + BitVec.ofInt 64 a := by
  unfold bvStage; cases ((if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64) <;> rfl
theorem shamt (i : Nat) (hi : i < 64) : (BitVec.ofInt 64 (i : Int)).toNat % 64 = i := by
  have h : ∀ j : Fin 64, (BitVec.ofInt 64 ((j.val : Nat) : Int)).toNat % 64 = j.val := by decide
  exact h ⟨i, hi⟩
theorem shr_div (m : Int) (i : Nat) : m >>> i = m / (2 : Int) ^ i := by
  rw [Int.shiftRight_eq_div_pow, Int.natCast_pow]; rfl
theorem bvStage_toInt (i : Nat) (hi : i < 64) (a : Int) (x y z : BitVec 64) (B Zb : Int)
    (hx : -B ≤ x.toInt ∧ x.toInt ≤ B) (hy : -B ≤ y.toInt ∧ y.toInt ≤ B) (hB : 2 * B < 2 ^ 63)
    (hz : -Zb ≤ z.toInt ∧ z.toInt ≤ Zb) (ha : -2 ^ 30 ≤ a ∧ a ≤ 2 ^ 30) (hZ : Zb + 2 ^ 30 < 2 ^ 63) :
    (bvStage i a x y z).1.toInt = (if y.toInt < 0 then x.toInt - y.toInt / 2 ^ i else x.toInt + y.toInt / 2 ^ i) ∧
    (bvStage i a x y z).2.1.toInt = (if y.toInt < 0 then y.toInt + x.toInt / 2 ^ i else y.toInt - x.toInt / 2 ^ i) ∧
    (bvStage i a x y z).2.2.toInt = (if y.toInt < 0 then z.toInt - a else z.toInt + a) := by
  have hd : (1 : Int) ≤ 2 ^ i := by have := two_pow_pos i; omega
  have qy := ediv_within y.toInt (2 ^ i) B hd hy.1 hy.2
  have qx := ediv_within x.toInt (2 ^ i) B hd hx.1 hx.2
  have h0 : (BitVec.ofInt 64 0).toInt = 0 := by decide
  have hA : (BitVec.ofInt 64 a).toInt = a := by rw [BitVec.toInt_ofInt]; exact bmod64 a (by omega) (by omega)
  have hs : BitVec.slt y (BitVec.ofInt 64 0) = true ↔ y.toInt < 0 := by rw [BitVec.slt_iff_toInt_lt, h0]
  unfold bvStage
  rw [shamt i hi]
  by_cases hneg : y.toInt < 0
  · have h1 : BitVec.slt y (BitVec.ofInt 64 0) = true := hs.mpr hneg
    have h2 : ((1#64 : BitVec 64) != 0#64) = true := by decide
    simp only [h1, h2, hneg, ↓reduceIte]
    rw [BitVec.toInt_sub, BitVec.toInt_add, BitVec.toInt_sub, BitVec.toInt_sshiftRight, BitVec.toInt_sshiftRight,
      shr_div, shr_div, hA]
    refine ⟨bmod64 _ (by omega) (by omega), bmod64 _ (by omega) (by omega), bmod64 _ (by omega) (by omega)⟩
  · have h1 : BitVec.slt y (BitVec.ofInt 64 0) = false := by
      cases h : BitVec.slt y (BitVec.ofInt 64 0)
      · rfl
      · exact absurd (hs.mp h) hneg
    have h2 : ((0#64 : BitVec 64) != 0#64) = false := by decide
    simp only [h1, h2, hneg, ↓reduceIte, Bool.false_eq_true]
    rw [BitVec.toInt_add, BitVec.toInt_sub, BitVec.toInt_add, BitVec.toInt_sshiftRight, BitVec.toInt_sshiftRight,
      shr_div, shr_div, hA]
    refine ⟨bmod64 _ (by omega) (by omega), bmod64 _ (by omega) (by omega), bmod64 _ (by omega) (by omega)⟩
def bvIter : Nat → List Int → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64 × BitVec 64
  | _, [], x, y, z => (x, y, z)
  | i, a :: as, x, y, z =>
    bvIter (i + 1) as (bvStage i a x y z).1 (bvStage i a x y z).2.1 (bvStage i a x y z).2.2
theorem bvIter_toInt (as : List Int) : ∀ (i : Nat) (x y z : BitVec 64) (B Zb : Int),
    i + as.length ≤ 64 → (-B ≤ x.toInt ∧ x.toInt ≤ B) → (-B ≤ y.toInt ∧ y.toInt ≤ B) →
    2 ^ as.length * B < 2 ^ 62 → (-Zb ≤ z.toInt ∧ z.toInt ≤ Zb) → Zb + as.length * 2 ^ 30 < 2 ^ 63 →
    (∀ a ∈ as, -2 ^ 30 ≤ a ∧ a ≤ 2 ^ 30) →
    (bvIter i as x y z).1.toInt = (cordicIter i as x.toInt y.toInt z.toInt).1 ∧
    (bvIter i as x y z).2.1.toInt = (cordicIter i as x.toInt y.toInt z.toInt).2.1 ∧
    (bvIter i as x y z).2.2.toInt = (cordicIter i as x.toInt y.toInt z.toInt).2.2 := by
  induction as with
  | nil => intro i x y z B Zb _ _ _ _ _ _ _; exact ⟨rfl, rfl, rfl⟩
  | cons a as ih =>
    intro i x y z B Zb hi hx hy hB hz hZ hall
    have hlen : (a :: as).length = as.length + 1 := rfl
    rw [hlen] at hi hB hZ
    have hB0 : 0 ≤ B := by omega
    have hp : (1 : Int) ≤ 2 ^ as.length := by have := two_pow_pos as.length; omega
    have hpB : B ≤ 2 ^ as.length * B := by
      have := Int.mul_le_mul_of_nonneg_right hp hB0; omega
    have e2 : (2 : Int) ^ (as.length + 1) * B = 2 * (2 ^ as.length * B) := by rw [Int.pow_succ]; grind
    rw [e2] at hB
    have e4 : (2 : Int) ^ as.length * (2 * B) = 2 * (2 ^ as.length * B) := by grind
    have hcast : ((as.length + 1 : Nat) : Int) = (as.length : Int) + 1 := by omega
    rw [hcast] at hZ
    have e3 : ((as.length : Int) + 1) * 2 ^ 30 = (as.length : Int) * 2 ^ 30 + 2 ^ 30 := by grind
    have hlen0 : (0 : Int) ≤ (as.length : Int) * 2 ^ 30 := Int.mul_nonneg (by omega) (by decide)
    have hd : (1 : Int) ≤ 2 ^ i := by have := two_pow_pos i; omega
    have qy := ediv_within y.toInt (2 ^ i) B hd hy.1 hy.2
    have qx := ediv_within x.toInt (2 ^ i) B hd hx.1 hx.2
    obtain ⟨s1, s2, s3⟩ := bvStage_toInt i (by omega) a x y z B Zb hx hy (by omega) hz
      (hall a (List.mem_cons_self)) (by omega)
    have ha := hall a (List.mem_cons_self)
    obtain ⟨k1, k2, k3⟩ := ih (i + 1) (bvStage i a x y z).1 (bvStage i a x y z).2.1 (bvStage i a x y z).2.2
      (2 * B) (Zb + 2 ^ 30) (by omega) (by rw [s1]; split <;> omega) (by rw [s2]; split <;> omega)
      (by rw [e4]; exact hB)
      (by rw [s3]; split <;> omega) (by omega) (fun a' h => hall a' (List.mem_cons_of_mem _ h))
    simp only [bvIter, cordicIter]
    rw [k1, k2, k3, s1, s2, s3]
    by_cases hneg : y.toInt < 0 <;> simp [hneg]
/-- The quadrant fold as the wires compute it. -/
def bvFold (re im : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let n := (if BitVec.slt re (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64
  (if n then BitVec.ofInt 64 0 - re else re, if n then BitVec.ofInt 64 0 - im else im,
   if n then (if (if BitVec.slt im (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64 then BitVec.ofInt 64 (-cordicPiUrad)
     else BitVec.ofInt 64 cordicPiUrad) else BitVec.ofInt 64 0)
theorem slt_zero (y : BitVec 64) :
    ((if BitVec.slt y (BitVec.ofInt 64 0) then 1#64 else 0#64) != 0#64) = decide (y.toInt < 0) := by
  have h0 : (BitVec.ofInt 64 0).toInt = 0 := by decide
  by_cases h : y.toInt < 0
  · have : BitVec.slt y (BitVec.ofInt 64 0) = true := by rw [BitVec.slt_iff_toInt_lt, h0]; exact h
    simp only [this, h, ↓reduceIte, decide_true]; decide
  · have : BitVec.slt y (BitVec.ofInt 64 0) = false := by
      cases hs : BitVec.slt y (BitVec.ofInt 64 0)
      · rfl
      · rw [BitVec.slt_iff_toInt_lt, h0] at hs; exact absurd hs h
    simp only [this, h, decide_false, Bool.false_eq_true, ↓reduceIte]; decide
theorem bvFold_toInt (re im : BitVec 64) (hr : -2 ^ 48 ≤ re.toInt ∧ re.toInt ≤ 2 ^ 48)
    (hi : -2 ^ 48 ≤ im.toInt ∧ im.toInt ≤ 2 ^ 48) :
    (bvFold re im).1.toInt = (cordicFold re.toInt im.toInt).1 ∧
    (bvFold re im).2.1.toInt = (cordicFold re.toInt im.toInt).2.1 ∧
    (bvFold re im).2.2.toInt = (cordicFold re.toInt im.toInt).2.2 := by
  have h0 : (BitVec.ofInt 64 0).toInt = 0 := by decide
  have hp : (BitVec.ofInt 64 cordicPiUrad).toInt = cordicPiUrad := by decide
  have hn : (BitVec.ofInt 64 (-cordicPiUrad)).toInt = -cordicPiUrad := by decide
  simp only [bvFold, cordicFold, slt_zero]
  by_cases hx : re.toInt < 0
  · simp only [hx, decide_true, ↓reduceIte]
    rw [BitVec.toInt_sub, BitVec.toInt_sub, h0]
    refine ⟨?_, ?_, ?_⟩
    · rw [bmod64 _ (by omega) (by omega)]; omega
    · rw [bmod64 _ (by omega) (by omega)]; omega
    · by_cases hy : im.toInt < 0 <;> simp only [hy, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, hp, hn]
  · simp [hx]
/-- One wire assignment's effect on the wire environment. -/
def wireStep (inp regs env : Nat → BitVec 64) (a : WireAssign) : Nat → BitVec 64 :=
  fun i => if i == a.wireIdx then evalRtlExpr inp env regs a.expr else env i
theorem evalWireTable_foldl (inp regs : Nat → BitVec 64) (ws : List WireAssign) :
    evalWireTable inp regs ws = ws.foldl (wireStep inp regs) (fun _ => 0#64) := by rfl
theorem foldl_wireStep_untouched (inp regs : Nat → BitVec 64) :
    ∀ (ws : List WireAssign) (env : Nat → BitVec 64) (j : Nat),
      (∀ a ∈ ws, a.wireIdx ≠ j) → ws.foldl (wireStep inp regs) env j = env j
  | [], _, _, _ => rfl
  | a :: ws, env, j, h => by
    simp only [List.foldl_cons]
    rw [foldl_wireStep_untouched inp regs ws _ j (fun a' h' => h a' (List.mem_cons_of_mem _ h'))]
    have hne : ¬ (j = a.wireIdx) := fun e => h a List.mem_cons_self e.symm
    simp only [wireStep, beq_iff_eq, hne, ↓reduceIte]
/-- The index of the angle the stage wires end in. -/
def cordicLastWire : List Int → Nat → Nat
  | [], b => b
  | [_], b => b
  | [_, _], b => b + 2
  | _ :: as, b => cordicLastWire as (b + 3)
theorem bvIter_single (i : Nat) (a : Int) (x x' y z : BitVec 64) :
    (bvIter i [a] x y z).2.2 = (bvIter i [a] x' y z).2.2 := by
  simp only [bvIter, bvStage_z]
/-- **The stage wires compute the iteration.** Appended to any wire environment in which wires
`x, y, z` (below `base`) hold a vector and an angle, `cordicWires` leaves in its last wire the angle
`bvIter` computes from them. -/
theorem cordicWires_eval (inp regs : Nat → BitVec 64) : ∀ (as : List Int) (i base x y z : Nat)
    (env : Nat → BitVec 64), as ≠ [] → x < base → y < base → z < base →
    (cordicWires i as base x y z).foldl (wireStep inp regs) env (cordicLastWire as base)
      = (bvIter i as (env x) (env y) (env z)).2.2
  | [], _, _, _, _, _, _, h, _, _, _ => absurd rfl h
  | [a], i, base, x, y, z, env, _, hx, hy, hz => by
    have h1 : ¬ (y = base) := by omega
    have h2 : ¬ (z = base) := by omega
    simp only [cordicWires, List.foldl_cons, List.foldl_nil, cordicLastWire, wireStep, beq_self_eq_true,
      ↓reduceIte, evalRtlExpr, evalAluOp, slt, subE, addE, ci, bvIter, bvStage_z]
    rfl
  | [a, b], i, base, x, y, z, env, _, hx, hy, hz => by
    have ih := cordicWires_eval inp regs [b] (i + 1) (base + 2) 0 base (base + 1)
    simp only [cordicWires, List.cons_append, List.nil_append, List.foldl_cons, cordicLastWire] at ih ⊢
    rw [ih _ (by simp) (by omega) (by omega) (by omega)]
    have e1 : ¬ (base + 1 = base) := (by omega); have e2 : ¬ (base = base + 1) := (by omega); have e3 : ¬ (x = base) := (by omega)
    have e4 : ¬ (y = base) := (by omega); have e5 : ¬ (z = base) := (by omega); have e6 : ¬ (y = base + 1) := (by omega)
    have e7 : ¬ (z = base + 1) := by omega
    rw [bvIter_single (i + 1) b _ (bvStage i a (env x) (env y) (env z)).1]
    simp only [wireStep, beq_iff_eq, beq_self_eq_true, ↓reduceIte, e1, e2, e3, e4, e5, e6, e7, evalRtlExpr,
      evalAluOp, slt, subE, addE, ashrE, ci, bvIter, bvStage_x, bvStage_y, bvStage_z]
    rfl
  | a :: b :: c :: as, i, base, x, y, z, env, _, hx, hy, hz => by
    have ih := cordicWires_eval inp regs (b :: c :: as) (i + 1) (base + 3) base (base + 1) (base + 2)
    simp only [cordicWires, cordicStage, List.cons_append, List.nil_append, List.foldl_cons, cordicLastWire] at ih ⊢
    rw [ih _ (by simp) (by omega) (by omega) (by omega)]
    have e1 : ¬ (base + 1 = base) := (by omega); have e2 : ¬ (base = base + 1) := (by omega); have e3 : ¬ (x = base) := (by omega)
    have e4 : ¬ (y = base) := (by omega); have e5 : ¬ (z = base) := (by omega); have e6 : ¬ (y = base + 1) := (by omega)
    have e7 : ¬ (z = base + 1) := (by omega); have e8 : ¬ (base = base + 2) := (by omega); have e9 : ¬ (base + 1 = base + 2) := (by omega)
    have e10 : ¬ (base + 2 = base) := (by omega); have e11 : ¬ (base + 2 = base + 1) := (by omega); have e12 : ¬ (x = base + 1) := (by omega)
    have e13 : ¬ (z = base + 2) := by omega
    conv => rhs; rw [bvIter]
    simp only [wireStep, beq_iff_eq, beq_self_eq_true, ↓reduceIte, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
      e12, e13, evalRtlExpr, evalAluOp, slt, subE, addE, ashrE, ci, bvStage_x, bvStage_y, bvStage_z]
    rfl
theorem disc_angle_wire (inp regs : Nat → BitVec 64) :
    evalWireTable inp regs sdrFt8DiscModule.wires angleWire
      = (bvIter 0 cordicAtanUrad (bvFold (regs 4) (regs 5)).1 (bvFold (regs 4) (regs 5)).2.1
          (bvFold (regs 4) (regs 5)).2.2).2.2 := by
  have hw : sdrFt8DiscModule.wires = (sdrFt8DiscModule.wires.take 9) ++ cordicWires 0 cordicAtanUrad 9 6 7 8 := by rfl
  rw [evalWireTable_foldl, hw, List.foldl_append]
  have hl : angleWire = cordicLastWire cordicAtanUrad 9 := by decide
  rw [hl, cordicWires_eval inp regs cordicAtanUrad 0 9 6 7 8 _ (by decide) (by omega) (by omega) (by omega)]
  have h6 : (sdrFt8DiscModule.wires.take 9).foldl (wireStep inp regs) (fun _ => 0#64) 6
      = (bvFold (regs 4) (regs 5)).1 := by rfl
  have h7 : (sdrFt8DiscModule.wires.take 9).foldl (wireStep inp regs) (fun _ => 0#64) 7
      = (bvFold (regs 4) (regs 5)).2.1 := by rfl
  have h8 : (sdrFt8DiscModule.wires.take 9).foldl (wireStep inp regs) (fun _ => 0#64) 8
      = (bvFold (regs 4) (regs 5)).2.2 := by rfl
  rw [h6, h7, h8]
/-- **The angle wire is `cordicAtan2` of the accumulators**, for accumulators within `±2^48` (the
lag products of two 16-bit CIC outputs summed over a symbol are far inside). -/
theorem disc_angle_eq_cordicAtan2 (inp regs : Nat → BitVec 64)
    (hre : -2 ^ 48 ≤ (regs 4).toInt ∧ (regs 4).toInt ≤ 2 ^ 48)
    (him : -2 ^ 48 ≤ (regs 5).toInt ∧ (regs 5).toInt ≤ 2 ^ 48) :
    (evalWireTable inp regs sdrFt8DiscModule.wires angleWire).toInt
      = cordicAtan2 (regs 4).toInt (regs 5).toInt := by
  rw [disc_angle_wire]
  obtain ⟨f1, f2, f3⟩ := bvFold_toInt (regs 4) (regs 5) hre him
  have b1 : -2 ^ 48 ≤ (bvFold (regs 4) (regs 5)).1.toInt ∧ (bvFold (regs 4) (regs 5)).1.toInt ≤ 2 ^ 48 := by
    rw [f1]; unfold cordicFold; split <;> constructor <;> simp only [] <;> omega
  have b2 : -2 ^ 48 ≤ (bvFold (regs 4) (regs 5)).2.1.toInt ∧ (bvFold (regs 4) (regs 5)).2.1.toInt ≤ 2 ^ 48 := by
    rw [f2]; unfold cordicFold; split <;> constructor <;> simp only [] <;> omega
  have b3 : -2 ^ 22 ≤ (bvFold (regs 4) (regs 5)).2.2.toInt ∧ (bvFold (regs 4) (regs 5)).2.2.toInt ≤ 2 ^ 22 := by
    rw [f3]; unfold cordicFold cordicPiUrad; split
    · split <;> constructor <;> simp only [] <;> omega
    · constructor <;> simp only [] <;> omega
  obtain ⟨-, -, k3⟩ := bvIter_toInt cordicAtanUrad 0 _ _ _ (2 ^ 48) (2 ^ 22) (by decide) b1 b2 (by decide) b3
    (by decide) (by decide)
  rw [k3, f1, f2, f3]; rfl
/-- **The discriminator decides the tone, at the register-transfer level.** With the symbol's
correlation `acc_re + j·acc_im` (registers 4 and 5, read signed) inside tone `k`'s cone and of
magnitude `|re| + |im| ≥ 2^13`, the value the slicer presents to the `tone_bin` register is `k` and
the out-of-band flag is clear. -/
theorem disc_tone_exact (inp regs : Nat → BitVec 64) (k : Nat) (hk : k ≤ 7)
    (hre : -2 ^ 48 ≤ (regs 4).toInt ∧ (regs 4).toInt ≤ 2 ^ 48)
    (him : -2 ^ 48 ≤ (regs 5).toInt ∧ (regs 5).toInt ≤ 2 ^ 48)
    (hR : 8192 ≤ (regs 4).toInt.natAbs + (regs 5).toInt.natAbs)
    (hc : InToneCone k (regs 4).toInt (regs 5).toInt) :
    evalRtlExpr inp (evalWireTable inp regs sdrFt8DiscModule.wires) regs (binExpr (.wireRef angleWire))
      = BitVec.ofNat 64 k ∧
    evalRtlExpr inp (evalWireTable inp regs sdrFt8DiscModule.wires) regs (oobExpr (.wireRef angleWire))
      = 0#64 := by
  obtain ⟨hb, ho⟩ := binExpr_correct inp (evalWireTable inp regs sdrFt8DiscModule.wires) regs (.wireRef angleWire)
  have ha : (evalRtlExpr inp (evalWireTable inp regs sdrFt8DiscModule.wires) regs (.wireRef angleWire)).toInt
      = cordicAtan2 (regs 4).toInt (regs 5).toInt := disc_angle_eq_cordicAtan2 inp regs hre him
  obtain ⟨t1, t2⟩ := ft8_iq_cordic_slicer_exact_tone k hk _ _ hR hc
  rw [hb, ho, ha, t1, t2]
  exact ⟨rfl, rfl⟩
/-- **A sub-module's wire table inside a larger one.** If the sub-module's wire environment `e`
agrees with the larger environment `env` shifted by `wOff`, and `inp'` are the values of the
expressions driving its ports (which read no wire at or above `wOff`), then after its embedded
wires are evaluated the two still agree, and nothing below `wOff` has changed. -/
theorem embed_wires (pre : String) (wOff rOff : Nat) (inMap : Nat → RtlExpr) (inp regs inp' : Nat → BitVec 64)
    (hdep : ∀ (j : Nat) (env env' : Nat → BitVec 64), (∀ i, i < wOff → env i = env' i) →
      evalRtlExpr inp env regs (inMap j) = evalRtlExpr inp env' regs (inMap j)) :
    ∀ (S : List WireAssign) (env e : Nat → BitVec 64),
      (∀ i, e i = env (i + wOff)) → (∀ j, inp' j = evalRtlExpr inp env regs (inMap j)) →
      (∀ i, S.foldl (wireStep inp' (fun i => regs (i + rOff))) e i
          = (shiftWires pre wOff rOff inMap S).foldl (wireStep inp regs) env (i + wOff)) ∧
      (∀ i, i < wOff → (shiftWires pre wOff rOff inMap S).foldl (wireStep inp regs) env i = env i)
  | [], _, _, hrel, _ => ⟨hrel, fun _ _ => rfl⟩
  | a :: S, env, e, hrel, hin => by
    have hc : shiftWires pre wOff rOff inMap (a :: S)
        = shiftWire pre wOff rOff inMap a :: shiftWires pre wOff rOff inMap S := rfl
    rw [hc]
    simp only [List.foldl_cons]
    have hlow : ∀ i, i < wOff → wireStep inp regs env (shiftWire pre wOff rOff inMap a) i = env i := by
      intro i hi
      have : ¬ (i = a.wireIdx + wOff) := by omega
      simp only [wireStep, shiftWire, beq_iff_eq, this, ↓reduceIte]
    have hrel' : ∀ i, wireStep inp' (fun i => regs (i + rOff)) e a i
        = wireStep inp regs env (shiftWire pre wOff rOff inMap a) (i + wOff) := by
      intro i
      have he : (fun i => env (i + wOff)) = e := funext (fun i => (hrel i).symm)
      have hi' : (fun j => evalRtlExpr inp env regs (inMap j)) = inp' := funext (fun j => (hin j).symm)
      simp only [wireStep, shiftWire, beq_iff_eq, Nat.add_right_cancel_iff, shiftExpr_eval, he, hi', hrel i]
    have hin' : ∀ j, inp' j
        = evalRtlExpr inp (wireStep inp regs env (shiftWire pre wOff rOff inMap a)) regs (inMap j) := by
      intro j; rw [hin j]; exact hdep j _ _ (fun i hi => (hlow i hi).symm)
    obtain ⟨r1, r2⟩ := embed_wires pre wOff rOff inMap inp regs inp' hdep S _ _ hrel' hin'
    exact ⟨r1, fun i hi => by rw [r2 i hi, hlow i hi]⟩
/-- **The discriminator's wires inside the top module are the discriminator's wires**, on the two
CIC output registers and the control ports. -/
theorem top_disc_wires (inp st : Nat → BitVec 64) (i : Nat) :
    evalWireTable (topDiscInputs inp st) (fun j => st (j + 18)) sdrFt8DiscModule.wires i
      = evalWireTable inp st sdrFt8RxTopModule.wires (i + 31) := by
  have hw : sdrFt8RxTopModule.wires = topPrefixWires ++ shiftWires "" 31 18 discIn sdrFt8DiscModule.wires := by rfl
  have hP : ∀ a ∈ topPrefixWires, a.wireIdx < 31 := by decide +kernel
  rw [evalWireTable_foldl, evalWireTable_foldl, hw, List.foldl_append]
  refine (embed_wires "" 31 18 discIn inp st (topDiscInputs inp st) ?_ sdrFt8DiscModule.wires _ _ ?_ ?_).1 i
  · intro j env env' _
    simp only [discIn]; split
    · rfl
    · split <;> rfl
  · intro i
    rw [foldl_wireStep_untouched inp st topPrefixWires _ (i + 31) (fun a ha => by have := hP a ha; omega)]
  · intro j
    simp only [topDiscInputs, discIn]; split
    · rfl
    · split <;> rfl
/-- **End to end in the unified module.** On a clock edge with the decimation strobe high (the
counter at `0`) and `sym_latch` asserted, if the symbol's correlation in the accumulator registers
22 and 23 is inside tone `k`'s cone with `|re| + |im| ≥ 2^13`, the `tone_bin` register (24) loads `k`. -/
theorem top_tone_latch (inp st : Nat → BitVec 64) (k : Nat) (hk : k ≤ 7) (hstrobe : st 3 = 0#64)
    (hlatch : inp 5 ≠ 0#64)
    (hre : -2 ^ 48 ≤ (st 22).toInt ∧ (st 22).toInt ≤ 2 ^ 48)
    (him : -2 ^ 48 ≤ (st 23).toInt ∧ (st 23).toInt ≤ 2 ^ 48)
    (hR : 8192 ≤ (st 22).toInt.natAbs + (st 23).toInt.natAbs)
    (hc : InToneCone k (st 22).toInt (st 23).toInt) :
    stepModuleRegs sdrFt8RxTopModule false inp st 24 = BitVec.ofNat 64 k := by
  have e : stepModuleRegs sdrFt8RxTopModule false inp st 24
      = if evalWireTable inp st sdrFt8RxTopModule.wires strobeWire != 0#64 then
          (if inp 5 != 0#64 then
            evalRtlExpr inp (evalWireTable inp st sdrFt8RxTopModule.wires) st
              (shiftExpr 31 18 discIn (binExpr (.wireRef angleWire)))
           else st 24)
        else st 24 := by rfl
  have hs : evalWireTable inp st sdrFt8RxTopModule.wires strobeWire
      = if st 3 == BitVec.ofInt 64 0 then 1#64 else 0#64 := by rfl
  have h1 : (inp 5 != 0#64) = true := by simpa using hlatch
  rw [e, hs, hstrobe, h1]
  simp only [show ((0#64 : BitVec 64) == BitVec.ofInt 64 0) = true from by decide,
    show ((1#64 : BitVec 64) != 0#64) = true from by decide, ↓reduceIte]
  rw [shiftExpr_eval]
  have hwires : (fun i => evalWireTable inp st sdrFt8RxTopModule.wires (i + 31))
      = evalWireTable (topDiscInputs inp st) (fun j => st (j + 18)) sdrFt8DiscModule.wires :=
    funext (fun i => (top_disc_wires inp st i).symm)
  rw [hwires]
  obtain ⟨hb, -⟩ := binExpr_correct (fun i => evalRtlExpr inp (evalWireTable inp st sdrFt8RxTopModule.wires) st (discIn i))
    (evalWireTable (topDiscInputs inp st) (fun j => st (j + 18)) sdrFt8DiscModule.wires) (fun i => st (i + 18))
    (.wireRef angleWire)
  have ha := disc_angle_eq_cordicAtan2 (topDiscInputs inp st) (fun j => st (j + 18)) hre him
  have hav : (evalRtlExpr (fun i => evalRtlExpr inp (evalWireTable inp st sdrFt8RxTopModule.wires) st (discIn i))
      (evalWireTable (topDiscInputs inp st) (fun j => st (j + 18)) sdrFt8DiscModule.wires) (fun i => st (i + 18))
      (.wireRef angleWire)).toInt = cordicAtan2 (st 22).toInt (st 23).toInt := ha
  rw [hb, hav, (ft8_iq_cordic_slicer_exact_tone k hk _ _ hR hc).1]
end CordicWires
/-- RF-to-discriminator composition. The passive N-path/preselector bound supplies
 the perturbation budget to a calibrated receiver's robust tone cone. The cone margin
 and input power floor are explicit receiver assumptions; passive filtering alone
 does not establish gain/phase calibration or sufficient signal strength. -/
theorem sdr_rf_frontEnd_composition (R : Type) [M : AnalyticModel R]
    (ω r1 r2 incident g φ : CanonicalRat) (es : List Obend.Hardware.SwitchedCapRf.LadderElem)
    (m k : Nat) (hk : k ≤ 7) (x y dx dy : Int)
    (h1 : 0 < r1) (h2 : 0 < r2) (hp : ∀ e ∈ es, e.Passive) (hi : 0 ≤ incident)
    (he : (dx : CanonicalRat)*(dx : CanonicalRat) + (dy : CanonicalRat)*(dy : CanonicalRat) ≤
      Obend.Hardware.SwitchedCapRf.compositeAliasPower ω r1 r2 es m * incident)
    (margin : ∀ ex ey : Int,
      (ex : CanonicalRat)*(ex : CanonicalRat) + (ey : CanonicalRat)*(ey : CanonicalRat) ≤
        (1 / (((2*m+1 : Nat) : CanonicalRat) * ((2*m+1 : Nat) : CanonicalRat))) * incident →
      InToneCone k (x+ex) (y+ey))
    (hR : 8192 ≤ (x+dx).natAbs + (y+dy).natAbs)
    (hg : CanonicalRat.mk 999 1000 ≤ g ∧ g ≤ CanonicalRat.mk 1001 1000)
    (hφ : φ ∈ irrPhaseDom) :
    ft8Bin (Obend.Hardware.SwitchedCapRf.cordicAtan2 (x+dx) (y+dy)) = k ∧
    ft8Oob (Obend.Hardware.SwitchedCapRf.cordicAtan2 (x+dx) (y+dy)) = false ∧
    irrK * (1 - 2*g*M.cosFn φ + g*g) ≤ 1 + 2*g*M.cosFn φ + g*g := by
  have hb := Obend.Hardware.SwitchedCapRf.rf_frontEnd_error_power ω r1 r2 incident _ es m h1 h2 hp hi he
  have ht := ft8_iq_cordic_slicer_exact_tone k hk _ _ hR (margin dx dy hb)
  exact ⟨ht.1, ht.2, sdr_irr_ge_63dB R g φ hg hφ⟩
end Obend.Apps.SdrFt8Rx
