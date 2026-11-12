module
public import Obend.Hardware.HDL
public import Obend.Hardware.Cic
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
-/

@[expose] public section

namespace Obend.Apps.SdrFt8Rx

open Obend.Hardware.HDL
open Obend.Hardware.Cic

set_option autoImplicit false

def trunc34 (e : RtlExpr) : RtlExpr := .resize (.trunc 34) e

def cicReg (i : Nat) (n : String) (e : RtlExpr) : RegSpec :=
  { regIdx := i, name := n, domain := .coreClk, resetKind := .syncReset 0#64,
    isSynchronizer := false, nextExpr := e, width := 34 }

def sdrCicModule : RtlModule where
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

theorem c3_eq_cicOut (x : Signal) : c3 x = cicOut 64 1 3 x := rfl

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

theorem sel_one (a b : BitVec 64) : sel 1#64 a b = a := rfl
theorem sel_zero (a b : BitVec 64) : sel 0#64 a b = b := rfl

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

/-- `atan(2^-i)` in µrad, `i = 0..11`. -/
def cordicAtanUrad : List Int :=
  [785398, 463648, 244979, 124355, 62419, 31240, 15624, 7812, 3906, 1953, 977, 488]

def piUrad : Int := 3141593

/-- The slicer thresholds `(2k-1)·π/15` in µrad, `k = 1..7` (rounded to the nearest µrad). -/
def ft8Thresholds : List Int := [209440, 628319, 1047198, 1466077, 1884956, 2303835, 2722714]

/-- The tone the slicer decides for an angle `a` (µrad): the number of thresholds at or below `a`. -/
def ft8Bin (a : Int) : Nat := (ft8Thresholds.filter (fun t => decide (t ≤ a))).length

/-- Out of band: more than half a tone spacing below tone 0. -/
def ft8Oob (a : Int) : Bool := decide (a < -209440)

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

def sdrFt8DiscModule : RtlModule where
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

def sdrNcoModule : RtlModule where
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

end Obend.Apps.SdrFt8Rx
