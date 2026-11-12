module

public import Lean
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Logic.Program
public import Obend.Logic.Obligation
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Static
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.Types
public import Obend.Hardware.CurrentLoop
public import Obend.Hardware.Analog
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.SosLyapunov
public import Obend.Analysis.EqSatHypergraph
public meta import Lean
public meta import Obend.Core.Term
public meta import Obend.Law
public meta import Obend.Spec.Syntax
public meta import Obend.Spec.Parse
public meta import Obend.Spec.Elaborate
public meta import Obend.Spec.FrontEnd
public meta import Obend.Spec.Capture
public meta import Obend.Spec.Sha256
public meta import Obend.Logic.LateBinding
public meta import Obend.Logic.Claim
public meta import Obend.Logic.Rewrite
public meta import Obend.Logic.Frame
public meta import Obend.Logic.Obligation
public meta import Obend.Logic.Program
public meta import Obend.Leaf.Flatten
public meta import Obend.Leaf.Emit
public meta import Obend.Judge.RealAnalysis
public import Obend.Analysis.RealAnalysis
public import Obend.Elab.Workbook
public meta import Obend.Analysis.RealAnalysis
public meta import Obend.Analysis.TaylorModel
public meta import Obend.Analysis.SosLyapunov
public meta import Obend.Elab.Workbook
import all Obend.Judge.Class
import all Obend.Logic.Obligation

/-!
# Obend.Apps.FocHil — Flagship App #2: Closed-Loop 20 kHz FOC Motor Drive & 6-Level SiC FCML HIL

Formalizes and verifies **Flagship Application #2** (`apps/foc-hil/`) from
`QUALIFICATION-AND-SILICON-LEAN.md` §4:

1. **Multi-Layer `.obend` Motor-Control & Power-Electronics Stack (`#import_obend`)**:
   Elaborates all four `.obend` modules in `apps/foc-hil/` at Lean compile time:
   - `apps/foc-hil/ClarkePark.obend` (`FocClarkePark`)
   - `apps/foc-hil/PiCurrentLoop.obend` (`FocPiCurrentLoop`)
   - `apps/foc-hil/SicFcmlInverterLeg.obend` (`FocSicFcmlLeg`)
   - `apps/foc-hil/FocDriveTop.obend` (`FocDriveTop`)
   including transitive multi-file `import ./....obend as ...` closure resolution,
   `FrontEnd.accept`, open-recursive `Composition` extraction, `Leaf.Book` emission,
   compile-time `AutoCert` witness synthesis for `by judge("taylor-model@1")`,
   `by judge("interval@1")`, and `by judge("sos-lyapunov-cbf@1")`, and machine-checked
   `obligationMeaningWithJudges` proofs for all 10 `.obend` claims (6 open-recursive
   `.byDerivation` claims + 4 external-judge `.byExternalJudge` claims).

2. **Closed-Loop 20 kHz Sampled-Data ISS Contraction, Thermal/Current CBF & Coupled Adjoint**:
   Connects the elaborated `.obend` FOC + 6-level SiC FCML controller to:
   - `Obend.Hardware.DigitalTwin.sampled_data_current_loop_iss_contraction`
   - `Obend.Hardware.DigitalTwin.sampled_data_closed_loop_powertrain_safety_invariant`
   - `Obend.Hardware.PowerElectronics.fcml_active_balancing_lyapunov_contraction`
   - `Obend.Analysis.statorCoupledLoss_adjoint_eqSat_sound`
   - `Obend.Analysis.sos_lyapunov_cbf_dae_showcase_sound` (`"sos-lyapunov-cbf@1"`)
   in the master theorem `foc_hil_closed_loop_iss_and_thermal_safe`.

4. **Sequential `always_ff` Hardware Synthesis & Live Mid-Run ICAP DPR Hot-Swap**:
   Synthesizes both 1-arg and multi-argument stateful `always_ff` `.obend` `Book`s
   (`compileStatefulTermsToRtl` / `compileStatefulStepToRtl`) and the full sequential
   `always_ff` FOC + FCML controller (`int_d`, `int_q`, `fcml_cap_err`, `thermal_trip_latch`,
   `skid_vq_hold`, `skid_vd_hold`) to verified `RtlModule`s and FPGA `BelNetlist`s, and proves
   cross-package dependency cone survival
   (`foc_hil_crossPackage_dpr_hotswap_and_cone_survives`).
-/

@[expose] public section

namespace Obend.Apps.FocHil

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Judge
open Obend.Hardware.HDL
open Obend.Hardware.Types
open Obend.Hardware.Compiler
open Obend.Hardware.Synth
open Obend.Hardware.CurrentLoop
open Obend.Hardware.Analog
open Obend.Hardware.OpenHypergraph
open Obend.Analysis

set_option autoImplicit false

/-! ## 1. Kernel-Verified `AutoCert` External Judge Formats (`interval@1`, `taylor-model@1`, `sos-lyapunov-cbf@1`) -/

def focNatToCharsFuel : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let d := Char.ofNat (48 + (n % 10))
    let q := n / 10
    if q == 0 then d :: acc
    else focNatToCharsFuel fuel q (d :: acc)

def focNatToStr (n : Nat) : String :=
  String.ofList (focNatToCharsFuel 32 n [])

def focIntToStr : Int → String
  | .ofNat n   => focNatToStr n
  | .negSucc n => "-" ++ focNatToStr (n + 1)

def focJoinSep (sep : String) : List String → String
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ focJoinSep sep xs

def focSplitCharAux (sep : Char) : List Char → List Char → List String
  | [], cur => [String.ofList cur.reverse]
  | c :: cs, cur =>
    if c == sep then
      String.ofList cur.reverse :: focSplitCharAux sep cs []
    else
      focSplitCharAux sep cs (c :: cur)

def focSplitChar (sep : Char) (s : String) : List String :=
  focSplitCharAux sep s.toList []

def focParseNatChars : List Char → Nat → Bool → Option Nat
  | [], acc, true  => some acc
  | [], _, false   => none
  | c :: cs, acc, _ =>
    if '0' ≤ c && c ≤ '9' then
      focParseNatChars cs (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      none

def focParseNat? (s : String) : Option Nat :=
  focParseNatChars s.toList 0 false

def focParseInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (focParseNatChars cs 0 false).map fun n => -(Int.ofNat n)
  | cs        => (focParseNatChars cs 0 false).map Int.ofNat

def focEncodeRatWire (q : CanonicalRat) : String :=
  focIntToStr q.num ++ "/" ++ focNatToStr q.den

def focDecodeRatWire? (s : String) : Option CanonicalRat :=
  match focSplitChar '/' s with
  | [nStr, dStr] => do
    let n ← focParseInt? nStr
    let d ← focParseNat? dStr
    if d == 0 then none else some (CanonicalRat.mk n d)
  | [nStr] => do
    let n ← focParseInt? nStr
    some (Rat.ofInt n)
  | _ => none

def focEncodeIntervalWire (iv : Interval) : String :=
  focEncodeRatWire iv.lo ++ ":" ++ focEncodeRatWire iv.hi

def focDecodeIntervalWire? (s : String) : Option Interval :=
  match focSplitChar ':' s with
  | [loStr, hiStr] => do
    let lo ← focDecodeRatWire? loStr
    let hi ← focDecodeRatWire? hiStr
    some ⟨lo, hi⟩
  | _ => none

def focFindQuotedJsonFieldAux (key : String) : List String → Option String
  | k :: sep :: val :: rest =>
    if k == key && sep == ":" then some val
    else focFindQuotedJsonFieldAux key (sep :: val :: rest)
  | _ => none

def focExtractJsonStringField? (key : String) (raw : String) : Option String :=
  focFindQuotedJsonFieldAux key (focSplitChar '"' raw)

def focEncodeRealExprTokens : RealExpr → List String
  | .const q => ["C", focEncodeRatWire q]
  | .var v   => ["V", v]
  | .add l r => "A" :: (focEncodeRealExprTokens l ++ focEncodeRealExprTokens r)
  | .sub l r => "S" :: (focEncodeRealExprTokens l ++ focEncodeRealExprTokens r)
  | .mul l r => "M" :: (focEncodeRealExprTokens l ++ focEncodeRealExprTokens r)
  | .sqr a   => "Q" :: focEncodeRealExprTokens a

def focDecodeRealExprTokens : Nat → List String → Option (RealExpr × List String)
  | 0, _ => none
  | _ + 1, "C" :: qStr :: rest => do
    let q ← focDecodeRatWire? qStr
    some (.const q, rest)
  | _ + 1, "V" :: v :: rest => some (.var v, rest)
  | fuel + 1, "A" :: rest => do
    let (l, r1) ← focDecodeRealExprTokens fuel rest
    let (r, r2) ← focDecodeRealExprTokens fuel r1
    some (.add l r, r2)
  | fuel + 1, "S" :: rest => do
    let (l, r1) ← focDecodeRealExprTokens fuel rest
    let (r, r2) ← focDecodeRealExprTokens fuel r1
    some (.sub l r, r2)
  | fuel + 1, "M" :: rest => do
    let (l, r1) ← focDecodeRealExprTokens fuel rest
    let (r, r2) ← focDecodeRealExprTokens fuel r1
    some (.mul l r, r2)
  | fuel + 1, "Q" :: rest => do
    let (a, r1) ← focDecodeRealExprTokens fuel rest
    some (.sqr a, r1)
  | _, _ => none

def focEncodeIntervalEnvWire (env : List (String × Interval)) : String :=
  if env.isEmpty then "-"
  else focJoinSep "," (env.map fun (v, iv) => v ++ "=" ++ focEncodeIntervalWire iv)

def focDecodeIntervalEnvWire? (s : String) : Option (List (String × Interval)) :=
  if s == "-" || s == "" then some []
  else
    (focSplitChar ',' s).mapM fun item =>
      match focSplitChar '=' item with
      | [v, ivStr] => do
        let iv ← focDecodeIntervalWire? ivStr
        some (v, iv)
      | _ => none

def focEncodeIntervalQuery (q : IntervalQuery) : String :=
  let wire :=
    focJoinSep "~" (focEncodeRealExprTokens q.expr) ++ "|" ++
    focEncodeIntervalEnvWire q.env ++ "|" ++
    focEncodeIntervalWire q.claimedBound
  "{\"kind\":\"interval@1\",\"wire\":\"" ++ wire ++ "\"}"

def focDecodeIntervalQuery (s : String) : Except String IntervalQuery :=
  if s == "{}" || s == "" then
    .error "invalid IntervalQuery JSON: missing required fields"
  else
    match focExtractJsonStringField? "wire" s with
    | some wire =>
      match focSplitChar '|' wire with
      | [exprW, envW, bndW] =>
        match focDecodeRealExprTokens 64 (focSplitChar '~' exprW),
              focDecodeIntervalEnvWire? envW,
              focDecodeIntervalWire? bndW with
        | some (expr, []), some env, some claimedBound => .ok { expr, env, claimedBound }
        | _, _, _ => .error "invalid IntervalQuery wire fields"
      | _ => .error "invalid IntervalQuery wire envelope"
    | none => .error "invalid IntervalQuery JSON: missing wire field"

def focEncodeIntervalCert : IntervalCert → String
  | .direct => "{\"kind\":\"direct\",\"wire\":\"D\"}"
  | .counterexample _ => "{\"kind\":\"counterexample\",\"wire\":\"X\"}"

def focDecodeIntervalCert (s : String) : Except String IntervalCert :=
  if s == "{}" || s == "" then
    .error "invalid IntervalCert JSON: missing required fields"
  else
    match focExtractJsonStringField? "wire" s with
    | some "D" => .ok .direct
    | _ => .error "invalid IntervalCert wire"

def focBadIntervalQuery : IntervalQuery where
  expr         := .var "x"
  env          := [("x", ⟨0, 10⟩)]
  claimedBound := ⟨0, 2⟩

theorem focBadIntervalCert_refused :
    intervalCheck 0 focBadIntervalQuery .direct =
      .refused (.boundViolated ⟨0, 10⟩ ⟨0, 2⟩) [] := rfl

/-- Registered kernel-verified `"interval@1"` `Judge.Format` backed by `Obend.Judge.intervalJudge`. -/
def focIntervalFormat : Judge.Format where
  name        := "interval"
  version     := "1"
  Obj         := IntervalQuery
  Cert        := IntervalCert
  judge       := intervalJudge
  decodeObj   := focDecodeIntervalQuery
  decodeCert  := focDecodeIntervalCert
  trust       := .kernel
  regime      := .decidable
  bad         := (focBadIntervalQuery, .direct)
  badGrade    := 0
  bad_refused := ⟨_, _, focBadIntervalCert_refused⟩

/-- Query for certified `"taylor-model@1"` CORDIC trigonometric enclosure $\cos(\theta) + \sin(\theta)$
    over `domain` $\subseteq [-1, 1]$ inside `claimedBound`. -/
structure FocTaylorTrigQuery where
  domain       : Interval
  claimedBound : Interval
  deriving DecidableEq, Repr

def verifyFocTaylorTrigCert (q : FocTaylorTrigQuery) (tm : TaylorModel) : Bool :=
  decide (q.domain.lo ≤ q.domain.hi) &&
  q.domain.isSubintervalOf ⟨-1, 1⟩ &&
  (let compTm := tmAdd (tmCosCertified q.domain) (tmSinCertified q.domain)
   (compTm == tm) && (evalTaylorModelRange tm).isSubintervalOf q.claimedBound)

def checkFocTaylorTrigJudge (_grade : Nat) (q : FocTaylorTrigQuery) (tm : TaylorModel) :
    Judge.Verdict String :=
  if verifyFocTaylorTrigCert q tm then .ok
  else .refused "taylor_model_enclosure_violation" []

theorem checkFocTaylorTrigJudge_sound (grade : Nat) (q : FocTaylorTrigQuery) (tm : TaylorModel)
    (h : checkFocTaylorTrigJudge grade q tm = .ok) :
    verifyFocTaylorTrigCert q tm = true ∧
    (evalTaylorModelRange tm).isSubintervalOf q.claimedBound = true := by
  unfold checkFocTaylorTrigJudge at h
  cases hV : verifyFocTaylorTrigCert q tm with
  | false => rw [hV] at h; contradiction
  | true =>
    refine ⟨rfl, ?_⟩
    unfold verifyFocTaylorTrigCert at hV
    rcases (Bool.and_eq_true _ _).mp hV with ⟨_, hSub⟩
    exact ((Bool.and_eq_true _ _).mp hSub).2

@[instance_reducible] def focTaylorTrigJudge : Judge FocTaylorTrigQuery TaylorModel where
  Clause := String
  Meaning q tm :=
    verifyFocTaylorTrigCert q tm = true ∧
    (evalTaylorModelRange tm).isSubintervalOf q.claimedBound = true
  check := checkFocTaylorTrigJudge
  sound := by intro r q tm h; exact checkFocTaylorTrigJudge_sound r q tm h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ tm, verifyFocTaylorTrigCert q tm = true
  complete := by
    intro q _ ⟨tm, htm⟩
    exact ⟨tm, 0, by simp [checkFocTaylorTrigJudge, htm]⟩
  mono := by intro _ _ _ _ _ _; rfl

def focEncodeTaylorTrigQuery (q : FocTaylorTrigQuery) : String :=
  let wire := focEncodeIntervalWire q.domain ++ "|" ++ focEncodeIntervalWire q.claimedBound
  "{\"kind\":\"taylor-model@1\",\"wire\":\"" ++ wire ++ "\"}"

def focDecodeTaylorTrigQuery (s : String) : Except String FocTaylorTrigQuery :=
  if s == "{}" || s == "" then
    .error "invalid FocTaylorTrigQuery JSON: missing required fields"
  else
    match focExtractJsonStringField? "wire" s with
    | some wire =>
      match focSplitChar '|' wire with
      | [domW, bndW] =>
        match focDecodeIntervalWire? domW, focDecodeIntervalWire? bndW with
        | some domain, some claimedBound => .ok { domain, claimedBound }
        | _, _ => .error "invalid FocTaylorTrigQuery wire fields"
      | _ => .error "invalid FocTaylorTrigQuery wire envelope"
    | none => .error "invalid FocTaylorTrigQuery JSON: missing wire field"

def focEncodeTaylorModelCert (tm : TaylorModel) : String :=
  let coeffsW :=
    if tm.coeffs.isEmpty then "-"
    else focJoinSep "," (tm.coeffs.map focEncodeRatWire)
  let wire :=
    coeffsW ++ "|" ++
    focEncodeRatWire tm.center ++ "|" ++
    focEncodeIntervalWire tm.domain ++ "|" ++
    focEncodeIntervalWire tm.rem
  "{\"kind\":\"taylor-model-cert@1\",\"wire\":\"" ++ wire ++ "\"}"

def focDecodeTaylorModelCert (s : String) : Except String TaylorModel :=
  if s == "{}" || s == "" then
    .error "invalid TaylorModel JSON: missing required fields"
  else
    match focExtractJsonStringField? "wire" s with
    | some wire =>
      match focSplitChar '|' wire with
      | [coeffsW, ctrW, domW, remW] =>
        let coeffsOpt : Option (List CanonicalRat) :=
          if coeffsW == "-" || coeffsW == "" then some []
          else (focSplitChar ',' coeffsW).mapM focDecodeRatWire?
        match coeffsOpt, focDecodeRatWire? ctrW, focDecodeIntervalWire? domW, focDecodeIntervalWire? remW with
        | some coeffs, some center, some domain, some rem =>
          .ok { coeffs, center, domain, rem }
        | _, _, _, _ => .error "invalid TaylorModel wire fields"
      | _ => .error "invalid TaylorModel wire envelope"
    | none => .error "invalid TaylorModel JSON: missing wire field"

def focGoldenTaylorTrigQuery : FocTaylorTrigQuery where
  domain       := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  claimedBound := ⟨CanonicalRat.mk 4 5, CanonicalRat.mk 6 5⟩

def focBadTaylorModelCert : TaylorModel where
  coeffs := [0]
  center := 0
  domain := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  rem    := ⟨0, 0⟩

theorem focBadTaylorModelCert_refused :
    checkFocTaylorTrigJudge 0 focGoldenTaylorTrigQuery focBadTaylorModelCert =
      .refused "taylor_model_enclosure_violation" [] := by
  decide +kernel

/-- Registered kernel-verified `"taylor-model@1"` `Judge.Format` backed by `Obend.Analysis.TaylorModel`. -/
def focTaylorModelFormat : Judge.Format where
  name        := "taylor-model"
  version     := "1"
  Obj         := FocTaylorTrigQuery
  Cert        := TaylorModel
  judge       := focTaylorTrigJudge
  decodeObj   := focDecodeTaylorTrigQuery
  decodeCert  := focDecodeTaylorModelCert
  trust       := .kernel
  regime      := .decidable
  bad         := (focGoldenTaylorTrigQuery, focBadTaylorModelCert)
  badGrade    := 0
  bad_refused := ⟨_, _, focBadTaylorModelCert_refused⟩

/-- Registered external judge formats for `apps/foc-hil/` (`interval@1`, `taylor-model@1`,
    `sos-lyapunov-cbf@1`, plus `Obend.Logic.defaultExternalFormats`). -/
def focAutoCertFormats : List Judge.Format :=
  [focIntervalFormat, focTaylorModelFormat, sosLyapunovFormat] ++ Obend.Logic.defaultExternalFormats

theorem focAutoCertFormats_refuse_empty_json :
    focIntervalFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid IntervalQuery JSON: missing required fields") [] ∧
    focTaylorModelFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid FocTaylorTrigQuery JSON: missing required fields") [] ∧
    sosLyapunovFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid SosLyapunovProblem JSON: missing required fields") [] := by
  exact ⟨rfl, rfl, sosLyapunovFormat_refuses_empty_json⟩

/-! ## 0. `#import_obend` is `Obend.Elab.Workbook`'s (the one importer, 2026-11-04); this module
only consumes the constants it emits (`<def>_comp`, `<def>_book`, `<def>_val`, `claim_*_{obj,just,holds}`,
`laws_count`). -/

/-! ## 3. Compile-Time Elaboration of `apps/foc-hil/*.obend` -/

#import_obend "apps/foc-hil/ClarkePark.obend" as FocClarkePark
#import_obend "apps/foc-hil/PiCurrentLoop.obend" as FocPiCurrentLoop
#import_obend "apps/foc-hil/SicFcmlInverterLeg.obend" as FocSicFcmlLeg
#import_obend "apps/foc-hil/FocDriveTop.obend" as FocDriveTop

/-! ## 4. Open-Recursive Compositions, Vtable Flattening & `Leaf.Book` Soundness -/

/-- Open-recursive `Composition` for `compensatedClarkePark()` in `ClarkePark.obend`. -/
def clarkeParkComp : Composition :=
  FocClarkePark.compensatedClarkePark_comp

/-- Open-recursive `Composition` for `decoupledPiCurrentController()` in `PiCurrentLoop.obend`. -/
def piCurrentLoopComp : Composition :=
  FocPiCurrentLoop.decoupledPiCurrentController_comp

/-- Open-recursive `Composition` for `lyapunovBalancedSicFcmlLeg()` in `SicFcmlInverterLeg.obend`. -/
def sicFcmlLegComp : Composition :=
  FocSicFcmlLeg.lyapunovBalancedSicFcmlLeg_comp

/-- Nominal 20 kHz FOC `Composition` (`nominalFocDrive()`) before ICAP DPR hot-swap. -/
def nominalFocDriveComp : Composition :=
  FocDriveTop.nominalFocDrive_comp

/-- Hot-swapped high-bandwidth ICAP DPR FOC `Composition` (`icapDprHotSwappedFocDrive()`). -/
def focDriveTopComp : Composition :=
  FocDriveTop.icapDprHotSwappedFocDrive_comp

theorem clarkeParkComp_closed : clarkeParkComp.closedB = true := by decide +kernel
theorem piCurrentLoopComp_closed : piCurrentLoopComp.closedB = true := by decide +kernel
theorem sicFcmlLegComp_closed : sicFcmlLegComp.closedB = true := by decide +kernel
theorem nominalFocDriveComp_closed : nominalFocDriveComp.closedB = true := by decide +kernel
theorem focDriveTopComp_closed : focDriveTopComp.closedB = true := by decide +kernel

/-- **Vtable Flattening & Leaf Book Soundness across all 4 `apps/foc-hil/` Layers**. -/
theorem foc_hil_flatten_and_book_sound (m : String) :
    (.get clarkeParkComp.flatten m ≈b .get clarkeParkComp.object m) ∧
    (.get (emit clarkeParkComp).link m ≈b .get clarkeParkComp.object m) ∧
    (.get piCurrentLoopComp.flatten m ≈b .get piCurrentLoopComp.object m) ∧
    (.get (emit piCurrentLoopComp).link m ≈b .get piCurrentLoopComp.object m) ∧
    (.get sicFcmlLegComp.flatten m ≈b .get sicFcmlLegComp.object m) ∧
    (.get (emit sicFcmlLegComp).link m ≈b .get sicFcmlLegComp.object m) ∧
    (.get focDriveTopComp.flatten m ≈b .get focDriveTopComp.object m) ∧
    (.get (emit focDriveTopComp).link m ≈b .get focDriveTopComp.object m) :=
  ⟨flatten_sound clarkeParkComp clarkeParkComp_closed m,
   book_sound clarkeParkComp clarkeParkComp_closed m,
   flatten_sound piCurrentLoopComp piCurrentLoopComp_closed m,
   book_sound piCurrentLoopComp piCurrentLoopComp_closed m,
   flatten_sound sicFcmlLegComp sicFcmlLegComp_closed m,
   book_sound sicFcmlLegComp sicFcmlLegComp_closed m,
   flatten_sound focDriveTopComp focDriveTopComp_closed m,
   book_sound focDriveTopComp focDriveTopComp_closed m⟩

/-- **Static `super` Elimination & Slot Dependency Certificate for `FocDriveTop.obend`**. -/
theorem focDriveTop_book_shape_verified :
    let B := emit focDriveTopComp
    B.slots = [ "icapDprBandwidthGain"
              , "statorThermalResPermille"
              , "activeFcmlBalanceMv"
              , "controlFreqKhz"
              , "closedLoopVqMv"
              , "statorWindingTempC" ] ∧
    B.defs.map (fun d => (d.member, d.slot, d.kind, d.reads)) =
      [ ("icapDprBandwidthGain", 0, .cell, [])
      , ("statorThermalResPermille", 1, .cell, [])
      , ("activeFcmlBalanceMv", 2, .method, [])
      , ("controlFreqKhz", 3, .cell, [])
      , ("closedLoopVqMv", 4, .method, [0])
      , ("statorWindingTempC", 5, .method, [1])
      ] ∧
    B.closedB = true := by
  decide +kernel

/-! ## 6. Closed-Loop 20 kHz Sampled-Data ISS Contraction, Thermal/Current CBF & Coupled Adjoint -/

/-- **Master Closed-Loop ISS Ultimate-Boundedness, Quantized PI/ADC, FCML Balancing & Coupled Adjoint Theorem
    (`foc_hil_closed_loop_iss_and_thermal_safe`)**:
    1. **20 kHz Exact ZOH RL Current-Loop Contraction (`CurrentLoop.lc_drives_current_loop_converges`)**:
       For every pole $(a, b)$ inside the certified Taylor-model enclosure of $\exp(-(R/L) T_s)$ across the
       LC Drives stator resistance/inductance box ($R \in [10, 14]\,\text{m}\Omega$, $L = 150\,\mu\text{H}$,
       $T_s = 50\,\mu\text{s}$), $V_P(s_{k+1}) \le \frac{135}{136} V_P(s_k)$ with $4(i_k - r)^2 \le (135/136)^k \cdot 34 (x_0^2 + z_0^2)$.
    2. **Quantized `rtlPiStep` + 1-mA ADC ISS Ultimate-Boundedness Ball (`CurrentLoop.lc_drives_quantized_current_loop_iss_ball`)**:
       Combining `discrete_lyapunov_decay` with `rtlPiStep_within_lsb` and `adcFloorMa_within_lsb` via
       `discrete_lyapunov_iss_ball`, the integer-quantized 20 kHz PI loop contracts geometrically at rate
       $\rho_{\text{iss}} = 271/272 < 1$ into the forward-invariant sublevel ball
       $V_P \le R_{\text{ball}} = 626552 / 125000 \approx 5.0124$, strictly decaying outside $R_{\text{ball}}$
       on every tick and bounding ultimate current error for all $k \in \mathbb{N}$, while
       `rtlPiStepQ32_within_lsb` and `runSarAdcN_exact_quantization_bounds` bound Q32 multiplier shifts
       and $N$-bit SAR ADC quantization strictly within $1\text{ LSB}$.
    3. **6-Level SiC FCML Active Lyapunov Capacitor Balancing**:
       For any flying-capacitor voltage unbalance $e_k$ and damped active balancing correction $c_k$
       satisfying $0 \le c_k (2 e_k - c_k)$, quadratic capacitor unbalance energy contracts:
       $(e_k - c_k)^2 \le e_k^2$.
    4. **Coupled Electro-Thermal Stator Loss Adjoint Soundness**:
       `statorCoupledLoss_adjoint_eqSat_sound` proves that E-Graph optimization reduces hardware cost
       from $96 \to 76$ while preserving exact forward peak temperature and all 4 reverse-mode adjoint
       sensitivities.
    5. **SOS Lyapunov, Control Barrier & DAE Certificate (`"sos-lyapunov-cbf@1"`)**:
       `checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok`. -/
theorem foc_hil_closed_loop_iss_and_thermal_safe :
    (∀ (d : ZohRl),
      d.a ∈ (⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩ : Interval) →
      d.b ∈ (⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩ : Interval) →
      d.b * d.plant.rOhm = 1 - d.a →
      ∀ (rMa vffMv : Int) (qs0 : QuantizedLoopState),
        let r := ratMilli rMa
        let vff := ratMilli vffMv
        let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
          let s := (iterateQuantizedRtlLoop d 400 50 rMa vffMv k qs0).toLoopState
          (errX r s, errZ d r vff s)
        (∀ k, quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 - lcIssBallRadius ≤
          ratPow lcRhoIss k * (quadForm lcP11 lcP12 lcP22 (traj 0).1 (traj 0).2 - lcIssBallRadius)) ∧
        (∀ k, lcIssBallRadius < quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 →
          quadForm lcP11 lcP12 lcP22 (traj (k + 1)).1 (traj (k + 1)).2 <
            quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2) ∧
        (quadForm lcP11 lcP12 lcP22 (traj 0).1 (traj 0).2 ≤ lcIssBallRadius →
          ∀ k, quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 ≤ lcIssBallRadius) ∧
        (∀ k, lcM * ((traj k).1 * (traj k).1) ≤
          ratPow lcRhoIss k * (lcC * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + lcIssBallRadius)) ∧
    (∀ (kpQ32 kiQ32 errMa intMv : Int) (bits vInMv vLsbMv : Nat),
      0 < vLsbMv →
      let (int', v) := rtlPiStepQ32 kpQ32 kiQ32 errMa intMv
      4294967296 * (int' - intMv) ≤ errMa * kiQ32 ∧
      errMa * kiQ32 < 4294967296 * (int' - intMv) + 4294967296 ∧
      4294967296 * (v - int') ≤ errMa * kpQ32 ∧
      errMa * kpQ32 < 4294967296 * (v - int') + 4294967296 ∧
      (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
      (vInMv < 2 ^ bits * vLsbMv → vInMv < (runSarAdcN bits 0 vInMv vLsbMv + 1) * vLsbMv)) ∧
    (∀ (vErrMv corrMv : Int),
      0 ≤ corrMv * (2 * vErrMv - corrMv) →
      (vErrMv - corrMv) * (vErrMv - corrMv) ≤ vErrMv * vErrMv) ∧
    (∀ (currentA toothWidthUm channelAspect fcmlFreqKhz dOut : Int),
      let gAdj := compileGraphAdjoint statorCoupledLossHypergraph
      let gOpt := optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph
      let env := statorCoupledLossAdjointEnv currentA toothWidthUm channelAspect fcmlFreqKhz dOut
      evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
      evalHypergraphComb gOpt env = evalHypergraphComb gAdj env) ∧
    checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok := by
  refine ⟨?_, ?_, ?_, ?_, sos_lyapunov_cbf_dae_showcase_sound.2.2.2⟩
  · intro d ha hb hbR rMa vffMv qs0
    exact lc_drives_quantized_current_loop_iss_ball d ha hb hbR rMa vffMv qs0
  · intro kpQ32 kiQ32 errMa intMv bits vInMv vLsbMv hLsbPos
    have hPi := rtlPiStepQ32_within_lsb kpQ32 kiQ32 errMa intMv
    have hAdc := runSarAdcN_exact_quantization_bounds bits vInMv vLsbMv hLsbPos
    exact ⟨hPi.1, hPi.2.1, hPi.2.2.1, hPi.2.2.2, hAdc.1, hAdc.2.2⟩
  · intro vErrMv corrMv hDamp
    have hExpand : vErrMv * vErrMv - (vErrMv - corrMv) * (vErrMv - corrMv) =
        corrMv * (2 * vErrMv - corrMv) := by grind
    omega
  · intro currentA toothWidthUm channelAspect fcmlFreqKhz dOut
    have h := statorCoupledLoss_adjoint_eqSat_sound currentA toothWidthUm channelAspect fcmlFreqKhz dOut
    exact ⟨h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## 7. Hardware Synthesis, Multi-Arg `compileStatefulStepToRtl` & ICAP DPR Hot-Swap -/

/-- Compile all 4 `apps/foc-hil/` `.obend` `Book`s to `RtlModule`s via `compileBookToRtl`. -/
def clarkeParkRtl? : Option RtlModule :=
  compileBookToRtl "foc_clarke_park" FocClarkePark.compensatedClarkePark_book

def piCurrentLoopRtl? : Option RtlModule :=
  compileBookToRtl "foc_pi_current_loop" FocPiCurrentLoop.decoupledPiCurrentController_book

def sicFcmlLegRtl? : Option RtlModule :=
  compileBookToRtl "foc_sic_fcml_leg" FocSicFcmlLeg.lyapunovBalancedSicFcmlLeg_book

def focDriveTopRtl? : Option RtlModule :=
  compileBookToRtl "foc_drive_top_comb" FocDriveTop.icapDprHotSwappedFocDrive_book

/-- Empty struct/union layout context for scalar 64-bit multi-argument stateful step lowering. -/
def emptyFocLayoutCtx : RtlLayoutCtx :=
  { structSlices := [], unionTagBits := 8, unionArms := [] }

/-- Compile the multi-argument stateful `always_ff` `.obend` methods (`alwaysFfNextIntD`,
    `alwaysFfNextIntQ`, `alwaysFfOutVqMv`) from `FocPiCurrentLoop.hotSwappedPiStatefulStep_book`
    directly into a synchronous `RtlModule` via `compileStatefulTermsToRtl`. -/
def focStatefulPiFromObendRtl? : Option RtlModule := do
  let B := FocPiCurrentLoop.hotSwappedPiStatefulStep_book
  let nextIntD ← lookupBookCode B "alwaysFfNextIntD"
  let nextIntQ ← lookupBookCode B "alwaysFfNextIntQ"
  let outVq    ← lookupBookCode B "alwaysFfOutVqMv"
  compileStatefulTermsToRtl
    "foc_pi_stateful_step"
    emptyFocLayoutCtx
    ["kpStepMv", "kiStepMv"]
    [ .alu .mul (.inputPort 0) (.const 480#64)
    , .alu .mul (.inputPort 0) (.const 65#64) ]
    ["err_d_ma", "err_q_ma"]
    [("int_d", 0#64), ("int_q", 0#64)]
    [nextIntD, nextIntQ]
    [("vq_cmd_mv", outVq)]

/-- Reference `StatefulStepSpec` corresponding to `focStatefulPiFromObendRtl?`. -/
def focPiStatefulSpec : StatefulStepSpec where
  moduleName := "foc_pi_stateful_step"
  inputNames := ["err_d_ma", "err_q_ma"]
  stateRegs  :=
    [ { regIdx := 0
        name := "int_d"
        initVal := 0#64
        nextExpr := .alu .add (.regRead 0) (.alu .mul (.inputPort 0) (.const 65#64)) }
    , { regIdx := 1
        name := "int_q"
        initVal := 0#64
        nextExpr := .alu .add (.regRead 1) (.alu .mul (.inputPort 1) (.const 65#64)) }
    ]
  outputExprs :=
    [ ("vq_cmd_mv", .alu .add (.regRead 1) (.alu .mul (.inputPort 1) (.const 480#64))) ]

/-- **Theorem (`foc_hil_stateful_pi_rtl_verified`)**:
    1. Lowering `FocPiCurrentLoop.hotSwappedPiStatefulStep_book` via `compileStatefulTermsToRtl`
       produces `some (compileStatefulStepToRtl focPiStatefulSpec)`,
    2. The synthesized `always_ff` module passes `checkRtlModule` and lowers to a valid FPGA `BelNetlist`,
    3. Every single-cycle clock edge and arbitrary multi-cycle execution trace of the compiled
       `RtlModule` matches `evalStatefulStepPure` and `runStatefulTracePure` (`compileStatefulStepToRtl_simulates_step`,
       `compileStatefulStepToRtl_trace_sound`). -/
theorem foc_hil_stateful_pi_rtl_verified :
    focStatefulPiFromObendRtl? = some (compileStatefulStepToRtl focPiStatefulSpec) ∧
    checkRtlModule (compileStatefulStepToRtl focPiStatefulSpec) = true ∧
    checkBelNetlistValid (synthesizeModuleToBels (compileStatefulStepToRtl focPiStatefulSpec)) = true ∧
    (∀ (rst : Bool) (inputs regState : Nat → BitVec 64),
      stepModuleRegs (compileStatefulStepToRtl focPiStatefulSpec) rst inputs regState =
        evalStatefulStepPure focPiStatefulSpec rst inputs regState) ∧
    (∀ (initRegs : Nat → BitVec 64) (trace : List (Bool × (Nat → BitVec 64))),
      runModuleTrace (compileStatefulStepToRtl focPiStatefulSpec) initRegs trace =
        runStatefulTracePure focPiStatefulSpec initRegs trace) :=
  ⟨by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   compileStatefulStepToRtl_simulates_step focPiStatefulSpec,
   compileStatefulStepToRtl_trace_sound focPiStatefulSpec⟩

/-- Signed 64-bit constant literal helper for `focHilSequentialRtlModule`. -/
def focCi (v : Int) : RtlExpr :=
  .const (BitVec.ofInt 64 v)

/-- Sign-extend a 32-bit two's-complement port or register to 64 bits. -/
def focSext32 (e : RtlExpr) : RtlExpr :=
  .resize (.sext 32 64) e

/-- Truncate a 64-bit word to its low 32 bits. -/
def focTrunc32 (e : RtlExpr) : RtlExpr :=
  .resize (.trunc 32) e

/-- Signed saturation clamp to `[lo, hi]` on the 64-bit datapath. -/
def focClamp (e : RtlExpr) (lo hi : Int) : RtlExpr :=
  .mux (.alu .slt (focCi hi) e) (focCi hi)
    (.mux (.alu .slt e (focCi lo)) (focCi lo) e)

/-- Full sequential `always_ff` `RtlModule` (`foc_drive_top`) implementing the 20 kHz
    salient IPM FOC + 6-level SiC FCML controller (`apps/foc-hil/verilator/foc_drive_top.sv`),
    emitted byte-for-byte via `Obend.Hardware.HDL.emitModuleSV` and LEC-verified via
    `Obend.Hardware.YosysLec.emitYosysLecSmt2`:
    - Inputs (`10` ports, `[1, 32, 32, 32, 32, 32, 32, 32, 1, 1]`):
      `ctrl_tick_en`, `id_ref_ma`, `iq_ref_ma`, `id_meas_ma`, `iq_meas_ma`,
      `omega_e_rads`, `cap_err_mv`, `winding_temp_c`, `dpr_isolate_en`, `dpr_high_bw_sel`.
    - Cross-coupling decoupling + PM flux feedforward (`L_d = 150 uH`, `L_q = 380 uH`, `psi_PM = 180 mWb`),
      Q32 fixed-point proportional/integral paths (`Kp = 400/480 mOhm`, `Ki = 20/25 mOhm/tick`),
      `±600 V` integrator anti-windup saturation, and `±800 V` DC-bus output clamping.
    - Registers (`7` regs, `[32, 32, 32, 1, 32, 32, 32]`):
      `int_d`, `int_q`, `fcml_cap_err`, `thermal_trip_latch`, `skid_vd_hold`, `skid_vq_hold`, `ctrl_tick_count`.
    - Safety dominance: `fault_trip_comb` (`wireIdx 28`) unconditionally clamps `vd_cmd_mv = 0`,
      `vq_cmd_mv = 0`, `fcml_duty_permille = 0`, and `pwm_gate_en = 0` in 1 clock cycle even during
      `dpr_isolate_en = 1`. -/
def focPrefixWires : List WireAssign :=
  [ { wireIdx := 0,  name := "id_ref_64",       expr := focSext32 (.inputPort 1), width := 64 }
  , { wireIdx := 1,  name := "iq_ref_64",       expr := focSext32 (.inputPort 2), width := 64 }
  , { wireIdx := 2,  name := "id_meas_64",      expr := focSext32 (.inputPort 3), width := 64 }
  , { wireIdx := 3,  name := "iq_meas_64",      expr := focSext32 (.inputPort 4), width := 64 }
  , { wireIdx := 4,  name := "omega_e_64",      expr := focSext32 (.inputPort 5), width := 64 }
  , { wireIdx := 5,  name := "cap_err_64",      expr := focSext32 (.inputPort 6), width := 64 }
  , { wireIdx := 6,  name := "id_err_64",       expr := .alu .sub (.wireRef 0) (.wireRef 2), width := 64 }
  , { wireIdx := 7,  name := "iq_err_64",       expr := .alu .sub (.wireRef 1) (.wireRef 3), width := 64 }
  , { wireIdx := 8,  name := "kp_q32",          expr := .mux (.inputPort 9) (.const 2061584303#64) (.const 1717986919#64), width := 64 }
  , { wireIdx := 9,  name := "ki_q32",          expr := .mux (.inputPort 9) (.const 107374183#64) (.const 85899346#64), width := 64 }
  , { wireIdx := 10, name := "omega_iq_prod",   expr := .alu .mul (.wireRef 4) (.wireRef 3), width := 64 }
  , { wireIdx := 11, name := "vd_ff_64",        expr := .alu .sub (.const 0#64) (.alu .qmul32 (.wireRef 10) (.const 1632088#64)), width := 64 }
  , { wireIdx := 12, name := "omega_id_prod",   expr := .alu .mul (.wireRef 4) (.wireRef 2), width := 64 }
  , { wireIdx := 13, name := "vq_ff_64",
      expr := .alu .add (.alu .qmul32 (.wireRef 12) (.const 644246#64))
                (.alu .add (.alu .add (.alu .shl (.wireRef 4) (.const 7#64)) (.alu .shl (.wireRef 4) (.const 5#64)))
                           (.alu .add (.alu .shl (.wireRef 4) (.const 4#64)) (.alu .shl (.wireRef 4) (.const 2#64)))),
      width := 64 }
  , { wireIdx := 14, name := "prop_d_64",       expr := .alu .qmul32 (.wireRef 6) (.wireRef 8), width := 64 }
  , { wireIdx := 15, name := "prop_q_64",       expr := .alu .qmul32 (.wireRef 7) (.wireRef 8), width := 64 }
  , { wireIdx := 16, name := "int_d_64",        expr := focSext32 (.regRead 0), width := 64 }
  , { wireIdx := 17, name := "int_q_64",        expr := focSext32 (.regRead 1), width := 64 }
  , { wireIdx := 18, name := "int_d_cand",      expr := .alu .add (.wireRef 16) (.alu .qmul32 (.wireRef 6) (.wireRef 9)), width := 64 }
  , { wireIdx := 19, name := "int_q_cand",      expr := .alu .add (.wireRef 17) (.alu .qmul32 (.wireRef 7) (.wireRef 9)), width := 64 }
  , { wireIdx := 20, name := "int_d_sat",       expr := focClamp (.wireRef 18) (-600000) 600000, width := 64 }
  , { wireIdx := 21, name := "int_q_sat",       expr := focClamp (.wireRef 19) (-600000) 600000, width := 64 }
  , { wireIdx := 22, name := "vd_active_raw",   expr := .alu .add (.alu .add (.wireRef 14) (.wireRef 20)) (.wireRef 11), width := 64 }
  , { wireIdx := 23, name := "vq_active_raw",   expr := .alu .add (.alu .add (.wireRef 15) (.wireRef 21)) (.wireRef 13), width := 64 }
  , { wireIdx := 24, name := "vd_active_mv",    expr := focTrunc32 (focClamp (.wireRef 22) (-800000) 800000), width := 32 }
  , { wireIdx := 25, name := "vq_active_mv",    expr := focTrunc32 (focClamp (.wireRef 23) (-800000) 800000), width := 32 }
  , { wireIdx := 26, name := "cap_bal_next_32", expr := focTrunc32 (.alu .qmul32 (.wireRef 5) (.const 3435973837#64)), width := 32 }
  ]

def focSuffixWires : List WireAssign :=
  [ { wireIdx := 27, name := "overtemp_now",    expr := .alu .ult (.const 154#64) (.inputPort 7), width := 1 }
  , { wireIdx := 28, name := "fault_trip_comb", expr := .alu .bitOr (.regRead 3) (.wireRef 27), width := 1 }
  , { wireIdx := 29, name := "ctrl_update_en",
      expr := .alu .bitAnd (.inputPort 0)
                (.alu .bitAnd (.mux (.inputPort 8) (.const 0#64) (.const 1#64))
                              (.mux (.wireRef 28) (.const 0#64) (.const 1#64))),
      width := 1 }
  , { wireIdx := 30, name := "vd_cmd_32",       expr := .mux (.wireRef 28) (.const 0#64) (.regRead 4), width := 32 }
  , { wireIdx := 31, name := "vq_cmd_32",       expr := .mux (.wireRef 28) (.const 0#64) (.regRead 5), width := 32 }
  , { wireIdx := 32, name := "duty_signed",     expr := .alu .add (.const 500#64) (.alu .qmul32 (focSext32 (.wireRef 31)) (.const 2684355#64)), width := 64 }
  , { wireIdx := 33, name := "duty_clamped_32", expr := .mux (.wireRef 28) (.const 0#64) (focTrunc32 (focClamp (.wireRef 32) 0 1000)), width := 32 }
  ]

def focHilSequentialRtlModule : RtlModule where
  name := "foc_drive_top"
  inputNames :=
    [ "ctrl_tick_en"
    , "id_ref_ma"
    , "iq_ref_ma"
    , "id_meas_ma"
    , "iq_meas_ma"
    , "omega_e_rads"
    , "cap_err_mv"
    , "winding_temp_c"
    , "dpr_isolate_en"
    , "dpr_high_bw_sel"
    ]
  inputWidths := [1, 32, 32, 32, 32, 32, 32, 32, 1, 1]
  wires := focPrefixWires ++ focSuffixWires
  regs :=
    [ { regIdx := 0, name := "int_d",              domain := .coreClk, resetKind := .syncReset 0#64,     isSynchronizer := false, nextExpr := .mux (.wireRef 29) (focTrunc32 (.wireRef 20)) (.regRead 0), width := 32 }
    , { regIdx := 1, name := "int_q",              domain := .coreClk, resetKind := .syncReset 0#64,     isSynchronizer := false, nextExpr := .mux (.wireRef 29) (focTrunc32 (.wireRef 21)) (.regRead 1), width := 32 }
    , { regIdx := 2, name := "fcml_cap_err",       domain := .coreClk, resetKind := .syncReset 15000#64, isSynchronizer := false, nextExpr := .mux (.wireRef 29) (.wireRef 26) (.regRead 2),             width := 32 }
    , { regIdx := 3, name := "thermal_trip_latch", domain := .coreClk, resetKind := .syncReset 0#64,     isSynchronizer := false, nextExpr := .mux (.wireRef 28) (.const 1#64) (.const 0#64),             width := 1 }
    , { regIdx := 4, name := "skid_vd_hold",       domain := .coreClk, resetKind := .syncReset 0#64,     isSynchronizer := false, nextExpr := .mux (.wireRef 29) (.wireRef 24) (.regRead 4),             width := 32 }
    , { regIdx := 5, name := "skid_vq_hold",       domain := .coreClk, resetKind := .syncReset 0#64,     isSynchronizer := false, nextExpr := .mux (.wireRef 29) (.wireRef 25) (.regRead 5),             width := 32 }
    , { regIdx := 6, name := "ctrl_tick_count",    domain := .coreClk, resetKind := .syncReset 0#64,     isSynchronizer := false, nextExpr := .mux (.inputPort 0) (focTrunc32 (.alu .add (.regRead 6) (.const 1#64))) (.regRead 6), width := 32 }
    ]
  outputs :=
    [ { name := "vd_cmd_mv",           expr := .wireRef 30,                                    width := 32 }
    , { name := "vq_cmd_mv",           expr := .wireRef 31,                                    width := 32 }
    , { name := "cap_bal_mv",          expr := .regRead 2,                                     width := 32 }
    , { name := "fcml_duty_permille",  expr := .wireRef 33,                                    width := 32 }
    , { name := "fault_trip",          expr := .mux (.wireRef 28) (.const 1#64) (.const 0#64), width := 1 }
    , { name := "pwm_gate_en",         expr := .mux (.wireRef 28) (.const 0#64) (.const 1#64), width := 1 }
    , { name := "dbg_int_d_mv",        expr := .regRead 0,                                     width := 32 }
    , { name := "dbg_int_q_mv",        expr := .regRead 1,                                     width := 32 }
    , { name := "dbg_ctrl_tick_count", expr := .regRead 6,                                     width := 32 }
    ]

/-- **Hardware Well-Formedness, Emission Width Gate (`checkRtlModuleW`) & FPGA `BelNetlist`
    Trace Equivalence Certificate for `apps/foc-hil/`**. -/
theorem foc_hil_rtl_and_bel_synthesis_verified :
    checkRtlModule focHilSequentialRtlModule = true ∧
    checkRtlModuleW focHilSequentialRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels focHilSequentialRtlModule) = true ∧
    (∀ (initRegs : Nat → BitVec 64) (trace : List (Bool × (Nat → BitVec 64))),
      runBelNetlistTrace (synthesizeModuleToBels focHilSequentialRtlModule) initRegs trace =
        runRtlModuleTrace focHilSequentialRtlModule initRegs trace) ∧
    (match clarkeParkRtl?, piCurrentLoopRtl?, sicFcmlLegRtl?, focDriveTopRtl? with
     | some m1, some m2, some m3, some m4 =>
       checkRtlModule m1 &&
       checkRtlModule m2 &&
       checkRtlModule m3 &&
       checkRtlModule m4 &&
       checkBelNetlistValid (synthesizeModuleToBels m4)
     | _, _, _, _ => false) = true :=
  ⟨by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   synthesizeModuleToBels_trace_equiv focHilSequentialRtlModule (by decide +kernel),
   by decide +kernel⟩

private def focSuffixEnv (inputs regState env27 : Nat → BitVec 64) : Nat → BitVec 64 :=
  focSuffixWires.foldl
    (fun (env : Nat → BitVec 64) a =>
      let v := evalRtlExpr inputs env regState a.expr
      fun i => if i == a.wireIdx then v else env i)
    env27

private theorem focEvalWires_eq_suffixEnv (inputs regState : Nat → BitVec 64) :
    evalWireTable inputs regState focHilSequentialRtlModule.wires =
      focSuffixEnv inputs regState (evalWireTable inputs regState focPrefixWires) := by
  change evalWireTable inputs regState (focPrefixWires ++ focSuffixWires) = _
  unfold evalWireTable focSuffixEnv
  exact List.foldl_append

private theorem focSuffixEnv_fault_props
    (inputs regState env27 : Nat → BitVec 64)
    (hBne : ((regState 3 ||| (if BitVec.ult 154#64 (inputs 7) then 1#64 else 0#64)) != 0#64) = true) :
    (focSuffixEnv inputs regState env27 28 != 0#64) = true ∧
    focSuffixEnv inputs regState env27 30 = 0#64 ∧
    focSuffixEnv inputs regState env27 31 = 0#64 ∧
    focSuffixEnv inputs regState env27 33 = 0#64 := by
  refine ⟨hBne, ?_, ?_, ?_⟩
  · change (if ((regState 3 ||| (if BitVec.ult 154#64 (inputs 7) then 1#64 else 0#64)) != 0#64) then 0#64 else regState 4) = 0#64
    rw [hBne]; rfl
  · change (if ((regState 3 ||| (if BitVec.ult 154#64 (inputs 7) then 1#64 else 0#64)) != 0#64) then 0#64 else regState 5) = 0#64
    rw [hBne]; rfl
  · change (if ((regState 3 ||| (if BitVec.ult 154#64 (inputs 7) then 1#64 else 0#64)) != 0#64) then 0#64 else _) = 0#64
    rw [hBne]; rfl

private theorem focSuffixEnv_dpr_prop
    (inputs regState env27 : Nat → BitVec 64)
    (hDprBne : (inputs 8 != 0#64) = true) :
    (focSuffixEnv inputs regState env27 29 != 0#64) = false := by
  have hw29 : focSuffixEnv inputs regState env27 29 = 0#64 := by
    change (inputs 0 &&& ((if (inputs 8 != 0#64) then 0#64 else 1#64) &&& _)) = 0#64
    rw [hDprBne]
    simp
  rw [hw29]
  rfl

/-- **Universal Safety Dominance & ICAP DPR Isolation Theorem (`focHilSequentialRtlModule_safety_and_dpr_hold`)**:
    1. Whenever `154 <u winding_temp_c` (`inputs 7`) OR `thermal_trip_latch` (`regState 3`) is set,
       `focHilSequentialRtlModule` unconditionally outputs `vd_cmd_mv = 0`, `vq_cmd_mv = 0`,
       `fcml_duty_permille = 0`, `fault_trip = 1`, and `pwm_gate_en = 0` in 1 cycle — even when
       `dpr_isolate_en` (`inputs 8`) is simultaneously asserted — and latches `thermal_trip_latch = 1`
       on the next non-reset clock edge.
    2. Whenever `dpr_isolate_en != 0` (`inputs 8 != 0#64`), every non-reset clock edge freezes
       `int_d`, `int_q`, `fcml_cap_err`, `skid_vd_hold`, and `skid_vq_hold`. -/
theorem focHilSequentialRtlModule_safety_and_dpr_hold
    (inputs regState : Nat → BitVec 64) :
    ((BitVec.ult 154#64 (inputs 7) = true ∨ regState 3 ≠ 0#64) →
      let outs := evalModuleOutputs focHilSequentialRtlModule inputs regState
      outs.lookup "vd_cmd_mv" = some 0#64 ∧
      outs.lookup "vq_cmd_mv" = some 0#64 ∧
      outs.lookup "fcml_duty_permille" = some 0#64 ∧
      outs.lookup "fault_trip" = some 1#64 ∧
      outs.lookup "pwm_gate_en" = some 0#64 ∧
      stepModuleRegs focHilSequentialRtlModule false inputs regState 3 = 1#64) ∧
    (inputs 8 ≠ 0#64 →
      let next := stepModuleRegs focHilSequentialRtlModule false inputs regState
      next 0 = regState 0 ∧
      next 1 = regState 1 ∧
      next 2 = regState 2 ∧
      next 4 = regState 4 ∧
      next 5 = regState 5) := by
  unfold evalModuleOutputs stepModuleRegs
  rw [focEvalWires_eq_suffixEnv]
  generalize evalWireTable inputs regState focPrefixWires = env27
  constructor
  · intro hFault
    have hBne : ((regState 3 ||| (if BitVec.ult 154#64 (inputs 7) then 1#64 else 0#64)) != 0#64) = true := by
      rw [bne_iff_ne]
      intro hEq
      have hZero := BitVec.or_eq_zero_iff.mp hEq
      rcases hFault with hUlt | hLatch
      · simp [hUlt] at hZero
      · exact hLatch hZero.1
    obtain ⟨hw28, hw30, hw31, hw33⟩ := focSuffixEnv_fault_props inputs regState env27 hBne
    generalize focSuffixEnv inputs regState env27 = wEnv at hw28 hw30 hw31 hw33 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change some (wEnv 30) = some 0#64; rw [hw30]
    · change some (wEnv 31) = some 0#64; rw [hw31]
    · change some (wEnv 33) = some 0#64; rw [hw33]
    · change some (if (wEnv 28 != 0#64) then 1#64 else 0#64) = some 1#64; rw [hw28]; rfl
    · change some (if (wEnv 28 != 0#64) then 0#64 else 1#64) = some 0#64; rw [hw28]; rfl
    · change (if (wEnv 28 != 0#64) then 1#64 else 0#64) = 1#64; rw [hw28]; rfl
  · intro hDpr
    have hDprBne : (inputs 8 != 0#64) = true := bne_iff_ne.mpr hDpr
    have hw29 := focSuffixEnv_dpr_prop inputs regState env27 hDprBne
    generalize focSuffixEnv inputs regState env27 = wEnv at hw29 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change (if (wEnv 29 != 0#64) then _ else regState 0) = regState 0; rw [hw29]; rfl
    · change (if (wEnv 29 != 0#64) then _ else regState 1) = regState 1; rw [hw29]; rfl
    · change (if (wEnv 29 != 0#64) then _ else regState 2) = regState 2; rw [hw29]; rfl
    · change (if (wEnv 29 != 0#64) then _ else regState 4) = regState 4; rw [hw29]; rfl
    · change (if (wEnv 29 != 0#64) then _ else regState 5) = regState 5; rw [hw29]; rfl

/-- **Multi-Cycle Sequential `always_ff` HIL Trace Verification (5 Ticks)**:
    Verifies across a 5-tick sequence covering:
    1. Tick 0 (`focIn0`): Nominal 20 kHz torque step (`id* = 100 A`, `iq* = 250 A`, `omega_e = 1000 rad/s`, `T = 85°C`).
    2. Tick 1 (`focIn1`): Fault-free mid-run ICAP DPR isolation (`dpr_isolate_en = 1`), freezing `int_d`, `int_q`
       and outputting glitch-free held `skid_vd_hold` (`42,000 mV`) and `skid_vq_hold` (`285,000 mV`).
    3. Tick 2 (`focIn2`): Post-DPR hot-swap release (`dpr_isolate_en = 0`, `dpr_high_bw_sel = 1`, `Kp = 480 mOhm`, `Ki = 25 mOhm`).
    4. Tick 3 (`focIn3`): Simultaneous `dpr_isolate_en = 1` AND `155°C` over-temperature injection
       (`winding_temp_c = 155`), proving `fault_trip = 1` overrides `dpr_isolate_en = 1` in 1 clock cycle
       (`vd_cmd_mv = 0`, `vq_cmd_mv = 0`, `fcml_duty_permille = 0`, `pwm_gate_en = 0`).
    5. Tick 4 (`focIn4`): Cool-down to `90°C` (`dpr_isolate_en = 0`), proving write-once
       `thermal_trip_latch = 1` keeps `vd_cmd_mv = 0`, `vq_cmd_mv = 0`, `fault_trip = 1`, `pwm_gate_en = 0`. -/
def focInitRegs : Nat → BitVec 64
  | 2 => 15000#64
  | _ => 0#64

def focIn0 : Nat → BitVec 64
  | 0 => 1#64
  | 1 => 100000#64
  | 2 => 250000#64
  | 5 => 1000#64
  | 6 => 15000#64
  | 7 => 85#64
  | _ => 0#64

def focIn1 : Nat → BitVec 64
  | 0 => 1#64
  | 1 => 100000#64
  | 2 => 250000#64
  | 5 => 1000#64
  | 6 => 12000#64
  | 7 => 90#64
  | 8 => 1#64
  | 9 => 1#64
  | _ => 0#64

def focIn2 : Nat → BitVec 64
  | 0 => 1#64
  | 1 => 50000#64
  | 2 => 250000#64
  | 5 => 1000#64
  | 6 => 5000#64
  | 7 => 110#64
  | 9 => 1#64
  | _ => 0#64

def focIn3 : Nat → BitVec 64
  | 0 => 1#64
  | 1 => 50000#64
  | 2 => 250000#64
  | 5 => 1000#64
  | 7 => 155#64
  | 8 => 1#64
  | 9 => 1#64
  | _ => 0#64

def focIn4 : Nat → BitVec 64
  | 0 => 1#64
  | 1 => 50000#64
  | 2 => 250000#64
  | 5 => 1000#64
  | 7 => 90#64
  | 9 => 1#64
  | _ => 0#64

def focRegs1 : Nat → BitVec 64
  | 0 => 2000#64
  | 1 => 5000#64
  | 2 => 12000#64
  | 4 => 42000#64
  | 5 => 285000#64
  | 6 => 1#64
  | _ => 0#64

def focRegs2 : Nat → BitVec 64
  | 0 => 2000#64
  | 1 => 5000#64
  | 2 => 12000#64
  | 4 => 42000#64
  | 5 => 285000#64
  | 6 => 2#64
  | _ => 0#64

def focRegs3 : Nat → BitVec 64
  | 0 => 3250#64
  | 1 => 11250#64
  | 2 => 4000#64
  | 4 => 27250#64
  | 5 => 311250#64
  | 6 => 3#64
  | _ => 0#64

def focRegs4 : Nat → BitVec 64
  | 0 => 3250#64
  | 1 => 11250#64
  | 2 => 4000#64
  | 3 => 1#64
  | 4 => 27250#64
  | 5 => 311250#64
  | 6 => 4#64
  | _ => 0#64

private theorem evalWireTable_eq_arr
    (inputs regs : Nat → BitVec 64) (assigns : List WireAssign) :
    evalWireTable inputs regs assigns =
      (fun i => (evalWireTableArr inputs regs assigns).getD i 0#64) :=
  funext fun i => (evalWireTableArr_getD inputs regs assigns i).symm

private def evalFocOutputsArr (inputs regs : Nat → BitVec 64) : List (String × BitVec 64) :=
  let arr := evalWireTableArr inputs regs focHilSequentialRtlModule.wires
  let wEnv : Nat → BitVec 64 := fun i => arr.getD i 0#64
  focHilSequentialRtlModule.outputs.map fun o => (o.name, evalRtlExpr inputs wEnv regs o.expr)

private theorem evalFocOutputs_eq_arr (inputs regs : Nat → BitVec 64) :
    evalModuleOutputs focHilSequentialRtlModule inputs regs = evalFocOutputsArr inputs regs := by
  unfold evalModuleOutputs evalFocOutputsArr
  rw [evalWireTable_eq_arr]

private def stepFocRegsArr (inputs regs : Nat → BitVec 64) : Nat → BitVec 64 :=
  let arr := evalWireTableArr inputs regs focHilSequentialRtlModule.wires
  let wEnv : Nat → BitVec 64 := fun i => arr.getD i 0#64
  focHilSequentialRtlModule.regs.foldl
    (fun (nextSt : Nat → BitVec 64) r =>
      let v := match r.resetKind with
        | .resetFree => evalRtlExpr inputs wEnv regs r.nextExpr
        | .syncReset _ => evalRtlExpr inputs wEnv regs r.nextExpr
      fun i => if i == r.regIdx then v else nextSt i)
    regs

private theorem stepFocRegs_false_eq_arr (inputs regs : Nat → BitVec 64) :
    stepModuleRegs focHilSequentialRtlModule false inputs regs = stepFocRegsArr inputs regs := by
  unfold stepModuleRegs stepFocRegsArr
  rw [evalWireTable_eq_arr]
  rfl

private theorem stepFocRegs_eq_of_lt7
    (inputs prev target : Nat → BitVec 64)
    (hTail : ∀ i, 7 ≤ i → prev i = target i)
    (h7 : (List.range 7).all (fun i => stepFocRegsArr inputs prev i == target i) = true) :
    stepModuleRegs focHilSequentialRtlModule false inputs prev = target := by
  rw [stepFocRegs_false_eq_arr]
  funext i
  by_cases hi : i < 7
  · simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h7
    exact h7 i hi
  · have hGe : 7 ≤ i := by omega
    have hNe0 : (i == 0) = false := by simp; omega
    have hNe1 : (i == 1) = false := by simp; omega
    have hNe2 : (i == 2) = false := by simp; omega
    have hNe3 : (i == 3) = false := by simp; omega
    have hNe4 : (i == 4) = false := by simp; omega
    have hNe5 : (i == 5) = false := by simp; omega
    have hNe6 : (i == 6) = false := by simp; omega
    dsimp only [stepFocRegsArr, focHilSequentialRtlModule, List.foldl]
    simp only [hNe6, hNe5, hNe4, hNe3, hNe2, hNe1, hNe0, Bool.false_eq_true, ite_false]
    exact hTail i hGe

private theorem focZeroTail_init_1 : ∀ i, 7 ≤ i → focInitRegs i = focRegs1 i := by
  intro i hi
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
  | _ + 7 => rfl

private theorem focZeroTail_1_2 : ∀ i, 7 ≤ i → focRegs1 i = focRegs2 i := by
  intro i hi
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
  | _ + 7 => rfl

private theorem focZeroTail_2_3 : ∀ i, 7 ≤ i → focRegs2 i = focRegs3 i := by
  intro i hi
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
  | _ + 7 => rfl

private theorem focZeroTail_3_4 : ∀ i, 7 ≤ i → focRegs3 i = focRegs4 i := by
  intro i hi
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
  | _ + 7 => rfl

theorem foc_hil_sequential_4tick_trace_verified :
    let regs1 := stepModuleRegs focHilSequentialRtlModule false focIn0 focInitRegs
    let regs2 := stepModuleRegs focHilSequentialRtlModule false focIn1 regs1
    let regs3 := stepModuleRegs focHilSequentialRtlModule false focIn2 regs2
    let regs4 := stepModuleRegs focHilSequentialRtlModule false focIn3 regs3
    -- After Tick 0: ZOH holds vd = 42,000 mV, vq = 285,000 mV (180 V back-EMF + 105 V PI), cap_bal = 12,000 mV
    evalModuleOutputs focHilSequentialRtlModule focIn1 regs1 =
      [ ("vd_cmd_mv", 42000#64)
      , ("vq_cmd_mv", 285000#64)
      , ("cap_bal_mv", 12000#64)
      , ("fcml_duty_permille", 678#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64)
      , ("dbg_int_d_mv", 2000#64)
      , ("dbg_int_q_mv", 5000#64)
      , ("dbg_ctrl_tick_count", 1#64) ] ∧
    -- After Tick 1 (`dpr_isolate_en = 1`): ZOH skid outputs & integrators frozen glitch-free, tick count = 2
    evalModuleOutputs focHilSequentialRtlModule focIn2 regs2 =
      [ ("vd_cmd_mv", 42000#64)
      , ("vq_cmd_mv", 285000#64)
      , ("cap_bal_mv", 12000#64)
      , ("fcml_duty_permille", 678#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64)
      , ("dbg_int_d_mv", 2000#64)
      , ("dbg_int_q_mv", 5000#64)
      , ("dbg_ctrl_tick_count", 2#64) ] ∧
    -- After Tick 2 (post-DPR hot-swap `dpr_high_bw_sel = 1`): vd = 27,250 mV, vq = 311,250 mV, cap_bal = 4,000 mV
    evalModuleOutputs focHilSequentialRtlModule focIn4 regs3 =
      [ ("vd_cmd_mv", 27250#64)
      , ("vq_cmd_mv", 311250#64)
      , ("cap_bal_mv", 4000#64)
      , ("fcml_duty_permille", 694#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64)
      , ("dbg_int_d_mv", 3250#64)
      , ("dbg_int_q_mv", 11250#64)
      , ("dbg_ctrl_tick_count", 3#64) ] ∧
    -- Tick 3: Simultaneous dpr_isolate_en=1 + 155°C over-temp forces 1-cycle zeroing of vd, vq, duty & pwm_gate_en
    evalModuleOutputs focHilSequentialRtlModule focIn3 regs3 =
      [ ("vd_cmd_mv", 0#64)
      , ("vq_cmd_mv", 0#64)
      , ("cap_bal_mv", 4000#64)
      , ("fcml_duty_permille", 0#64)
      , ("fault_trip", 1#64)
      , ("pwm_gate_en", 0#64)
      , ("dbg_int_d_mv", 3250#64)
      , ("dbg_int_q_mv", 11250#64)
      , ("dbg_ctrl_tick_count", 3#64) ] ∧
    -- Tick 4: Write-once thermal_trip_latch=1 holds vd=0, vq=0, duty=0, fault_trip=1, pwm_gate_en=0 after cooling to 90°C
    evalModuleOutputs focHilSequentialRtlModule focIn4 regs4 =
      [ ("vd_cmd_mv", 0#64)
      , ("vq_cmd_mv", 0#64)
      , ("cap_bal_mv", 4000#64)
      , ("fcml_duty_permille", 0#64)
      , ("fault_trip", 1#64)
      , ("pwm_gate_en", 0#64)
      , ("dbg_int_d_mv", 3250#64)
      , ("dbg_int_q_mv", 11250#64)
      , ("dbg_ctrl_tick_count", 4#64) ] := by
  have hr1 : stepModuleRegs focHilSequentialRtlModule false focIn0 focInitRegs = focRegs1 :=
    stepFocRegs_eq_of_lt7 focIn0 focInitRegs focRegs1 focZeroTail_init_1 (by decide +kernel)
  have hr2 : stepModuleRegs focHilSequentialRtlModule false focIn1 focRegs1 = focRegs2 :=
    stepFocRegs_eq_of_lt7 focIn1 focRegs1 focRegs2 focZeroTail_1_2 (by decide +kernel)
  have hr3 : stepModuleRegs focHilSequentialRtlModule false focIn2 focRegs2 = focRegs3 :=
    stepFocRegs_eq_of_lt7 focIn2 focRegs2 focRegs3 focZeroTail_2_3 (by decide +kernel)
  have hr4 : stepModuleRegs focHilSequentialRtlModule false focIn3 focRegs3 = focRegs4 :=
    stepFocRegs_eq_of_lt7 focIn3 focRegs3 focRegs4 focZeroTail_3_4 (by decide +kernel)
  dsimp only
  rw [hr1, hr2, hr3, hr4]
  simp only [evalFocOutputs_eq_arr]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The compiled `FocDriveTop.obend`: `checkRtlModule` and one input's outputs (a closed check; a GPU
co-execution claim on an interpreter nobody ran was removed 2026-11-05, the GPU path is `Obend.Hardware.Gpu`). -/
example :
    (match focDriveTopRtl? with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 250#64) (fun _ => 0#64) ==
         [ ("out_icapDprBandwidthGain", 480#64)
         , ("out_statorThermalResPermille", 4#64)
         , ("out_activeFcmlBalanceMv", 5025#64)
         , ("out_controlFreqKhz", 20#64)
         , ("out_closedLoopVqMv", 120250#64)
         , ("out_statorWindingTempC", 1045#64)
         ])
     | none => false) = true := by
  decide +kernel

/-! ## 7. Cross-Package Dependency Cone Survival & Live ICAP DPR Hot-Swap Guard -/

/-- Extract the inner method body (under the outer `λself.` binder) from a `Leaf.Book` slot. -/
def extractFocBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

def focClosedLoopVqBody : Term :=
  extractFocBookMethodInner (emit focDriveTopComp) "closedLoopVqMv"

def focStatorTempBody : Term :=
  extractFocBookMethodInner (emit focDriveTopComp) "statorWindingTempC"

/-- **Cross-Package Dependency Cone Survival & Live ICAP DPR Hot-Swap Guard
    (`foc_hil_crossPackage_dpr_hotswap_and_cone_survives`)**:
    1. `slotReadCone focDriveTopComp "closedLoopVqMv"` depends only on
       `["closedLoopVqMv", "icapDprBandwidthGain"]`, and `slotReadCone focDriveTopComp "statorWindingTempC"`
       depends only on `["statorWindingTempC", "statorThermalResPermille"]`.
    2. By `extractReadMembers_mutation_invariant`, mutating any disjoint member (such as
       `"controlFreqKhz"` or `"activeFcmlBalanceMv"`) leaves `substMemberEnv` of both
       `focClosedLoopVqBody` and `focStatorTempBody` identically unchanged. -/
theorem foc_hil_crossPackage_dpr_hotswap_and_cone_survives
    (env : String → Option Term) (newVal : Option Term) :
    extractReadMembers focClosedLoopVqBody = ["icapDprBandwidthGain"] ∧
    extractReadMembers focStatorTempBody = ["statorThermalResPermille"] ∧
    substMemberEnv (mutateMemberEnv env "controlFreqKhz" newVal) focClosedLoopVqBody =
      substMemberEnv env focClosedLoopVqBody ∧
    substMemberEnv (mutateMemberEnv env "activeFcmlBalanceMv" newVal) focStatorTempBody =
      substMemberEnv env focStatorTempBody :=
  ⟨by decide +kernel,
   by decide +kernel,
   (extractReadMembers_mutation_invariant focClosedLoopVqBody env newVal (by decide +kernel)).1,
   (extractReadMembers_mutation_invariant focStatorTempBody env newVal (by decide +kernel)).1⟩

end Obend.Apps.FocHil
end
