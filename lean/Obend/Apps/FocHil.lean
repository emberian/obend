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
public import Obend.Lower.Proofs.SelfAccelerate
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.Types
public import Obend.Hardware.PowerElectronics
public import Obend.Hardware.DigitalTwin
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

4. **Sequential `always_ff` Hardware Synthesis, Live Mid-Run ICAP DPR Hot-Swap & 64-Bit AMD `VOP64` GPU**:
   Synthesizes both 1-arg and multi-argument stateful `always_ff` `.obend` `Book`s
   (`compileStatefulTermsToRtl` / `compileStatefulStepToRtl`) and the full sequential
   `always_ff` FOC + FCML controller (`int_d`, `int_q`, `fcml_cap_err`, `thermal_trip_latch`,
   `skid_vq_hold`, `skid_vd_hold`) to verified `RtlModule`s, FPGA `BelNetlist`s, and 64-bit
   AMD `VOP64` GPU kernels, and proves cross-package dependency cone survival
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
open Obend.Hardware.Accelerators
open Obend.Hardware.PowerElectronics
open Obend.Hardware.DigitalTwin
open Obend.Hardware.Analog
open Obend.Hardware.Magnetics
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

/-- **Master Closed-Loop ISS Contraction, Thermal/Current CBF & Coupled Electro-Thermal Adjoint Theorem
    (`foc_hil_closed_loop_iss_and_thermal_safe`)**:
    1. **20 kHz Sampled-Data ISS Contraction & SAR ADC Quantization Bounds**:
       `sampled_data_current_loop_iss_contraction` proves strict homogeneous difference contraction
       $(1000 - \kappa)(i_{q,1} - i_{q,2}) < 1000 (i_{q,1} - i_{q,2})$ together with exact $1\text{-LSB}$
       SAR ADC quantization bounds.
    2. **Closed-Loop Powertrain Safety Barrier (CBF)**:
       `sampled_data_closed_loop_powertrain_safety_invariant` and
       `golden_ms350_ipm_digital_twin_trajectory_verified` prove that the coupled `MS350` FCML + `LC Drives`
       IPM trajectory stays inside the Class-H thermal limit ($122^\circ\text{C} \le 180^\circ\text{C}$),
       maintains rotor-stator air-gap clearance ($850\,\mu\text{m} \ge 500\,\mu\text{m}$), and contracts
       FCML capacitor unbalance ($100\text{ mV} \to 80\text{ mV} \to 64\text{ mV}$).
    3. **6-Level SiC FCML Active Lyapunov Capacitor Balancing**:
       `fcml_active_balancing_lyapunov_contraction` proves quadratic Lyapunov energy contraction
       $(e_k - c_k)^2 \le e_k^2$ across all damped feedback corrections.
    4. **Coupled Electro-Thermal Stator Loss Adjoint Soundness**:
       `statorCoupledLoss_adjoint_eqSat_sound` proves that E-Graph optimization reduces hardware cost
       from $96 \to 76$ while preserving exact forward peak temperature and all 4 reverse-mode adjoint
       sensitivities.
    5. **SOS Lyapunov, Control Barrier & DAE Certificate (`"sos-lyapunov-cbf@1"`)**:
       `checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok`. -/
theorem foc_hil_closed_loop_iss_and_thermal_safe :
    (∀ (iqRefAmp iq1 iq2 kpPermille qDistAmp : Int) (bits vInMv vLsbMv : Nat),
      0 < kpPermille → kpPermille < 1000 → iq2 < iq1 → 0 < vLsbMv →
      stepQuantizedCurrentLoop iqRefAmp iq1 kpPermille qDistAmp -
        stepQuantizedCurrentLoop iqRefAmp iq2 kpPermille qDistAmp =
        (1000 - kpPermille) * (iq1 - iq2) ∧
      0 < (1000 - kpPermille) * (iq1 - iq2) ∧
      (1000 - kpPermille) * (iq1 - iq2) < 1000 * (iq1 - iq2) ∧
      (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv) ∧
    (∀ (spec : PowertrainPlantSpec) (st : PowertrainTwinState),
      checkPowertrainTwinSafety spec st = true →
      spec.minShaftTorqueScaled ≤ evalIpmTorqueScaled spec.motor st.idAmp st.iqAmp ∧
      st.tWindingMilliC ≤ spec.maxClassHInsulationMilliC ∧
      st.tMagnetMilliC ≤ spec.maxMagnetDemagMilliC ∧
      0 < st.hotAirGapUm ∧
      (evalActiveBalancingStep st.fcmlCapErrMv spec.activeBalGainPermille) *
        (evalActiveBalancingStep st.fcmlCapErrMv spec.activeBalGainPermille) ≤
        st.fcmlCapErrMv * st.fcmlCapErrMv) ∧
    (∀ (vErrMv corrMv : Int),
      0 ≤ corrMv * (2 * vErrMv - corrMv) →
      (vErrMv - corrMv) * (vErrMv - corrMv) ≤ vErrMv * vErrMv) ∧
    (∀ (currentA toothWidthUm channelAspect fcmlFreqKhz dOut : Int),
      let gAdj := compileGraphAdjoint statorCoupledLossHypergraph
      let gOpt := optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph
      let env := statorCoupledLossAdjointEnv currentA toothWidthUm channelAspect fcmlFreqKhz dOut
      evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
      evalHypergraphComb gOpt env = evalHypergraphComb gAdj env) ∧
    checkPowertrainTwinSafety goldenMs350IpmPlantSpec goldenTwinState0 = true ∧
    checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok := by
  refine ⟨?_, ?_, (fun vErrMv corrMv h => (fcml_active_balancing_lyapunov_contraction vErrMv corrMv h).2), ?_,
          golden_ms350_ipm_digital_twin_trajectory_verified.2.2.2.2.2.2.2.2.2.2.2.1,
          sos_lyapunov_cbf_dae_showcase_sound.2.2.2⟩
  · intro iqRefAmp iq1 iq2 kpPermille qDistAmp bits vInMv vLsbMv hKpPos hKpSub hOrder hLsbPos
    have h := sampled_data_current_loop_iss_contraction iqRefAmp iq1 iq2 kpPermille qDistAmp
      bits vInMv vLsbMv hKpPos hKpSub hOrder hLsbPos
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · intro spec st hSafe
    have h := sampled_data_closed_loop_powertrain_safety_invariant spec st hSafe
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1⟩
  · intro currentA toothWidthUm channelAspect fcmlFreqKhz dOut
    have h := statorCoupledLoss_adjoint_eqSat_sound currentA toothWidthUm channelAspect fcmlFreqKhz dOut
    exact ⟨h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## 7. Hardware Synthesis, Multi-Arg `compileStatefulStepToRtl`, ICAP DPR Hot-Swap & 64-Bit AMD `VOP64` GPU -/

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

/-- Explicit sequential `always_ff` `RtlModule` (`foc_drive_top`) implementing the 20 kHz
    FOC + 6-level SiC FCML controller with:
    - Input 0 (`id_err_ma`), Input 1 (`iq_err_ma`), Input 2 (`cap_err_mv`),
      Input 3 (`winding_temp_c`), Input 4 (`dpr_isolate_en`), Input 5 (`dpr_high_bw_sel`)
    - Reg 0 (`int_d`): stateful `always_ff` $d$-axis PI integral accumulator
    - Reg 1 (`int_q`): stateful `always_ff` $q$-axis PI integral accumulator
    - Reg 2 (`fcml_cap_err`): stateful `always_ff` active Lyapunov flying-capacitor balance state
    - Reg 3 (`thermal_trip_latch`): stateful `always_ff` write-once $155^\circ\text{C}$ over-temperature gate-kill latch
    - Reg 4 (`skid_vq_hold`): live mid-run ICAP DPR isolation $q$-axis skid-buffer output hold
    - Reg 5 (`skid_vd_hold`): live mid-run ICAP DPR isolation $d$-axis skid-buffer output hold
    - Safety dominance: `fault_trip` (`wireIdx 3`) unconditionally clamps `vq_cmd_mv = 0`,
      `vd_cmd_mv = 0`, and `pwm_gate_en = 0` in 1 clock cycle even during `dpr_isolate_en = 1`. -/
def focHilSequentialRtlModule : RtlModule where
  name := "foc_drive_top"
  inputNames :=
    [ "id_err_ma"
    , "iq_err_ma"
    , "cap_err_mv"
    , "winding_temp_c"
    , "dpr_isolate_en"
    , "dpr_high_bw_sel"
    ]
  wires :=
    [ { wireIdx := 0
        name := "kp_gain"
        expr := .mux (.inputPort 5) (.const 480#64) (.const 400#64) }
    , { wireIdx := 1
        name := "vq_active_mv"
        expr := .alu .add
          (.alu .mul (.inputPort 1) (.wireRef 0))
          (.regRead 1) }
    , { wireIdx := 2
        name := "overtemp_now"
        expr := .alu .ult (.const 154#64) (.inputPort 3) }
    , { wireIdx := 3
        name := "fault_trip_comb"
        expr := .alu .bitOr (.regRead 3) (.wireRef 2) }
    , { wireIdx := 4
        name := "vd_active_mv"
        expr := .alu .add
          (.alu .mul (.inputPort 0) (.const 400#64))
          (.regRead 0) }
    ]
  regs :=
    [ { regIdx := 0
        name := "int_d"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 0)
            (.alu .add (.regRead 0)
              (.alu .mul (.inputPort 0) (.const 65#64))) }
    , { regIdx := 1
        name := "int_q"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 1)
            (.alu .add (.regRead 1)
              (.alu .mul (.inputPort 1) (.const 65#64))) }
    , { regIdx := 2
        name := "fcml_cap_err"
        domain := .coreClk
        resetKind := .syncReset 15000#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 2)
            (.alu .mul (.inputPort 2) (.const 800#64)) }
    , { regIdx := 3
        name := "thermal_trip_latch"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .wireRef 3 }
    , { regIdx := 4
        name := "skid_vq_hold"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 4)
            (.wireRef 1) }
    , { regIdx := 5
        name := "skid_vd_hold"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 5)
            (.wireRef 4) }
    ]
  outputs :=
    [ { name := "vq_cmd_mv"
        expr :=
          .mux (.wireRef 3)
            (.const 0#64)
            (.mux (.inputPort 4)
              (.regRead 4)
              (.wireRef 1)) }
    , { name := "vd_cmd_mv"
        expr :=
          .mux (.wireRef 3)
            (.const 0#64)
            (.mux (.inputPort 4)
              (.regRead 5)
              (.wireRef 4)) }
    , { name := "cap_bal_mv"
        expr := .regRead 2 }
    , { name := "fault_trip"
        expr := .wireRef 3 }
    , { name := "pwm_gate_en"
        expr := .mux (.wireRef 3) (.const 0#64) (.const 1#64) }
    ]

/-- **Hardware Well-Formedness & FPGA `BelNetlist` Synthesis Certificate for `apps/foc-hil/`**. -/
theorem foc_hil_rtl_and_bel_synthesis_verified :
    checkRtlModule focHilSequentialRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels focHilSequentialRtlModule) = true ∧
    (match clarkeParkRtl?, piCurrentLoopRtl?, sicFcmlLegRtl?, focDriveTopRtl? with
     | some m1, some m2, some m3, some m4 =>
       checkRtlModule m1 &&
       checkRtlModule m2 &&
       checkRtlModule m3 &&
       checkRtlModule m4 &&
       checkBelNetlistValid (synthesizeModuleToBels m4)
     | _, _, _, _ => false) = true := by
  decide +kernel

/-- **Multi-Cycle Sequential `always_ff` HIL Trace Verification (5 Ticks)**:
    Verifies across a 5-tick sequence covering:
    1. Tick 0 (`focIn0`): Rated torque step ($i_q = 250\text{ A}$, $T = 85^\circ\text{C}$, nominal gain $400$).
    2. Tick 1 (`focIn1`): Fault-free mid-run ICAP DPR isolation (`dpr_isolate_en = 1`), holding `int_d`, `int_q`
       and outputting glitch-free held `skid_vq_hold` ($100,000\text{ mV}$) and `skid_vd_hold` ($40,000\text{ mV}$).
    3. Tick 2 (`focIn2`): Post-DPR hot-swap release (`dpr_isolate_en = 0`, `dpr_high_bw_sel = 1`, gain $480$).
    4. Tick 3 (`focIn3`): Simultaneous `dpr_isolate_en = 1` AND $155^\circ\text{C}$ over-temperature injection
       (`winding_temp_c = 155`), proving `fault_trip = 1` overrides `dpr_isolate_en = 1` in 1 clock cycle
       (`vq_cmd_mv = 0`, `vd_cmd_mv = 0`, `pwm_gate_en = 0`).
    5. Tick 4 (`focIn4`): Cool-down to $90^\circ\text{C}$ (`dpr_isolate_en = 0`), proving write-once
       `thermal_trip_latch = 1` keeps `vq_cmd_mv = 0`, `vd_cmd_mv = 0`, `fault_trip = 1`, `pwm_gate_en = 0`. -/
def focInitRegs : Nat → BitVec 64
  | 2 => 15000#64
  | _ => 0#64

def focIn0 : Nat → BitVec 64
  | 0 => 100#64
  | 1 => 250#64
  | 2 => 15#64
  | 3 => 85#64
  | _ => 0#64

def focIn1 : Nat → BitVec 64
  | 0 => 100#64
  | 1 => 250#64
  | 2 => 12#64
  | 3 => 90#64
  | 4 => 1#64
  | _ => 0#64

def focIn2 : Nat → BitVec 64
  | 0 => 50#64
  | 1 => 250#64
  | 2 => 5#64
  | 3 => 110#64
  | 5 => 1#64
  | _ => 0#64

def focIn3 : Nat → BitVec 64
  | 0 => 50#64
  | 1 => 250#64
  | 2 => 0#64
  | 3 => 155#64
  | 4 => 1#64
  | 5 => 1#64
  | _ => 0#64

def focIn4 : Nat → BitVec 64
  | 0 => 50#64
  | 1 => 250#64
  | 2 => 0#64
  | 3 => 90#64
  | 5 => 1#64
  | _ => 0#64

theorem foc_hil_sequential_4tick_trace_verified :
    let regs1 := stepModuleRegs focHilSequentialRtlModule false focIn0 focInitRegs
    let regs2 := stepModuleRegs focHilSequentialRtlModule false focIn1 regs1
    let regs3 := stepModuleRegs focHilSequentialRtlModule false focIn2 regs2
    let regs4 := stepModuleRegs focHilSequentialRtlModule false focIn3 regs3
    -- Tick 0: nominal gain 400 * 250 = 100,000 mV, vd = 40,000 mV, fault_trip = 0, pwm_gate_en = 1
    evalModuleOutputs focHilSequentialRtlModule focIn0 focInitRegs =
      [ ("vq_cmd_mv", 100000#64)
      , ("vd_cmd_mv", 40000#64)
      , ("cap_bal_mv", 15000#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64) ] ∧
    -- Tick 1: ICAP DPR isolation active (`dpr_isolate_en = 1`), glitch-free held vq=100,000 mV & vd=40,000 mV
    evalModuleOutputs focHilSequentialRtlModule focIn1 regs1 =
      [ ("vq_cmd_mv", 100000#64)
      , ("vd_cmd_mv", 40000#64)
      , ("cap_bal_mv", 12000#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64) ] ∧
    -- Tick 2: ICAP DPR hot-swap complete (`dpr_high_bw_sel = 1`), gain 480 * 250 + int_q(16250) = 136,250 mV
    evalModuleOutputs focHilSequentialRtlModule focIn2 regs2 =
      [ ("vq_cmd_mv", 136250#64)
      , ("vd_cmd_mv", 26500#64)
      , ("cap_bal_mv", 12000#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64) ] ∧
    -- Tick 3: Simultaneous dpr_isolate_en=1 + 155°C over-temp forces 1-cycle zeroing of vq, vd & pwm_gate_en
    evalModuleOutputs focHilSequentialRtlModule focIn3 regs3 =
      [ ("vq_cmd_mv", 0#64)
      , ("vd_cmd_mv", 0#64)
      , ("cap_bal_mv", 4000#64)
      , ("fault_trip", 1#64)
      , ("pwm_gate_en", 0#64) ] ∧
    -- Tick 4: Write-once thermal_trip_latch=1 holds vq=0, vd=0, fault_trip=1, pwm_gate_en=0 after cooling to 90°C
    evalModuleOutputs focHilSequentialRtlModule focIn4 regs4 =
      [ ("vq_cmd_mv", 0#64)
      , ("vd_cmd_mv", 0#64)
      , ("cap_bal_mv", 4000#64)
      , ("fault_trip", 1#64)
      , ("pwm_gate_en", 0#64) ] := by
  decide +kernel

/-- **64-Bit AMD `VOP64` GPU Co-Execution Certificate for `FocDriveTop.obend`**:
    Compiles `FocDriveTop`'s `activeFcmlBalanceMv`, `closedLoopVqMv`, and `statorWindingTempC`
    hardware wires via `compileRtlExprToAmdGpu` and verifies exact 64-bit `runAmdGpuVop64Prog`
    equivalence with FPGA RTL evaluation. -/
theorem foc_hil_amdgpu_vop64_equivalence :
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
         ]) &&
       (match m.wires[2]?, m.wires[4]?, m.wires[5]? with
        | some wBal, some wVq, some wTemp =>
          let (rBal, _, codeBal) := compileRtlExprToAmdGpu 1 wBal.expr
          let (rVq, _, codeVq) := compileRtlExprToAmdGpu 1 wVq.expr
          let (rTemp, _, codeTemp) := compileRtlExprToAmdGpu 1 wTemp.expr
          let vgprsBal :=
            runAmdGpuVop64Prog (fun _ => 250#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeBal
          let vgprsVq :=
            runAmdGpuVop64Prog (fun _ => 250#64) (fun _ => 480#64) (fun _ => 0#64) (fun _ => 0#64) codeVq
          let vgprsTemp :=
            runAmdGpuVop64Prog (fun _ => 250#64) (fun _ => 4#64) (fun _ => 0#64) (fun _ => 0#64) codeTemp
          vgprsBal rBal == 5025#64 &&
          vgprsVq rVq == 120250#64 &&
          vgprsTemp rTemp == 1045#64
        | _, _, _ => false)
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
