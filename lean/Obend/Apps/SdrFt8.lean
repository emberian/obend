module

public import Lean
public import Obend.Core.Term
public import Obend.Core.Check
public import Obend.Equiv.Cost
public import Obend.Equiv.Improvement
public import Obend.Logic.Obligation
public import Obend.Logic.Program
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Static
public import Obend.Spec.Parse
public import Obend.Spec.Elaborate
public import Obend.Spec.Workspace
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Spec.CrossPackage
public import Obend.Hardware.HDL
public import Obend.Hardware.Types
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.Accelerators
public import Obend.Hardware.RF
public import Obend.Hardware.DSP
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.SosLyapunov
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
# Flagship App #3: All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver (`Obend.Apps.SdrFt8`)

End-to-end formalization, multi-layer `.obend` elaboration, compile-time `AutoCert` external-judge
synthesis (`"taylor-model@1"`, `"interval@1"`), RF/DSP signoff proofs, stateful `always_ff` 3-stage CIC + folded symmetric FIR + 4-stage
CORDIC + $\Delta\phi[n] = \phi[n] - \phi[n-1]$ 8-FSK FT8 hardware synthesis (`compileStatefulTermsToRtl` /
`compileStatefulStepToRtl`), and cross-package dependency cone
verification for **Flagship App #3 (`apps/sdr-ft8/`)**:

* `apps/sdr-ft8/TayloeQuadratureMixer.obend` — 40m ($7.074\text{ MHz}$) 4-phase ($0^\circ, 90^\circ, 180^\circ, 270^\circ$)
  Tayloe quadrature switching mixer & Hartley/Weaver image-sideband cancellation (`TayloeQuadratureMixer`,
  `UncalibratedTayloeMixer` $\to$ `Calibrated4PhaseTayloeOverride`).
* `apps/sdr-ft8/CicDecimatorFir.obend` — Stateful `always_ff` 3-stage Hogenauer CIC decimator
  ($R = 64, M = 1, N = 3$) and folded symmetric compensation FIR filter (`CicDecimatorFirChain`,
  `BaseCicDecimatorFirSpec` $\to$ `HogenauerCompensatedCicFirOverride`).
* `apps/sdr-ft8/CordicFt8Demod.obend` — 4-stage unrolled vectoring CORDIC `atan2`/`hypot` + stateful
  `always_ff` $\Delta\phi[n] = \phi[n] - \phi[n-1]$ 8-FSK FT8 tone discriminator (`CordicFt8Demodulator`,
  `CordicStatefulDiscrim`).
* `apps/sdr-ft8/SdrFt8Top.obend` — Top-level all-digital 40m FT8 SDR transceiver (`SdrFt8Transceiver`,
  `Nominal40mSdrFt8Transceiver` $\to$ `Calibrated40mFt8TransceiverOverride`) importing `TayloeQuadratureMixer`,
  `CicDecimatorFir`, and `CordicFt8Demod`.

**Not established.** Four bound claims the designs used to carry are gone, because none of them holds
as stated: each quantified over an unbounded natural with no `given` range, so no judge can certify
it and `#import_obend` refused all four (2026-11-04). They were `lo_phasor_taylor_enclosure`
(`thetaMrad <= 1000`), `cic_bitgrowth_interval_bound` (`16 + stages * 6 <= 64`),
`ft8_tone_bin_interval_bound` (`125 + bin * 125 <= 1000`) and `rx_irr_interval_bound`
(`60 + trimErr * 2 <= 90`). The LO phasor enclosure, the CIC register growth, the FT8 tone-bin
range and the image-rejection margin are not established for this app; the judge formats below
(`interval@1`, `taylor-model@1`) remain and are tested on their own queries.
-/

@[expose] public section

namespace Obend.Apps.SdrFt8

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Judge
open Obend.Analysis
open Obend.Spec.CrossPackage
open Obend.Hardware.HDL
open Obend.Hardware.Types
open Obend.Hardware.Compiler
open Obend.Hardware.Synth
open Obend.Hardware.PlaceRoute
open Obend.Hardware.Accelerators
open Obend.Hardware.RF
open Obend.Hardware.DSP

set_option autoImplicit false

/-! ## 1. Kernel-Verified `AutoCert` External Judge Formats (`interval@1`, `taylor-model@1`, `sos-lyapunov-cbf@1`) -/

def sdrNatToCharsFuel : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let d := Char.ofNat (48 + (n % 10))
    let q := n / 10
    if q == 0 then d :: acc
    else sdrNatToCharsFuel fuel q (d :: acc)

def sdrNatToStr (n : Nat) : String :=
  String.ofList (sdrNatToCharsFuel 32 n [])

def sdrIntToStr : Int → String
  | .ofNat n   => sdrNatToStr n
  | .negSucc n => "-" ++ sdrNatToStr (n + 1)

def sdrJoinSep (sep : String) : List String → String
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ sdrJoinSep sep xs

def sdrSplitCharAux (sep : Char) : List Char → List Char → List String
  | [], cur => [String.ofList cur.reverse]
  | c :: cs, cur =>
    if c == sep then
      String.ofList cur.reverse :: sdrSplitCharAux sep cs []
    else
      sdrSplitCharAux sep cs (c :: cur)

def sdrSplitChar (sep : Char) (s : String) : List String :=
  sdrSplitCharAux sep s.toList []

def sdrParseNatChars : List Char → Nat → Bool → Option Nat
  | [], acc, true  => some acc
  | [], _, false   => none
  | c :: cs, acc, _ =>
    if '0' ≤ c && c ≤ '9' then
      sdrParseNatChars cs (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      none

def sdrParseNat? (s : String) : Option Nat :=
  sdrParseNatChars s.toList 0 false

def sdrParseInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (sdrParseNatChars cs 0 false).map fun n => -(Int.ofNat n)
  | cs        => (sdrParseNatChars cs 0 false).map Int.ofNat

def sdrEncodeRatWire (q : CanonicalRat) : String :=
  sdrIntToStr q.num ++ "/" ++ sdrNatToStr q.den

def sdrDecodeRatWire? (s : String) : Option CanonicalRat :=
  match sdrSplitChar '/' s with
  | [nStr, dStr] => do
    let n ← sdrParseInt? nStr
    let d ← sdrParseNat? dStr
    if d == 0 then none else some (CanonicalRat.mk n d)
  | [nStr] => do
    let n ← sdrParseInt? nStr
    some (Rat.ofInt n)
  | _ => none

def sdrEncodeIntervalWire (iv : Interval) : String :=
  sdrEncodeRatWire iv.lo ++ ":" ++ sdrEncodeRatWire iv.hi

def sdrDecodeIntervalWire? (s : String) : Option Interval :=
  match sdrSplitChar ':' s with
  | [loStr, hiStr] => do
    let lo ← sdrDecodeRatWire? loStr
    let hi ← sdrDecodeRatWire? hiStr
    some ⟨lo, hi⟩
  | _ => none

def sdrFindQuotedJsonFieldAux (key : String) : List String → Option String
  | k :: sep :: val :: rest =>
    if k == key && sep == ":" then some val
    else sdrFindQuotedJsonFieldAux key (sep :: val :: rest)
  | _ => none

def sdrExtractJsonStringField? (key : String) (raw : String) : Option String :=
  sdrFindQuotedJsonFieldAux key (sdrSplitChar '"' raw)

def sdrEncodeRealExprTokens : RealExpr → List String
  | .const q => ["C", sdrEncodeRatWire q]
  | .var v   => ["V", v]
  | .add l r => "A" :: (sdrEncodeRealExprTokens l ++ sdrEncodeRealExprTokens r)
  | .sub l r => "S" :: (sdrEncodeRealExprTokens l ++ sdrEncodeRealExprTokens r)
  | .mul l r => "M" :: (sdrEncodeRealExprTokens l ++ sdrEncodeRealExprTokens r)
  | .sqr a   => "Q" :: sdrEncodeRealExprTokens a

def sdrDecodeRealExprTokens : Nat → List String → Option (RealExpr × List String)
  | 0, _ => none
  | _ + 1, "C" :: qStr :: rest => do
    let q ← sdrDecodeRatWire? qStr
    some (.const q, rest)
  | _ + 1, "V" :: v :: rest => some (.var v, rest)
  | fuel + 1, "A" :: rest => do
    let (l, r1) ← sdrDecodeRealExprTokens fuel rest
    let (r, r2) ← sdrDecodeRealExprTokens fuel r1
    some (.add l r, r2)
  | fuel + 1, "S" :: rest => do
    let (l, r1) ← sdrDecodeRealExprTokens fuel rest
    let (r, r2) ← sdrDecodeRealExprTokens fuel r1
    some (.sub l r, r2)
  | fuel + 1, "M" :: rest => do
    let (l, r1) ← sdrDecodeRealExprTokens fuel rest
    let (r, r2) ← sdrDecodeRealExprTokens fuel r1
    some (.mul l r, r2)
  | fuel + 1, "Q" :: rest => do
    let (a, r1) ← sdrDecodeRealExprTokens fuel rest
    some (.sqr a, r1)
  | _, _ => none

def sdrEncodeIntervalEnvWire (env : List (String × Interval)) : String :=
  if env.isEmpty then "-"
  else sdrJoinSep "," (env.map fun (v, iv) => v ++ "=" ++ sdrEncodeIntervalWire iv)

def sdrDecodeIntervalEnvWire? (s : String) : Option (List (String × Interval)) :=
  if s == "-" || s == "" then some []
  else
    (sdrSplitChar ',' s).mapM fun item =>
      match sdrSplitChar '=' item with
      | [v, ivStr] => do
        let iv ← sdrDecodeIntervalWire? ivStr
        some (v, iv)
      | _ => none

def sdrEncodeIntervalQuery (q : IntervalQuery) : String :=
  let wire :=
    sdrJoinSep "~" (sdrEncodeRealExprTokens q.expr) ++ "|" ++
    sdrEncodeIntervalEnvWire q.env ++ "|" ++
    sdrEncodeIntervalWire q.claimedBound
  "{\"kind\":\"interval@1\",\"wire\":\"" ++ wire ++ "\"}"

def sdrDecodeIntervalQuery (s : String) : Except String IntervalQuery :=
  if s == "{}" || s == "" then
    .error "invalid IntervalQuery JSON: missing required fields"
  else
    match sdrExtractJsonStringField? "wire" s with
    | some wire =>
      match sdrSplitChar '|' wire with
      | [exprW, envW, bndW] =>
        match sdrDecodeRealExprTokens 64 (sdrSplitChar '~' exprW),
              sdrDecodeIntervalEnvWire? envW,
              sdrDecodeIntervalWire? bndW with
        | some (expr, []), some env, some claimedBound => .ok { expr, env, claimedBound }
        | _, _, _ => .error "invalid IntervalQuery wire fields"
      | _ => .error "invalid IntervalQuery wire envelope"
    | none => .error "invalid IntervalQuery JSON: missing wire field"

def sdrEncodeIntervalCert : IntervalCert → String
  | .direct => "{\"kind\":\"direct\",\"wire\":\"D\"}"
  | .counterexample _ => "{\"kind\":\"counterexample\",\"wire\":\"X\"}"

def sdrDecodeIntervalCert (s : String) : Except String IntervalCert :=
  if s == "{}" || s == "" then
    .error "invalid IntervalCert JSON: missing required fields"
  else
    match sdrExtractJsonStringField? "wire" s with
    | some "D" => .ok .direct
    | _ => .error "invalid IntervalCert wire"

def sdrBadIntervalQuery : IntervalQuery where
  expr         := .var "x"
  env          := [("x", ⟨0, 10⟩)]
  claimedBound := ⟨0, 2⟩

theorem sdrBadIntervalCert_refused :
    intervalCheck 0 sdrBadIntervalQuery .direct =
      .refused (.boundViolated ⟨0, 10⟩ ⟨0, 2⟩) [] := rfl

def sdrIntervalFormat : Judge.Format where
  name        := "interval"
  version     := "1"
  Obj         := IntervalQuery
  Cert        := IntervalCert
  judge       := intervalJudge
  decodeObj   := sdrDecodeIntervalQuery
  decodeCert  := sdrDecodeIntervalCert
  trust       := .kernel
  regime      := .decidable
  bad         := (sdrBadIntervalQuery, .direct)
  badGrade    := 0
  bad_refused := ⟨_, _, sdrBadIntervalCert_refused⟩

structure SdrTaylorTrigQuery where
  domain       : Interval
  claimedBound : Interval
  deriving DecidableEq, Repr

def verifySdrTaylorTrigCert (q : SdrTaylorTrigQuery) (tm : TaylorModel) : Bool :=
  decide (q.domain.lo ≤ q.domain.hi) &&
  q.domain.isSubintervalOf ⟨-1, 1⟩ &&
  (let compTm := tmAdd (tmCosCertified q.domain) (tmSinCertified q.domain)
   (compTm == tm) && (evalTaylorModelRange tm).isSubintervalOf q.claimedBound)

def checkSdrTaylorTrigJudge (_grade : Nat) (q : SdrTaylorTrigQuery) (tm : TaylorModel) :
    Judge.Verdict String :=
  if verifySdrTaylorTrigCert q tm then .ok
  else .refused "taylor_model_enclosure_violation" []

theorem checkSdrTaylorTrigJudge_sound (grade : Nat) (q : SdrTaylorTrigQuery) (tm : TaylorModel)
    (h : checkSdrTaylorTrigJudge grade q tm = .ok) :
    verifySdrTaylorTrigCert q tm = true ∧
    (evalTaylorModelRange tm).isSubintervalOf q.claimedBound = true := by
  unfold checkSdrTaylorTrigJudge at h
  cases hV : verifySdrTaylorTrigCert q tm with
  | false => rw [hV] at h; contradiction
  | true =>
    refine ⟨rfl, ?_⟩
    unfold verifySdrTaylorTrigCert at hV
    rcases (Bool.and_eq_true _ _).mp hV with ⟨_, hSub⟩
    exact ((Bool.and_eq_true _ _).mp hSub).2

@[instance_reducible] def sdrTaylorTrigJudge : Judge SdrTaylorTrigQuery TaylorModel where
  Clause := String
  Meaning q tm :=
    verifySdrTaylorTrigCert q tm = true ∧
    (evalTaylorModelRange tm).isSubintervalOf q.claimedBound = true
  check := checkSdrTaylorTrigJudge
  sound := by intro r q tm h; exact checkSdrTaylorTrigJudge_sound r q tm h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ tm, verifySdrTaylorTrigCert q tm = true
  complete := by
    intro q _ ⟨tm, htm⟩
    exact ⟨tm, 0, by simp [checkSdrTaylorTrigJudge, htm]⟩
  mono := by intro _ _ _ _ _ _; rfl

def sdrEncodeTaylorTrigQuery (q : SdrTaylorTrigQuery) : String :=
  let wire := sdrEncodeIntervalWire q.domain ++ "|" ++ sdrEncodeIntervalWire q.claimedBound
  "{\"kind\":\"taylor-model@1\",\"wire\":\"" ++ wire ++ "\"}"

def sdrDecodeTaylorTrigQuery (s : String) : Except String SdrTaylorTrigQuery :=
  if s == "{}" || s == "" then
    .error "invalid SdrTaylorTrigQuery JSON: missing required fields"
  else
    match sdrExtractJsonStringField? "wire" s with
    | some wire =>
      match sdrSplitChar '|' wire with
      | [domW, bndW] =>
        match sdrDecodeIntervalWire? domW, sdrDecodeIntervalWire? bndW with
        | some domain, some claimedBound => .ok { domain, claimedBound }
        | _, _ => .error "invalid SdrTaylorTrigQuery wire fields"
      | _ => .error "invalid SdrTaylorTrigQuery wire envelope"
    | none => .error "invalid SdrTaylorTrigQuery JSON: missing wire field"

def sdrEncodeTaylorModelCert (tm : TaylorModel) : String :=
  let coeffsW :=
    if tm.coeffs.isEmpty then "-"
    else sdrJoinSep "," (tm.coeffs.map sdrEncodeRatWire)
  let wire :=
    coeffsW ++ "|" ++
    sdrEncodeRatWire tm.center ++ "|" ++
    sdrEncodeIntervalWire tm.domain ++ "|" ++
    sdrEncodeIntervalWire tm.rem
  "{\"kind\":\"taylor-model-cert@1\",\"wire\":\"" ++ wire ++ "\"}"

def sdrDecodeTaylorModelCert (s : String) : Except String TaylorModel :=
  if s == "{}" || s == "" then
    .error "invalid TaylorModel JSON: missing required fields"
  else
    match sdrExtractJsonStringField? "wire" s with
    | some wire =>
      match sdrSplitChar '|' wire with
      | [coeffsW, ctrW, domW, remW] =>
        let coeffsOpt : Option (List CanonicalRat) :=
          if coeffsW == "-" || coeffsW == "" then some []
          else (sdrSplitChar ',' coeffsW).mapM sdrDecodeRatWire?
        match coeffsOpt, sdrDecodeRatWire? ctrW, sdrDecodeIntervalWire? domW, sdrDecodeIntervalWire? remW with
        | some coeffs, some center, some domain, some rem =>
          .ok { coeffs, center, domain, rem }
        | _, _, _, _ => .error "invalid TaylorModel wire fields"
      | _ => .error "invalid TaylorModel wire envelope"
    | none => .error "invalid TaylorModel JSON: missing wire field"

def sdrGoldenTaylorTrigQuery : SdrTaylorTrigQuery where
  domain       := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  claimedBound := ⟨CanonicalRat.mk 4 5, CanonicalRat.mk 6 5⟩

def sdrBadTaylorModelCert : TaylorModel where
  coeffs := [0]
  center := 0
  domain := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  rem    := ⟨0, 0⟩

theorem sdrBadTaylorModelCert_refused :
    checkSdrTaylorTrigJudge 0 sdrGoldenTaylorTrigQuery sdrBadTaylorModelCert =
      .refused "taylor_model_enclosure_violation" [] := by
  decide +kernel

def sdrTaylorModelFormat : Judge.Format where
  name        := "taylor-model"
  version     := "1"
  Obj         := SdrTaylorTrigQuery
  Cert        := TaylorModel
  judge       := sdrTaylorTrigJudge
  decodeObj   := sdrDecodeTaylorTrigQuery
  decodeCert  := sdrDecodeTaylorModelCert
  trust       := .kernel
  regime      := .decidable
  bad         := (sdrGoldenTaylorTrigQuery, sdrBadTaylorModelCert)
  badGrade    := 0
  bad_refused := ⟨_, _, sdrBadTaylorModelCert_refused⟩

def sdrAutoCertFormats : List Judge.Format :=
  [sdrIntervalFormat, sdrTaylorModelFormat, sosLyapunovFormat] ++ Obend.Logic.defaultExternalFormats

theorem sdrAutoCertFormats_refuse_empty_json :
    sdrIntervalFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid IntervalQuery JSON: missing required fields") [] ∧
    sdrTaylorModelFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid SdrTaylorTrigQuery JSON: missing required fields") [] ∧
    sosLyapunovFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid SosLyapunovProblem JSON: missing required fields") [] := by
  exact ⟨rfl, rfl, sosLyapunovFormat_refuses_empty_json⟩

/-! ## 0. `#import_obend` is `Obend.Elab.Workbook`'s (the one importer, 2026-11-04); this module
only consumes the constants it emits (`<def>_comp`, `<def>_book`, `<def>_val`, `claim_*_{obj,just,holds}`,
`laws_count`). -/

/-! ## 3. Compile-Time Elaboration of `apps/sdr-ft8/*.obend` -/

#import_obend "apps/sdr-ft8/TayloeQuadratureMixer.obend" as SdrTayloe
#import_obend "apps/sdr-ft8/CicDecimatorFir.obend" as SdrCicFir
#import_obend "apps/sdr-ft8/CordicFt8Demod.obend" as SdrCordicFt8
#import_obend "apps/sdr-ft8/SdrFt8Top.obend" as SdrFt8Top

/-! ## 3. Open-Recursive Compositions, Vtable Flattening & `Leaf.Book` Soundness -/

def tayloeMixerComp : Composition :=
  SdrTayloe.calibratedTayloeMixer_comp

def cicFirChainComp : Composition :=
  SdrCicFir.compensatedCicFirChain_comp

def cordicFt8DemodComp : Composition :=
  SdrCordicFt8.unrolled4StageCordicFt8Demod_comp

def nominal40mSdrFt8Comp : Composition :=
  SdrFt8Top.nominal40mSdrFt8_comp

def sdrFt8TopComp : Composition :=
  SdrFt8Top.calibrated40mSdrFt8_comp

theorem tayloeMixerComp_closed : tayloeMixerComp.closedB = true := by decide +kernel
theorem cicFirChainComp_closed : cicFirChainComp.closedB = true := by decide +kernel
theorem cordicFt8DemodComp_closed : cordicFt8DemodComp.closedB = true := by decide +kernel
theorem nominal40mSdrFt8Comp_closed : nominal40mSdrFt8Comp.closedB = true := by decide +kernel
theorem sdrFt8TopComp_closed : sdrFt8TopComp.closedB = true := by decide +kernel

/-- **Vtable Flattening & Leaf Book Soundness across all 4 `apps/sdr-ft8/` Layers**. -/
theorem sdr_ft8_flatten_and_book_sound (m : String) :
    (.get tayloeMixerComp.flatten m ≈b .get tayloeMixerComp.object m) ∧
    (.get (emit tayloeMixerComp).link m ≈b .get tayloeMixerComp.object m) ∧
    (.get cicFirChainComp.flatten m ≈b .get cicFirChainComp.object m) ∧
    (.get (emit cicFirChainComp).link m ≈b .get cicFirChainComp.object m) ∧
    (.get cordicFt8DemodComp.flatten m ≈b .get cordicFt8DemodComp.object m) ∧
    (.get (emit cordicFt8DemodComp).link m ≈b .get cordicFt8DemodComp.object m) ∧
    (.get sdrFt8TopComp.flatten m ≈b .get sdrFt8TopComp.object m) ∧
    (.get (emit sdrFt8TopComp).link m ≈b .get sdrFt8TopComp.object m) :=
  ⟨ flatten_sound tayloeMixerComp tayloeMixerComp_closed m
  , book_sound tayloeMixerComp tayloeMixerComp_closed m
  , flatten_sound cicFirChainComp cicFirChainComp_closed m
  , book_sound cicFirChainComp cicFirChainComp_closed m
  , flatten_sound cordicFt8DemodComp cordicFt8DemodComp_closed m
  , book_sound cordicFt8DemodComp cordicFt8DemodComp_closed m
  , flatten_sound sdrFt8TopComp sdrFt8TopComp_closed m
  , book_sound sdrFt8TopComp sdrFt8TopComp_closed m ⟩

/-- **Static `super` Elimination & Slot Dependency Certificate for `SdrFt8Top.obend`**. -/
theorem sdrFt8Top_book_shape_verified :
    let B := emit sdrFt8TopComp
    B.slots = [ "imageRejectionDb"
              , "friisNoiseFactorMilli"
              , "ddcFilteredMag"
              , "carrierFreqKhz"
              , "demodFt8SymbolStream"
              , "rxSensitivityMarginDb" ] ∧
    B.defs.map (fun d => (d.member, d.slot, d.kind, d.reads)) =
      [ ("imageRejectionDb", 0, .cell, [])
      , ("friisNoiseFactorMilli", 1, .cell, [])
      , ("ddcFilteredMag", 2, .method, [])
      , ("carrierFreqKhz", 3, .cell, [])
      , ("demodFt8SymbolStream", 4, .method, [0])
      , ("rxSensitivityMarginDb", 5, .method, [1])
      ] ∧
    B.closedB = true := by
  decide +kernel

/-! ## 5. Tayloe IQ Image Rejection, Hogenauer CIC Bit-Width, Folded Symmetric FIR & 4-Stage CORDIC Proofs -/

/-- **3-stage Hogenauer CIC specification (`sdrFt8Cic3Spec`)** for the 40m FT8 SDR DDC:
$B_{\text{in}} = 16\text{ bits}$, $N = 3\text{ stages}$, $R = 64$ ($\lceil\log_2(64 \times 1)\rceil = 6$),
requiring $B_{\text{out}} = 16 + 3 \times 6 = 34\text{ bits}$ (allocated inside 36-bit / 64-bit registers). -/
def sdrFt8Cic3Spec : CicFilterSpec where
  filterName      := "sdr_ft8_cic3_r64_m1"
  inputWidthBits  := 16
  numStages       := 3
  decimationRatio := 64
  diffDelay       := 1
  ceilLog2Rm      := 6

/-- **Theorem (`sdr_ft8_image_rejection_and_ddc_signoff_sound`)**:
Connects the `apps/sdr-ft8/` `.obend` transceiver stack to the RF and DSP mathematical theorems:
1. **Tayloe Quadrature Image-Sideband Cancellation (`tayloe_iq_cancels_image_sideband`)**:
   When $I/Q$ conversion gains match (`gainI = gainQ`) and quadrature phase skew is zero (`phaseErr = 0`),
   the opposite-sideband image cancels identically (`evalQuadratureImagePhaseCancel = 0`) while the
   desired sideband coherently doubles (`evalQuadratureDesiredSideband = 2 * gainI * sigAmp`).
2. **40m FT8 RF Front-End & Cascaded Friis Noise Signoff (`rf_transceiver_signoff_poles`, `golden3StageSdrRxChain_verified`)**:
   `checkRfTransceiverSignoff golden40mFt8TransceiverCert = true`, refusing unfiltered PA harmonic
   violations and $6:1$ VSWR mismatches, while the 3-stage LNA + Tayloe + PGA receiver front-end
   achieves $+38.0\text{ dB}$ (`380` tenths dB) gain and $1410$ milli-NF ($\approx 1.49\text{ dB}$ NF).
3. **3-Stage Hogenauer CIC Bit-Growth Bound (`cic_register_width_sound`)**:
   `sdrFt8Cic3Spec` requires $16 + 3 \times 6 = 34\text{ bits}$ and passes `checkCicOverflowFree`
   at $36\text{ bits}$.
4. **Folded Symmetric FIR Multiplier Halving (`firSymmetric_folds_multipliers`)**:
   Pre-adding symmetric delay-line samples `coeff * (xEarly + xLate)` equals the 2-multiplier
   direct form `coeff * xEarly + coeff * xLate` identically for all `coeff, xEarly, xLate`.
5. **4-Stage Unrolled CORDIC Convergence (`cordic_4stage_pipeline_verified`)**:
   `runCordicMicroPipeline 1000 0 442 goldenCordic4Stages = (1484, 704, 0)` with zero residual
   angle error (`z4 = 0`).
6. **End-to-End SDR DDC Signoff (`sdrDdcChain_signoff_sound`, `sdrDdcChain_signoff_poles`)**:
   `checkSdrDdcSignoff goldenSdrDdcChainSpec = true`, guaranteeing NCO phase bounds, $10\times$
   2-stage CORDIC LO norm scaling, zero image residual, overflow-free CIC accumulators, and
   exact folded symmetric FIR sample equivalence. -/
theorem sdr_ft8_image_rejection_and_ddc_signoff_sound :
    (∀ (gainI gainQ phaseErr sigAmp : Int),
      gainI = gainQ → phaseErr = 0 →
      evalQuadratureImagePhaseCancel gainI gainQ phaseErr sigAmp = 0 ∧
      evalQuadratureDesiredSideband gainI gainQ sigAmp = 2 * gainI * sigAmp) ∧
    checkRfTransceiverSignoff golden40mFt8TransceiverCert = true ∧
    checkRfTransceiverSignoff unfilteredPaTransceiverCert = false ∧
    checkRfTransceiverSignoff highVswrTransceiverCert = false ∧
    evalCascadedGainDbTenths golden3StageSdrRxChain = 380 ∧
    evalCascadedFriisMilliNf golden3StageSdrRxChain = 1410 ∧
    evalCicRequiredWidthBits sdrFt8Cic3Spec = 34 ∧
    checkCicOverflowFree sdrFt8Cic3Spec 36 = true ∧
    (sdrFt8Cic3Spec.inputWidthBits ≤ evalCicRequiredWidthBits sdrFt8Cic3Spec ∧
     evalCicRequiredWidthBits sdrFt8Cic3Spec ≤ 36) ∧
    (∀ (coeff xEarly xLate : Int),
      evalFoldedSymmetricFirTapPair coeff xEarly xLate =
      evalDirectFirTapPair coeff xEarly xLate) ∧
    runCordicMicroPipeline 1000 0 442 goldenCordic4Stages = (1484, 704, 0) ∧
    checkSdrDdcSignoff goldenSdrDdcChainSpec = true ∧
    checkSdrDdcSignoff unbalancedIqSdrDdcSpec = false ∧
    checkSdrDdcSignoff underAllocatedCicSdrDdcSpec = false ∧
    (∀ (rfSigAmp xEarly xLate : Int),
      (stepNco goldenSdrDdcChainSpec.nco).phaseWord < goldenSdrDdcChainSpec.nco.phaseModulus ∧
      evalQuadratureImagePhaseCancel goldenSdrDdcChainSpec.iqGainI goldenSdrDdcChainSpec.iqGainQ
        goldenSdrDdcChainSpec.iqPhaseErr rfSigAmp = 0 ∧
      evalSymmetricFirTapPair goldenSdrDdcChainSpec.firTapCoeff xEarly xLate =
        evalDirectFirTapPair goldenSdrDdcChainSpec.firTapCoeff xEarly xLate) := by
  refine ⟨ tayloe_iq_cancels_image_sideband
         , rf_transceiver_signoff_poles.1
         , rf_transceiver_signoff_poles.2.1
         , rf_transceiver_signoff_poles.2.2
         , golden3StageSdrRxChain_verified.1
         , golden3StageSdrRxChain_verified.2.1
         , rfl
         , rfl
         , cic_register_width_sound sdrFt8Cic3Spec 36 rfl
         , firSymmetric_folds_multipliers
         , cordic_4stage_pipeline_verified.1
         , sdrDdcChain_signoff_poles.1
         , sdrDdcChain_signoff_poles.2.1
         , sdrDdcChain_signoff_poles.2.2.2
         , ?_ ⟩
  intro rfSigAmp xEarly xLate
  have hDdc := sdrDdcChain_signoff_sound goldenSdrDdcChainSpec rfSigAmp xEarly xLate rfl
  exact ⟨hDdc.1, hDdc.2.2.1, hDdc.2.2.2.2.2.1⟩

/-! ## 6. Hardware Synthesis: `.obend` Books, Stateful `always_ff` 3-Stage CIC + Folded FIR + CORDIC $\Delta\phi$ FT8 Demodulator -/

/-- Compile all 4 `apps/sdr-ft8/` `.obend` `Book`s to `RtlModule`s via `compileBookToRtl`. -/
def tayloeMixerRtl? : Option RtlModule :=
  compileBookToRtl "sdr_tayloe_mixer" SdrTayloe.calibratedTayloeMixer_book

def cicFirRtl? : Option RtlModule :=
  compileBookToRtl "sdr_cic_fir" SdrCicFir.compensatedCicFirChain_book

def cordicFt8Rtl? : Option RtlModule :=
  compileBookToRtl "sdr_cordic_ft8" SdrCordicFt8.unrolled4StageCordicFt8Demod_book

def sdrFt8TopRtl? : Option RtlModule :=
  compileBookToRtl "sdr_ft8_top_book" SdrFt8Top.calibrated40mSdrFt8_book

/-- Empty struct/union layout context for scalar 64-bit multi-argument stateful $z^{-1}$ step lowering. -/
def emptySdrLayoutCtx : RtlLayoutCtx :=
  { structSlices := [], unionTagBits := 8, unionArms := [] }

/-- Compile the multi-argument stateful $z^{-1}$ `always_ff` `.obend` methods (`alwaysFfNextCicInt1`,
    `alwaysFfNextPrevPhase`, `alwaysFfOutDeltaPhase`) from `SdrCordicFt8.calibratedCordicStatefulDiscrim_book`
    directly into a synchronous `RtlModule` via `compileStatefulTermsToRtl`. -/
def sdrStatefulDiscrimFromObendRtl? : Option RtlModule := do
  let B := SdrCordicFt8.calibratedCordicStatefulDiscrim_book
  let nextCic1 ← lookupBookCode B "alwaysFfNextCicInt1"
  let nextPrev ← lookupBookCode B "alwaysFfNextPrevPhase"
  let outDelta ← lookupBookCode B "alwaysFfOutDeltaPhase"
  compileStatefulTermsToRtl
    "sdr_cordic_stateful_discrim"
    emptySdrLayoutCtx
    ["cicScaleSample"]
    [.alu .mul (.inputPort 0) (.const 2#64)]
    ["usb_sample_mv", "phase_mrad"]
    [("cic_int1", 0#64), ("prev_phase_mrad", 0#64)]
    [nextCic1, nextPrev]
    [("delta_phase_mrad", outDelta)]

/-- Reference `StatefulStepSpec` corresponding to `sdrStatefulDiscrimFromObendRtl?`. -/
def sdrCordicStatefulSpec : StatefulStepSpec where
  moduleName := "sdr_cordic_stateful_discrim"
  inputNames := ["usb_sample_mv", "phase_mrad"]
  stateRegs  :=
    [ { regIdx := 0
        name := "cic_int1"
        initVal := 0#64
        nextExpr := .alu .add (.regRead 0) (.alu .mul (.inputPort 0) (.const 2#64)) }
    , { regIdx := 1
        name := "prev_phase_mrad"
        initVal := 0#64
        nextExpr := .inputPort 1 }
    ]
  outputExprs :=
    [ ( "delta_phase_mrad"
      , .mux (.alu .ult (.inputPort 1) (.regRead 1))
          (.const 0#64)
          (.alu .sub (.inputPort 1) (.regRead 1)) ) ]

/-- **Theorem (`sdr_ft8_stateful_discrim_rtl_verified`)**:
    1. Lowering `SdrCordicFt8.calibratedCordicStatefulDiscrim_book` via `compileStatefulTermsToRtl`
       produces `some (compileStatefulStepToRtl sdrCordicStatefulSpec)`,
    2. The synthesized `always_ff` $z^{-1}$ module passes `checkRtlModule` and lowers to a valid
       FPGA `BelNetlist`,
    3. Every single-cycle clock edge and arbitrary multi-cycle execution trace of the compiled
       `RtlModule` matches `evalStatefulStepPure` and `runStatefulTracePure`
       (`compileStatefulStepToRtl_simulates_step`, `compileStatefulStepToRtl_trace_sound`). -/
theorem sdr_ft8_stateful_discrim_rtl_verified :
    sdrStatefulDiscrimFromObendRtl? = some (compileStatefulStepToRtl sdrCordicStatefulSpec) ∧
    checkRtlModule (compileStatefulStepToRtl sdrCordicStatefulSpec) = true ∧
    checkBelNetlistValid (synthesizeModuleToBels (compileStatefulStepToRtl sdrCordicStatefulSpec)) = true ∧
    (∀ (rst : Bool) (inputs regState : Nat → BitVec 64),
      stepModuleRegs (compileStatefulStepToRtl sdrCordicStatefulSpec) rst inputs regState =
        evalStatefulStepPure sdrCordicStatefulSpec rst inputs regState) ∧
    (∀ (initRegs : Nat → BitVec 64) (trace : List (Bool × (Nat → BitVec 64))),
      runModuleTrace (compileStatefulStepToRtl sdrCordicStatefulSpec) initRegs trace =
        runStatefulTracePure sdrCordicStatefulSpec initRegs trace) :=
  ⟨by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   compileStatefulStepToRtl_simulates_step sdrCordicStatefulSpec,
   compileStatefulStepToRtl_trace_sound sdrCordicStatefulSpec⟩

/-- **Stateful `always_ff` 40m Tayloe IQ + 3-Stage CIC + Folded FIR + CORDIC $\Delta\phi$ FT8 RTL Module
(`sdrFt8SequentialRtlModule`)**:

Inputs (`inputPorts`):
* `in 0` (`i_mix_mv`): In-phase Tayloe quadrature mixer output sample $I[n]$,
* `in 1` (`q_mix_mv`): Quadrature Tayloe mixer output sample $Q[n]$ (shifted by $+90^\circ$ Hilbert path),
* `in 2` (`cordic_phase_mrad`): Instantaneous 4-stage CORDIC unwrapped phase $\phi[n]$ in mrad,
* `in 3` (`decim_strobe`): Decimation strobe ($1$ on $R=64$ decimated symbol boundary, $0$ between),
* `in 4` (`clk_en`): Master synchronous clock enable (`inputPorts.length - 1 = 4`).

Synchronous `always_ff` Registers (`regs`):
* `reg 0` (`cic_int1`, init `0`): 1st-stage Hogenauer CIC integrator $z^{-1}$ register,
* `reg 1` (`cic_int2`, init `0`): 2nd-stage Hogenauer CIC integrator $z^{-1}$ register,
* `reg 2` (`cic_int3`, init `0`): 3rd-stage Hogenauer CIC integrator $z^{-1}$ register,
* `reg 3` (`cic_comb_d1`, init `0`): CIC comb stage $z^{-1}$ delay register,
* `reg 4` (`fir_tap_d1`, init `0`): Folded symmetric FIR delay-line register,
* `reg 5` (`prev_phase_mrad`, init `0`): Previous symbol CORDIC phase register $\phi[n-1]$ for
  stateful $\Delta\phi[n] = \phi[n] - \phi[n-1]$ FT8 8-FSK tone discrimination. -/
def sdrFt8SequentialRtlModule : RtlModule where
  name := "sdr_ft8_top"
  inputNames := ["i_mix_mv", "q_mix_mv", "cordic_phase_mrad", "decim_strobe"]
  wires :=
    [ { wireIdx := 0
        name := "desired_usb_comb"
        expr := .alu .add (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 1
        name := "image_cancel_comb"
        expr := .alu .sub (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 2
        name := "comb_diff_comb"
        expr := .alu .sub (.regRead 2) (.regRead 3) }
    ]
  regs :=
    [ { regIdx := 0
        name := "cic_int1"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .alu .add (.regRead 0) (.wireRef 0) }
    , { regIdx := 1
        name := "cic_int2"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .alu .add (.regRead 1) (.alu .add (.regRead 0) (.wireRef 0)) }
    , { regIdx := 2
        name := "cic_int3"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .alu .add (.regRead 2)
            (.alu .add (.regRead 1)
              (.alu .add (.regRead 0) (.wireRef 0))) }
    , { regIdx := 3
        name := "cic_comb_d1"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .mux (.inputPort 3) (.regRead 2) (.regRead 3) }
    , { regIdx := 4
        name := "fir_tap_d1"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .mux (.inputPort 3) (.wireRef 2) (.regRead 4) }
    , { regIdx := 5
        name := "prev_phase_mrad"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .mux (.inputPort 3) (.inputPort 2) (.regRead 5) }
    ]
  outputs :=
    [ { name := "desired_usb_mv"
        expr := .wireRef 0 }
    , { name := "image_cancel_mv"
        expr := .wireRef 1 }
    , { name := "folded_fir_out"
        expr := .alu .mul (.alu .add (.wireRef 2) (.regRead 4)) (.const 256#64) }
    , { name := "delta_phase_mrad"
        expr := .alu .sub (.inputPort 2) (.regRead 5) }
    ]

/-- **Theorem (`sdr_ft8_rtl_and_bel_synthesis_verified`)**:
1. All 4 `apps/sdr-ft8/` `.obend` `Book`s (`TayloeQuadratureMixer`, `CicDecimatorFir`,
   `CordicFt8Demod`, `SdrFt8Top`) compile to well-formed `RtlModule`s (`checkRtlModule = true`)
   and valid FPGA `BelNetlist`s (`checkBelNetlistValid = true`), and
2. The stateful `always_ff` 3-stage CIC + folded symmetric FIR + CORDIC $\Delta\phi$ FT8 module
   `sdrFt8SequentialRtlModule` passes `checkRtlModule` and lowers to a valid `BelNetlist` with
   6 `FDRE` flip-flop registers. -/
theorem sdr_ft8_rtl_and_bel_synthesis_verified :
    checkRtlModule sdrFt8SequentialRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels sdrFt8SequentialRtlModule) = true ∧
    sdrFt8SequentialRtlModule.regs.length = 6 ∧
    (match tayloeMixerRtl?, cicFirRtl?, cordicFt8Rtl?, sdrFt8TopRtl? with
     | some m1, some m2, some m3, some m4 =>
       checkRtlModule m1 &&
       checkRtlModule m2 &&
       checkRtlModule m3 &&
       checkRtlModule m4 &&
       checkBelNetlistValid (synthesizeModuleToBels m1) &&
       checkBelNetlistValid (synthesizeModuleToBels m2) &&
       checkBelNetlistValid (synthesizeModuleToBels m3) &&
       checkBelNetlistValid (synthesizeModuleToBels m4)
     | _, _, _, _ => false) = true := by
  decide +kernel

/-- Concrete 4-cycle SDR DDC + CORDIC $\Delta\phi$ FT8 input stimulus:
* **Cycle 0**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), initial CORDIC phase $\phi[0] = 100\text{ mrad}$, `decim_strobe = 1`
* **Cycle 1**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), CORDIC phase $\phi[1] = 350\text{ mrad}$ ($\Delta\phi = 250\text{ mrad}$, FT8 tone 2), `decim_strobe = 1`
* **Cycle 2**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), CORDIC phase $\phi[2] = 975\text{ mrad}$ ($\Delta\phi = 625\text{ mrad}$, FT8 tone 5), `decim_strobe = 1`
* **Cycle 3**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), CORDIC phase $\phi[3] = 1850\text{ mrad}$ ($\Delta\phi = 875\text{ mrad}$, FT8 tone 7), `decim_strobe = 1`. -/
def sdrFt8Cycle0Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 100#64
  | 3 => 1#64
  | _ => 0#64

def sdrFt8Cycle1Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 350#64
  | 3 => 1#64
  | _ => 0#64

def sdrFt8Cycle2Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 975#64
  | 3 => 1#64
  | _ => 0#64

def sdrFt8Cycle3Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 1850#64
  | 3 => 1#64
  | _ => 0#64

/-- **Theorem (`sdr_ft8_sequential_cic_cordic_trace_verified`)**:
Simulates `sdrFt8SequentialRtlModule` across the 4-cycle FT8 symbol trace and proves:
1. **Tayloe Image Cancellation (`image_cancel_mv = 0`) & Coherent Desired Sideband (`desired_usb_mv = 1000`)**
   hold across all cycles,
2. **3-Stage Hogenauer CIC Integrator Accumulation**:
   - After Cycle 0: `cic_int1 = 1000`, `cic_int2 = 1000`, `cic_int3 = 1000`,
   - After Cycle 1: `cic_int1 = 2000`, `cic_int2 = 3000`, `cic_int3 = 4000`,
   - After Cycle 2: `cic_int1 = 3000`, `cic_int2 = 6000`, `cic_int3 = 10000`,
   - After Cycle 3: `cic_int1 = 4000`, `cic_int2 = 10000`, `cic_int3 = 20000`,
3. **Folded Symmetric FIR Output (`folded_fir_out`)**:
   At Cycle 2 (with `cic_int3 = 4000`, `cic_comb_d1 = 1000`, `fir_tap_d1 = 1000`),
   `folded_fir_out = ((4000 - 1000) + 1000) * 256 = 1024000`, and
4. **Stateful $\Delta\phi[n] = \phi[n] - \phi[n-1]$ 8-FSK FT8 Tone Discrimination**:
   - Cycle 1 output `delta_phase_mrad = 350 - 100 = 250#64`,
   - Cycle 2 output `delta_phase_mrad = 975 - 350 = 625#64`,
   - Cycle 3 output `delta_phase_mrad = 1850 - 975 = 875#64`. -/
theorem sdr_ft8_sequential_cic_cordic_trace_verified :
    let initRegs : Nat → BitVec 64 := fun _ => 0#64
    let regsAfter1 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle0Inputs initRegs
    let regsAfter2 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle1Inputs regsAfter1
    let regsAfter3 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle2Inputs regsAfter2
    let regsAfter4 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle3Inputs regsAfter3
    evalModuleOutputs sdrFt8SequentialRtlModule sdrFt8Cycle1Inputs regsAfter1 =
      [ ("desired_usb_mv", 1000#64)
      , ("image_cancel_mv", 0#64)
      , ("folded_fir_out", 256000#64)
      , ("delta_phase_mrad", 250#64) ] ∧
    evalModuleOutputs sdrFt8SequentialRtlModule sdrFt8Cycle2Inputs regsAfter2 =
      [ ("desired_usb_mv", 1000#64)
      , ("image_cancel_mv", 0#64)
      , ("folded_fir_out", 1024000#64)
      , ("delta_phase_mrad", 625#64) ] ∧
    evalModuleOutputs sdrFt8SequentialRtlModule sdrFt8Cycle3Inputs regsAfter3 =
      [ ("desired_usb_mv", 1000#64)
      , ("image_cancel_mv", 0#64)
      , ("folded_fir_out", 2304000#64)
      , ("delta_phase_mrad", 875#64) ] ∧
    regsAfter4 0 = 4000#64 ∧
    regsAfter4 1 = 10000#64 ∧
    regsAfter4 2 = 20000#64 ∧
    regsAfter4 5 = 1850#64 := by
  decide +kernel

/-- The compiled `SdrFt8Top.obend`: `checkRtlModule` and one input's outputs (a closed check; a GPU
co-execution claim on an interpreter nobody ran was removed 2026-11-05, the GPU path is `Obend.Hardware.Gpu`). -/
example :
    (match sdrFt8TopRtl? with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 100#64) (fun _ => 0#64) ==
         [ ("out_imageRejectionDb", 68#64)
         , ("out_friisNoiseFactorMilli", 1410#64)
         , ("out_ddcFilteredMag", 828#64)
         , ("out_carrierFreqKhz", 7074#64)
         , ("out_demodFt8SymbolStream", 8050#64)
         , ("out_rxSensitivityMarginDb", 2410#64)
         ])
     | none => false) = true := by
  decide +kernel

/-! ## 7. Cross-Package Dependency Cone Survival & Calibration Hot-Swap Guard (`sdr_ft8_crossPackage_cone_survives`) -/

def extractSdrBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

def sdrDemodFt8Body : Term :=
  extractSdrBookMethodInner (emit sdrFt8TopComp) "demodFt8SymbolStream"

def sdrRxSensitivityBody : Term :=
  extractSdrBookMethodInner (emit sdrFt8TopComp) "rxSensitivityMarginDb"

/-- **Cross-Package Dependency Cone Survival (`sdr_ft8_crossPackage_cone_survives`)**:
    1. `extractReadMembers sdrDemodFt8Body = ["imageRejectionDb"]` and
       `extractReadMembers sdrRxSensitivityBody = ["friisNoiseFactorMilli"]`.
    2. By `extractReadMembers_mutation_invariant`, mutating any disjoint member (such as
       `"carrierFreqKhz"` or `"ddcFilteredMag"`) leaves `substMemberEnv` of both
       `sdrDemodFt8Body` and `sdrRxSensitivityBody` identically unchanged. -/
theorem sdr_ft8_crossPackage_cone_survives
    (env : String → Option Term) (newVal : Option Term) :
    extractReadMembers sdrDemodFt8Body = ["imageRejectionDb"] ∧
    extractReadMembers sdrRxSensitivityBody = ["friisNoiseFactorMilli"] ∧
    substMemberEnv (mutateMemberEnv env "carrierFreqKhz" newVal) sdrDemodFt8Body =
      substMemberEnv env sdrDemodFt8Body ∧
    substMemberEnv (mutateMemberEnv env "ddcFilteredMag" newVal) sdrRxSensitivityBody =
      substMemberEnv env sdrRxSensitivityBody :=
  ⟨ by decide +kernel
  , by decide +kernel
  , (extractReadMembers_mutation_invariant sdrDemodFt8Body env newVal (by decide +kernel)).1
  , (extractReadMembers_mutation_invariant sdrRxSensitivityBody env newVal (by decide +kernel)).1 ⟩

end Obend.Apps.SdrFt8
end
