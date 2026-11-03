/-
# Automatic Certificate Synthesis (`AutoCert`) & Module-Mode Workbook Test Suite (`WS-4A-2`)

Exercises Foundation C (`lean/Obend/Elab/AutoCert.lean`) across `Obend.Elab.Workbook` and
`Obend.Spec.FrontEnd`, `Obend.Hardware.Judge` (`encodeRtlSynthObj` / `encodeRtlSynthCert` /
`rtlSynthFormat`), `Obend.Stdlib`, and `Obend.Tactic.DocsCensus`:

1. **Judge 1 (`"interval@1"`)**:
   - Adaptive bisection witness synthesis (`IntervalCert.bisect`) where naive depth-0 interval
     evaluation fails due to dependency blowup (`x - x` on `[0, 1]`), JSON wire roundtrips,
     `checkIntervalAutoCert_sound`, and negative refusals (`badIntervalObj`, `"{}"`, false AST bounds).
2. **Judge 2 (`"taylor-model@1"`)**:
   - Degree-4 univariate Taylor Model synthesis (`cos(x) + sin(x)` on `[-1/10, 1/10]`), JSON wire
     roundtrips, `checkTaylorModelJudge_sound`, and negative refusals (`badTaylorModelCert`, `"{}"`,
     false transcendental bounds).
3. **Judge 3 (`"sos-lyapunov-cbf@1"`)**:
   - SOS Gram / Lyapunov / CBF / Index-1 DAE witness synthesis (`synthesizeSosLyapunovCert`),
     both canonical and structured JSON wire roundtrips (`encodeSosLyapunovProblemJson` /
     `encodeSosLyapunovCertJson`), `sosLyapunovFormat.checkBytes`, and negative refusals.
4. **Judge 4 (`"groebner@1"`)**:
   - Multi-divisor `polyDivModWithQuotients` + S-polynomial Buchberger completion
     (`completeGroebnerBasis`) where direct uncompleted reduction fails (`g1 = x1^2 - x0`,
     `g2 = x0*x1 - 1 |- x1 - x0^2 = 0`), Positivstellensatz non-negativity mode, wire roundtrips,
     `checkGroebnerJudge_sound`, and negative refusals.
5. **Judge 5 (`"rtl-synth@1"` & `"hw-rtl-synth@1"`)**:
   - `decodeRtlSynthObj_encodeRtlSynthObj_roundtrip` and `decodeRtlSynthCert_encodeRtlSynthCert_roundtrip`,
     real `.obend` `Leaf.Book` lowering (`StdlibCell.versionedCell_book`), and negative refusals on
     combinational loops (`badLoopRtlModule`), empty `Book`, and `"{}"`.
6. **End-to-End `Workbook` (`#obend_decl`) + `FrontEnd` (`elaborateContractsWithCerts` /
   `elaborateContractsWithAutoCerts`) + Bitwise/Shift/Q32 `Primitive` `ToExpr`**:
   - Inline `.obend` spec & Isar `contract` exercising all 5 auto-synthesized judges, bitwise/shift/Q32
     primitives (`.bitAnd`, `.bitOr`, `.bitXor`, `.shl`, `.lshr`, `.ashr`, `.slt`, `.qmul32`),
     and fail-closed negative refusals on false claims, false `by weave` claims, false contract steps,
     and unregistered judges.
7. **`#tooth` Mutation Tests & Compile-Time `0 sorryAx` Audit (`#verify_autocert_axioms`)**.
-/
import Obend.Elab.AutoCert
import Obend.Elab.Workbook
import Obend.Stdlib
import Obend.Tactic.DocsCensus
import Obend.Tactic.Tooth

open Obend.Core.Term (Primitive Term)
open Obend.Judge (Verdict Format IntervalQuery)
open Obend.Judge.SOS (Poly)
open Obend.Analysis
  (polyVarPow polyConst SosLyapunovProblem SosLyapunovCert
   goldenSosProblem goldenSosCert badSosCert
   decodeSosLyapunovProblem decodeSosLyapunovCert sosLyapunovFormat)
open Obend.Hardware.HDL (RtlModule)
open Obend.Hardware.Judge
  (encodeRtlSynthObj decodeRtlSynthObj encodeRtlSynthCert decodeRtlSynthCert
   normalizeRtlModuleForWire goldenFlatRtlModule badLoopRtlModule
   rtlSynthFormat hwSynthFormat checkRtlSynth
   verdict_eq_ok_of_isOk verdict_ne_ok_of_isOk_false
   decodeRtlSynthObj_encodeRtlSynthObj_roundtrip
   decodeRtlSynthCert_encodeRtlSynthCert_roundtrip)
open Obend.Logic
  (ClaimObj Justification obligationCheckWithJudges obligationMeaningWithJudges)
open Obend.Spec.FrontEnd
  (defaultAutoCertAdmitsTag elaborateContractsWithCerts elaborateContractsWithAutoCerts)
open Obend.Elab.AutoCert
open Obend.Elab.Workbook
open Obend.Stdlib

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Judge 1: `"interval@1"` (Adaptive Bisection, Wire Roundtrip, Soundness & Refusals) -/

/-- Naive depth-0 interval evaluation fails on `goldenBisectIntervalObj` (`x - x ∈ [-1/4, 1/4]`
    over `x ∈ [0, 1]`) because `[0, 1] - [0, 1] = [-1, 1]` exceeds `[-1/4, 1/4]`. -/
theorem interval_direct_fails_without_bisection :
    (checkIntervalAutoCert goldenBisectIntervalObj .direct).isOk = false := by decide +kernel

def synthesizedBisectCert : IntervalCert :=
  (synthesizeIntervalCert 4 goldenBisectIntervalObj).getD .direct

/-- Adaptive bisection (`synthesizeIntervalCert 4`) synthesizes a multi-level `.bisect` tree
    accepted by `checkIntervalAutoCert` and `intervalFormat.checkBytes`. -/
theorem interval_bisect_synthesizes_and_checks :
    synthesizeIntervalCert 4 goldenBisectIntervalObj = some synthesizedBisectCert ∧
    synthesizedBisectCert ≠ .direct ∧
    checkIntervalAutoCert goldenBisectIntervalObj synthesizedBisectCert = Verdict.ok ∧
    decodeIntervalObj (encodeIntervalObj goldenBisectIntervalObj) = Except.ok goldenBisectIntervalObj ∧
    decodeIntervalCert (encodeIntervalCert synthesizedBisectCert) = Except.ok synthesizedBisectCert ∧
    intervalFormat.checkBytes 0
      (encodeIntervalObj goldenBisectIntervalObj) (encodeIntervalCert synthesizedBisectCert) = Verdict.ok :=
  ⟨by decide +kernel,
   by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel),
   decodeIntervalObj_encodeIntervalObj_golden,
   by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel)⟩

/-- Universal semantic enclosure proved via `checkIntervalAutoCert_sound`. -/
theorem interval_bisect_semantic_sound :
    IntervalQuery.SemanticMeaning goldenBisectIntervalObj.toQuery :=
  checkIntervalAutoCert_sound goldenBisectIntervalObj synthesizedBisectCert
    interval_bisect_synthesizes_and_checks.2.2.1

/-- Negative refusal tests for `"interval@1"`: `badIntervalObj`, empty JSON `"{}"`, and false
    `.obend` inequality `x + 5n <= 2n` are all strictly refused. -/
theorem interval_negative_refusals :
    checkIntervalAutoCert badIntervalObj .direct ≠ Verdict.ok ∧
    (intervalFormat.checkBytes 0 "{}" "{}").isOk = false ∧
    synthesizeJudgeWirePair "interval@1" "Mod"
      (some (.binary "<=" (.binary "+" (.var "x") (.nat "5")) (.nat "2"))) none = none ∧
    synthesizeJudgeWirePair "interval@1" "Mod" (some (.bool false)) none = none :=
  ⟨verdict_ne_ok_of_isOk_false (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   rfl⟩

/-! ## 2. Judge 2: `"taylor-model@1"` (Degree-4 Transcendental Enclosure, Wire Roundtrip & Refusals) -/

def synthesizedTaylorCert : Obend.Analysis.TaylorModel :=
  (synthesizeTaylorModelCert goldenTaylorModelQuery).getD badTaylorModelCert

theorem taylor_model_synthesizes_and_checks :
    synthesizeTaylorModelCert goldenTaylorModelQuery = some synthesizedTaylorCert ∧
    checkTaylorModelJudge 0 goldenTaylorModelQuery synthesizedTaylorCert = Verdict.ok ∧
    decodeTaylorModelQuery (encodeTaylorModelQuery goldenTaylorModelQuery) =
      Except.ok goldenTaylorModelQuery ∧
    decodeTaylorModelCert (encodeTaylorModelCert synthesizedTaylorCert) =
      Except.ok synthesizedTaylorCert ∧
    taylorModelFormat.checkBytes 0
      (encodeTaylorModelQuery goldenTaylorModelQuery) (encodeTaylorModelCert synthesizedTaylorCert) =
      Verdict.ok :=
  ⟨by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel),
   decodeTaylorModelQuery_encodeTaylorModelQuery_golden,
   by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel)⟩

theorem taylor_model_semantic_sound :
    verifyTaylorModelCert goldenTaylorModelQuery synthesizedTaylorCert = true ∧
    (Obend.Analysis.evalTaylorModelRange synthesizedTaylorCert).isSubintervalOf
      goldenTaylorModelQuery.claimedBound = true :=
  checkTaylorModelJudge_sound 0 goldenTaylorModelQuery synthesizedTaylorCert
    taylor_model_synthesizes_and_checks.2.1

/-- Negative refusal tests for `"taylor-model@1"`: `badTaylorModelCert`, empty JSON `"{}"`,
    `cos(x) + 5n <= 2n`, and `sin(x) <= 0n` (since `sin(0.1) > 0` on `[-1/10, 1/10]`) all fail closed. -/
theorem taylor_model_negative_refusals :
    checkTaylorModelJudge 0 goldenTaylorModelQuery badTaylorModelCert ≠ Verdict.ok ∧
    (taylorModelFormat.checkBytes 0 "{}" "{}").isOk = false ∧
    synthesizeJudgeWirePair "taylor-model@1" "Mod"
      (some (.binary "<=" (.binary "+" (.call (.var "cos") [.var "x"]) (.nat "5")) (.nat "2"))) none = none ∧
    synthesizeJudgeWirePair "taylor-model@1" "Mod"
      (some (.binary "<=" (.call (.var "sin") [.var "x"]) (.nat "0"))) none = none :=
  ⟨verdict_ne_ok_of_isOk_false (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   by decide +kernel⟩

/-! ## 3. Judge 3: `"sos-lyapunov-cbf@1"` (SOS Gram / Lyapunov / CBF / DAE Synthesis & JSON Codec) -/

theorem sos_lyapunov_synthesizes_and_checks :
    synthesizeSosLyapunovCert goldenSosProblem = some goldenSosCert ∧
    sosLyapunovFormat.checkBytes 0
      (encodeSosLyapunovProblem goldenSosProblem) (encodeSosLyapunovCert goldenSosCert) = Verdict.ok :=
  ⟨by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel)⟩

/-- Exercise the structured JSON wire encoder/decoder path (`encodeSosLyapunovProblemJson` /
    `encodeSosLyapunovCertJson`) through `decodeSosLyapunovProblem`, `decodeSosLyapunovCert`,
    and `sosLyapunovFormat.checkBytes`. -/
def checkStructuredSosJsonRoundtrip : Bool :=
  let probJson := encodeSosLyapunovProblemJson goldenSosProblem
  let certJson := encodeSosLyapunovCertJson goldenSosCert
  (decodeSosLyapunovProblem probJson).isOk &&
  (decodeSosLyapunovCert certJson).isOk &&
  (sosLyapunovFormat.checkBytes 0 probJson certJson).isOk

#guard checkStructuredSosJsonRoundtrip == true

/-- Positive & negative `.obend` AST extraction for `"sos-lyapunov-cbf@1"`:
    `0n <= x * x + y * y` succeeds, while non-SOS `0n <= x`, false `x + 5n <= 2n`, and `"{}"` fail closed. -/
theorem sos_lyapunov_ast_and_negative_refusals :
    (synthesizeJudgeWirePair "sos-lyapunov-cbf@1" "Mod"
      (some (.binary "<=" (.nat "0")
        (.binary "+" (.binary "*" (.var "x") (.var "x")) (.binary "*" (.var "y") (.var "y"))))) none).isSome = true ∧
    synthesizeJudgeWirePair "sos-lyapunov-cbf@1" "Mod"
      (some (.binary "<=" (.nat "0") (.var "x"))) none = none ∧
    synthesizeJudgeWirePair "sos-lyapunov-cbf@1" "Mod"
      (some (.binary "<=" (.binary "+" (.var "x") (.nat "5")) (.nat "2"))) none = none ∧
    (sosLyapunovFormat.checkBytes 0 "{}" "{}").isOk = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 4. Judge 4: `"groebner@1"` (Buchberger S-Polynomial Completion, Positivstellensatz & Soundness) -/

/-- Without Buchberger S-polynomial completion, direct division of `x1 - x0^2` by `[x1^2 - x0, x0*x1 - 1]`
    cannot eliminate `x1 - x0^2` (remainder is non-zero). -/
theorem groebner_direct_division_insufficient :
    (polyDivModWithQuotients 16 goldenGroebnerQuery.target goldenGroebnerQuery.eqGens).1.isZero = false := by
  decide +kernel

def synthesizedGroebnerCert : GroebnerCert :=
  (synthesizeGroebnerCert goldenGroebnerQuery).getD badGroebnerCert

/-- With `completeGroebnerBasis` cofactor tracking, `synthesizeGroebnerCert` discovers the S-polynomial
    consequence and synthesizes an ideal-membership witness directly over the original generators! -/
theorem groebner_buchberger_synthesizes_and_checks :
    synthesizeGroebnerCert goldenGroebnerQuery = some synthesizedGroebnerCert ∧
    checkGroebnerJudge 0 goldenGroebnerQuery synthesizedGroebnerCert = Verdict.ok ∧
    decodeGroebnerQuery (encodeGroebnerQuery goldenGroebnerQuery) = Except.ok goldenGroebnerQuery ∧
    decodeGroebnerCert (encodeGroebnerCert synthesizedGroebnerCert) = Except.ok synthesizedGroebnerCert ∧
    groebnerFormat.checkBytes 0
      (encodeGroebnerQuery goldenGroebnerQuery) (encodeGroebnerCert synthesizedGroebnerCert) = Verdict.ok :=
  ⟨by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel),
   decodeGroebnerQuery_encodeGroebnerQuery_golden,
   by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel)⟩

theorem groebner_buchberger_semantic_sound :
    verifyGroebnerCert goldenGroebnerQuery synthesizedGroebnerCert = true :=
  (checkGroebnerJudge_sound 0 goldenGroebnerQuery synthesizedGroebnerCert
    groebner_buchberger_synthesizes_and_checks.2.1).1

/-- Positivstellensatz non-negativity query (`isNonneg = true`) on `x0^2 + x1^2 >= 0` modulo `x2 - 1 = 0`. -/
def samplePsatzGroebnerQuery : GroebnerQuery where
  target   := Poly.add (polyVarPow 0 2) (polyVarPow 1 2)
  eqGens   := [Poly.sub (polyVarPow 2 1) (polyConst 1)]
  ineqGens := []
  isNonneg := true
  divFuel  := 16

def synthesizedPsatzGroebnerCert : GroebnerCert :=
  (synthesizeGroebnerCert samplePsatzGroebnerQuery).getD badGroebnerCert

theorem groebner_psatz_nonneg_synthesizes_and_sound :
    synthesizeGroebnerCert samplePsatzGroebnerQuery = some synthesizedPsatzGroebnerCert ∧
    verifyGroebnerCert samplePsatzGroebnerQuery synthesizedPsatzGroebnerCert = true :=
  have hOk : checkGroebnerJudge 0 samplePsatzGroebnerQuery synthesizedPsatzGroebnerCert = Verdict.ok :=
    verdict_eq_ok_of_isOk (by decide +kernel)
  ⟨by decide +kernel,
   (checkGroebnerJudge_sound 0 samplePsatzGroebnerQuery synthesizedPsatzGroebnerCert hOk).1⟩

/-- Negative refusal tests for `"groebner@1"`: `badGroebnerCert`, empty JSON `"{}"`, and false
    polynomial identity `(x + 1n) * (x + 1n) == x * x + 1n` fail closed, while true identity
    `(x + 1n) * (x + 1n) == x * x + 2n * x + 1n` succeeds. -/
theorem groebner_negative_and_positive_ast :
    checkGroebnerJudge 0 goldenGroebnerQuery badGroebnerCert ≠ Verdict.ok ∧
    (groebnerFormat.checkBytes 0 "{}" "{}").isOk = false ∧
    synthesizeJudgeWirePair "groebner@1" "Mod"
      (some (.binary "=="
        (.binary "*" (.binary "+" (.var "x") (.nat "1")) (.binary "+" (.var "x") (.nat "1")))
        (.binary "+" (.binary "*" (.var "x") (.var "x")) (.nat "1")))) none = none ∧
    (synthesizeJudgeWirePair "groebner@1" "Mod"
      (some (.binary "=="
        (.binary "*" (.binary "+" (.var "x") (.nat "1")) (.binary "+" (.var "x") (.nat "1")))
        (.binary "+" (.binary "+" (.binary "*" (.var "x") (.var "x"))
          (.binary "*" (.nat "2") (.var "x"))) (.nat "1")))) none).isSome = true :=
  ⟨verdict_ne_ok_of_isOk_false (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   by decide +kernel⟩

/-! ## 5. Judge 5: `"rtl-synth@1"` & `"hw-rtl-synth@1"` (Wire Roundtrips, Real `Leaf.Book` & Refusals) -/

theorem rtl_synth_wire_roundtrips :
    decodeRtlSynthObj (encodeRtlSynthObj "test_rtl_synth") = Except.ok "test_rtl_synth" ∧
    decodeRtlSynthCert (encodeRtlSynthCert goldenFlatRtlModule) = Except.ok goldenFlatRtlModule :=
  ⟨decodeRtlSynthObj_encodeRtlSynthObj_roundtrip.1,
   decodeRtlSynthCert_encodeRtlSynthCert_roundtrip.1⟩

def synthesizedStdlibCellRtl : RtlModule :=
  (synthesizeRtlSynthCert "versioned_cell_rtl" (some StdlibCell.versionedCell_book)).getD badLoopRtlModule

/-- Synthesize a real `RtlModule` from `StdlibCell.versionedCell_book` (`stdlib/core/Cell.obend`)
    and verify wire acceptance under BOTH `"rtl-synth@1"` and `"hw-rtl-synth@1"`. -/
theorem rtl_synth_from_stdlib_book_checks :
    synthesizeRtlSynthCert "versioned_cell_rtl" (some StdlibCell.versionedCell_book) =
      some synthesizedStdlibCellRtl ∧
    rtlSynthFormat.checkBytes 0
      (encodeRtlSynthObj "versioned_cell_rtl") (encodeRtlSynthCert synthesizedStdlibCellRtl) = Verdict.ok ∧
    hwSynthFormat.checkBytes 0
      (encodeRtlSynthObj "versioned_cell_rtl") (encodeRtlSynthCert synthesizedStdlibCellRtl) = Verdict.ok :=
  ⟨by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel),
   verdict_eq_ok_of_isOk (by decide +kernel)⟩

/-- Negative refusal tests for `"rtl-synth@1"` / `"hw-rtl-synth@1"`:
    empty `Leaf.Book` (`⟨[]⟩`) returns `none`, combinational-loop `badLoopRtlModule` is refused,
    and empty JSON `"{}"` is refused. -/
theorem rtl_synth_negative_refusals :
    synthesizeRtlSynthCert "empty_book_mod" (some ⟨[]⟩) = none ∧
    checkRtlSynth 0 "bad_loop_mod" badLoopRtlModule ≠ Verdict.ok ∧
    (rtlSynthFormat.checkBytes 0 "{}" "{}").isOk = false ∧
    (hwSynthFormat.checkBytes 0 "{}" "{}").isOk = false :=
  ⟨rfl,
   verdict_ne_ok_of_isOk_false (by decide +kernel),
   by decide +kernel,
   by decide +kernel⟩

/-! ## 6. End-to-End `#obend_decl` (`Workbook`), `FrontEnd` Contracts & All 8 New `Primitive` Ops -/

#obend_decl AutoCertSuite "
record FocState:
  step() -> Nat
  aluMix(a: Nat, b: Nat) -> Nat

def sin(x: Nat) -> Nat:
  x

def cos(x: Nat) -> Nat:
  1n

spec FocSpec for FocState:
  def step() -> Nat:
    7n
  def aluMix(a: Nat, b: Nat) -> Nat:
    ((a & 0xFFn) | (b ^ 0x0Fn)) + (a << 2n) + (b >>> 1n) + (a >> 1n) + qmul32(a, b)
  claim bisected_bound(x: Nat) by judge(\"interval@1\"): 4n * x <= 4n * x + 1n
  claim trig_enclosure(x: Nat) by judge(\"taylor-model@1\"): cos(x) + sin(x) <= 2n
  claim lyapunov_sos(x: Nat, y: Nat) by judge(\"sos-lyapunov-cbf@1\"): 0n <= x * x + y * y
  claim poly_ring_id(x: Nat, y: Nat) by judge(\"groebner@1\"): (x + y) * (x + y) == x * x + 2n * x * y + y * y
  claim rtl_core_synth(k: Nat) by judge(\"rtl-synth@1\"): self.step == 7n

def seedFoc() -> FocState:
  {step: 0n, aluMix: fn(a: Nat, b: Nat) -> Nat: a + b}

def focCore() -> FocState:
  fix(FocSpec, seedFoc())

def checkSignedLt(a: Nat, b: Nat) -> Bool:
  a <s b

contract FocContract for FocState by frame:
  invariant: self.step <= 10n
  law: monotone(step)
  have hIv: 4n * x <= 4n * x + 1n by judge(\"interval@1\")
  have hTm: cos(x) + sin(x) <= 2n by judge(\"taylor-model@1\")
  have hSos: 0n <= x * x + y * y by judge(\"sos-lyapunov-cbf@1\")
  have hGb: (x + 1n) * (x + 1n) == x * x + 2n * x + 1n by judge(\"groebner@1\")
  have hRtl: 1n == 1n by judge(\"rtl-synth@1\")
  show self.step <= 10n by frame
"

/-- `#obend_decl AutoCertSuite` passed `FrontEnd.accept` and `verifyWorkbookObligationsWithLean`
    verified all 5 external-judge claims (`interval@1`, `taylor-model@1`, `sos-lyapunov-cbf@1`,
    `groebner@1`, `rtl-synth@1`)! -/
theorem autoCertSuite_accepted_and_obligations_verified :
    AutoCertSuite.accepted = true ∧
    verifyWorkbookObligationsWithLean AutoCertSuite.package = true :=
  ⟨AutoCertSuite.accepted_eq, by decide +kernel⟩

/-- All 5 emitted `*_holds` theorems from `#obend_decl AutoCertSuite` establish kernel-verified
    `obligationMeaningWithJudges workbookFormats`! -/
theorem autoCertSuite_all_5_external_judges_hold :
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_bisected_bound_obj
      AutoCertSuite.claim_bisected_bound_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_trig_enclosure_obj
      AutoCertSuite.claim_trig_enclosure_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_lyapunov_sos_obj
      AutoCertSuite.claim_lyapunov_sos_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_poly_ring_id_obj
      AutoCertSuite.claim_poly_ring_id_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_rtl_core_synth_obj
      AutoCertSuite.claim_rtl_core_synth_just :=
  ⟨AutoCertSuite.claim_bisected_bound_holds,
   AutoCertSuite.claim_trig_enclosure_holds,
   AutoCertSuite.claim_lyapunov_sos_holds,
   AutoCertSuite.claim_poly_ring_id_holds,
   AutoCertSuite.claim_rtl_core_synth_holds⟩

/-- Verify that all 8 Wave-4 bitwise/shift/signed/fixed-point `Primitive` constructors
    (`.bitAnd`, `.bitOr`, `.bitXor`, `.shl`, `.lshr`, `.ashr`, `.slt`, `.qmul32`) elaborated cleanly
    through `toExprPrimitive` / `metaToExprPrimitive` inside `#obend_decl AutoCertSuite`. -/
theorem autoCertSuite_wave4_primitives_elaborated :
    AutoCertSuite.checkSignedLt_term =
      .lam (.lam (.binary .slt (.bound 1) (.bound 0))) := rfl

/-- End-to-end `FrontEnd.elaborateContractsWithAutoCerts` positive test: synthesizes 5 verified
    `(tag, objWire, certWire)` witnesses for `FocContract`. -/
def checkFrontEndContractAutoCerts : Bool :=
  match parseAndCheckObendModule AutoCertSuite.package.source "AutoCertSuite" [] with
  | .error _ => false
  | .ok (_, decodedMod) =>
    match elaborateContractsWithAutoCerts defaultAutoCertAdmitsTag decodedMod (some AutoCertSuite.focCore_book) with
    | .error _ => false
    | .ok (contracts, certs, bundles) =>
      contracts.length == 1 &&
      certs.length == 1 &&
      match bundles with
      | [("FocContract", ws)] =>
        ws.length == 5 &&
        ws.any (fun (t, _, _) => t == "interval@1") &&
        ws.any (fun (t, _, _) => t == "taylor-model@1") &&
        ws.any (fun (t, _, _) => t == "sos-lyapunov-cbf@1") &&
        ws.any (fun (t, _, _) => t == "groebner@1") &&
        ws.any (fun (t, _, _) => t == "rtl-synth@1")
      | _ => false

#guard checkFrontEndContractAutoCerts == true

/-- Fail-closed negative test 1: a false `by judge("interval@1")` claim (`x + 5n <= 2n`) is NOT
    auto-verified (`autoVerified == false`) and never falls through to another judge. -/
def falseIntervalClaimSrc : String :=
"edition ObjectiveBend 1
record Box:
  v() -> Nat
spec S for Box:
  def v() -> Nat:
    1n
  claim bad_bound(x: Nat) by judge(\"interval@1\"): x + 5n <= 2n
def mkBox() -> Box:
  fix(S, {v: 0n})
"

#guard
  (match elaborateObendSource falseIntervalClaimSrc "FalseIvMod" with
   | .ok pkg =>
     match pkg.findClaim? "bad_bound" with
     | some wc => wc.autoVerified == false && wc.autoJustification?.isNone
     | none => false
   | .error _ => false) == true

/-- Fail-closed negative test 2: a false `by weave` claim (`self.v == 999n`) is NEVER hijacked
    by `AutoCert` (`autoVerified == false`). -/
def falseWeaveClaimSrc : String :=
"edition ObjectiveBend 1
record Box:
  v() -> Nat
spec S for Box:
  def v() -> Nat:
    1n
  claim bad_weave(x: Nat) by weave: self.v == 999n
def mkBox() -> Box:
  fix(S, {v: 0n})
"

#guard
  (match elaborateObendSource falseWeaveClaimSrc "FalseWeaveMod" with
   | .ok pkg =>
     match pkg.findClaim? "bad_weave" with
     | some wc => wc.autoVerified == false
     | none => false
   | .error _ => false) == true

/-- Fail-closed negative test 3: a `contract` mixing a valid `by judge("interval@1")` step with a
    SECOND false `by judge("interval@1")` step (`x + 5n <= 2n`) is strictly REFUSED by both
    `Workbook.elaborateObendSource` AND `FrontEnd.elaborateContractsWithCerts`! -/
def falseMixedContractSrc : String :=
"edition ObjectiveBend 1
record Box:
  v: Nat
def idBox(b: Box) -> Box:
  b
contract BadMixed for Box by frame:
  invariant: self.v <= 10n
  law: monotone(v)
  have hGood: 4n * x <= 4n * x + 1n by judge(\"interval@1\")
  have hBad: x + 5n <= 2n by judge(\"interval@1\")
  show self.v <= 10n by frame
"

#guard (elaborateObendSource falseMixedContractSrc "BadMixedMod").isOk == false
#guard
  (match parseAndCheckObendModule falseMixedContractSrc "BadMixedMod" [] with
   | .ok (_, dm) => (elaborateContractsWithCerts defaultAutoCertAdmitsTag dm).isOk == false
   | .error _ => false) == true

/-- Fail-closed negative test 4: a `contract` citing an unregistered judge (`"nonexistent@99"`)
    is refused by `FrontEnd.elaborateContractsWithCerts`. -/
def unregisteredJudgeContractSrc : String :=
"edition ObjectiveBend 1
record Box:
  v: Nat
def idBox(b: Box) -> Box:
  b
contract Unreg for Box by frame:
  invariant: self.v <= 10n
  law: monotone(v)
  have hUnreg: 1n == 1n by judge(\"nonexistent@99\")
  show self.v <= 10n by frame
"

#guard
  (match parseAndCheckObendModule unregisteredJudgeContractSrc "UnregMod" [] with
   | .ok (_, dm) => (elaborateContractsWithCerts defaultAutoCertAdmitsTag dm).isOk == false
   | .error _ => false) == true

/-! ## 7. `#check_docs_census`, `#tooth` Mutation Tests & Compile-Time `0 sorryAx` Audit -/

#check_docs_census

#tooth checkIntervalAutoCert_sound by
  mutation Obend.Elab.AutoCert.checkIntervalAutoCert := fun _ _ => Verdict.ok

#tooth checkTaylorModelJudge_sound by
  mutation Obend.Elab.AutoCert.checkTaylorModelJudge := fun _ _ _ => Verdict.ok

#tooth checkGroebnerJudge_sound by
  mutation Obend.Elab.AutoCert.checkGroebnerJudge := fun _ _ _ => Verdict.ok

#tooth synthesizeClaimExternalJudge_sound by
  mutation Obend.Elab.AutoCert.synthesizeClaimJudgeTag :=
    fun _ _ _ _ _ _ tag => some (Justification.byExternalJudge tag ByteArray.empty)

#tooth rtl_synth_wire_roundtrips by
  mutation Obend.Hardware.Judge.encodeRtlSynthObj := fun _ => "{}"

open Lean Elab Command in
elab "#verify_autocert_axioms" : command => do
  let targets : List Name := [
    ``Obend.Hardware.Judge.decodeRtlSynthObj_encodeRtlSynthObj_roundtrip,
    ``Obend.Hardware.Judge.decodeRtlSynthCert_encodeRtlSynthCert_roundtrip,
    ``Obend.Hardware.Judge.rtlSynthFormat_sound,
    ``Obend.Elab.AutoCert.checkIntervalAutoCert_sound,
    ``Obend.Elab.AutoCert.checkTaylorModelJudge_sound,
    ``Obend.Elab.AutoCert.checkGroebnerJudge_sound,
    ``Obend.Elab.AutoCert.synthesizeClaimExternalJudge_sound,
    ``Obend.Stdlib.stdlib_all_accepted,
    ``Obend.Stdlib.stdlib_all_claims_hold,
    ``Obend.Stdlib.stdlib_quantum_photonic_accepted_and_claims_hold,
    ``interval_bisect_synthesizes_and_checks,
    ``interval_bisect_semantic_sound,
    ``interval_negative_refusals,
    ``taylor_model_synthesizes_and_checks,
    ``taylor_model_semantic_sound,
    ``taylor_model_negative_refusals,
    ``sos_lyapunov_synthesizes_and_checks,
    ``sos_lyapunov_ast_and_negative_refusals,
    ``groebner_direct_division_insufficient,
    ``groebner_buchberger_synthesizes_and_checks,
    ``groebner_buchberger_semantic_sound,
    ``groebner_psatz_nonneg_synthesizes_and_sound,
    ``groebner_negative_and_positive_ast,
    ``rtl_synth_wire_roundtrips,
    ``rtl_synth_from_stdlib_book_checks,
    ``rtl_synth_negative_refusals,
    ``autoCertSuite_accepted_and_obligations_verified,
    ``autoCertSuite_all_5_external_judges_hold,
    ``autoCertSuite_wave4_primitives_elaborated
  ]
  let allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for t in targets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    for a in axs do
      if !allowedStandard.contains a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on non-standard axiom {a}"
  logInfo m!"[PASS] AutoCert axiom audit verified: {targets.length} theorems & obligations have 0 sorryAx and only standard Lean kernel axioms"

#verify_autocert_axioms
