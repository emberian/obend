module
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
public import Obend.Analysis.RealAnalysis
public import Obend.Judge.Class
public import Obend.Logic.Obligation
public import Obend.Elab.AutoCert
public import Obend.Elab.Workbook
public import Obend.Tactic.DocsCensus
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import Lean
meta import Obend.Elab.AutoCert
meta import Obend.Elab.Workbook
meta import Obend.Hardware.Judge
meta import Obend.Analysis.SosLyapunov
meta import Obend.Spec.FrontEnd
meta import Obend.Tactic.DocsCensus
meta import Obend.Tactic.Tooth
meta import Obend.AssertAxioms
import all Obend.Judge.Class
import all Obend.Logic.Obligation
import all Obend.Hardware.Judge
import all Obend.Analysis.SosLyapunov
import all Obend.Elab.AutoCert

open Obend.Core.Term (Primitive Term)
open Obend.Judge (Verdict Format IntervalQuery)
open Obend.Judge.SOS (Poly)
open Obend.Analysis
  (CanonicalRat polyVarPow polyConst SosLyapunovProblem SosLyapunovCert
   goldenSosProblem goldenSosCert badSosCert checkSosLyapunovProblem
   renderSosLyapunovProblemJson renderSosLyapunovCertJson
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

set_option autoImplicit false
set_option maxHeartbeats 800000

#import_obend "stdlib/core/Cell.obend" as StdlibCell

/-! ## 1. Judge 1: `"interval@1"` (Adaptive Bisection, Wire Roundtrip, Soundness & Refusals) -/

/-- Naive depth-0 interval evaluation fails on `goldenBisectIntervalObj` (`x - x ∈ [-1/4, 1/4]`
    over `x ∈ [0, 1]`) because `[0, 1] - [0, 1] = [-1, 1]` exceeds `[-1/4, 1/4]`. -/
example :
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

/-- `taylorModelJudge` establishes mathematical `TaylorModelMeaning` (polynomial + remainder range
    enclosure without restating `verifyTaylorModelCert`) and certifies genuine `refuted` witnesses. -/
theorem taylor_model_judge_meaning_and_refusal :
    TaylorModelMeaning goldenTaylorModelQuery synthesizedTaylorCert ∧
    ¬ TaylorModelMeaning badTaylorModelQuery badTaylorModelCert :=
  ⟨taylorModelJudge.sound (r := 0) taylor_model_synthesizes_and_checks.2.1,
   fun h => taylorModelJudge.refuted (r := 0) (o := badTaylorModelQuery) (c := badTaylorModelCert)
     badTaylorModelCert_refused rfl badTaylorModelCert h⟩

/-- Negative refusal tests for `"taylor-model@1"`: `badTaylorModelCert`, empty JSON `"{}"`,
    `cos(x) + 5n <= 2n`, `sin(x) <= 0n` (since `sin(0.1) > 0` on `[-1/10, 1/10]`), and the
    composite domain-confusion attack `0 - sin(1) ∈ [-0.01, 0.01]` on `domain = [0, 0]` all fail closed. -/
theorem taylor_model_negative_refusals :
    checkTaylorModelJudge 0 goldenTaylorModelQuery badTaylorModelCert ≠ Verdict.ok ∧
    (taylorModelFormat.checkBytes 0 "{}" "{}").isOk = false ∧
    synthesizeJudgeWirePair "taylor-model@1" "Mod"
      (some (.binary "<=" (.binary "+" (.call (.var "cos") [.var "x"]) (.nat "5")) (.nat "2"))) none = none ∧
    synthesizeJudgeWirePair "taylor-model@1" "Mod"
      (some (.binary "<=" (.call (.var "sin") [.var "x"]) (.nat "0"))) none = none ∧
    synthesizeTaylorModelCert
      { expr := .sub (.const 0) (.sin (.const 1))
      , domain := ⟨0, 0⟩
      , center := 0
      , degree := 4
      , claimedBound := ⟨CanonicalRat.mk (-1) 100, CanonicalRat.mk 1 100⟩ } = none ∧
    (synthesizeTaylorModelCert
      { expr := .sub (.const 0) (.sin (.const 1))
      , domain := ⟨0, 0⟩
      , center := 0
      , degree := 4
      , claimedBound := ⟨-1, CanonicalRat.mk (-4) 5⟩ }).isSome = true :=
  ⟨verdict_ne_ok_of_isOk_false (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   by decide +kernel⟩

/-! ## 3. Judge 3: `"sos-lyapunov-cbf@1"` (SOS Gram / Lyapunov / CBF / DAE Synthesis & JSON Codec) -/

theorem sos_lyapunov_synthesizes_and_checks :
    synthesizeSosLyapunovCert goldenSosProblem = some goldenSosCert ∧
    checkSosLyapunovProblem 0 goldenSosProblem goldenSosCert = Verdict.ok ∧
    encodeSosLyapunovProblem goldenSosProblem = renderSosLyapunovProblemJson goldenSosProblem ∧
    encodeSosLyapunovCert goldenSosCert = renderSosLyapunovCertJson goldenSosCert ∧
    (∀ r rawObj rawCert,
      (autoSosLyapunovFormat.checkBytes r rawObj rawCert).isOk =
        (sosLyapunovFormat.checkBytes r rawObj rawCert).isOk) :=
  ⟨by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel),
   rfl,
   rfl,
   fun _ _ _ => rfl⟩

/-- Exercise the full general AST JSON wire encoder/decoder path (`renderSosLyapunovProblemJson` /
    `renderSosLyapunovCertJson`) through `decodeSosLyapunovProblem`, `decodeSosLyapunovCert`,
    `autoDecodeSosLyapunovProblem`, `autoDecodeSosLyapunovCert`, and `checkSosLyapunovProblem`. -/
private def checkStructuredSosJsonRoundtrip : Bool :=
  let probJson := renderSosLyapunovProblemJson goldenSosProblem
  let certJson := renderSosLyapunovCertJson goldenSosCert
  let autoProbJson := encodeSosLyapunovProblemJson goldenSosProblem
  let autoCertJson := encodeSosLyapunovCertJson goldenSosCert
  let verdictOk :=
    match checkSosLyapunovProblem 0 goldenSosProblem goldenSosCert with
    | .ok => true
    | _ => false
  (decodeSosLyapunovProblem probJson == .ok goldenSosProblem) &&
  (decodeSosLyapunovCert certJson == .ok goldenSosCert) &&
  (autoDecodeSosLyapunovProblem autoProbJson == .ok goldenSosProblem) &&
  (autoDecodeSosLyapunovCert autoCertJson == .ok goldenSosCert) &&
  verdictOk

#guard checkStructuredSosJsonRoundtrip == true

/-- Custom non-golden `SosLyapunovProblem` with negative and non-integer rational coefficients
    (`-3/2`, `-5/4`, `1/3`, `1/7`) and multi-variable monomials (`x0 * x1`), verifying lossless JSON
    roundtrip (`P0 #23`: zero `c.num.toNat` truncation, zero `goldenLyapunovSpec2D` injection)
    and fail-closed refusal of removed preset wire strings (`"golden-cubic-cbf-dae"`, `"valid-sos-cert"`,
    `"bad-sos-cert"`). -/
def customNonGoldenSosProblem : SosLyapunovProblem :=
  { goldenSosProblem with
    lyapunov :=
      { goldenSosProblem.lyapunov with
        vectorField :=
          [ Poly.scale (CanonicalRat.mk (-3) 2) (polyVarPow 0 1)
          , Poly.scale (CanonicalRat.mk (-5) 4) (polyVarPow 1 1) ]
        lyapunovV :=
          Poly.add
            (Poly.scale (CanonicalRat.mk 1 3) (Poly.sqr (polyVarPow 0 1)))
            (Poly.mul (polyVarPow 0 1) (polyVarPow 1 1))
        radialEps := CanonicalRat.mk 1 7 } }

def checkCustomNonGoldenSosRoundtrip : Bool :=
  let wire := encodeSosLyapunovProblem customNonGoldenSosProblem
  (decodeSosLyapunovProblem wire == .ok customNonGoldenSosProblem) &&
  (autoDecodeSosLyapunovProblem wire == .ok customNonGoldenSosProblem)

#guard checkCustomNonGoldenSosRoundtrip == true

theorem sos_lyapunov_lossless_and_no_presets :
    customNonGoldenSosProblem.lyapunov ≠ goldenSosProblem.lyapunov ∧
    encodeSosLyapunovProblem customNonGoldenSosProblem =
      renderSosLyapunovProblemJson customNonGoldenSosProblem ∧
    (autoDecodeSosLyapunovProblem "golden-cubic-cbf-dae").isOk = false ∧
    (autoDecodeSosLyapunovCert "valid-sos-cert").isOk = false ∧
    (autoDecodeSosLyapunovCert "bad-sos-cert").isOk = false ∧
    (autoSosLyapunovFormat.checkBytes 0 "golden-cubic-cbf-dae" "valid-sos-cert").isOk = false :=
  ⟨by decide +kernel,
   rfl,
   by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   by decide +kernel⟩

/-- `"sos-lyapunov-cbf@1"` has no claim or step surface (2026-11-04): nothing in a `.obend` claim states a
    Lyapunov/CBF/DAE problem, so every syntax extraction fails closed; polynomial inequalities go to
    `groebner@1`. The wire format itself still checks (`sos_lyapunov_synthesizes_and_checks`). -/
theorem sos_lyapunov_ast_and_negative_refusals :
    synthesizeJudgeWirePair "sos-lyapunov-cbf@1" "Mod"
      (some (.binary "<=" (.nat "0")
        (.binary "+" (.binary "*" (.var "x") (.var "x")) (.binary "*" (.var "y") (.var "y"))))) none = none ∧
    synthesizeJudgeWirePair "sos-lyapunov-cbf@1" "Mod"
      (some (.binary "<=" (.nat "0")
        (.binary "*" (.binary "+" (.var "x") (.var "y")) (.binary "+" (.var "x") (.var "y"))))) none = none ∧
    synthesizeJudgeWirePair "sos-lyapunov-cbf@1" "Mod"
      (some (.binary "<=" (.nat "0") (.var "x"))) none = none ∧
    synthesizeJudgeWirePair "sos-lyapunov-cbf@1" "Mod"
      (some (.binary "<=" (.binary "+" (.var "x") (.nat "5")) (.nat "2"))) none = none ∧
    (sosLyapunovFormat.checkBytes 0 "{}" "{}").isOk = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 4. Judge 4: `"groebner@1"` (Buchberger S-Polynomial Completion, Positivstellensatz & Soundness) -/

/-- Without Buchberger S-polynomial completion, direct division of `x1 - x0^2` by `[x1^2 - x0, x0*x1 - 1]`
    cannot eliminate `x1 - x0^2` (remainder is non-zero). -/
theorem groebner_direct_division_insufficient :
    (polyDivModWithQuotients 16 goldenGroebnerQuery.target goldenGroebnerQuery.eqGens).1.isZero = false := by
  decide +kernel

def synthesizedGroebnerCert : GroebnerCert :=
  (synthesizeGroebnerCert goldenGroebnerQuery).getD badGroebnerCert

/-- With `completeGroebnerBasisWithCofactors` cofactor tracking, `synthesizeGroebnerCert` discovers
    the S-polynomial consequence and synthesizes an ideal-membership witness directly over `q.eqGens`! -/
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

/-- Semantic root soundness over `goldenGroebnerQuery.eqGens`: at every common root `ρ` of
    `eqGens = [x1^2 - x0, x0*x1 - 1]`, `target = x1 - x0^2` evaluates to `0`! -/
theorem groebner_buchberger_semantic_sound :
    verifyGroebnerCert goldenGroebnerQuery synthesizedGroebnerCert = true ∧
    (∀ (ρ : Nat → CanonicalRat),
      (∀ g ∈ goldenGroebnerQuery.eqGens, g.eval ρ = 0) →
      goldenGroebnerQuery.target.eval ρ = 0) :=
  checkGroebnerJudge_sound_membership 0 goldenGroebnerQuery synthesizedGroebnerCert rfl
    groebner_buchberger_synthesizes_and_checks.2.1

/-- Positivstellensatz non-negativity query (`isNonneg = true`) on `(x0 + x1)^2 + (x2 - 1) >= 0`
    modulo `x2 - 1 = 0` (exercising both non-empty ideal quotient reduction AND cross-term Lagrange SOS!). -/
def samplePsatzGroebnerQuery : GroebnerQuery where
  target   := Poly.add (Poly.sqr (Poly.add (polyVarPow 0 1) (polyVarPow 1 1)))
                       (Poly.sub (polyVarPow 2 1) (polyConst 1))
  eqGens   := [Poly.sub (polyVarPow 2 1) (polyConst 1)]
  ineqGens := []
  isNonneg := true
  divFuel  := 16

def synthesizedPsatzGroebnerCert : GroebnerCert :=
  (synthesizeGroebnerCert samplePsatzGroebnerQuery).getD badGroebnerCert

theorem groebner_psatz_nonneg_checks :
    synthesizeGroebnerCert samplePsatzGroebnerQuery = some synthesizedPsatzGroebnerCert ∧
    verifyGroebnerCert samplePsatzGroebnerQuery synthesizedPsatzGroebnerCert = true :=
  have hOk : checkGroebnerJudge 0 samplePsatzGroebnerQuery synthesizedPsatzGroebnerCert = Verdict.ok :=
    verdict_eq_ok_of_isOk (by decide +kernel)
  ⟨by decide +kernel,
   (checkGroebnerJudge_sound 0 samplePsatzGroebnerQuery synthesizedPsatzGroebnerCert hOk).1⟩

/-- `groebnerJudge` establishes mathematical `GroebnerQuery.SemanticMeaning` and certifies genuine
    counterexample `refuted` witnesses (`1 ∉ ⟨x0⟩`), while receiver-qualified `.member` extraction
    refuses `a.val == b.val` (`P0 #8`) and certifies `a.val == a.val`. -/
theorem groebner_judge_meaning_and_refusal :
    goldenGroebnerQuery.SemanticMeaning ∧
    ¬ forgedUnitBasisQuery.SemanticMeaning ∧
    (synthesizeJudgeWirePair "groebner@1" "Mod"
      (some (.binary "==" (.member (.var "a") "val") (.member (.var "b") "val"))) none).isNone = true ∧
    (synthesizeJudgeWirePair "groebner@1" "Mod"
      (some (.binary "==" (.member (.var "a") "val") (.member (.var "a") "val"))) none).isSome = true :=
  ⟨groebnerJudge.sound (r := 0) groebner_buchberger_synthesizes_and_checks.2.1,
   fun h => groebnerJudge.refuted (r := 0) (o := forgedUnitBasisQuery) (c := badGroebnerCert)
     badGroebnerCert_refused rfl badGroebnerCert h,
   by decide +kernel,
   by decide +kernel⟩

/-- Negative refusal tests for `"groebner@1"`: `badGroebnerCert`, forged unit basis `[Poly.one]`
    claiming `1 ∈ ⟨x0⟩`, empty JSON `"{}"`, and false polynomial identity `(x + 1n) * (x + 1n) == x * x + 1n`
    all fail closed, while true identity `(x + 1n) * (x + 1n) == x * x + 2n * x + 1n` succeeds. -/
theorem groebner_negative_and_positive_ast :
    checkGroebnerJudge 0 goldenGroebnerQuery badGroebnerCert ≠ Verdict.ok ∧
    checkGroebnerJudge 0
      { target := Poly.one, eqGens := [polyVarPow 0 1], ineqGens := [], isNonneg := false, divFuel := 16 }
      (.membership [Poly.one] { quotients := [(Poly.one, 0)] }) ≠ Verdict.ok ∧
    (groebnerFormat.checkBytes 0 "{}" "{}").isOk = false :=
  ⟨verdict_ne_ok_of_isOk_false (by decide +kernel),
   verdict_ne_ok_of_isOk_false (by decide +kernel),
   by decide +kernel⟩

/-! The wire-pair synthesizer emits JSON, which the kernel does not evaluate, so these two are
    evaluated rather than decided: the false identity `(x + 1n) * (x + 1n) == x * x + 1n` is refused
    and the true identity `(x + 1n) * (x + 1n) == x * x + 2n * x + 1n` is certified. -/
#eval (do
  let falseId : Option Obend.Spec.Syntax.Expr := some (.binary "=="
    (.binary "*" (.binary "+" (.var "x") (.nat "1")) (.binary "+" (.var "x") (.nat "1")))
    (.binary "+" (.binary "*" (.var "x") (.var "x")) (.nat "1")))
  let trueId : Option Obend.Spec.Syntax.Expr := some (.binary "=="
    (.binary "*" (.binary "+" (.var "x") (.nat "1")) (.binary "+" (.var "x") (.nat "1")))
    (.binary "+" (.binary "+" (.binary "*" (.var "x") (.var "x"))
      (.binary "*" (.nat "2") (.var "x"))) (.nat "1")))
  unless (synthesizeJudgeWirePair "groebner@1" "Mod" falseId none).isNone do
    throw (IO.userError "groebner@1 wire pair: the false identity (x+1)^2 == x^2+1 was certified")
  unless (synthesizeJudgeWirePair "groebner@1" "Mod" trueId none).isSome do
    throw (IO.userError "groebner@1 wire pair: the identity (x+1)^2 == x^2+2x+1 was refused")
  : IO Unit)

/-! ## 5. Judge 5: `"rtl-synth@1"` & `"hw-rtl-synth@1"` (Wire Roundtrips, Real `Leaf.Book` & Refusals) -/

theorem rtl_synth_wire_roundtrips :
    decodeRtlSynthObj (encodeRtlSynthObj "test_rtl_synth") = Except.ok "test_rtl_synth" ∧
    decodeRtlSynthCert (encodeRtlSynthCert goldenFlatRtlModule) = Except.ok goldenFlatRtlModule :=
  ⟨decodeRtlSynthObj_encodeRtlSynthObj_roundtrip.1,
   decodeRtlSynthCert_encodeRtlSynthCert_roundtrip.1⟩

/-- Closed 1-slot `Leaf.Book` (`out := x * 2 + 1`) for fast kernel `decide +kernel` synthesis proof,
    plus VM `#guard` check on the 4-slot open-recursive `StdlibCell.versionedCell_book`. -/
def sampleAffineBook : Obend.Leaf.Book :=
  ⟨[.slot { member := "affine2"
          , slot   := 0
          , kind   := .method
          , code   := .lam (.lam (.binary .add (.binary .multiply (.bound 0) (.nat 2)) (.nat 1)))
          , reads  := [] }]⟩

def synthesizedAffineRtl : RtlModule :=
  (synthesizeRtlSynthCert "affine2_rtl" (some sampleAffineBook)).getD badLoopRtlModule

/-- Synthesize a real `RtlModule` from `sampleAffineBook` and verify wire acceptance under
    BOTH `"rtl-synth@1"` and `"hw-rtl-synth@1"`, plus verify `StdlibCell.versionedCell_book`. -/
theorem rtl_synth_from_stdlib_book_checks :
    synthesizeRtlSynthCert "affine2_rtl" (some sampleAffineBook) =
      some synthesizedAffineRtl ∧
    rtlSynthFormat.checkBytes 0
      (encodeRtlSynthObj "affine2_rtl") (encodeRtlSynthCert synthesizedAffineRtl) = Verdict.ok ∧
    hwSynthFormat.checkBytes 0
      (encodeRtlSynthObj "affine2_rtl") (encodeRtlSynthCert synthesizedAffineRtl) = Verdict.ok :=
  ⟨by decide +kernel,
   verdict_eq_ok_of_isOk (by decide +kernel),
   verdict_eq_ok_of_isOk (by decide +kernel)⟩

#guard
  (match synthesizeRtlSynthCert "versioned_cell_rtl" (some StdlibCell.versionedCell_book) with
   | some rtlMod =>
     (rtlSynthFormat.checkBytes 0 (encodeRtlSynthObj "versioned_cell_rtl") (encodeRtlSynthCert rtlMod)).isOk &&
     (hwSynthFormat.checkBytes 0 (encodeRtlSynthObj "versioned_cell_rtl") (encodeRtlSynthCert rtlMod)).isOk
   | none => false) == true

/-- Closed 1-slot `Leaf.Book` with saturating subtraction (`x - 3`, which lowers to `RtlExpr.mux`
    in `compilePrimSat`) verifying exact 6-wire branchless ALU mux normalization. -/
def sampleSatSubBook : Obend.Leaf.Book :=
  ⟨[.slot { member := "satSub3"
          , slot   := 0
          , kind   := .method
          , code   := .lam (.lam (.binary .subtract (.bound 0) (.nat 3)))
          , reads  := [] }]⟩

#guard
  (match synthesizeRtlSynthCert "satSub3_rtl" (some sampleSatSubBook) with
   | some rtlMod =>
     (rtlSynthFormat.checkBytes 0 (encodeRtlSynthObj "satSub3_rtl") (encodeRtlSynthCert rtlMod)).isOk &&
     (hwSynthFormat.checkBytes 0 (encodeRtlSynthObj "satSub3_rtl") (encodeRtlSynthCert rtlMod)).isOk
   | none => false) == true

def unsynthesizableEffectBook : Obend.Leaf.Book :=
  ⟨[.slot { member := "io_eff", slot := 0, kind := .method, code := .lam (.perform (.label "io")), reads := [] }]⟩

/-- Negative refusal tests for `"rtl-synth@1"` / `"hw-rtl-synth@1"`:
    empty `Leaf.Book` (`⟨[]⟩`) and effectful `unsynthesizableEffectBook` return `none`,
    combinational-loop `badLoopRtlModule` is refused, and empty JSON `"{}"` is refused. -/
theorem rtl_synth_negative_refusals :
    synthesizeRtlSynthCert "empty_book_mod" (some ⟨[]⟩) = none ∧
    synthesizeRtlSynthCert "eff_book_mod" (some unsynthesizableEffectBook) = none ∧
    checkRtlSynth 0 "bad_loop_mod" badLoopRtlModule ≠ Verdict.ok ∧
    (rtlSynthFormat.checkBytes 0 "{}" "{}").isOk = false ∧
    (hwSynthFormat.checkBytes 0 "{}" "{}").isOk = false :=
  ⟨by decide +kernel,
   by decide +kernel,
   verdict_ne_ok_of_isOk_false (by decide +kernel),
   by decide +kernel,
   by decide +kernel⟩

/-! ## 6. End-to-End `#obend_decl` (`Workbook`), `FrontEnd` Contracts & All 8 New `Primitive` Ops -/

#obend_decl AutoCertSuite "
record FocState:
  step() -> Nat
  aluMix(a: Nat, b: Nat) -> Nat

spec FocSpec for FocState:
  def step() -> Nat:
    7n
  def aluMix(a: Nat, b: Nat) -> Nat:
    ((a & 0xFFn) | (b ^ 0x0Fn)) + (a << 2n) + (b >>> 1n) + (a >> 1n) + qmul32(a, b)
  claim bisected_bound(x: Nat) given x <= 1n by judge(\"interval@1\"): 4n * x <= 4n * x + 1n
  claim given_box_bound(x: Nat) given x <= 10n by judge(\"interval@1\"): x * x <= 100n
  claim large_margin_bound(x: Nat) given x <= 1400n by judge(\"interval@1\"): 120n + x * 400n <= 600000n
  claim lyapunov_sos(x: Nat, y: Nat) by judge(\"groebner@1\"): 0n <= x * x + y * y
  claim cross_term_sos(x: Nat, y: Nat) by judge(\"groebner@1\"): 0n <= (x + y) * (x + y)
  claim poly_ring_id(x: Nat, y: Nat) by judge(\"groebner@1\"): (x + y) * (x + y) == x * x + 2n * x * y + y * y
  claim buchberger_given(x: Nat, y: Nat) given y * y == x && x * y == 1n by judge(\"groebner@1\"): y == x * x

def seedFoc() -> FocState:
  {step: 0n, aluMix: fn(a: Nat, b: Nat) -> Nat: a + b}

def focCore() -> FocState:
  fix(FocSpec, seedFoc())

def checkSignedLt(a: Nat, b: Nat) -> Bool:
  a <s b

def checkWave4SurfaceOps(a: Nat, b: Nat) -> Bool:
  (~a + q32ToInt(q32FromInt(b))) <=s a

contract FocContract for FocState by frame:
  invariant: self.step <= 10n
  law: monotone(step)
  have hIv: 4n * 2n <= 9n by judge(\"interval@1\")
  have hSos: 0n <= (x + y) * (x + y) by judge(\"groebner@1\")
  have hGb: (x + 1n) * (x + 1n) == x * x + 2n * x + 1n by judge(\"groebner@1\")
  have hRtl: true by judge(\"rtl-synth@1\")
  show self.step <= 10n by frame
"

/-- `#obend_decl AutoCertSuite` passed `FrontEnd.accept` and `verifyWorkbookObligationsWithLean`
    verified its seven external-judge claims (`interval@1` over `given` boxes, `groebner@1` for the
    two sums of squares, the ring identity and the Buchberger claim under `given` equations). -/
theorem autoCertSuite_obligations_pass :
    verifyWorkbookObligationsWithLean AutoCertSuite.package = true := by
  decide +kernel

/-- All emitted `*_holds` theorems from `#obend_decl AutoCertSuite` establish kernel-verified
    `obligationMeaningWithJudges workbookFormats`, which since 2026-11-04 includes the format's claim
    binding (`externalClaimBound`): each judged object is the one re-derived from the claim's Core4 body. -/
theorem autoCertSuite_all_external_judges_hold :
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_bisected_bound_obj
      AutoCertSuite.claim_bisected_bound_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_given_box_bound_obj
      AutoCertSuite.claim_given_box_bound_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_large_margin_bound_obj
      AutoCertSuite.claim_large_margin_bound_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_lyapunov_sos_obj
      AutoCertSuite.claim_lyapunov_sos_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_cross_term_sos_obj
      AutoCertSuite.claim_cross_term_sos_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_poly_ring_id_obj
      AutoCertSuite.claim_poly_ring_id_just ∧
    obligationMeaningWithJudges workbookFormats
      AutoCertSuite.claim_buchberger_given_obj
      AutoCertSuite.claim_buchberger_given_just :=
  ⟨AutoCertSuite.claim_bisected_bound_holds,
   AutoCertSuite.claim_given_box_bound_holds,
   AutoCertSuite.claim_large_margin_bound_holds,
   AutoCertSuite.claim_lyapunov_sos_holds,
   AutoCertSuite.claim_cross_term_sos_holds,
   AutoCertSuite.claim_poly_ring_id_holds,
   AutoCertSuite.claim_buchberger_given_holds⟩

/-- Verify that all 8 Wave-4 bitwise/shift/signed/fixed-point `Primitive` constructors
    (`.bitAnd`, `.bitOr`, `.bitXor`, `.shl`, `.lshr`, `.ashr`, `.slt`, `.qmul32`) elaborated cleanly
    through `toExprPrimitive` / `metaToExprPrimitive` inside `#obend_decl AutoCertSuite`. -/
theorem autoCertSuite_wave4_primitives_elaborated :
    AutoCertSuite.checkSignedLt_term =
      .lam (.lam (.binary .slt (.bound 1) (.bound 0))) := rfl

/-- End-to-end `FrontEnd.elaborateContractsWithAutoCerts` positive test: synthesizes 4 verified
    `(tag, objWire, certWire)` witnesses for `FocContract` (a closed interval step, two Gröbner steps,
    and an `rtl-synth@1` step whose proposition is `true`), AND refuses when passed an
    unsynthesizable `Leaf.Book` (`unsynthesizableEffectBook`). -/
def checkFrontEndContractAutoCerts : Bool :=
  match parseAndCheckObendModule AutoCertSuite.package.source "AutoCertSuite" [] with
  | .error _ => false
  | .ok (_, decodedMod) =>
    let badBookRefused :=
      !(elaborateContractsWithAutoCerts defaultAutoCertAdmitsTag decodedMod (some unsynthesizableEffectBook)).isOk
    match elaborateContractsWithAutoCerts defaultAutoCertAdmitsTag decodedMod (some AutoCertSuite.focCore_book) with
    | .error _ => false
    | .ok (contracts, certs, bundles) =>
      badBookRefused &&
      contracts.length == 1 &&
      certs.length == 1 &&
      match bundles with
      | [("FocContract", ws)] =>
        ws.length == 4 &&
        ws.any (fun (t, _, _) => t == "interval@1") &&
        ws.any (fun (t, _, _) => t == "groebner@1") &&
        ws.any (fun (t, _, _) => t == "rtl-synth@1")
      | _ => false

#guard checkFrontEndContractAutoCerts == true

/-- Fail-closed negative test 1: a false `by judge("interval@1")` claim (`x + 5n <= 2n`) AND a
    false `given`-widened claim (`given x <= 100n: x <= 5n`, which holds on `[0, 1]` but FAILS on `[0, 100]`)
    are both NOT auto-verified (`autoVerified == false`). -/
def falseIntervalClaimSrc : String :=
"edition ObjectiveBend 1
record Box:
  v() -> Nat
spec S for Box:
  def v() -> Nat:
    1n
  claim bad_bound(x: Nat) by judge(\"interval@1\"): x + 5n <= 2n
  claim bad_given_bound(x: Nat) given x <= 100n by judge(\"interval@1\"): x <= 5n
def mkBox() -> Box:
  fix(S, {v: 0n})
"

#guard
  (match elaborateObendSource falseIntervalClaimSrc "FalseIvMod" with
   | .ok pkg =>
     match pkg.findClaim? "bad_bound", pkg.findClaim? "bad_given_bound" with
     | some wc1, some wc2 =>
       wc1.autoVerified == false && wc1.autoJustification?.isNone &&
       wc2.autoVerified == false && wc2.autoJustification?.isNone
     | _, _ => false
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

/-- Fail-closed negative test 5 (`P0 #8`): distinct member receivers `a.val == b.val` inside a
    `contract` Isar step never collapse to `"val" - "val" = 0` and are strictly refused by both
    `Workbook.elaborateObendSource` AND `FrontEnd.elaborateContractsWithCerts`! -/
def falseDistinctMemberContractSrc : String :=
"edition ObjectiveBend 1
record Box:
  val: Nat
def idBox(b: Box) -> Box:
  b
contract BadReceiverCollapse for Box by frame:
  invariant: self.val <= 10n
  law: monotone(val)
  have hCollapse: a.val == b.val by judge(\"groebner@1\")
  show self.val <= 10n by frame
"

#guard (elaborateObendSource falseDistinctMemberContractSrc "BadRecvMod").isOk == false
#guard
  (match parseAndCheckObendModule falseDistinctMemberContractSrc "BadRecvMod" [] with
   | .ok (_, dm) => (elaborateContractsWithCerts defaultAutoCertAdmitsTag dm).isOk == false
   | .error _ => false) == true

/-! ## 7. `#check_docs_census`, `#tooth` Mutation Tests & Compile-Time `0 sorryAx` Audit -/

#check_docs_census

#tooth checkIntervalAutoCert_sound by
  mutation Obend.Elab.AutoCert.checkIntervalAutoCert := fun _ _ => Verdict.ok

#tooth checkTaylorModelJudge_sound by
  mutation Obend.Elab.AutoCert.checkTaylorModelJudge := fun _ _ _ => Verdict.ok

#tooth checkTaylorModelJudge_refuted by
  mutation Obend.Elab.AutoCert.checkTaylorModelJudge := fun _ _ _ => Verdict.refused "forged" []

#tooth checkGroebnerJudge_sound by
  mutation Obend.Elab.AutoCert.checkGroebnerJudge := fun _ _ _ => Verdict.ok

#tooth checkGroebnerJudge_refuted by
  mutation Obend.Elab.AutoCert.checkGroebnerJudge := fun _ _ _ => Verdict.refused "forged" []

#tooth distinct_member_receivers_refused by
  mutation Obend.Elab.AutoCert.syntaxVarName? :=
    fun
      | .var v => some v
      | .member _ f => some f
      | _ => none

#tooth synthesizeClaimExternalJudge_sound by
  mutation Obend.Elab.AutoCert.synthesizeClaimJudgeTag :=
    fun _ _ _ _ _ _ tag => some (Justification.byExternalJudge tag ByteArray.empty)

#tooth Obend.Hardware.Judge.rtlSynthFormat_sound by
  mutation Obend.Hardware.Judge.checkRtlSynth := fun _ _ _ => Verdict.ok

open Lean Elab Command in
run_cmd do
  let targets : List Name := [
    ``Obend.Hardware.Judge.decodeRtlSynthObj_encodeRtlSynthObj_roundtrip,
    ``Obend.Hardware.Judge.decodeRtlSynthCert_encodeRtlSynthCert_roundtrip,
    ``Obend.Hardware.Judge.rtlSynthFormat_sound,
    ``Obend.Elab.AutoCert.checkIntervalAutoCert_sound,
    ``Obend.Elab.AutoCert.checkTaylorModelJudge_sound,
    ``Obend.Elab.AutoCert.checkTaylorModelJudge_refuted,
    ``Obend.Elab.AutoCert.checkGroebnerJudge_sound,
    ``Obend.Elab.AutoCert.checkGroebnerJudge_refuted,
    ``Obend.Elab.AutoCert.distinct_member_receivers_refused,
    ``Obend.Elab.AutoCert.synthesizeClaimExternalJudge_sound,
    ``StdlibCell.claim_next_value_open_recursion_holds,
    ``interval_bisect_synthesizes_and_checks,
    ``interval_bisect_semantic_sound,
    ``interval_negative_refusals,
    ``taylor_model_synthesizes_and_checks,
    ``taylor_model_semantic_sound,
    ``taylor_model_judge_meaning_and_refusal,
    ``taylor_model_negative_refusals,
    ``sos_lyapunov_synthesizes_and_checks,
    ``sos_lyapunov_lossless_and_no_presets,
    ``sos_lyapunov_ast_and_negative_refusals,
    ``groebner_direct_division_insufficient,
    ``groebner_buchberger_synthesizes_and_checks,
    ``groebner_buchberger_semantic_sound,
    ``groebner_psatz_nonneg_checks,
    ``groebner_judge_meaning_and_refusal,
    ``groebner_negative_and_positive_ast,
    ``rtl_synth_wire_roundtrips,
    ``rtl_synth_from_stdlib_book_checks,
    ``rtl_synth_negative_refusals,
    ``autoCertSuite_obligations_pass,
    ``autoCertSuite_all_external_judges_hold,
    ``autoCertSuite_wave4_primitives_elaborated
  ]
  let allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  -- The compiled trust (`native_decide`'s `…._native…` axioms) is the repo's counted exception
  -- (`Obend.AssertAxioms`, ember 2026-11-02: compiled trust is not a concern now): the importer
  -- proves each imported claim's `_check` by `native_decide` and re-runs it by `#assert_compiled`
  -- (`Obend.Elab.Workbook`, 2026-11-04). It is reported by name here, never passed silently.
  let mut trusted : Array Name := #[]
  for t in targets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    for a in axs do
      if Obend.AssertAxioms.isCompilerTrust a then
        unless trusted.contains t do trusted := trusted.push t
      else if !allowedStandard.contains a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on non-standard axiom {a}"
  logInfo m!"[PASS] AutoCert axiom audit verified: {targets.length} theorems & obligations have 0 sorryAx and no axiom outside the standard three and the compiled trust; resting on compiled trust (an imported claim's `_check`, re-run by `#assert_compiled`): {trusted}"
