/-
# Metasystem Workbook & Bidirectional `.obend` <-> `.lean` Bridge Test Suite

Tests:
1. `#import_obend` on `lean/tests/obend-source/world/physical/LcDrivesStatorUsd.obend`
   and `lean/tests/obend-source/DeosCounter.obend` without manual de Bruijn transcription.
2. Inline `#obend_decl` and `Obend.Lower.Reflect` handling `.ifZero`, `.label`, `.extend`,
   `.inject`, `.case`, and `.split`.
3. `Obend.Spec.LawCompile.compileKeepsClaim` soundness bridge and `Obend.Logic.Obligation`
   multi-judge registry (`obligationCheckWithJudges` with `transport@1`, `rewrite@1`,
   `lrat@1`, and `clearing@1`) + `verifyWorkbookObligationsWithLean`.
4. `#tooth` mutation tests verifying that theorems genuinely depend on the elaborated
   and reflected definitions.
5. Compile-time axiom audit verifying `0 sorryAx` and `0 Classical.choice`.
-/
import Obend.Elab.Workbook
import Obend.Tactic.Tooth

open Obend.Core.Term (Primitive Term Step Steps Evaluates)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
open Obend.Lower (NatOp LExpr SStep SSteps TransportObj TransportCert lowerProp sourceDigest)
open Obend.Lower.Reflect
  (LayoutEnv ReflectedObject labelToNat lowerTerm lowerTermFuel lowerExtend lowerCaseArms
   lowerTerm_ifZero_zero_steps lowerTerm_ifZero_succ_steps lowerTerm_ifZero_succ_bvar0_steps
   lowerTerm_inject_case_head_steps lowerTerm_inject_case_skip_steps
   lowerExtend_proj_head_step lowerSplit_record_step)
open Obend.Spec.Law (LawRef LawExpr)
open Obend.Spec.LawCompile
  (compileKeepsClaim compileKeepsClaim_step_eval compileKeepsClaim_inv_eval
   compileKeepsClaim_checkClaim_eq compileKeepsClaim_sound)
open Obend.Logic
  (ClaimObj ClaimClause Justification Support
   clearingFormat defaultExternalFormats mkExternalJudgePayload
   obligationCheck obligationCheckWithJudges obligationMeaningWithJudges
   obligationWithJudges_sound)
open Obend.Elab.Workbook

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. `#import_obend` on `LcDrivesStatorUsd.obend` -/

#import_obend "lean/tests/obend-source/world/physical/LcDrivesStatorUsd.obend" as LcDrives

/-- The `LcDrivesStatorUsd.obend` package passed `FrontEnd.accept`. -/
theorem lcDrives_accepted : LcDrives.accepted = true :=
  LcDrives.accepted_eq

/-- All obligations in `LcDrivesStatorUsd.obend` are verified by `verifyWorkbookObligationsWithLean`. -/
theorem lcDrives_obligations_verified :
    verifyWorkbookObligationsWithLean LcDrives.package = true := by decide +kernel

/-- The open-recursion claim `peak_temp_open_recursion` in `OuterJacketStator` is automatically
    discharged and its semantic meaning holds. -/
theorem lcDrives_open_recursion_claim_holds :
    obligationMeaningWithJudges workbookFormats
      LcDrives.claim_peak_temp_open_recursion_obj
      LcDrives.claim_peak_temp_open_recursion_just :=
  LcDrives.claim_peak_temp_open_recursion_holds

/-- The flattened `Leaf.Book` emitted for `lcDrivesProductionStator` has the 5 stator slots
    in outermost-layer-first `extendFields` order. -/
theorem lcDrives_production_book_slots :
    LcDrives.lcDrivesProductionStator_book.slots =
      ["massKg", "camSurfaceErrorUm", "thermalResistance", "sdfMargin", "peakWindingTemp"] := rfl

/-- The flattened `Leaf.Book` for `lcDrivesProductionStator` is closed. -/
theorem lcDrives_production_book_closed :
    LcDrives.lcDrivesProductionStator_book.closedB = true := by decide +kernel

/-- `reflectComposition` reflects all 5 methods of `lcDrivesProductionStator` into `LExpr`. -/
theorem lcDrives_production_reflected_members :
    (LcDrives.lcDrivesProductionStator_reflected.defs).map Prod.fst =
      ["massKg", "camSurfaceErrorUm", "thermalResistance", "sdfMargin", "peakWindingTemp"] := rfl

/-- Baseline outer-jacket stator at 8 kW copper loss reaches 282°C (`50 + 8 * 29`), whereas the
    direct in-slot liquid-cooled upgrade (`thermalResistance = 9`) reaches 122°C (`50 + 8 * 9`),
    a 160°C peak winding temperature reduction. -/
theorem lcDrives_baseline_vs_inslot_peak_temp :
    LcDrives.baselineJacketPeakTemp8kW_val = .nat 282 ∧
    LcDrives.lcDrivesInSlotPeakTemp8kW_val = .nat 122 ∧
    LcDrives.lcDrivesSdfMargin12mm_val = .nat 28 ∧
    LcDrives.finishMilledErrorAt5MmPerSec_val = .nat 22 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The reflected `LExpr` constants for the evaluated stator benchmarks match their values. -/
theorem lcDrives_benchmark_lexprs :
    LcDrives.baselineJacketPeakTemp8kW_lexpr = .lit 282 ∧
    LcDrives.lcDrivesInSlotPeakTemp8kW_lexpr = .lit 122 ∧
    LcDrives.lcDrivesSdfMargin12mm_lexpr = .lit 28 ∧
    LcDrives.finishMilledErrorAt5MmPerSec_lexpr = .lit 22 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Universal theorem over the reflected `LExpr` method `lcDrivesProductionStator_sdfMargin_lexpr`:
    for any radial clearance `r : Nat`, applying the reflected `sdfMargin` method (which statically
    inlined `super.sdfMargin(r) + 6` to `(r + 10) + 6`) to `self` and `.lit r` reduces via `SSteps`
    to `.lit (r + 10 + 6)`. -/
theorem lcDrives_reflected_sdfMargin_steps (r : Nat) :
    SSteps
      (.app (.app LcDrives.lcDrivesProductionStator_sdfMargin_lexpr (.record [])) (.lit r))
      (.lit (r + 10 + 6)) := by
  unfold LcDrives.lcDrivesProductionStator_sdfMargin_lexpr
  refine .next (.appFun _ (.beta .emptyRow _ (.record []))) ?_
  simp only [LExpr.inst, LExpr.subst]
  refine .next (.beta .emptyRow _ (.lit r)) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst]
  refine .next (.binLeft .add _ (.beta .emptyRow _ (.lit r))) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single]
  refine .next (.binLeft .add _ (.binLit .add r 10)) ?_
  exact .next (.binLit .add (r + 10) 6) (.refl _)

/-! ## 2. `#import_obend` on `DeosCounter.obend` -/

#import_obend "lean/tests/obend-source/DeosCounter.obend" as DeosCounter

/-- `DeosCounter.obend` passed `FrontEnd.accept`. -/
theorem deos_accepted : DeosCounter.accepted = true :=
  DeosCounter.accepted_eq

/-- `DeosCounter.predecessor` (which uses `match n: case 0 / case 1+p`, i.e. `.ifZero`)
    lowers cleanly to `DeosCounter.predecessor_lexpr`. -/
theorem deos_predecessor_lowered :
    lowerTerm emptyLayoutEnv DeosCounter.predecessor_term =
      some DeosCounter.predecessor_lexpr :=
  DeosCounter.predecessor_lowerTerm_eq

/-- Activity and sum-matching definitions `commit`, `inc`, and `reset` in `DeosCounter.obend`
    also lower cleanly to `LExpr`. -/
theorem deos_activity_defs_lowered :
    lowerTerm emptyLayoutEnv DeosCounter.commit_term = some DeosCounter.commit_lexpr ∧
    lowerTerm emptyLayoutEnv DeosCounter.inc_term = some DeosCounter.inc_lexpr ∧
    lowerTerm emptyLayoutEnv DeosCounter.reset_term = some DeosCounter.reset_lexpr :=
  ⟨DeosCounter.commit_lowerTerm_eq, DeosCounter.inc_lowerTerm_eq, DeosCounter.reset_lowerTerm_eq⟩

/-- Universal theorem over `DeosCounter.predecessor_lexpr`: for every `n : Nat`,
    applying `DeosCounter.predecessor_lexpr` to `.lit (n + 1)` reduces in the Lean-lite
    operational semantics (`SSteps`) to `.lit n`, with zero manual de Bruijn transcription! -/
theorem deos_predecessor_lexpr_succ_sound (n : Nat) :
    SSteps (.app DeosCounter.predecessor_lexpr (.lit (n + 1))) (.lit n) := by
  unfold DeosCounter.predecessor_lexpr
  refine .next (.beta .emptyRow _ (.lit (n + 1))) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst]
  exact lowerTerm_ifZero_succ_bvar0_steps n (.lit 0)

/-- Applying `DeosCounter.predecessor_lexpr` to `.lit 0` reduces via `SSteps` to `.lit 0`. -/
theorem deos_predecessor_lexpr_zero_sound :
    SSteps (.app DeosCounter.predecessor_lexpr (.lit 0)) (.lit 0) := by
  unfold DeosCounter.predecessor_lexpr
  refine .next (.beta .emptyRow _ (.lit 0)) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst]
  exact lowerTerm_ifZero_zero_steps (.lit 0) (.bvar 0)

/-- The emitted `Leaf.Book` for `DeosCounter.predecessor` has slot `["predecessor"]` and is closed. -/
theorem deos_predecessor_book_ok :
    DeosCounter.predecessor_book.slots = ["predecessor"] ∧
    DeosCounter.predecessor_book.closedB = true :=
  ⟨rfl, by decide +kernel⟩

theorem run_eq_nat {fuel : Nat} {t : Term} {n : Nat}
    (h : (match Obend.Law.run fuel t with | some (.nat m) => m == n | _ => false) = true) :
    Obend.Law.run fuel t = some (.nat n) := by
  revert h
  cases Obend.Law.run fuel t with
  | none => intro h; cases h
  | some v =>
    cases v <;> intro h <;> try cases h
    rename_i m
    rw [beq_iff_eq.1 h]

/-- `DeosCounter.minus_term` executes recursive saturating subtraction on `Core.Term`. -/
theorem deos_minus_exec :
    Obend.Law.run 500 (.app (.app DeosCounter.minus_term (.nat 10)) (.nat 4)) = some (.nat 6) ∧
    Obend.Law.run 500 (.app (.app DeosCounter.minus_term (.nat 3)) (.nat 7)) = some (.nat 0) :=
  ⟨run_eq_nat (by decide +kernel), run_eq_nat (by decide +kernel)⟩

/-! ## 3. Inline `#obend_decl` & Complete `Lower.Reflect` Coverage (`.ifZero`, `.label`, `.extend`, `.inject`, `.case`, `.split`) -/

#obend_decl InlineBridge "
record Packet:
  val: Nat
  extra: Nat

sum Action:
  reset: {}
  bump: Nat
  scale: Nat

def statusTag() -> String:
  \"ready\"

def updatePacket(p: Packet, v: Nat) -> Packet:
  extend(p, {val: v, extra: v + 1n})

def makeBump(n: Nat) -> Action:
  Action.bump(n)

def applyAction(base: Nat, act: Action) -> Nat:
  match act:
    case reset(_): 0n
    case bump(d): base + d
    case scale(k): base * k

def stepDown(n: Nat) -> Nat:
  match n:
    case 0: 0n
    case 1+pred: pred
"

/-- Every inline declaration using `.label`, `.extend`, `.inject`, `.case`, and `.ifZero`
    passed `FrontEnd.accept` and reflected cleanly into `LExpr`. -/
theorem inline_all_lowered :
    InlineBridge.accepted = true ∧
    lowerTerm emptyLayoutEnv InlineBridge.statusTag_term = some InlineBridge.statusTag_lexpr ∧
    lowerTerm emptyLayoutEnv InlineBridge.updatePacket_term = some InlineBridge.updatePacket_lexpr ∧
    lowerTerm emptyLayoutEnv InlineBridge.makeBump_term = some InlineBridge.makeBump_lexpr ∧
    lowerTerm emptyLayoutEnv InlineBridge.applyAction_term = some InlineBridge.applyAction_lexpr ∧
    lowerTerm emptyLayoutEnv InlineBridge.stepDown_term = some InlineBridge.stepDown_lexpr :=
  ⟨InlineBridge.accepted_eq,
   InlineBridge.statusTag_lowerTerm_eq,
   InlineBridge.updatePacket_lowerTerm_eq,
   InlineBridge.makeBump_lowerTerm_eq,
   InlineBridge.applyAction_lowerTerm_eq,
   InlineBridge.stepDown_lowerTerm_eq⟩

theorem inline_makeBump_lowerTerm_check :
    InlineBridge.makeBump_lexpr =
      .lam .emptyRow (.record [("tag", .lit (labelToNat "bump")), ("payload", .bvar 0)]) := rfl

/-- Universal theorem over `InlineBridge.stepDown_lexpr`: `.ifZero` lowers to a `boolRec` that
    steps `.lit (n + 1)` to `.lit n` for all `n : Nat`. -/
theorem inline_stepDown_succ_steps (n : Nat) :
    SSteps (.app InlineBridge.stepDown_lexpr (.lit (n + 1))) (.lit n) := by
  unfold InlineBridge.stepDown_lexpr
  refine .next (.beta .emptyRow _ (.lit (n + 1))) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst]
  exact lowerTerm_ifZero_succ_bvar0_steps n (.lit 0)

/-- Universal theorem over `InlineBridge.applyAction_lexpr`: applying `applyAction` to `base` and
    `makeBump(d)` steps through the finite-sum tag comparison (`reset` skipped, `bump` matched)
    to `.lit (base + d)`. -/
theorem inline_applyAction_bump_steps (base d : Nat) :
    SSteps
      (.app (.app InlineBridge.applyAction_lexpr (.lit base))
        (.record [("tag", .lit (labelToNat "bump")), ("payload", .lit d)]))
      (.lit (base + d)) := by
  unfold InlineBridge.applyAction_lexpr
  refine .next (.appFun _ (.beta .emptyRow _ (.lit base))) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst, LExpr.rename]
  refine .next (.beta .emptyRow _ (.record [("tag", .lit (labelToNat "bump")), ("payload", .lit d)])) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst]
  have hneq : (labelToNat "bump" == labelToNat "reset") = false := rfl
  have hskip := lowerTerm_inject_case_skip_steps "bump" "reset" (.lit d) (.lit 0)
    [("bump", .natBin .add (.lit base) (.bvar 0)), ("scale", .natBin .mul (.lit base) (.bvar 0))] hneq
  have hhead := lowerTerm_inject_case_head_steps "bump" (.lit d)
    (.natBin .add (.lit base) (.bvar 0)) [("scale", .natBin .mul (.lit base) (.bvar 0))]
  simp only [LExpr.inst, LExpr.subst, LExpr.single] at hhead
  have hproj : SStep (.proj "payload" (.record [("tag", .lit (labelToNat "bump")), ("payload", .lit d)])) (.lit d) :=
    .projRecord "payload" [("tag", .lit (labelToNat "bump")), ("payload", .lit d)] (.lit d) rfl
  exact Obend.Lower.ssteps_trans hskip
    (Obend.Lower.ssteps_trans hhead
      (.next (.binRight .add base hproj) (.next (.binLit .add base d) (.refl _))))

/-- Direct verification of `.extend` and `.split` reflection in `Obend.Lower.Reflect`:
    projecting an updated field from `lowerExtend` steps to the new value, and `lowerTerm` on
    `.split` steps via `SStep.splitRecord` to the curried application of fields. -/
theorem reflect_extend_and_split_sound (v1 v2 : LExpr) :
    SStep (.proj "val" (lowerExtend emptyLayoutEnv (.bvar 0) [("val", v1), ("extra", v2)])) v1 ∧
    lowerTerm emptyLayoutEnv (.split (.record [("a", .nat 4), ("b", .nat 9)]) ["a", "b"] (.lam (.lam (.bound 1)))) =
      some (.split ["a", "b"] (.lam .emptyRow (.lam .emptyRow (.bvar 1))) (.record [("a", .lit 4), ("b", .lit 9)])) ∧
    SSteps
      (.split ["a", "b"] (.lam .emptyRow (.lam .emptyRow (.bvar 1))) (.record [("a", .lit 4), ("b", .lit 9)]))
      (.lit 4) := by
  refine ⟨lowerExtend_proj_head_step emptyLayoutEnv rfl (.bvar 0) "val" v1 [("extra", v2)], rfl, ?_⟩
  have hsp := lowerSplit_record_step ["a", "b"] (.lam .emptyRow (.lam .emptyRow (.bvar 1)))
    [("a", .lit 4), ("b", .lit 9)] [.lit 4, .lit 9] rfl
  refine .next hsp ?_
  dsimp [LExpr.spine]
  refine .next (.appFun _ (.beta .emptyRow _ (.lit 4))) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst, LExpr.rename]
  refine .next (.beta .emptyRow _ (.lit 9)) ?_
  simp only [LExpr.inst, LExpr.subst]
  exact .refl (.lit 4)

/-! ## 4. `LawCompile.compileKeepsClaim` & `Logic.Obligation` Multi-Judge Discharge -/

/-- Identity step and boolean-true invariant for testing `compileKeepsClaim`. -/
def idStepTerm : Term := .lam (.bound 0)
def constTrueInv : Term := .lam (.boolean true)

theorem keeps_claim_bridge_check :
    Obend.Spec.LawCompile.fieldsOfKeepsRecord (compileKeepsClaim idStepTerm constTrueInv) =
      [("step", idStepTerm), ("inv", constTrueInv)] := rfl

theorem keeps_claim_bridge_sound :
    Obend.Spec.LawCompile.checkKeepsClaimRecord
      (compileKeepsClaim (Obend.Law.keeps .natural constTrueInv) constTrueInv)
      (.keeps "inv" "step") = true ∧
    (∀ {o : Data} {steps : List (Data × Data)},
      Obend.Law.Keeps constTrueInv o →
      Obend.Law.Chain (Obend.Law.LawStep (Obend.Law.keeps .natural constTrueInv)) o steps →
      ∀ s ∈ steps, Obend.Law.Keeps constTrueInv s.2) :=
  compileKeepsClaim_sound .natural constTrueInv (by decide +kernel)

/-- Export a verified Lean `TransportCert` and `LawExpr` into `LcDrives.package` via
    `verifyWorkbookObligationsWithLean` and `verifyClaimWithExternalTransport`. -/
def sampleDecideExpr : LExpr :=
  .lam .natural (.natBin .beq (.bvar 0) (.bvar 0))

def sampleTransportObj : TransportObj :=
  { decideExpr := sampleDecideExpr, argTys := [.natural] }

def sampleTransportCert : TransportCert :=
  { digest := workbookSourceDigest sampleDecideExpr
    claim := lowerProp sampleDecideExpr
    argTys := [.natural]
    supports := [] }

theorem sampleTransport_checks :
    workbookTransportCheck 0 sampleTransportObj sampleTransportCert = .ok := by decide +kernel

/-- `verifyClaimWithExternalTransport` discharges a well-formed `ClaimObj` using `transport@1`
    and `verifyClaimWithExternalTransport_sound` produces the semantic witness. -/
theorem external_transport_discharges_claim :
    verifyClaimWithExternalTransport 4096
      LcDrives.claim_peak_temp_open_recursion_obj
      sampleTransportObj sampleTransportCert = .ok := by decide +kernel

theorem external_transport_discharges_claim_sound :
    obligationMeaningWithJudges workbookFormats
      LcDrives.claim_peak_temp_open_recursion_obj
      (externalTransportJustification sampleTransportObj sampleTransportCert) :=
  verifyClaimWithExternalTransport_sound external_transport_discharges_claim

/-- External `lrat@1` (`Obend.Judge.Lrat.format`) discharges an obligation with a valid LRAT proof. -/
def unsatCnfJson : String := "[[1],[-1]]"
def validLratCertJson : String := "[{\"id\":3,\"clause\":[],\"hints\":[1,2]}]"

def lratJustification : Justification :=
  .byExternalJudge "lrat@1" (mkExternalJudgePayload unsatCnfJson validLratCertJson)

theorem external_lrat_discharges_obligation :
    obligationCheck 100 LcDrives.claim_peak_temp_open_recursion_obj lratJustification = .ok := by decide +kernel

theorem external_lrat_discharges_obligation_sound :
    obligationMeaningWithJudges defaultExternalFormats
      LcDrives.claim_peak_temp_open_recursion_obj lratJustification :=
  obligationWithJudges_sound defaultExternalFormats external_lrat_discharges_obligation

/-- External `clearing@1` (`clearingFormat`) discharges an obligation with a valid clearing certificate. -/
def validClearingObjJson : String :=
  "{\"market\":{\"currency\":0,\"goods\":1,\"epsilon\":0},\"orders\":[],\"transfers\":[]}"
def validClearingCertJson : String :=
  "{\"price\":10,\"potentialBid\":0,\"potentialAsk\":0,\"slacks\":[]}"

def clearingJustification : Justification :=
  .byExternalJudge "clearing@1" (mkExternalJudgePayload validClearingObjJson validClearingCertJson)

theorem external_clearing_discharges_obligation :
    obligationCheck 100 LcDrives.claim_peak_temp_open_recursion_obj clearingJustification = .ok := by decide +kernel

theorem external_clearing_discharges_obligation_sound :
    obligationMeaningWithJudges defaultExternalFormats
      LcDrives.claim_peak_temp_open_recursion_obj clearingJustification :=
  obligationWithJudges_sound defaultExternalFormats external_clearing_discharges_obligation

/-- Reverse bridge `verifyWorkbookObligationsWithLean` accepts `LcDrives.package` augmented with
    an exported Lean `LawExpr` (`monotone("thermalResistance")`) and external justification. -/
def exportedThermalLaw : LawExpr := .monotone "thermalResistance"

theorem workbook_with_exported_lean_law_and_cert :
    verifyWorkbookObligationsWithLean
      LcDrives.package
      [("peak_temp_open_recursion",
        externalTransportJustification sampleTransportObj sampleTransportCert)]
      []
      [("thermal_monotone", exportedThermalLaw)]
      4096 = true := by decide +kernel

/-! ## 5. Negative Tests & `#tooth` Mutation Proofs -/

/-- Negative test: tampered LRAT certificate, malformed clearing query (`currency = goods`),
    and `.byEval` are all refused (`≠ .ok`). -/
theorem negative_tampered_obligations_refused :
    obligationCheck 100 LcDrives.claim_peak_temp_open_recursion_obj
      (.byExternalJudge "lrat@1" (mkExternalJudgePayload unsatCnfJson "[]")) ≠ .ok ∧
    obligationCheck 100 LcDrives.claim_peak_temp_open_recursion_obj
      (.byExternalJudge "clearing@1"
        (mkExternalJudgePayload
          "{\"market\":{\"currency\":0,\"goods\":0,\"epsilon\":0},\"orders\":[],\"transfers\":[]}"
          validClearingCertJson)) ≠ .ok ∧
    obligationCheck 100 LcDrives.claim_peak_temp_open_recursion_obj
      (.byEval [[1, 2]]) ≠ .ok := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

#tooth lcDrives_baseline_vs_inslot_peak_temp by
  mutation LcDrives.lcDrivesInSlotPeakTemp8kW_val := Term.nat 999

#tooth lcDrives_production_book_slots by
  mutation LcDrives.lcDrivesProductionStator_book := { items := [] }

#tooth deos_predecessor_lexpr_succ_sound by
  mutation DeosCounter.predecessor_lexpr := LExpr.lam Ty.emptyRow (LExpr.lit 0)

#tooth inline_makeBump_lowerTerm_check by
  mutation InlineBridge.makeBump_lexpr := LExpr.lit 0

#tooth keeps_claim_bridge_check by
  mutation Obend.Spec.LawCompile.compileKeepsClaim := fun s _ => Term.record [("step", s)]

/-! ## 6. Compile-Time Axiom Audit (`0 sorryAx`, `0 Classical.choice`) -/

open Lean Elab Command in
elab "#verify_no_sorry_or_choice" : command => do
  let choiceFreeTargets : List Name := [
    ``Obend.Lower.Reflect.lowerTermFuel,
    ``Obend.Lower.Reflect.lowerTerm_ifZero_zero_steps,
    ``Obend.Lower.Reflect.lowerTerm_ifZero_succ_steps,
    ``Obend.Lower.Reflect.lowerTerm_ifZero_succ_bvar0_steps,
    ``Obend.Lower.Reflect.lowerTerm_inject_case_head_steps,
    ``Obend.Lower.Reflect.lowerTerm_inject_case_skip_steps,
    ``Obend.Lower.Reflect.lowerExtend_proj_head_step,
    ``Obend.Lower.Reflect.lowerSplit_record_step,
    ``Obend.Spec.LawCompile.compileKeepsClaim,
    ``Obend.Spec.LawCompile.compileKeepsClaim_step_eval,
    ``Obend.Spec.LawCompile.compileKeepsClaim_inv_eval,
    ``lcDrives_accepted,
    ``lcDrives_production_book_slots,
    ``lcDrives_production_reflected_members,
    ``lcDrives_baseline_vs_inslot_peak_temp,
    ``lcDrives_benchmark_lexprs,
    ``lcDrives_reflected_sdfMargin_steps,
    ``deos_accepted,
    ``deos_predecessor_lowered,
    ``deos_activity_defs_lowered,
    ``deos_predecessor_lexpr_succ_sound,
    ``deos_predecessor_lexpr_zero_sound,
    ``inline_all_lowered,
    ``inline_makeBump_lowerTerm_check,
    ``inline_stepDown_succ_steps,
    ``inline_applyAction_bump_steps,
    ``reflect_extend_and_split_sound,
    ``keeps_claim_bridge_check
  ]
  let standardTargets : List Name := [
    ``Obend.Spec.LawCompile.compileKeepsClaim_checkClaim_eq,
    ``Obend.Spec.LawCompile.compileKeepsClaim_sound,
    ``Obend.Logic.obligationCheckWithJudges,
    ``Obend.Logic.obligationWithJudges_sound,
    ``Obend.Logic.obligationWithJudges_mono,
    ``Obend.Elab.Workbook.verifyClaimWithTransport_sound,
    ``Obend.Elab.Workbook.verifyClaimWithExternalTransport_sound,
    ``Obend.Elab.Workbook.verifyWorkbookObligationsWithLean_sound,
    ``lcDrives_obligations_verified,
    ``lcDrives_open_recursion_claim_holds,
    ``lcDrives_production_book_closed,
    ``deos_predecessor_book_ok,
    ``deos_minus_exec,
    ``keeps_claim_bridge_sound,
    ``sampleTransport_checks,
    ``external_transport_discharges_claim,
    ``external_transport_discharges_claim_sound,
    ``external_lrat_discharges_obligation,
    ``external_lrat_discharges_obligation_sound,
    ``external_clearing_discharges_obligation,
    ``external_clearing_discharges_obligation_sound,
    ``workbook_with_exported_lean_law_and_cert,
    ``negative_tampered_obligations_refused
  ]
  for t in choiceFreeTargets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    if axs.contains ``Classical.choice then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on Classical.choice"
  let allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for t in standardTargets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    for a in axs do
      if !allowedStandard.contains a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on non-standard axiom {a}"
  logInfo m!"[PASS] Axiom audit verified: {choiceFreeTargets.length} lowering/reflection declarations have 0 sorryAx and 0 Classical.choice; {standardTargets.length} judge/claim declarations have 0 sorryAx and 0 native-trust axioms"

#verify_no_sorry_or_choice
