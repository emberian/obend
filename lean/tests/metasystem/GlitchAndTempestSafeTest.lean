module
public import Obend.Hardware.GlitchAndTempestSafe
import all Obend.Analysis.Diff
import all Obend.Analysis.Groebner
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.SosLyapunov
import all Obend.AssertAxioms
import all Obend.Core.Data
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Hardware.CircuitDae
import all Obend.Hardware.GlitchAndTempestSafe
import all Obend.Hardware.HDL
import all Obend.Hardware.PipelinedRiscCore
import all Obend.Judge.Class
import all Obend.Judge.RealAnalysis
import all Obend.Tactic.Cases
import all Obend.Tactic.Tooth
import all Init.Data.Rat.Basic
public section
namespace Obend.Tests.GlitchAndTempestSafeTest

open Obend
open Obend.Analysis
open Obend.Hardware.HDL
open Obend.Hardware.PipelinedRisc
open Obend.Hardware.CircuitDae
open Obend.Hardware.GlitchAndTempestSafe

set_option autoImplicit false

private theorem stepIsa_unauth_trap_invariant :
    ∀ n : Nat,
      (n = 0 → stepIsaN (progToImem authGuardProg) n unauthInitIsaState = unauthInitIsaState) ∧
      (0 < n → stepIsaN (progToImem authGuardProg) n unauthInitIsaState = { unauthInitIsaState with pc := 8#64 })
  | 0 => ⟨fun _ => rfl, fun h => by omega⟩
  | 1 => ⟨fun h => by omega, fun _ => by decide +kernel⟩
  | n + 2 => by
    refine ⟨fun h => by omega, fun _ => ?_⟩
    have hSplit : stepIsaN (progToImem authGuardProg) ((n + 1) + 1) unauthInitIsaState =
        stepIsa (progToImem authGuardProg) (stepIsaN (progToImem authGuardProg) (n + 1) unauthInitIsaState) := by
      simpa [stepIsaN_one] using stepIsaN_add (progToImem authGuardProg) (n + 1) 1 unauthInitIsaState
    rw [hSplit, (stepIsa_unauth_trap_invariant (n + 1)).2 (by omega)]; decide +kernel

/-- **Single-Rail Power-Glitch Instruction-Skip Vulnerability (`singleRail_powerGlitch_skips_auth_check`)**:
At concrete brownout $V_{\text{glitch}} = 0.7\,\text{V} \in (V_{\text{ret}}, V_{\text{nom}}) = (0.6, 1.0)$,
single-rail execution skips `BEQ r1 r0 8` and commits `dmem[0x1000] = 0xCAFEBABEDEADBEEF`, an architectural
state provably unreachable by `PipelinedRisc.stepIsaN` at every $n \in \mathbb{N}$! -/
theorem singleRail_powerGlitch_skips_auth_check :
    let t := nominal1GhzTiming
    let vBrownout : CanonicalRat := CanonicalRat.mk 7 10
    let imem := progToImem authGuardProg
    let sAfterGlitch :=
      stepSingleRailGlitched t imem t.vNom t.tClkNom
        (stepSingleRailGlitched t imem vBrownout t.tClkNom unauthInitIsaState)
    cmosAlphaDelay t.kCritAlu t.vTh t.vNom ≤ t.tClkNom - t.tSetup ∧
    t.vRet < vBrownout ∧ vBrownout < t.vNom ∧
    cmosAlphaDelay t.kFastPc t.vTh vBrownout ≤ t.tClkNom - t.tSetup ∧
    t.tClkNom - t.tSetup < cmosAlphaDelay t.kCritAlu t.vTh vBrownout ∧
    sAfterGlitch.dmem.read 0x1000#64 = 0xCAFEBABEDEADBEEF#64 ∧
    ∀ n : Nat,
      (stepIsaN imem n unauthInitIsaState).dmem.read 0x1000#64 = 0#64 ∧
      sAfterGlitch ≠ stepIsaN imem n unauthInitIsaState := by
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, fun n => ?_⟩
  have hMemZero : (stepIsaN (progToImem authGuardProg) n unauthInitIsaState).dmem.read 0x1000#64 = 0#64 := by
    rcases Nat.eq_zero_or_pos n with rfl | hPos
    · rw [(stepIsa_unauth_trap_invariant 0).1 rfl]; rfl
    · rw [(stepIsa_unauth_trap_invariant n).2 hPos]; rfl
  refine ⟨hMemZero, fun hEq => ?_⟩
  have hRead := congrArg (fun st : IsaState => st.dmem.read 0x1000#64) hEq
  rw [hMemZero] at hRead; revert hRead; decide +kernel


theorem wddl_gates_spacer_exact_and_monotone :
    DualRailBit.wddlAnd .spacer .spacer = .spacer ∧
    DualRailBit.wddlOr  .spacer .spacer = .spacer ∧
    DualRailBit.wddlXor .spacer .spacer = .spacer ∧
    (∀ x y : Bool,
      DualRailBit.wddlNot (.encode x) = .encode (!x) ∧
      DualRailBit.wddlAnd (.encode x) (.encode y) = .encode (x && y) ∧
      DualRailBit.wddlOr  (.encode x) (.encode y) = .encode (x || y) ∧
      DualRailBit.wddlXor (.encode x) (.encode y) = .encode (xor x y)) ∧
    (∀ a1 a2 b1 b2 : DualRailBit, DualRailBit.delayLe a1 a2 → DualRailBit.delayLe b1 b2 →
      DualRailBit.delayLe (DualRailBit.wddlAnd a1 b1) (DualRailBit.wddlAnd a2 b2) ∧
      DualRailBit.delayLe (DualRailBit.wddlOr  a1 b1) (DualRailBit.wddlOr  a2 b2) ∧
      DualRailBit.delayLe (DualRailBit.wddlXor a1 b1) (DualRailBit.wddlXor a2 b2)) := by
  refine ⟨rfl, rfl, rfl, fun x y => by cases x <;> cases y <;> decide, ?_⟩
  intro ⟨at1, af1⟩ ⟨at2, af2⟩ ⟨bt1, bf1⟩ ⟨bt2, bf2⟩ hA hB
  cases at1 <;> cases af1 <;> cases at2 <;> cases af2 <;>
    cases bt1 <;> cases bf1 <;> cases bt2 <;> cases bf2 <;>
    simp_all [DualRailBit.delayLe, DualRailBit.wddlAnd, DualRailBit.wddlOr, DualRailBit.wddlXor]


theorem dualRailWddlGuardRtl_wellFormed : checkRtlModuleW dualRailWddlGuardRtlModule = true := by decide +kernel


-- Inhabitedness witnesses required by `lean/uninhabited-premise-risk`
theorem certified2p5GhzStriplineEnv_valid : checkTempestEmcEnvelope certified2p5GhzStriplineEnv = true := by decide +kernel
theorem certifiedTempestGlitch_valid :
    checkTempestGlitchEmc 1 certifiedTempestGlitchProblem certifiedTempestGlitchCert = .ok := by decide +kernel



private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (h ▸ rfl) else isFalse (fun heq => by injection heq; contradiction)
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (h ▸ rfl) else isFalse (fun heq => by injection heq; contradiction)
  | .error _, .ok _ => isFalse (fun heq => by injection heq)
  | .ok _, .error _ => isFalse (fun heq => by injection heq)

-- ============================================================================
-- 1. PDN RLC Passivity, CMOS Alpha-Power Delay & Single-Rail Glitch Auth-Skip
-- ============================================================================

/-- Concrete PDN passivity + nominal vs brownout single-rail `PipelinedRiscCore` execution checks. -/
example :
    let t := nominal1GhzTiming
    let imem := progToImem authGuardProg
    cmosAlphaDelay t.kCritAlu t.vTh 1 = CanonicalRat.mk 5 9 ∧
    cmosAlphaDelay t.kFastPc t.vTh (CanonicalRat.mk 7 10) = CanonicalRat.mk 5 9 ∧
    cmosAlphaDelay t.kCritAlu t.vTh (CanonicalRat.mk 7 10) = CanonicalRat.mk 20 9 ∧
    stepSingleRailGlitched t imem t.vNom t.tClkNom unauthInitIsaState = stepIsa imem unauthInitIsaState ∧
    (stepSingleRailGlitched t imem t.vNom t.tClkNom unauthInitIsaState).pc = 8#64 ∧
    (stepSingleRailGlitched t imem (CanonicalRat.mk 7 10) t.tClkNom unauthInitIsaState).pc = 4#64 := by
  decide +kernel

theorem test_pdn_passivity_and_single_rail_vulnerability (x : List CanonicalRat) (n : Nat) :
    0 ≤ mnaStoredEnergy 2 (pdnDecapRlcSpec 2 (CanonicalRat.mk 1 2) 3 1).matC x ∧
    0 ≤ quadFormN 2 (pdnDecapRlcSpec 2 (CanonicalRat.mk 1 2) 3 1).matG x x ∧
    (stepIsaN (progToImem authGuardProg) n unauthInitIsaState).dmem.read 0x1000#64 = 0#64 := by
  have hPass := pdnDecapRlc_passive_and_dissipative 2 (CanonicalRat.mk 1 2) 3 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hVuln := singleRail_powerGlitch_skips_auth_check
  exact ⟨hPass.1 x, hPass.2 x, (hVuln.2.2.2.2.2.2 n).1⟩

-- ============================================================================
-- 2. Dual-Rail WDDL RTL & Universal Multi-Turn Glitch Immunity on `authGuardProg`
-- ============================================================================

/-- Concrete WDDL RTL module well-formedness, complementary XOR/AND/OR outputs, and clean 2-cycle ISA step. -/
example :
    checkRtlModuleW dualRailWddlGuardRtlModule = true ∧
    checkRtlModuleW dualRailAluSliceRtlModule = true ∧
    checkRailClockWindow certifiedDualRailWindow 1 1 1 = true ∧
    (let a := DualRailWord64.encode 0xF0F0#64
     let b := DualRailWord64.encode 0x0FF0#64
     let ins : Nat → BitVec 64
       | 0 => a.tRail | 1 => a.fRail | 2 => b.tRail | 3 => b.fRail
       | 4 => 1#64 | 5 => 0xABCD#64 | 6 => 0x9999#64 | _ => 0#64
     let outs := evalModuleOutputs dualRailWddlGuardRtlModule ins (fun _ => 0#64)
     outs.lookup "xor_t" = some (0xF0F0#64 ^^^ 0x0FF0#64) ∧
     outs.lookup "and_t" = some (0xF0F0#64 &&& 0x0FF0#64) ∧
     outs.lookup "or_t"  = some (0xF0F0#64 ||| 0x0FF0#64) ∧
     outs.lookup "completion_valid"  = some 1#64 ∧
     outs.lookup "quarantine_active" = some 0#64 ∧
     outs.lookup "actuation_out"     = some 0xABCD#64 ∧
     outs.lookup "secret_key_out"    = some 0x9999#64) ∧
    (let f := mkCleanGlitchCycleFault 1 1
     let st2 := runGlitchProtectedCpuTrace certifiedDualRailWindow (progToImem authGuardProg)
       [.clockCycle f, .clockCycle f] (initGlitchProtectedCpu unauthInitIsaState 0x7777#64 0x5555#64)
     st2.mode = .normal .spacerPhase ∧ st2.isa.pc = 8#64 ∧ st2.isa.dmem.read 0x1000#64 = 0#64) := by
  decide +kernel

/-- Concrete adversarial brownout (`0.7 V < 0.85 V` window floor) and `11`-alarm overdrive faults
deterministically latch `.glitchQuarantine` and clamp actuation & secret-key buses to `0#64`. -/
example :
    let imem := progToImem authGuardProg
    let st0 := initGlitchProtectedCpu unauthInitIsaState 0xDEADBEEF#64 0x12345678#64
    let fClean := mkCleanGlitchCycleFault 1 1
    let fBrownout := { fClean with vGlitchDrop := CanonicalRat.mk 3 10 }
    let fOverdrive11 := { fClean with overdrivePc := 1#64 }
    let stAfterBrownout := runGlitchProtectedCpuTrace certifiedDualRailWindow imem
      [.clockCycle fClean, .clockCycle fBrownout, .clockCycle fClean] st0
    let stAfter11 := runGlitchProtectedCpuTrace certifiedDualRailWindow imem
      [.clockCycle fClean, .clockCycle fOverdrive11, .clockCycle fClean] st0
    stAfterBrownout.mode = .glitchQuarantine ∧
    externalActuationOut stAfterBrownout = 0#64 ∧
    externalKeyBusOut stAfterBrownout = 0#64 ∧
    stAfterBrownout.isa.dmem.read 0x1000#64 = 0#64 ∧
    stAfter11.mode = .glitchQuarantine ∧
    externalActuationOut stAfter11 = 0#64 ∧
    externalKeyBusOut stAfter11 = 0#64 := by
  decide +kernel

/-- **Universal Multi-Turn Unauthenticated Store-Immunity Theorem (`test_dualRail_never_unauthorized_store`)**:
Whereas a single `0.7 V` glitch makes the single-rail CPU overwrite `0x1000#64` on `authGuardProg`,
under **ANY** un-reset multi-turn sequence `turns` of arbitrary voltage glitches, clock runts, partial
wire arrivals `{00} → {00, 01, 10}`, and `11` overdrive faults, the Dual-Rail WDDL CPU either clamps into
`.glitchQuarantine` (`0#64` external outputs) or stays on an exact `stepIsaN` state where `dmem[0x1000] = 0#64`! -/
theorem test_dualRail_never_unauthorized_store
    (winSpec : RailClockWindowSpec) (turns : List DualRailCpuTurn)
    (key0 act0 : BitVec 64) (hUnreset : turns.all isUnresetTurn = true) :
    let imem := progToImem authGuardProg
    let stFinal := runGlitchProtectedCpuTrace winSpec imem turns
      (initGlitchProtectedCpu unauthInitIsaState key0 act0)
    (stFinal.mode = .glitchQuarantine ∧
     externalActuationOut stFinal = 0#64 ∧
     externalKeyBusOut stFinal = 0#64) ∨
    (stFinal.isa.dmem.read 0x1000#64 = 0#64) := by
  have hMain := (power_glitch_immunity_multi_turn_sound winSpec (progToImem authGuardProg)).2.1
    turns unauthInitIsaState key0 act0 hUnreset
  rcases hMain with hQuar | ⟨m, _, hIsaEq⟩
  · exact Or.inl hQuar
  · right
    rw [hIsaEq]
    exact (singleRail_powerGlitch_skips_auth_check.2.2.2.2.2.2 m).1

-- ============================================================================
-- 3. Multi-GHz Coupled-PCB TEMPEST Safety (Symmetric, PRNG-Masked & Imperfect DFM)
-- ============================================================================

def symmetric2p5GhzPcb : CoupledPcbPairSpec :=
  ⟨CanonicalRat.mk 2 25, CanonicalRat.mk 1 2000, CanonicalRat.mk 1 2000,
   CanonicalRat.mk 3 100, CanonicalRat.mk 1 50, CanonicalRat.mk 1 50000⟩

def asymmetricSkewed5GhzPcb : CoupledPcbPairSpec :=
  ⟨CanonicalRat.mk 2 25, CanonicalRat.mk 1 1500, -(CanonicalRat.mk 1 3000),
   CanonicalRat.mk 3 100, CanonicalRat.mk 1 50, CanonicalRat.mk 1 50000⟩

def edge5GhzSkewed : HighSpeedEdgeSpec :=
  ⟨5, CanonicalRat.mk 4 5, CanonicalRat.mk 2 25, CanonicalRat.mk 3 2000⟩

def imperfectRealized2p5GhzPcb : CoupledPcbPairSpec :=
  ⟨CanonicalRat.mk 2 25, CanonicalRat.mk 3 5000, -(CanonicalRat.mk 1 5000),
   CanonicalRat.mk 3 100, CanonicalRat.mk 1 50, CanonicalRat.mk 1 50000⟩

def imperfectRealized2p5GhzEdge : HighSpeedEdgeSpec :=
  ⟨CanonicalRat.mk 5 2, CanonicalRat.mk 4 5, CanonicalRat.mk 2 25, CanonicalRat.mk 1 1000⟩

theorem test_symmetric_and_masked_5ghz_tempest_zero_leakage
    (distinguisher : List RadiatedEmObservation → CanonicalRat) :
    let edgeSym5Ghz : HighSpeedEdgeSpec := ⟨5, CanonicalRat.mk 4 5, CanonicalRat.mk 2 25, 0⟩
    (∀ isSpacer s : Bool,
      pcbCommonModeCurrent symmetric2p5GhzPcb edgeSym5Ghz isSpacer s = 0 ∧
      pcbPdnSupplyCurrent symmetric2p5GhzPcb edgeSym5Ghz isSpacer false =
        pcbPdnSupplyCurrent symmetric2p5GhzPcb edgeSym5Ghz isSpacer true) ∧
    (let envSeq := fun idx => (asymmetricSkewed5GhzPcb, edge5GhzSkewed, idx % 2 == 1)
     uniformMaskExpectation 4
       (fun m => distinguisher (observeMaskedEmTrace envSeq 0 [false, true, false, true] m)) =
     uniformMaskExpectation 4
       (fun m => distinguisher (observeMaskedEmTrace envSeq 0 [true, true, false, false] m))) := by
  have hSym := balanced_wddl_zero_secret_dependent_power_and_cm
    symmetric2p5GhzPcb ⟨5, CanonicalRat.mk 4 5, CanonicalRat.mk 2 25, 0⟩ rfl rfl
  have hMask := (masked_dualRail_exact_mutual_info_zero
    asymmetricSkewed5GhzPcb edge5GhzSkewed false ⟨0, 0, 0, 0, 0, 0, 0⟩
    4 (fun idx => (asymmetricSkewed5GhzPcb, edge5GhzSkewed, idx % 2 == 1))
    [false, true, false, true] [true, true, false, false] rfl rfl distinguisher).2
  exact ⟨fun isSpacer s => ⟨(hSym.2.2 isSpacer s).1, hSym.2.1 isSpacer⟩, hMask⟩

theorem test_imperfect_pcb_snr_below_noise_floor_at_any_standoff
    (isSpacer s : Bool) (rDistM : CanonicalRat) (hR : 1 ≤ rDistM) :
    ratAbs (pcbCommonModeCurrent imperfectRealized2p5GhzPcb imperfectRealized2p5GhzEdge isSpacer s) ≤
      cmLeakageBound certified2p5GhzStriplineEnv ∧
    interceptedSnr certified2p5GhzStriplineEnv imperfectRealized2p5GhzPcb imperfectRealized2p5GhzEdge
      isSpacer s rDistM < CanonicalRat.mk 1 4 ∧
    CanonicalRat.ofNat certified2p5GhzStriplineEnv.snrMaxMilli / 1000 < 1 := by
  have hChk : checkTempestEmcEnvelope certified2p5GhzStriplineEnv = true := certified2p5GhzStriplineEnv_valid
  have hDfm : RealizesPcbDfm certified2p5GhzStriplineEnv imperfectRealized2p5GhzPcb imperfectRealized2p5GhzEdge :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have hRes := (imperfect_pcb_tempest_snr_below_noise_floor certified2p5GhzStriplineEnv).1
    imperfectRealized2p5GhzPcb imperfectRealized2p5GhzEdge
    isSpacer s rDistM hChk hDfm hR
  have hQuarter : CanonicalRat.ofNat certified2p5GhzStriplineEnv.snrMaxMilli / 1000 = CanonicalRat.mk 1 4 := by
    decide +kernel
  rw [hQuarter] at hRes
  exact ⟨hRes.1, hRes.2.1, by decide +kernel⟩

-- ============================================================================
-- 4. Total `Obend.Judge` & `"tempest-glitch-emc@1"` Wire Roundtrip + Refusals
-- ============================================================================

def cyclicRtlBadTempestProblem : TempestGlitchEmcProblem :=
  { certifiedTempestGlitchProblem with guardRtl := cyclicBadGuardRtlModule }

def sparseViaBadTempestProblem : TempestGlitchEmcProblem :=
  { certifiedTempestGlitchProblem with pcbEnv := { certified2p5GhzStriplineEnv with viaPitchUm := 5000 } }

-- Execute codec regressions without normalizing the complete string parser in kernel fixture proofs.
#guard decide (decodeTempestGlitchEmcProblem (encodeTempestGlitchEmcProblem certifiedTempestGlitchProblem) =
  .ok certifiedTempestGlitchProblem)
#guard decide (decodeTempestGlitchEmcProblem (encodeTempestGlitchEmcProblem groundSlotBadTempestProblem) =
  .ok groundSlotBadTempestProblem)
#guard decide (decodeTempestGlitchEmcCert (encodeTempestGlitchEmcCert certifiedTempestGlitchCert) =
  .ok certifiedTempestGlitchCert)
#guard match tempestGlitchEmcFormat.checkBytes 1
  (encodeTempestGlitchEmcProblem certifiedTempestGlitchProblem)
  (encodeTempestGlitchEmcCert certifiedTempestGlitchCert) with | .ok => true | _ => false
#guard match tempestGlitchEmcFormat.checkBytes 1
  (encodeTempestGlitchEmcProblem groundSlotBadTempestProblem)
  (encodeTempestGlitchEmcCert certifiedTempestGlitchCert) with
  | .refused (.judge .groundSlotOrMissingGroundPlanes) [] => true | _ => false
example :
    tempestGlitchEmcFormat.name ++ "@" ++ tempestGlitchEmcFormat.version = tempestGlitchEmcWireTag ∧
    checkTempestGlitchEmc 0 certifiedTempestGlitchProblem certifiedTempestGlitchCert = .uncovered ∧
    checkTempestGlitchEmc 1 certifiedTempestGlitchProblem certifiedTempestGlitchCert = .ok ∧
    checkTempestGlitchEmc 1 cyclicRtlBadTempestProblem certifiedTempestGlitchCert =
      .refused .invalidDualRailGuardRtl [] ∧
    checkTempestGlitchEmc 1 sparseViaBadTempestProblem certifiedTempestGlitchCert =
      .refused .sparseStitchingViaFence [] ∧
    checkTempestGlitchEmc 1 certifiedTempestGlitchProblem ⟨certifiedPdnDaeCert, 64⟩ =
      .refused .insufficientPrngMaskEntropy [] := by
  exact ⟨rfl, by decide +kernel, certifiedTempestGlitch_valid, by decide +kernel⟩

theorem test_planted_tempest_and_rtl_refusals_impossible (c' : TempestGlitchEmcCert) :
    ¬ TempestGlitchEmcMeaning groundSlotBadTempestProblem c' ∧
    ¬ TempestGlitchEmcMeaning cyclicRtlBadTempestProblem c' ∧
    ¬ TempestGlitchEmcMeaning sparseViaBadTempestProblem c' :=
  ⟨tempestGlitchEmcJudge.refuted (groundSlotBadTempest_refused 0) rfl c',
   tempestGlitchEmcJudge.refuted (c := certifiedTempestGlitchCert) (r := 1)
     (by decide +kernel : checkTempestGlitchEmc 1 cyclicRtlBadTempestProblem certifiedTempestGlitchCert =
       .refused .invalidDualRailGuardRtl []) rfl c',
   tempestGlitchEmcJudge.refuted (c := certifiedTempestGlitchCert) (r := 1)
     (by decide +kernel : checkTempestGlitchEmc 1 sparseViaBadTempestProblem certifiedTempestGlitchCert =
       .refused .sparseStitchingViaFence []) rfl c'⟩

-- ============================================================================
-- 5. `#tooth` Universal Theorem Mutation Kills (`8` witnesses, `≥ 6` required)
-- ============================================================================

#tooth Obend.Hardware.GlitchAndTempestSafe.subset_arrival_valid_implies_exact by
  mutation Obend.Hardware.GlitchAndTempestSafe.wordAllValid := fun _ => true

#tooth Obend.Hardware.GlitchAndTempestSafe.dualRailWddlGuardRtl_sticky_quarantine_clamps_outputs by
  mutation Obend.Hardware.HDL.evalModuleOutputs := fun _ _ _ => [("actuation_out", 1#64)]

#tooth Obend.Hardware.GlitchAndTempestSafe.power_glitch_immunity_multi_turn_sound by
  mutation Obend.Hardware.GlitchAndTempestSafe.externalActuationOut := fun _ => 1#64

#tooth Obend.Hardware.GlitchAndTempestSafe.dualRail_clean_2cycle_executes_stepIsa by
  mutation Obend.Hardware.GlitchAndTempestSafe.commitIsaFromDualRailBundle :=
    fun _ s _ => { s with pc := s.pc + 99#64 }

#tooth Obend.Hardware.GlitchAndTempestSafe.balanced_wddl_zero_secret_dependent_power_and_cm by
  mutation Obend.Hardware.GlitchAndTempestSafe.pcbCommonModeCurrent := fun _ _ _ _ => 1

#tooth Obend.Hardware.GlitchAndTempestSafe.masked_dualRail_exact_mutual_info_zero by
  mutation Obend.Hardware.GlitchAndTempestSafe.railSwap := fun w _ => w

#tooth Obend.Hardware.GlitchAndTempestSafe.imperfect_pcb_tempest_snr_below_noise_floor by
  mutation Obend.Hardware.GlitchAndTempestSafe.checkTempestEmcEnvelope := fun _ => true

#tooth Obend.Hardware.GlitchAndTempestSafe.checkTempestGlitchEmc_sound by
  mutation Obend.Hardware.GlitchAndTempestSafe.checkTempestGlitchEmc := fun _ _ _ => .ok

-- ============================================================================
-- 6. Axiom Purity Census (`0 sorryAx`, `0` custom axioms across entire import cone)
-- ============================================================================

private def bus : BusTempestSpec := ⟨3,2,5,#[⟨3,2,1,4⟩,⟨2,3,1,2⟩],6⟩
example : checkBusTempestEmc bus = true := by decide +kernel
example : checkBusTempestEmc { bus with xtalkMax := 5 } = false := by decide +kernel
example : (wddlBusSsnAndCrosstalk bus [false,false,false]).1 = 30 ∧
    (wddlBusSsnAndCrosstalk bus [true,false,true]).1 = 30 := by decide +kernel
example : singleRailBusSsn bus [false,false,false] [false,false,false] = 0 ∧
    singleRailBusSsn bus [false,false,false] [true,false,true] = 20 := by decide +kernel
example : ratAbs (busDifferentialVoltage bus.aggressors.toList (fun a => if a.cp = 3 then 4 else -2)) = 6 := by decide +kernel
example : checkTempestGlitchBus 1 certifiedTempestGlitchProblem certifiedTempestGlitchCert bus = true := by
  unfold checkTempestGlitchBus; rw [certifiedTempestGlitch_valid]; decide +kernel
example : checkTempestGlitchBus 1 certifiedTempestGlitchProblem certifiedTempestGlitchCert { bus with xtalkMax := 5 } = false := by
  unfold checkTempestGlitchBus; rw [certifiedTempestGlitch_valid]; decide +kernel
#tooth checkTempestGlitchBus_sound by
  mutation checkTempestGlitchBus := fun _ _ _ _ => true
#tooth balanced_wddl_bus_ssn_secret_independent by
  mutation wddlTransitions := fun word => (word.filter id).length
#tooth checkBusTempestEmc_sound by
  mutation checkBusTempestEmc := fun _ => true
#tooth checkBusTempestEmc_sound by
  mutation busDifferentialVoltage := fun as signal => (as.map (fun a => (a.cp+a.cn)*signal a)).sum

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]? == some `Obend.Hardware.GlitchAndTempestSafe do continue
    if let .thmInfo _ := info then
      if !name.isInternal && !name.isInternalDetail && name.components.getLast? != some `sizeOf_spec then
        if ← liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
          throwError "Closed library theorem: {name}"
  logInfo "Obend.Hardware.GlitchAndTempestSafe: zero closed theorems"
#assert_axioms_tree

end Obend.Tests.GlitchAndTempestSafeTest
