module
/-
# Obend.Hardware.TcadBridge — the `[FF, TT, SS]` corner envelope `TapeoutPipeline` stage 7 reads, and its signoff theorem

What a TCAD bridge is in this project after 2026-11-04 is `Obend/Hardware/Device/DriftDiffusion.lean`:
devsim solves a device fabricated by a recipe, the kernel checks the residual of every equation at every
node, and the terminal current is a theorem over the material and process parameters
(`devsim-dd1d@1`). This file is what remains of the earlier "cleanroom-to-TCAD" module once its
integer identities were deleted (the device-physics lane, `review/EXPERT-device-physics-20261104.md`):

0. **Three hand-typed corner formulas** (`evalEquivalentOxideThicknessPm`, `evalGateOxideCapScaled`,
   `evalSubthresholdSwingMvPerDec`), moved here from the deleted `Physics.lean` §7 and labelled as
   what they are: the arithmetic `extractTcadCornerEnvelope` was written against, not a model.
1. **`CleanroomToleranceBox`**: a wafer-lot tolerance box (gate dielectric, supply, temperature,
   metal thickness, gate area), with `Wf`/`checkWf`.
2. **`ProcessCornerEnvelope`**, `CornerBetween`, `ProcessCornerEnvelope.Valid`, and
   `extractTcadCornerEnvelope` with `extractTcadCornerEnvelope_valid` (the envelope of a well-formed
   box is ordered `FF ≤ TT ≤ SS`; a monotonicity statement about the formulas of §0).
3. **Dual-corner timing signoff** `checkEnvelopeTimingSignoff` and
   `envelope_timing_signoff_implies_all_intermediate_corners_safe`: setup at `SS` and hold at `FF`
   cover every corner between them. This is the one theorem here a timing engineer would keep.

Deleted: `ptm_2d_cancellation_tightens_ss_corner_delay` (a strict inequality between two literal
penalties) and `golden7nmCornerEnvelope_verified` (a preset closing timing on a preset path).
The replacement for stage 7 is a corner envelope derived from device certificates; until
`TapeoutPipeline` reads one, it runs on §0.
-/
public import Obend.Hardware.Process
public import Obend.Hardware.FabuBlox
public import Obend.Hardware.Analog
@[expose] public section

namespace Obend.Hardware.TcadBridge
open Obend.Hardware.Process
open Obend.Hardware.FabuBlox
open Obend.Hardware.Analog
set_option autoImplicit false

/-! ## 0. Hand-typed corner formulas (not physics; retained for `TapeoutPipeline` stage 7) -/

/-- `EOT = 3900 · t_phys / κ_permille` (pm). An integer formula, not a model of a dielectric. -/
def evalEquivalentOxideThicknessPm (physThicknessPm kDielectricPermille : Nat) : Nat :=
  (3900 * physThicknessPm) / max kDielectricPermille 1

/-- `C_ox = 3453000 / EOT` in scaled units. -/
def evalGateOxideCapScaled (eotPm : Nat) : Nat :=
  3453000 / max eotPm 1

/-- `S = 60 + (T − 300)/5 + 60 C_dep / C_ox` (mV/dec): a temperature slope typed as an integer. -/
def evalSubthresholdSwingMvPerDec (tempK cDepScaled coxScaled : Nat) : Nat :=
  60 + (tempK - 300) / 5 + (60 * cDepScaled) / max coxScaled 1

/-- The bookkeeping `extractInterconnectRCFromCutline` (`18000 / metal`) is antitone in the metal
thickness; the envelope proof needs this one line of `Nat.div_le_div_left`. -/
private theorem rcRes_antitone_in_metal (c1 c2 : CutlineColumn) (hThick : c1.metalThicknessNm ≤ c2.metalThicknessNm) :
    (extractInterconnectRCFromCutline c2).1 ≤ (extractInterconnectRCFromCutline c1).1 := by
  simp only [extractInterconnectRCFromCutline]
  have hMaxLe : max c1.metalThicknessNm 1 ≤ max c2.metalThicknessNm 1 := by omega
  have hPos : 0 < max c1.metalThicknessNm 1 := by omega
  exact Nat.div_le_div_left hMaxLe hPos

/-! ## 1. Cleanroom Manufacturing Tolerance Box (`CleanroomToleranceBox`) -/

/-- Wafer-lot cleanroom and operating tolerance box spanning `[FF, TT, SS]`:
* `gateOxideFastPm ≤ gateOxideNomPm ≤ gateOxideSlowPm`: physical high-$\kappa$ gate dielectric thickness (pm),
* `kDielectricPermille`: relative dielectric permittivity ($\times 1000$, e.g. `25000` for $\text{HfO}_2$),
* `vddSlowMv ≤ vddNomMv ≤ vddFastMv`: supply voltage range (mV),
* `tempFastK ≤ tempNomK ≤ tempSlowK`: junction temperature range (K),
* `primaSelfHeatDeltaK`: PRIMA reduced-order macromodel self-heating rise $\Delta T_{\text{SH}}$ (K) at `SS`,
* `metalSlowNm ≤ metalNomNm ≤ metalFastNm`: post-CMP copper interconnect thickness (nm),
* `gateAreaUm2`: active transistor gate area $W \cdot L$ ($\mu\text{m}^2$) for Pelgrom mismatch. -/
structure CleanroomToleranceBox where
  nodeNm              : Nat
  gateOxideFastPm     : Nat
  gateOxideNomPm      : Nat
  gateOxideSlowPm     : Nat
  kDielectricPermille : Nat
  vddFastMv           : Nat
  vddNomMv            : Nat
  vddSlowMv           : Nat
  tempFastK           : Nat
  tempNomK            : Nat
  tempSlowK           : Nat
  primaSelfHeatDeltaK : Nat
  metalFastNm         : Nat
  metalNomNm          : Nat
  metalSlowNm         : Nat
  gateAreaUm2         : Nat
  deriving DecidableEq, Repr

/-- Well-formedness of a `CleanroomToleranceBox`: parameter intervals are properly ordered from
fast (`FF`) through nominal (`TT`) to slow (`SS`). -/
def CleanroomToleranceBox.Wf (tol : CleanroomToleranceBox) : Prop :=
  tol.gateOxideFastPm ≤ tol.gateOxideNomPm ∧
  tol.gateOxideNomPm ≤ tol.gateOxideSlowPm ∧
  tol.vddSlowMv ≤ tol.vddNomMv ∧
  tol.vddNomMv ≤ tol.vddFastMv ∧
  tol.tempFastK ≤ tol.tempNomK ∧
  tol.tempNomK ≤ tol.tempSlowK ∧
  tol.metalSlowNm ≤ tol.metalNomNm ∧
  tol.metalNomNm ≤ tol.metalFastNm

/-- Executable boolean checker for `CleanroomToleranceBox.Wf`. -/
def CleanroomToleranceBox.checkWf (tol : CleanroomToleranceBox) : Bool :=
  decide (tol.gateOxideFastPm ≤ tol.gateOxideNomPm) &&
  decide (tol.gateOxideNomPm ≤ tol.gateOxideSlowPm) &&
  decide (tol.vddSlowMv ≤ tol.vddNomMv) &&
  decide (tol.vddNomMv ≤ tol.vddFastMv) &&
  decide (tol.tempFastK ≤ tol.tempNomK) &&
  decide (tol.tempNomK ≤ tol.tempSlowK) &&
  decide (tol.metalSlowNm ≤ tol.metalNomNm) &&
  decide (tol.metalNomNm ≤ tol.metalFastNm)

theorem CleanroomToleranceBox.checkWf_sound (tol : CleanroomToleranceBox)
    (h : tol.checkWf = true) : tol.Wf := by
  unfold CleanroomToleranceBox.checkWf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## 2. Process Corner Envelope (`[FF, TT, SS]`) & Partial Ordering (`CornerBetween`) -/

/-- A 3-corner process envelope `[fastCorner, nomCorner, slowCorner]` (`[FF, TT, SS]`). -/
structure ProcessCornerEnvelope where
  fastCorner : ProcessCorner
  nomCorner  : ProcessCorner
  slowCorner : ProcessCorner
  deriving DecidableEq, Repr

/-- An intermediate process corner `c` lies within the timing envelope `[cFast, cSlow]` iff:
1. Its maximum combinational and setup/skew parameters are bounded above by `cSlow` (`SS`), and
2. Its minimum contamination delays are bounded below by `cFast` (`FF`) while its hold/skew
   requirements are bounded above by `cFast`. -/
def CornerBetween (cFast c cSlow : ProcessCorner) : Prop :=
  c.tCqMaxPs ≤ cSlow.tCqMaxPs ∧
  c.tGateMaxPs ≤ cSlow.tGateMaxPs ∧
  c.tCarryMaxPs ≤ cSlow.tCarryMaxPs ∧
  c.tWireHopPs ≤ cSlow.tWireHopPs ∧
  c.tSetupPs ≤ cSlow.tSetupPs ∧
  c.tSkewPs ≤ cSlow.tSkewPs ∧
  cFast.tCqMinPs ≤ c.tCqMinPs ∧
  cFast.tGateMinPs ≤ c.tGateMinPs ∧
  c.tHoldPs ≤ cFast.tHoldPs ∧
  c.tSkewPs ≤ cFast.tSkewPs

/-- A `ProcessCornerEnvelope` is valid (`Valid`) when `fastCorner`, `nomCorner`, and `slowCorner`
all lie within `[fastCorner, slowCorner]`. -/
def ProcessCornerEnvelope.Valid (env : ProcessCornerEnvelope) : Prop :=
  CornerBetween env.fastCorner env.fastCorner env.slowCorner ∧
  CornerBetween env.fastCorner env.nomCorner env.slowCorner ∧
  CornerBetween env.fastCorner env.slowCorner env.slowCorner

/-! ## 3. Cleanroom-to-TCAD Corner Envelope Synthesis (`extractTcadCornerEnvelope`) -/

/-- Extract a single `ProcessCorner` from physical TCAD parameters (`eotPm`, `subthreshSwing`,
`sheetResMilliOhm`, `mismatchPenaltyPs`, `holdReqPs`). -/
def buildTcadCorner
    (name : String)
    (nodeNm voltageMv : Nat)
    (tempC : Int)
    (eotPm subthreshSwing sheetResMilliOhm mismatchPenaltyPs : Nat)
    (minCqPs minGatePs setupReqPs holdReqPs skewPs : Nat) : ProcessCorner where
  name        := name
  nodeNm      := nodeNm
  voltageMv   := voltageMv
  tempC       := tempC
  tCqMaxPs    := 30 + eotPm / 20 + mismatchPenaltyPs
  tCqMinPs    := minCqPs
  tGateMaxPs  := 20 + eotPm / 10 + subthreshSwing / 4 + mismatchPenaltyPs
  tGateMinPs  := minGatePs
  tCarryMaxPs := 8 + eotPm / 40
  tWireHopPs  := 60 + sheetResMilliOhm / 2
  tSetupPs    := setupReqPs
  tHoldPs     := holdReqPs
  tSkewPs     := skewPs

/-- Construct a cutline column for BEOL copper sheet resistance extraction at `metalNm`. -/
def mkTcadCutlineCol (metalNm : Nat) : CutlineColumn :=
  { xCoordNm := 0, siThicknessNm := 500, gateOxideNm := 2, tiNBarrierNm := 20
  , ildOxideNm := 100, metalThicknessNm := metalNm, resistThicknessNm := 0, sidewallAngleDeg := 90 }

/-- Synthesize the guaranteed `[FF, TT, SS]` `ProcessCornerEnvelope` from a `CleanroomToleranceBox`:
* Evaluates high-$\kappa$ Equivalent Oxide Thickness (`evalEquivalentOxideThicknessPm`) and $C_{\text{ox}}$
  (`evalGateOxideCapScaled`) across `[gateOxideFastPm, gateOxideNomPm, gateOxideSlowPm]`,
* Evaluates subthreshold swing (`evalSubthresholdSwingMvPerDec`) including PRIMA self-heating
  `primaSelfHeatDeltaK` at the `SS` corner,
* Extracts BEOL copper sheet resistance via `FabuBlox.extractInterconnectRCFromCutline`,
* Incorporates 2D PTM Pelgrom mismatch (`pelgromMismatchVariance`): when `usePtm2DCancellation = true`,
  the 2D common-centroid layout cancels first-order planar gradients and 2D Hessian curvature
  (`ptmPenaltyPs = 2`), whereas uncancelled 1D placement (`usePtm2DCancellation = false`) incurs
  an additional spatial gradient penalty (`ptmPenaltyPs = 18`). -/
def extractTcadCornerEnvelope
    (tol : CleanroomToleranceBox)
    (usePtm2DCancellation : Bool := true) : ProcessCornerEnvelope :=
  let eotFast := evalEquivalentOxideThicknessPm tol.gateOxideFastPm tol.kDielectricPermille
  let eotNom  := evalEquivalentOxideThicknessPm tol.gateOxideNomPm  tol.kDielectricPermille
  let eotSlow := evalEquivalentOxideThicknessPm tol.gateOxideSlowPm tol.kDielectricPermille
  let coxFast := evalGateOxideCapScaled eotFast
  let coxNom  := evalGateOxideCapScaled eotNom
  let coxSlow := evalGateOxideCapScaled eotSlow
  let ssFast  := evalSubthresholdSwingMvPerDec tol.tempFastK 100 coxFast
  let ssNom   := evalSubthresholdSwingMvPerDec tol.tempNomK  100 coxNom
  let ssSlow  := evalSubthresholdSwingMvPerDec (tol.tempSlowK + tol.primaSelfHeatDeltaK) 100 coxSlow
  let resFast := (extractInterconnectRCFromCutline (mkTcadCutlineCol tol.metalFastNm)).1
  let resNom  := (extractInterconnectRCFromCutline (mkTcadCutlineCol tol.metalNomNm)).1
  let resSlow := (extractInterconnectRCFromCutline (mkTcadCutlineCol tol.metalSlowNm)).1
  let ptmSlowPenaltyPs : Nat := if usePtm2DCancellation then 2 else 18
  { fastCorner :=
      buildTcadCorner "TCAD-7nm-FF" tol.nodeNm tol.vddFastMv
        (Int.ofNat tol.tempFastK - 273) eotFast ssFast resFast 0
        22 38 20 18 20
  , nomCorner :=
      buildTcadCorner "TCAD-7nm-TT" tol.nodeNm tol.vddNomMv
        (Int.ofNat tol.tempNomK - 273) eotNom ssNom resNom 1
        28 42 25 15 20
  , slowCorner :=
      buildTcadCorner "TCAD-7nm-SS" tol.nodeNm tol.vddSlowMv
        (Int.ofNat (tol.tempSlowK + tol.primaSelfHeatDeltaK) - 273)
        eotSlow ssSlow resSlow ptmSlowPenaltyPs
        34 46 35 12 20 }

/-- Monotonicity helper: `evalEquivalentOxideThicknessPm` is monotone in `physThicknessPm`. -/
theorem eot_monotone_in_phys_thickness
    {t1 t2 : Nat} (k : Nat) (ht : t1 ≤ t2) :
    evalEquivalentOxideThicknessPm t1 k ≤ evalEquivalentOxideThicknessPm t2 k := by
  simp only [evalEquivalentOxideThicknessPm]
  exact Nat.div_le_div_right (Nat.mul_le_mul_left 3900 ht)

/-- Monotonicity helper: `evalSubthresholdSwingMvPerDec` increases when temperature increases and
`coxScaled` decreases (`cox2 ≤ cox1`). -/
theorem subthreshold_swing_monotone_temp_and_antitone_cox
    {t1 t2 cox1 cox2 : Nat} (cDep : Nat) (ht : t1 ≤ t2) (hCox : cox2 ≤ cox1) :
    evalSubthresholdSwingMvPerDec t1 cDep cox1 ≤
      evalSubthresholdSwingMvPerDec t2 cDep cox2 := by
  simp only [evalSubthresholdSwingMvPerDec]
  have hT : (t1 - 300) / 5 ≤ (t2 - 300) / 5 := Nat.div_le_div_right (by omega)
  have hC : (60 * cDep) / max cox1 1 ≤ (60 * cDep) / max cox2 1 :=
    Nat.div_le_div_left (by omega) (by omega)
  omega

/-- **Theorem (`extractTcadCornerEnvelope_valid`)**:
For every well-formed `tol : CleanroomToleranceBox` (`tol.Wf`), the synthesized TCAD `[FF, TT, SS]`
process corner envelope `extractTcadCornerEnvelope tol usePtm2DCancellation` satisfies
`ProcessCornerEnvelope.Valid`! -/
theorem extractTcadCornerEnvelope_valid
    (tol : CleanroomToleranceBox)
    (usePtm2DCancellation : Bool)
    (hWf : tol.Wf) :
    (extractTcadCornerEnvelope tol usePtm2DCancellation).Valid := by
  rcases hWf with ⟨hOxFN, hOxNS, _hVddSN, _hVddNF, hTempFN, hTempNS, hMetSN, hMetNF⟩
  have hEotFN :
      evalEquivalentOxideThicknessPm tol.gateOxideFastPm tol.kDielectricPermille ≤
        evalEquivalentOxideThicknessPm tol.gateOxideNomPm tol.kDielectricPermille :=
    eot_monotone_in_phys_thickness tol.kDielectricPermille hOxFN
  have hEotNS :
      evalEquivalentOxideThicknessPm tol.gateOxideNomPm tol.kDielectricPermille ≤
        evalEquivalentOxideThicknessPm tol.gateOxideSlowPm tol.kDielectricPermille :=
    eot_monotone_in_phys_thickness tol.kDielectricPermille hOxNS
  have hCoxFN :
      evalGateOxideCapScaled (evalEquivalentOxideThicknessPm tol.gateOxideNomPm tol.kDielectricPermille) ≤
        evalGateOxideCapScaled (evalEquivalentOxideThicknessPm tol.gateOxideFastPm tol.kDielectricPermille) := by
    simp only [evalGateOxideCapScaled]
    exact Nat.div_le_div_left (by omega) (by omega)
  have hCoxNS :
      evalGateOxideCapScaled (evalEquivalentOxideThicknessPm tol.gateOxideSlowPm tol.kDielectricPermille) ≤
        evalGateOxideCapScaled (evalEquivalentOxideThicknessPm tol.gateOxideNomPm tol.kDielectricPermille) := by
    simp only [evalGateOxideCapScaled]
    exact Nat.div_le_div_left (by omega) (by omega)
  have hSsFN :=
    subthreshold_swing_monotone_temp_and_antitone_cox 100 hTempFN hCoxFN
  have hSsNS :=
    subthreshold_swing_monotone_temp_and_antitone_cox 100
      (Nat.le_trans hTempNS (Nat.le_add_right tol.tempSlowK tol.primaSelfHeatDeltaK)) hCoxNS
  have hResFN :
      (extractInterconnectRCFromCutline (mkTcadCutlineCol tol.metalFastNm)).1 ≤
        (extractInterconnectRCFromCutline (mkTcadCutlineCol tol.metalNomNm)).1 :=
    rcRes_antitone_in_metal (mkTcadCutlineCol tol.metalNomNm) (mkTcadCutlineCol tol.metalFastNm) hMetNF
  have hResNS :
      (extractInterconnectRCFromCutline (mkTcadCutlineCol tol.metalNomNm)).1 ≤
        (extractInterconnectRCFromCutline (mkTcadCutlineCol tol.metalSlowNm)).1 :=
    rcRes_antitone_in_metal (mkTcadCutlineCol tol.metalSlowNm) (mkTcadCutlineCol tol.metalNomNm) hMetSN
  have hPen : 1 ≤ (if usePtm2DCancellation then 2 else 18) := by
    cases usePtm2DCancellation <;> decide
  dsimp only [ProcessCornerEnvelope.Valid, CornerBetween, extractTcadCornerEnvelope, buildTcadCorner]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## 4. Dual-Corner `[SS, FF]` Timing Signoff (`checkEnvelopeTimingSignoff`) -/

/-- Dual-corner static timing signoff across a `ProcessCornerEnvelope`:
* Verifies **setup timing closure** (`requiredPeriodPs env.slowCorner p ≤ clockPeriodPs`) at `env.slowCorner` (`SS`), and
* Verifies **hold timing closure** (`env.fastCorner.tHoldPs + env.fastCorner.tSkewPs ≤ minArrivalPs env.fastCorner p`) at `env.fastCorner` (`FF`). -/
def checkEnvelopeTimingSignoff
    (env : ProcessCornerEnvelope) (clockPeriodPs : Nat) (p : TimingPath) : Bool :=
  decide (requiredPeriodPs env.slowCorner p ≤ clockPeriodPs) &&
  decide (env.fastCorner.tHoldPs + env.fastCorner.tSkewPs ≤ minArrivalPs env.fastCorner p)

/-- **Theorem (`envelope_timing_signoff_implies_all_intermediate_corners_safe`)**:
If `checkEnvelopeTimingSignoff env clockPeriodPs p = true` (setup closes at `SS` and hold closes at `FF`),
then for EVERY intermediate process corner `c : ProcessCorner` satisfying
`CornerBetween env.fastCorner c env.slowCorner`, full single-corner timing signoff
`checkTimingSignoff c clockPeriodPs p = true` holds! -/
theorem envelope_timing_signoff_implies_all_intermediate_corners_safe
    (env : ProcessCornerEnvelope)
    (clockPeriodPs : Nat)
    (p : TimingPath)
    (c : ProcessCorner)
    (hBetween : CornerBetween env.fastCorner c env.slowCorner)
    (hSignoff : checkEnvelopeTimingSignoff env clockPeriodPs p = true) :
    checkTimingSignoff c clockPeriodPs p = true ∧
    requiredPeriodPs c p ≤ clockPeriodPs ∧
    c.tHoldPs + c.tSkewPs ≤ minArrivalPs c p := by
  rcases hBetween with
    ⟨hCqMax, hGateMax, hCarryMax, hWireMax, hSetup, hSkewSlow,
     hCqMin, hGateMin, hHold, hSkewFast⟩
  simp only [checkEnvelopeTimingSignoff, Bool.and_eq_true, decide_eq_true_eq] at hSignoff
  rcases hSignoff with ⟨hSetupSS, hHoldFF⟩
  have hGateMaxMul : p.logicLevels * c.tGateMaxPs ≤ p.logicLevels * env.slowCorner.tGateMaxPs :=
    Nat.mul_le_mul_left p.logicLevels hGateMax
  have hCarryMaxMul : p.carryBits * c.tCarryMaxPs ≤ p.carryBits * env.slowCorner.tCarryMaxPs :=
    Nat.mul_le_mul_left p.carryBits hCarryMax
  have hWireMaxMul : p.tileHops * c.tWireHopPs ≤ p.tileHops * env.slowCorner.tWireHopPs :=
    Nat.mul_le_mul_left p.tileHops hWireMax
  have hGateMinMul : p.minLevels * env.fastCorner.tGateMinPs ≤ p.minLevels * c.tGateMinPs :=
    Nat.mul_le_mul_left p.minLevels hGateMin
  have hSetupC : requiredPeriodPs c p ≤ clockPeriodPs := by
    dsimp only [requiredPeriodPs, maxArrivalPs] at hSetupSS ⊢
    omega
  have hHoldC : c.tHoldPs + c.tSkewPs ≤ minArrivalPs c p := by
    dsimp only [minArrivalPs] at hHoldFF ⊢
    omega
  have hCheckC : checkTimingSignoff c clockPeriodPs p = true := by
    simp only [checkTimingSignoff, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hSetupC, hHoldC⟩
  exact ⟨hCheckC, hSetupC, hHoldC⟩

/-- Golden 7nm FinFET/GAA cleanroom tolerance box with $\text{HfO}_2$ gate dielectric ($\kappa = 25.0$),
PRIMA self-heating ($\Delta T_{\text{SH}} = 15\text{ K}$), and $2\text{ }\mu\text{m}^2$ active gate area. -/
def golden7nmToleranceBox : CleanroomToleranceBox where
  nodeNm              := 7
  gateOxideFastPm     := 1800
  gateOxideNomPm      := 2000
  gateOxideSlowPm     := 2200
  kDielectricPermille := 25000
  vddFastMv           := 825
  vddNomMv            := 750
  vddSlowMv           := 680
  tempFastK           := 233
  tempNomK            := 298
  tempSlowK           := 398
  primaSelfHeatDeltaK := 15
  metalFastNm         := 160
  metalNomNm          := 150
  metalSlowNm         := 135
  gateAreaUm2         := 2

end Obend.Hardware.TcadBridge
end
