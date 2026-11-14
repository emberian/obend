/-
# `Obend/Teeth/Hardware/Fixtures.lean` — the closed fixtures that left tier 1 (2026-11-04)

Each `example` here was a `theorem` in a tier-1 module of `Obend/Hardware/`: a closed statement, proved by
`decide +kernel` on literal data, that nothing cites. The triage of 2026-11-04 (`Obend/Census.lean`,
`review/DECISIONS-20261031.md`) keeps them as what they are, end-to-end runs worth doing before a
push and not on every library build. Each carries the module it came from and why it is kept. This
file is tier 2: `lake build Teeth`; a plain file, so it sees every definition with its body.
-/

import Obend.Hardware.AgenticEDA
import Obend.Hardware.GeometryCAM
import Obend.Hardware.Kinematics
import Obend.Hardware.OpenUSD
import Obend.Hardware.Retiming

set_option autoImplicit false

-- from Obend/Hardware/AgenticEDA.lean:407: refusal witness inside a 33-line fixture; worth a pre-push run
namespace Obend.Hardware.AgenticEDA
open Obend.Vault
open Obend.Spec.Law (LawExpr Facts)
open Obend.Hardware.Datasheet
open Obend.Hardware.PCB
/-- Theorem (`goldenAgenticBomSwap_admitted_and_overbudget_refused`):
1. `goldenEdaLaws` enforces 4 `.obend` smart-contract invariants (`drc_zero`, `thermal_cap`,
   `rf_vswr_cap`, `bom_budget`),
2. `judgeAgenticEdaProposal` **admits** `procurement_scout`'s valid QFN-16 second-source swap
   (`goldenSecondSourcePart`) after executing the compiled `Core4` smart contracts and verifying
   datasheet freshness and $400\,\text{mV}$ CMOS noise margins,
3. `judgeAgenticEdaProposal` **refuses** `overbudgetSecondSourcePart` by blaming the exact
   smart-contract law `"bom_budget"` (`new.cost_cents <= 250`),
4. `judgeAgenticEdaProposal` **refuses** a stale datasheet citation (`pinnedBlockHash ≠ currentDatasheetHash`)
   with `.refusedByPhysics "stale-datasheet-cite"`. -/
example :
    goldenEdaLaws.length = 4 ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      goldenSecondSourcePart
      lvcmos33ReceiverSpec
      400
      goldenFreshDatasheetCite
      "procurement_scout"
      defaultEdaFacts = .admitted ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      overbudgetSecondSourcePart
      lvcmos33ReceiverSpec
      400
      goldenFreshDatasheetCite
      "procurement_scout"
      defaultEdaFacts = .refusedBySmartContract "bom_budget" "bom_budget" ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      goldenSecondSourcePart
      lvcmos33ReceiverSpec
      400
      { goldenFreshDatasheetCite with currentDatasheetHash := 0x9A4F2C02 }
      "procurement_scout"
      defaultEdaFacts = .refusedByPhysics "stale-datasheet-cite" := by
  decide +kernel
end Obend.Hardware.AgenticEDA

-- from Obend/Hardware/GeometryCAM.lean:662: end-to-end run on a fixture (16 lines); worth a pre-push run, not every library build
namespace Obend.Hardware.GeometryCAM
open Obend.Hardware.Accelerators
/-- **Golden Multi-Feature Stator CSG Tape Compaction Certificate (`golden_fidget_tape_pruning_verified`)**:
On a 3-feature stator CSG expression combining:
1. Primary stator core cylinder $x^2 + y^2 - 100$,
2. Unioned mounting lug $(x - 20)^2 + y^2 - 4$, and
3. Subtracted axial cooling bore $(x + 20)^2 + y^2 - 4$,
specializing the 24-node CSG tape over an octree sub-box $B = [-2, 2]^3$ near the stator center
prunes away both the distant mounting lug (`.csgUnion` $\to$ `.left`) and the distant cooling bore
(`.csgDiff` $\to$ `.left`), compacting the tape from `24` AST nodes down to `6` AST nodes while
preserving exact point evaluations inside $B$! -/
example :
    let statorCore : FRepExpr := .offset 100 (.add (.sq .varX) (.sq .varY))
    let mountingLug : FRepExpr := .offset 4 (.add (.sq (.sub .varX (.const 20))) (.sq .varY))
    let coolingBore : FRepExpr := .offset 4 (.add (.sq (.add .varX (.const 20))) (.sq .varY))
    let fullStatorCsg : FRepExpr := .csgDiff (.csgUnion statorCore mountingLug) coolingBore
    let centerOctreeCell : Box3D :=
      { xIv := { lo := -2, hi := 2 }
        yIv := { lo := -2, hi := 2 }
        zIv := { lo := -2, hi := 2 } }
    let prunedTape := pruneFRepTape centerOctreeCell fullStatorCsg
    frepNodeCount fullStatorCsg = 24 ∧
    frepNodeCount prunedTape = 6 ∧
    frepNodeCount prunedTape < frepNodeCount fullStatorCsg ∧
    prunedTape = statorCore ∧
    evalFRepPoint 1 (-1) 0 prunedTape = evalFRepPoint 1 (-1) 0 fullStatorCsg := by
  decide +kernel
end Obend.Hardware.GeometryCAM

-- from Obend/Hardware/GeometryCAM.lean:2514: end-to-end run on a fixture (16 lines); worth a pre-push run, not every library build
namespace Obend.Hardware.GeometryCAM
open Obend.Hardware.Accelerators
/-- **Golden Self-Certified Dual-Interval Gradient & Swept-Volume Verification
(`golden_certified_lipschitz_swept_volume_verified`)**:
1. On a 3D plane $f_{\text{plane}}(x, y, z) = 3x - 4y + 2z - 10$, `evalFRepGradBox` derives exact
   constant gradient intervals $([3, 3], [-4, -4], [2, 2])$ and `computeCertifiedLipschitzBox = 9`,
2. On a non-Eikonal quadratic sphere polynomial $f_{\text{sphere}}(x, y, z) = x^2 + y^2 + z^2 - 100$
   over box $B = [10, 12]^3$, `evalFRepGradBox` derives $([-24, 24], [-24, 24], [-24, 24])$ and
   `computeCertifiedLipschitzBox = 72` ($\neq 1$!),
3. `synthesizeCertifiedSweptVolume` automatically pads the swept volume by `computeCertifiedStepPad`
   and certifies `checkVoxelNoGouge = true` without any caller-supplied Lipschitz parameter! -/
example :
    let box : Box3D :=
      { xIv := { lo := 10, hi := 12 }
      , yIv := { lo := 10, hi := 12 }
      , zIv := { lo := 10, hi := 12 } }
    let plane : FRepExpr :=
      .offset 10 (.add (.sub (.scalePos 3 .varX) (.scalePos 4 .varY)) (.scalePos 2 .varZ))
    let sphere : FRepExpr :=
      .offset 100 (.add (.add (.sq .varX) (.sq .varY)) (.sq .varZ))
    evalFRepGradBox box plane =
      ({ lo := 3, hi := 3 }, { lo := -4, hi := -4 }, { lo := 2, hi := 2 }) ∧
    computeCertifiedLipschitzBox box plane = 9 ∧
    computeCertifiedLipschitzBox box (.scalePos 100 plane) = 900 ∧
    computeCertifiedLipschitzBox box sphere = 72 ∧
    checkVoxelNoGouge box (synthesizeCertifiedSweptVolume box sphere [(0, 0, 0)] 2) = true := by
  decide +kernel
end Obend.Hardware.GeometryCAM

-- from Obend/Hardware/Kinematics.lean:297: end-to-end run on a fixture (14 lines); worth a pre-push run, not every library build
namespace Obend.Hardware.Kinematics
/-- Golden Verification of Featherstone Spatial Algebra, Ruckig S-Curve & 5-Axis Abbe Compensation. -/
example :
    let twist : SpatialTwist6D := { ang := { x := 3, y := -4, z := 12 }, lin := { x := 50, y := -20, z := 10 } }
    let mom   : SpatialWrench6D := { torque := { x := 90, y := -80, z := 240 }, force := { x := 250, y := -100, z := 50 } }
    let st0   : RuckigState1D := { posScaled6 := 0, velScaled2 := 0, acc := 0 }
    let st2   := stepRuckigSegment (stepRuckigSegment st0 5 4) (-5) 4
    let target : Vec3 := { x := 100000, y := 200000, z := 50000 }
    let linErr : Vec3 := { x := 12, y := -8, z := 5 }
    let angErr : Vec3 := { x := 2, y := -3, z := 1 }
    let arm    : Vec3 := { x := 0, y := 0, z := 150 }
    spatialPower (spatialCrossForce twist mom) twist = 0 ∧
    st2.acc = 0 ∧
    st2.velScaled2 = 160 ∧
    evalUncompensatedTipPos3D (evalAbbeCompensatedCmd3D target linErr angErr arm) linErr angErr arm = target := by
  decide +kernel
end Obend.Hardware.Kinematics

-- from Obend/Hardware/OpenUSD.lean:898: end-to-end run on a fixture (16 lines); worth a pre-push run, not every library build
namespace Obend.Hardware.OpenUSD
open Obend.Core.Term (Term Evaluates Value Step Steps)
open Obend.Core.Data (Data)
open Obend.Law (CellContract Holds Admits Narrows CellTrace cellContract_relaw_sound
  cellContract_trace_sound law3 guard okT andT falseT leNat natT lawEnv scons_zero scons_succ
  admits_iff guard_ok andT_true leNat_true natT_eval evaluates_self evaluates_step
  evaluates_steps evaluates_of_steps evaluates_ifBool)
open Obend.Hardware.Accelerators
open Obend.Hardware.GeometryCAM
/-- Golden OpenUSD Relocation, Affine SDF Cancellation & Temporal Persistence Verification. -/
example :
    let p := ["Factory", "Draft", "Stator", "Slot01"]
    let af : AffineForm1D := { c0 := 50, c1 := 7, c2 := 5 }
    let af3 : AffineForm3D := { c0 := 50, cx := 7, cy := 5, cz := 3, err := 0 }
    let t0 : UsdPhysicalState := { timeCode := 0,   wallThicknessUm := 5000, peakTempMilliC := 25000,  receiptDigest := 101 }
    let t1 : UsdPhysicalState := { timeCode := 10,  wallThicknessUm := 2200, peakTempMilliC := 65000,  receiptDigest := 202 }
    let t2 : UsdPhysicalState := { timeCode := 20,  wallThicknessUm := 1500, peakTempMilliC := 55000,  receiptDigest := 303 }
    let t3 : UsdPhysicalState := { timeCode := 100, wallThicknessUm := 1500, peakTempMilliC := 122000, receiptDigest := 404 }
    applyUsdRelocate ["Prod", "LCDrives"] ["Factory", "Draft"]
      (applyUsdRelocate ["Factory", "Draft"] ["Prod", "LCDrives"] p) = p ∧
    (AffineForm1D.sub af af).toInterval = { lo := 0, hi := 0 } ∧
    (AffineForm3D.sub af3 af3).toInterval = { lo := 0, hi := 0 } ∧
    checkPartLifecycleInvariant 1200 180000 t0 = true ∧
    checkUsdTimeSampleChain 1200 180000 t0 [t1, t2, t3] = true ∧
    checkPartLifecycleInvariant 1200 180000 (finalUsdState t0 [t1, t2, t3]) = true := by
  decide +kernel
end Obend.Hardware.OpenUSD

-- from Obend/Hardware/Retiming.lean:491: a 7-line closed evaluation; worth a pre-push run
namespace Obend.Hardware.Retiming
open Obend.Hardware.Process
/-- Theorem: `solveVerifiedRetiming? 2 macUnretimedGraph 1800` constructively discovers a valid
retiming certificate `cert` (`r(1) = 1`) that passes `checkRetimingCert` at 500 MHz (`2000 ps`) on `corner7nm_SS`! -/
example :
    (match solveVerifiedRetiming? 2 macUnretimedGraph 1800 with
     | some cert =>
       checkRetimingCert macUnretimedGraph cert corner7nm_SS 2000 &&
       ((applyRetimingCertToGraph macUnretimedGraph cert).edges.map (·.origRegs) == [1, 1])
     | none => false) = true := by
  decide +kernel
end Obend.Hardware.Retiming
