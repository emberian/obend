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
import Obend.Hardware.PowerElectronics
import Obend.Hardware.Retiming
import Obend.Hardware.UserspacePhysical

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
   datasheet freshness, QFN-16 courtyard fit, and $400\,\text{mV}$ CMOS noise margins,
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
      goldenQfn16Courtyard
      goldenFreshDatasheetCite
      "procurement_scout"
      defaultEdaFacts = .admitted ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      overbudgetSecondSourcePart
      lvcmos33ReceiverSpec
      400
      goldenQfn16Courtyard
      goldenFreshDatasheetCite
      "procurement_scout"
      defaultEdaFacts = .refusedBySmartContract "bom_budget" "bom_budget" ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      goldenSecondSourcePart
      lvcmos33ReceiverSpec
      400
      goldenQfn16Courtyard
      { goldenFreshDatasheetCite with currentDatasheetHash := 0x9A4F2C02 }
      "procurement_scout"
      defaultEdaFacts = .refusedByPhysics "stale-datasheet-cite" := by
  decide +kernel
end Obend.Hardware.AgenticEDA

-- from Obend/Hardware/GeometryCAM.lean:662: end-to-end run on a fixture (16 lines); worth a pre-push run, not every library build
namespace Obend.Hardware.GeometryCAM
open Obend.Hardware.Thermal
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
open Obend.Hardware.Thermal
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

-- from Obend/Hardware/GeometryCAM.lean:2672: end-to-end run on a fixture (20 lines); worth a pre-push run, not every library build
namespace Obend.Hardware.GeometryCAM
open Obend.Hardware.Thermal
open Obend.Hardware.Accelerators
/-- **Golden 5-Axis Stator-Slot Microchannel Milling & Evolutionary Search Certificate
(`golden_geometry_cam_evolutionary_search_verified`)**:
Verifies by kernel evaluation (`decide +kernel`):
1. Octree exterior pruning of a 3D F-Rep sphere $x^2 + y^2 + z^2 - 100$ over box $[10, 12]^3$ (`lo = 200 > 0`),
2. Zero-gouge CAM material removal on the stator tooth bounding box,
3. Machine-tool deflection + servo-lag error ($3500\,\text{nm} \le 5000\,\text{nm}$ tolerance), and
4. Evolutionary filtering of a 3-candidate design population (rejecting a gouging candidate and a
   chattering candidate, and selecting the verified high-torque candidate `#2`). -/
example :
    let sphereR10 := FRepExpr.offset 100 (.add (.add (.sq .varX) (.sq .varY)) (.sq .varZ))
    let farBox : Box3D :=
      { xIv := { lo := 10, hi := 12 }
        yIv := { lo := 10, hi := 12 }
        zIv := { lo := 10, hi := 12 } }
    let candGouge : PhysicalDesignCandidate :=
      { candidateId := 1, sweptLo := -5, surfaceErrNm := 2000, maxTolNm := 5000,
        apUm := 1500, kfScaled := 2, negReFrfScaled := 3, chatterLimitScaled := 25000, performanceScore := 950 }
    let candVerified : PhysicalDesignCandidate :=
      { candidateId := 2, sweptLo := 200, surfaceErrNm := 3500, maxTolNm := 5000,
        apUm := 2000, kfScaled := 2, negReFrfScaled := 3, chatterLimitScaled := 25000, performanceScore := 920 }
    let candChatter : PhysicalDesignCandidate :=
      { candidateId := 3, sweptLo := 150, surfaceErrNm := 3000, maxTolNm := 5000,
        apUm := 6000, kfScaled := 2, negReFrfScaled := 3, chatterLimitScaled := 25000, performanceScore := 980 }
    (evalFRepInterval farBox sphereR10).lo = 200 ∧
    checkVoxelNoGouge farBox sphereR10 = true ∧
    evalMachiningDimensionalErrorNm 50 10 3 1000 = 3500 ∧
    (filterVerifiedDesigns 800 [candGouge, candVerified, candChatter]).map (·.candidateId) = [2] := by
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
open Obend.Hardware.Thermal
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

-- from Obend/Hardware/PowerElectronics.lean:352: a 7-line closed evaluation; worth a pre-push run
namespace Obend.Hardware.PowerElectronics
open Obend.Hardware.Thermal
open Obend.Hardware.Magnetics
open Obend.Hardware.FluidThermal
/-- **Theorem (`ms350_7level_fcml_36x_inductance_and_6x_voltage_reduction`)**:
Upgrading from a 2-level inverter (`M = 1`) to a 7-level Mission Power `MS350` FCML stage (`M = 6`)
on a $1500\,\text{V}_{\text{DC}}$ solar string:
1. Reduces nominal per-cell switch blocking voltage $6\times$ from $1500\,\text{V}$ to $250\,\text{V}$,
2. Multiplies effective inductor ripple frequency $6\times$ (e.g. $50\,\text{kHz} \to 300\,\text{kHz}$), and
3. Reduces required filter inductance $M^2 = 36\times$ from $360\,\mu\text{H}$ to $10\,\mu\text{H}$! -/
example :
    evalFcmlCellBlockingVoltageV 1500 1 = 1500 ∧
    evalFcmlCellBlockingVoltageV 1500 6 = 250 ∧
    evalFcmlEffectiveRippleFreqHz 50000 6 = 300000 ∧
    evalFcmlRequiredInductanceUh 360 1 = 360 ∧
    evalFcmlRequiredInductanceUh 360 6 = 10 := by
  decide +kernel
end Obend.Hardware.PowerElectronics

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

-- from Obend/Hardware/UserspacePhysical.lean:124: end-to-end run on a fixture (12 lines); worth a pre-push run, not every library build
namespace Obend.Hardware.UserspacePhysical
open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
/-- **Static `super` Elimination & Slot Dependency Certificate**. -/
example :
    let B := emit lcDrivesStatorUsdComp
    B.slots = ["massKg", "camSurfaceErrorUm", "thermalResistance", "sdfMargin", "peakWindingTemp"] ∧
    B.defs.map (fun d => (d.member, d.slot, d.kind, d.reads)) =
      [ ("massKg", 0, .cell, [])
      , ("camSurfaceErrorUm", 1, .method, [])
      , ("thermalResistance", 2, .cell, [])
      , ("sdfMargin", 3, .method, [])
      , ("peakWindingTemp", 4, .method, [2])
      ] ∧
    B.closedB = true := by
  decide +kernel
end Obend.Hardware.UserspacePhysical

-- from Obend/Hardware/UserspacePhysical.lean:177: a 20-line closed evaluation; worth a pre-push run
namespace Obend.Hardware.UserspacePhysical
open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
/-- **End-to-End Userspace `stdlib/physical/LcDrivesStator.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
example :
    (match compileBookToRtl "lc_drives_userspace_stator" (emit lcDrivesStatorUsdComp) with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 8#64) (fun _ => 0#64) ==
         [ ("out_massKg", 395#64)
         , ("out_camSurfaceErrorUm", 34#64)
         , ("out_thermalResistance", 9#64)
         , ("out_sdfMargin", 24#64)
         , ("out_peakWindingTemp", 122#64)
         ]) &&
       (match m.wires[3]? with
        | some wSdf =>
          let (rSdf, _, codeSdf) := compileRtlExprToAmdGpu 1 wSdf.expr
          let finalVgprs :=
            runAmdGpuVop64Prog (fun _ => 8#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeSdf
          finalVgprs rSdf == 24#64
        | none => false)
     | none => false) = true := by
  decide +kernel
end Obend.Hardware.UserspacePhysical

-- from Obend/Hardware/UserspacePhysical.lean:199: a 24-line closed evaluation; worth a pre-push run
namespace Obend.Hardware.UserspacePhysical
open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
/-- **End-to-End Userspace `stdlib/physical/Cnc5AxisMill.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
example :
    (match compileBookToRtl "cnc_5axis_userspace_mill" (emit cnc5AxisMillComp) with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 6#64) (fun _ => 0#64) ==
         [ ("out_servoLagUm", 6#64)
         , ("out_endMillDeflectionUm", 12#64)
         , ("out_abbeAngularDriftUm", 6#64)
         , ("out_commandedAxisAt10mmUm", 10024#64)
         , ("out_totalVolumetricErrorUm", 26#64)
         ]) &&
       (match m.wires[3]?, m.wires[4]? with
        | some wCmd, some wErr =>
          let (rCmd, _, codeCmd) := compileRtlExprToAmdGpu 1 wCmd.expr
          let (rErr, _, codeErr) := compileRtlExprToAmdGpu 1 wErr.expr
          let vgprsCmd :=
            runAmdGpuVop64Prog (fun _ => 6#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeCmd
          let vgprsErr :=
            runAmdGpuVop64Prog (fun _ => 6#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeErr
          vgprsCmd rCmd == 10024#64 &&
          vgprsErr rErr == 26#64
        | _, _ => false)
     | none => false) = true := by
  decide +kernel
end Obend.Hardware.UserspacePhysical

-- from Obend/Hardware/UserspacePhysical.lean:967: a 16-line closed evaluation; worth a pre-push run
namespace Obend.Hardware.UserspacePhysical
open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
/-- **Theorem (`userspace_obend_bitwise_q32_surface_to_rtl_verified`)**:
Elaborates `obendBitwiseQ32Source` through `Spec.Parse` + `Spec.Elaborate` + `FrontEnd.accept`,
synthesizes a `Composition` -> `Leaf.Book` -> `RtlModule` + `AmdGpuVop64Inst`, and proves that:
1. `StdBitwiseQ32` elaborates (the `#obend_decl` command succeeded; `Obend.Core.Check` translation validation),
2. `maskVal = (0xFF & 0x0F) | (1 << 4) = 15 | 16 = 31`,
3. `q32Scaled(10) = q32ToInt(qmul32(10 << 32, 3 << 32)) ^ (31 >> 1) = 30 ^ 15 = 17` in both
   the synchronous `RtlModule` (`evalModuleOutputs`) and the 64-bit AMD `CDNA3` VOP64 GPU kernel! -/
example :
    (match compileBookToRtl "bitwise_q32_rtl" StdBitwiseQ32.bitwiseQ32Inst_book with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 10#64) (fun _ => 0#64) ==
         [ ("out_maskVal", 31#64)
         , ("out_q32Scaled", 17#64) ]) &&
       (match m.wires[1]? with
        | some wScaled =>
          let (rOut, _, code) := compileRtlExprToAmdGpu 1 wScaled.expr
          let wireEnv := evalWireTable (fun _ => 10#64) (fun _ => 0#64) m.wires
          let vgprs := runAmdGpuVop64Prog (fun _ => 10#64) wireEnv (fun _ => 0#64) (fun _ => 0#64) code
          vgprs rOut == 17#64
        | none => false)
     | none => false) = true := by
  decide +kernel
end Obend.Hardware.UserspacePhysical
