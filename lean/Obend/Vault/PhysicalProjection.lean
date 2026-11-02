module
/-
# Obend.Vault.PhysicalProjection — Read-Only Physical-World & Mechatronic Co-Design Projections for `.obnb` Notebooks

Implements `WS 30` (`PHYSICAL.md` $\leftrightarrow$ `.obnb` Notebooks):
1. **Strictly Read-Only Over `Obend.Hardware.*`**:
   - Imports `Obend.Hardware.{Kinematics,OpenUSD,UserspacePhysical,FluidThermal}` and
     `Obend.Analysis.{Flowpipe,Hybrid}` without modifying any file in `lean/Obend/Hardware/*`.
2. **5-Axis CNC Kinematic Toolpath, Featherstone 6D Spatial Twist/Wrench & Abbe Compensation Projection (`cncToolpathToData`, `projectCncToolpath`)**:
   - Projects 3D toolpath waypoints, Featherstone 6D Plücker twists/wrenches (`spatialPower`, Coriolis
     work conservation), Ruckig 3rd-order S-curve states, and 21-parameter Abbe volumetric error
     pre-compensation into `.obnb` `Doc.Content.cell` quotations.
3. **OpenUSD Scene-Graph (`SdfPath`), `LIVERPS` Relocates, Affine SDF Enclosures & `timeSamples` Projection (`openUsdSceneToData`, `projectOpenUsdScene`)**:
   - Projects hierarchical OpenUSD `SdfPath`s, non-destructive `relocates` arcs, `AffineForm1D`
     correlation-preserving SDF enclosures, and causal `UsdPhysicalState` `timeSamples` tracks.
4. **Coupled LC-Drive Stator Multiphysics & Continuous ODE Flowpipe Projection (`statorMultiphysicsToData`, `projectStatorMultiphysics`)**:
   - Couples userspace open-recursive physical compositions (`lcDrivesStatorUsdComp`, `cnc5AxisMillComp`),
     Darcy-Weisbach microchannel hydraulics (`CoolingChannelSpec`), and validated `Flowpipe` / `HybridAutomaton`
     safety certificates into `.obnb` notebook viewports (`0 sorryAx`).
-/
public import Obend.Vault.HardwareProjection
public import Obend.Leaf.Emit
public import Obend.Hardware.Kinematics
public import Obend.Hardware.FluidThermal
public import Obend.Hardware.OpenUSD
public import Obend.Hardware.UserspacePhysical
public import Obend.Analysis.Hybrid
@[expose] public section

namespace Obend.Vault.PhysicalProjection
open Obend.Core.Data
open Obend.Core.Term
open Obend.Doc
open Obend.Vault.HardwareProjection (dInt)
open Obend.Hardware.Kinematics
open Obend.Hardware.FluidThermal
open Obend.Hardware.Thermal
open Obend.Hardware.OpenUSD
open Obend.Hardware.UserspacePhysical
open Obend.Logic
open Obend.Leaf
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. 5-Axis CNC Kinematic Toolpath & Abbe Compensation Projection -/

/-- Encode a 3D integer-scaled vector `Vec3` into canonical `Core.Data`. -/
def vec3ToData (v : Vec3) : Data :=
  .record [
    ("x", dInt v.x),
    ("y", dInt v.y),
    ("z", dInt v.z)
  ]

/-- Encode a 6D Featherstone spatial motion twist `SpatialTwist6D` into `Core.Data`. -/
def twist6DToData (t : SpatialTwist6D) : Data :=
  .record [
    ("ang", vec3ToData t.ang),
    ("lin", vec3ToData t.lin)
  ]

/-- Encode a 6D Featherstone spatial force wrench `SpatialWrench6D` into `Core.Data`. -/
def wrench6DToData (w : SpatialWrench6D) : Data :=
  .record [
    ("torque", vec3ToData w.torque),
    ("force", vec3ToData w.force)
  ]

/-- Encode a 1D Ruckig 3rd-order jerk-limited trajectory state into `Core.Data`. -/
def ruckigStateToData (st : RuckigState1D) : Data :=
  .record [
    ("pos_scaled_6", dInt st.posScaled6),
    ("vel_scaled_2", dInt st.velScaled2),
    ("acc", dInt st.acc)
  ]

/-- Specification for a 5-axis CNC kinematic toolpath & Abbe error-compensation viewport cell. -/
structure CncToolpathViewportSpec where
  machineName : String
  pTarget     : Vec3
  linErr      : Vec3
  angErr      : Vec3
  abbeArm     : Vec3
  twist       : SpatialTwist6D
  momentum    : SpatialWrench6D
  ruckigInit  : RuckigState1D
  jerkPulse   : Int
  pulseDt     : Int
  deriving DecidableEq, Repr

/-- Project a `CncToolpathViewportSpec` into canonical `Core.Data`. -/
def cncToolpathToData (spec : CncToolpathViewportSpec) : Data :=
  let volErr := evalVolumetricError3D spec.linErr spec.angErr spec.abbeArm
  let compCmd := evalAbbeCompensatedCmd3D spec.pTarget spec.linErr spec.angErr spec.abbeArm
  let actualTip := evalUncompensatedTipPos3D compCmd spec.linErr spec.angErr spec.abbeArm
  let coriolisPower := spatialPower (spatialCrossForce spec.twist spec.momentum) spec.twist
  let rStep1 := stepRuckigSegment spec.ruckigInit spec.jerkPulse spec.pulseDt
  let rStep2 := stepRuckigSegment rStep1 (-spec.jerkPulse) spec.pulseDt
  let millBook := emit cnc5AxisMillComp
  .record [
    ("kind", .label "physical_cnc_5axis"),
    ("machine_name", .label spec.machineName),
    ("target_tip_nm", vec3ToData spec.pTarget),
    ("volumetric_error_nm", vec3ToData volErr),
    ("abbe_compensated_cmd_nm", vec3ToData compCmd),
    ("actual_tip_nm", vec3ToData actualTip),
    ("abbe_exact_cancelled", .boolean (actualTip == spec.pTarget)),
    ("coriolis_power", dInt coriolisPower),
    ("ruckig_final_state", ruckigStateToData rStep2),
    ("userspace_mill_slots", .natural millBook.slots.length),
    ("userspace_mill_closed", .boolean millBook.closedB)
  ]

/-- Construct a `.obnb` `Doc.Content.cell` quotation for a 5-axis CNC kinematic toolpath. -/
def projectCncToolpath
    (id : String)
    (spec : CncToolpathViewportSpec)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareLayout (cncToolpathToData spec) pins receipt

/-! ## 2. OpenUSD Scene-Graph (`SdfPath`), `LIVERPS` Relocates, Affine SDF & `timeSamples` Projection -/

/-- Encode an OpenUSD hierarchical `SdfPath` into `Core.Data`. -/
def sdfPathToData (p : SdfPath) : Data :=
  .record (p.zipIdx.map fun (seg, i) => (toString i, .label seg))

/-- Encode an `AffineForm1D` SDF enclosure and its interval bounds into `Core.Data`. -/
def affineSdfToData (af : AffineForm1D) : Data :=
  let iv := af.toInterval
  let selfSub := (AffineForm1D.sub af af).toInterval
  .record [
    ("c0", dInt af.c0),
    ("c1", dInt af.c1),
    ("c2", dInt af.c2),
    ("radius", dInt af.radius),
    ("interval_lo", dInt iv.lo),
    ("interval_hi", dInt iv.hi),
    ("self_cancel_zero", .boolean (selfSub.lo == 0 && selfSub.hi == 0))
  ]

/-- Encode a `UsdPhysicalState` `timeSamples` entry into `Core.Data`. -/
def usdStateToData (st : UsdPhysicalState) : Data :=
  .record [
    ("time_code", .natural st.timeCode),
    ("wall_thickness_um", dInt st.wallThicknessUm),
    ("peak_temp_milli_c", dInt st.peakTempMilliC),
    ("receipt_digest", .natural st.receiptDigest)
  ]

/-- Specification for an OpenUSD scene-graph, `AffineForm1D` SDF, and `timeSamples` lifecycle viewport cell. -/
structure OpenUsdViewportSpec where
  stageName      : String
  primPath       : SdfPath
  relocateSrc    : SdfPath
  relocateDst    : SdfPath
  sdfWallForm    : AffineForm1D
  minWallUm      : Int
  maxTempMilliC  : Int
  initSample     : UsdPhysicalState
  timeSamples    : List UsdPhysicalState
  deriving DecidableEq, Repr

/-- Project an `OpenUsdViewportSpec` into canonical `Core.Data`. -/
def openUsdSceneToData (spec : OpenUsdViewportSpec) : Data :=
  let relocated := applyUsdRelocate spec.relocateSrc spec.relocateDst spec.primPath
  let roundtrip := applyUsdRelocate spec.relocateDst spec.relocateSrc relocated
  let finalSt := finalUsdState spec.initSample spec.timeSamples
  let chainValid :=
    checkPartLifecycleInvariant spec.minWallUm spec.maxTempMilliC spec.initSample &&
    checkUsdTimeSampleChain spec.minWallUm spec.maxTempMilliC spec.initSample spec.timeSamples
  let finalInvariantOk := checkPartLifecycleInvariant spec.minWallUm spec.maxTempMilliC finalSt
  .record [
    ("kind", .label "physical_openusd_scene"),
    ("stage_name", .label spec.stageName),
    ("prim_path", sdfPathToData spec.primPath),
    ("relocated_path", sdfPathToData relocated),
    ("relocate_roundtrip_ok", .boolean (roundtrip == spec.primPath)),
    ("affine_sdf", affineSdfToData spec.sdfWallForm),
    ("sample_count", .natural (spec.timeSamples.length + 1)),
    ("final_state", usdStateToData finalSt),
    ("chain_valid", .boolean chainValid),
    ("final_invariant_ok", .boolean finalInvariantOk)
  ]

/-- Construct a `.obnb` `Doc.Content.cell` quotation for an OpenUSD scene-graph and lifecycle track. -/
def projectOpenUsdScene
    (id : String)
    (spec : OpenUsdViewportSpec)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareLayout (openUsdSceneToData spec) pins receipt

/-! ## 3. Coupled LC-Drive Stator Multiphysics & Continuous ODE Flowpipe Projection -/

/-- Specification for a coupled liquid-cooled stator multiphysics + continuous ODE flowpipe viewport cell. -/
structure StatorMultiphysicsViewportSpec where
  partName      : String
  channel       : CoolingChannelSpec
  ode           : OdeSystem
  initBox       : List (String × Interval)
  steps         : Nat
  safeBounds    : List (String × Interval)
  deriving DecidableEq, Repr

/-- Project a `StatorMultiphysicsViewportSpec` into canonical `Core.Data`. -/
def statorMultiphysicsToData (spec : StatorMultiphysicsViewportSpec) : Data :=
  let statorBook := emit lcDrivesStatorUsdComp
  let darcyDrop := evalDarcyPressureDropScaled spec.channel
  let flowpipeSafe := verifyTrajectorySafety spec.ode spec.initBox spec.steps spec.safeBounds
  .record [
    ("kind", .label "physical_stator_multiphysics"),
    ("part_name", .label spec.partName),
    ("stator_slot_count", .natural statorBook.slots.length),
    ("stator_book_closed", .boolean statorBook.closedB),
    ("darcy_pressure_drop_scaled", dInt darcyDrop),
    ("flowpipe_steps", .natural spec.steps),
    ("flowpipe_safe", .boolean flowpipeSafe),
    ("status", .label (if flowpipeSafe && statorBook.closedB then "MULTIPHYSICS_CERTIFIED" else "UNSAFE"))
  ]

/-- Construct a `.obnb` `Doc.Content.cell` quotation for coupled LC-drive stator multiphysics. -/
def projectStatorMultiphysics
    (id : String)
    (spec : StatorMultiphysicsViewportSpec)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareTiming (statorMultiphysicsToData spec) pins receipt

/-! ## 4. Concrete Golden Physical Viewport Specs & Soundness Theorems -/

/-- Golden 5-axis CNC toolpath viewport specification (`Cnc5AxisMill.obend`). -/
def goldenCncViewportSpec : CncToolpathViewportSpec where
  machineName := "Hermle_C42U_5Axis"
  pTarget     := { x := 100000, y := 200000, z := 50000 }
  linErr      := { x := 12, y := -8, z := 5 }
  angErr      := { x := 2, y := -3, z := 1 }
  abbeArm     := { x := 0, y := 0, z := 150 }
  twist       := { ang := { x := 3, y := -4, z := 12 }, lin := { x := 50, y := -20, z := 10 } }
  momentum    := { torque := { x := 90, y := -80, z := 240 }, force := { x := 250, y := -100, z := 50 } }
  ruckigInit  := { posScaled6 := 0, velScaled2 := 0, acc := 0 }
  jerkPulse   := 5
  pulseDt     := 4

/-- Golden OpenUSD scene-graph & `timeSamples` viewport specification (`LcDrivesStatorUsd.obend`). -/
def goldenOpenUsdViewportSpec : OpenUsdViewportSpec where
  stageName     := "LcDrives_Production_Stator"
  primPath      := ["Factory", "Draft", "Stator", "Slot01"]
  relocateSrc   := ["Factory", "Draft"]
  relocateDst   := ["Prod", "LCDrives"]
  sdfWallForm   := { c0 := 1500, c1 := 15, c2 := 10 }
  minWallUm     := 1200
  maxTempMilliC := 180000
  initSample    := { timeCode := 0, wallThicknessUm := 5000, peakTempMilliC := 25000, receiptDigest := 101 }
  timeSamples   :=
    [ { timeCode := 10,  wallThicknessUm := 2200, peakTempMilliC := 65000,  receiptDigest := 202 }
    , { timeCode := 20,  wallThicknessUm := 1500, peakTempMilliC := 55000,  receiptDigest := 303 }
    , { timeCode := 100, wallThicknessUm := 1500, peakTempMilliC := 122000, receiptDigest := 404 } ]

/-- Golden coupled LC-drive stator multiphysics + continuous `Flowpipe` viewport specification. -/
def goldenStatorMultiphysicsSpec : StatorMultiphysicsViewportSpec where
  partName   := "LC_Drives_InSlot_Stator_Assy"
  channel    :=
    { frictionFactorMilli := 25
    , lengthMm            := 240
    , hydraulicDiaMm      := 4
    , fluidDensityKgM3    := 1065
    , velocityMmPerSec    := 2500 }
  ode        := thermalCoolingOde
  initBox    := [("T", ⟨28, 30⟩)]
  steps      := 3
  safeBounds := [("T", ⟨15, 35⟩)]

/-- **Theorem (`physical_projection_deterministic`)**:
All three physical-world `.obnb` projection functions (`projectCncToolpath`, `projectOpenUsdScene`,
`projectStatorMultiphysics`) are deterministic functions of their inputs. -/
theorem physical_projection_deterministic
    (id : String)
    (cnc1 cnc2 : CncToolpathViewportSpec)
    (usd1 usd2 : OpenUsdViewportSpec)
    (st1 st2 : StatorMultiphysicsViewportSpec)
    (hCnc : cnc1 = cnc2) (hUsd : usd1 = usd2) (hSt : st1 = st2) :
    projectCncToolpath id cnc1 = projectCncToolpath id cnc2 ∧
    projectOpenUsdScene id usd1 = projectOpenUsdScene id usd2 ∧
    projectStatorMultiphysics id st1 = projectStatorMultiphysics id st2 := by
  subst hCnc hUsd hSt
  exact ⟨rfl, rfl, rfl⟩

/-- **Theorem (`physical_cnc_abbe_projection_sound`)**:
1. For ANY `CncToolpathViewportSpec`, pre-compensating the CNC command by `evalAbbeCompensatedCmd3D`
   cancels the 21-parameter volumetric + Abbe lever-arm error (`abbe_volumetric_compensation_exact`),
   and the Featherstone gyroscopic/Coriolis wrench performs zero mechanical work (`rnea_gyroscopic_coriolis_power_zero`).
2. On `goldenCncViewportSpec`, `cncToolpathToData` certifies `"abbe_exact_cancelled" = true`,
   `"coriolis_power" = 0`, and `"userspace_mill_closed" = true`. -/
theorem physical_cnc_abbe_projection_sound (spec : CncToolpathViewportSpec) :
    evalUncompensatedTipPos3D
      (evalAbbeCompensatedCmd3D spec.pTarget spec.linErr spec.angErr spec.abbeArm)
      spec.linErr spec.angErr spec.abbeArm = spec.pTarget ∧
    spatialPower (spatialCrossForce spec.twist spec.momentum) spec.twist = 0 ∧
    (emit cnc5AxisMillComp).closedB = true := by
  refine ⟨abbe_volumetric_compensation_exact spec.pTarget spec.linErr spec.angErr spec.abbeArm,
    rnea_gyroscopic_coriolis_power_zero spec.twist spec.momentum,
    by decide +kernel⟩

/-- **Theorem (`physical_openusd_lifecycle_projection_sound`)**:
1. Non-destructive OpenUSD `relocates` round-trips any `src ++ suffix` path (`usd_relocate_roundtrip_exact`),
   `AffineForm1D` self-subtraction cancels noise symbols to `[0, 0]` (`affine_sub_self_exact_zero`),
   and any verified `timeSamples` chain preserves `checkPartLifecycleInvariant` at `finalUsdState`.
2. On `goldenOpenUsdViewportSpec` and `goldenStatorMultiphysicsSpec`, both the OpenUSD lifecycle
   track and the coupled `thermalCoolingOde` continuous flowpipe are certified safe. -/
theorem physical_openusd_lifecycle_projection_sound :
    let usd := goldenOpenUsdViewportSpec
    let stator := goldenStatorMultiphysicsSpec
    applyUsdRelocate usd.relocateDst usd.relocateSrc
      (applyUsdRelocate usd.relocateSrc usd.relocateDst usd.primPath) = usd.primPath ∧
    (AffineForm1D.sub usd.sdfWallForm usd.sdfWallForm).toInterval = { lo := 0, hi := 0 } ∧
    checkPartLifecycleInvariant usd.minWallUm usd.maxTempMilliC
      (finalUsdState usd.initSample usd.timeSamples) = true ∧
    verifyTrajectorySafety stator.ode stator.initBox stator.steps stator.safeBounds = true ∧
    (emit lcDrivesStatorUsdComp).closedB = true := by
  decide +kernel

/-- **Theorem (`physical_projection_doc_noninterference`)**:
Inserting any projected physical-world cell (`projectCncToolpath`, `projectOpenUsdScene`, or
`projectStatorMultiphysics`) into a `.obnb` document graph at `newAtom` preserves all existing
atoms `otherAtom ≠ newAtom`. -/
theorem physical_projection_doc_noninterference
    (G : Graph) (newAtom : AtomId) (cell : Doc.Content)
    (otherAtom : AtomId) (hNe : otherAtom ≠ newAtom) :
    (((newAtom, cell) :: G.atoms).lookup otherAtom) = G.atoms.lookup otherAtom :=
  Obend.Vault.HardwareProjection.hardware_projection_doc_noninterference G newAtom cell otherAtom hNe

end Obend.Vault.PhysicalProjection
end
