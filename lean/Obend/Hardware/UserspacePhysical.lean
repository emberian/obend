module
/-
# Obend.Hardware.UserspacePhysical — Verified `.obend` Userspace Open-Recursive Physical Parts Lowered Through `Obend.Leaf` Into FPGA SystemVerilog RTL & AMD `CDNA3` GPU Wavefront ISA

Connects the executable `.obend` userspace physical engineering packages in
`lean/tests/obend-source/world/physical/`:
- `LcDrivesStatorUsd.obend` (`PhysicalStator`: `OuterJacketStator` -> `LcDrivesInSlotUpgrade` ->
  `FiveAxisFinishMilled`), and
- `Cnc5AxisMill.obend` (`Cnc5AxisMill`: `Uncompensated5AxisMill` -> `AbbeAndRuckigCompensatedMill`)

directly to `Obend.Logic.Composition`, `Obend.Leaf.Flatten` (`flatten_sound`), `Obend.Leaf.Emit`
(`book_sound`), `compileBookToRtl`, and `compileRtlExprToAmdGpu`.
-/
public import Obend.Leaf.Emit
public import Obend.Lower.Proofs.SelfAccelerate
public import Obend.Hardware.Kinematics
public import Obend.Hardware.OpenUSD
public import Obend.Hardware.FluidThermal
public import Obend.Hardware.GeometryCAM
@[expose] public section

namespace Obend.Hardware.UserspacePhysical
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators

set_option autoImplicit false

/-! ## 1. `LcDrivesStatorUsd.obend` as an Open-Recursive `Obend.Logic.Composition` -/

/-- Seed record for `PhysicalStator` (`seedStator()` in `LcDrivesStatorUsd.obend`). -/
def seedStatorFields : List (String × Term) :=
  [ ("thermalResistance", .nat 0)
  , ("massKg", .nat 0)
  , ("sdfMargin", .lam (.bound 0))
  , ("peakWindingTemp", .lam (.bound 0))
  , ("camSurfaceErrorUm", .lam (.bound 0))
  ]

/-- Layer 0 (innermost): `spec OuterJacketStator for PhysicalStator`. -/
def outerJacketStatorLayer : Layer where
  name := "LcDrivesStatorUsd.OuterJacketStator"
  metadata := .label "LcDrivesStatorUsd.OuterJacketStator"
  fields :=
    [ ("thermalResistance", .nat 29)
    , ("massKg", .nat 420)
    , ("sdfMargin", .lam (.binary .add (.bound 0) (.nat 10)))
    , ("peakWindingTemp",
        .lam (.binary .add (.nat 50)
          (.binary .multiply (.bound 0) (.get (.bound 2) "thermalResistance"))))
    , ("camSurfaceErrorUm", .lam (.binary .multiply (.bound 0) (.nat 4)))
    ]

/-- Layer 1 (middle): `spec LcDrivesInSlotUpgrade for PhysicalStator`. -/
def lcDrivesInSlotUpgradeLayer : Layer where
  name := "LcDrivesStatorUsd.LcDrivesInSlotUpgrade"
  metadata := .label "LcDrivesStatorUsd.LcDrivesInSlotUpgrade"
  fields :=
    [ ("thermalResistance", .nat 9)
    , ("sdfMargin",
        .lam (.binary .add (.app (.get (.bound 1) "sdfMargin") (.bound 0)) (.nat 6)))
    ]

/-- Layer 2 (outermost): `spec FiveAxisFinishMilled for PhysicalStator`. -/
def fiveAxisFinishMilledLayer : Layer where
  name := "LcDrivesStatorUsd.FiveAxisFinishMilled"
  metadata := .label "LcDrivesStatorUsd.FiveAxisFinishMilled"
  fields :=
    [ ("massKg", .nat 395)
    , ("camSurfaceErrorUm",
        .lam (.binary .add (.app (.get (.bound 1) "camSurfaceErrorUm") (.bound 0)) (.nat 2)))
    ]

/-- The full 3-layer open-recursive `Composition` for `lcDrivesProductionStator()`. -/
def lcDrivesStatorUsdComp : Composition where
  top := fiveAxisFinishMilledLayer
  below := [lcDrivesInSlotUpgradeLayer, outerJacketStatorLayer]
  seed := seedStatorFields

/-- **Closedness Certificate**: `lcDrivesStatorUsdComp` and its unresolved flattening are closed. -/
theorem lcDrivesStatorUsdComp_closed : lcDrivesStatorUsdComp.closedB = true := by
  decide +kernel

/-- **Vtable Flattening Soundness (`flatten_sound`)**. -/
theorem lcDrivesStatorUsd_flatten_sound (m : String) :
    .get lcDrivesStatorUsdComp.flatten m ≈b .get lcDrivesStatorUsdComp.object m :=
  flatten_sound lcDrivesStatorUsdComp lcDrivesStatorUsdComp_closed m

/-- **Leaf Book Emission Soundness (`book_sound`)**. -/
theorem lcDrivesStatorUsd_book_sound (m : String) :
    .get (emit lcDrivesStatorUsdComp).link m ≈b .get lcDrivesStatorUsdComp.object m :=
  book_sound lcDrivesStatorUsdComp lcDrivesStatorUsdComp_closed m

/-- **Static `super` Elimination & Slot Dependency Certificate**. -/
theorem lcDrivesStatorUsd_book_shape_verified :
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

/-! ## 2. `Cnc5AxisMill.obend` as an Open-Recursive `Obend.Logic.Composition` -/

/-- Seed record for `Cnc5AxisMill`. -/
def seedMillFields : List (String × Term) :=
  [ ("servoLagUm", .lam (.nat 0))
  , ("endMillDeflectionUm", .lam (.nat 0))
  , ("abbeAngularDriftUm", .lam (.nat 0))
  , ("commandedAxisAt10mmUm", .lam (.nat 10000))
  , ("totalVolumetricErrorUm", .lam (.nat 0))
  ]

/-- Layer 0 (innermost): `spec Uncompensated5AxisMill for Cnc5AxisMill`. -/
def uncompensated5AxisMillLayer : Layer where
  name := "Cnc5AxisMill.Uncompensated5AxisMill"
  metadata := .label "Cnc5AxisMill.Uncompensated5AxisMill"
  fields :=
    [ ("servoLagUm", .lam (.binary .multiply (.bound 0) (.nat 5)))
    , ("endMillDeflectionUm", .lam (.binary .multiply (.bound 0) (.nat 6)))
    , ("abbeAngularDriftUm", .lam (.binary .multiply (.bound 0) (.nat 4)))
    , ("commandedAxisAt10mmUm", .lam (.nat 10000))
    , ("totalVolumetricErrorUm",
        .lam
          (.binary .add
            (.binary .add
              (.app (.get (.bound 2) "servoLagUm") (.nat 10))
              (.app (.get (.bound 2) "endMillDeflectionUm") (.nat 5)))
            (.app (.get (.bound 2) "abbeAngularDriftUm") (.bound 0))))
    ]

/-- Layer 1 (outermost): `spec AbbeAndRuckigCompensatedMill for Cnc5AxisMill`. -/
def abbeAndRuckigCompensatedMillLayer : Layer where
  name := "Cnc5AxisMill.AbbeAndRuckigCompensatedMill"
  metadata := .label "Cnc5AxisMill.AbbeAndRuckigCompensatedMill"
  fields :=
    [ ("servoLagUm", .lam (.binary .multiply (.bound 0) (.nat 1)))
    , ("endMillDeflectionUm", .lam (.binary .multiply (.bound 0) (.nat 2)))
    , ("abbeAngularDriftUm", .lam (.binary .multiply (.bound 0) (.nat 1)))
    , ("commandedAxisAt10mmUm",
        .lam
          (.binary .add
            (.app (.get (.bound 1) "commandedAxisAt10mmUm") (.bound 0))
            (.app (.get (.bound 1) "abbeAngularDriftUm") (.bound 0))))
    ]

/-- The 2-layer open-recursive `Composition` for `compensated5AxisMill()` in `Cnc5AxisMill.obend`. -/
def cnc5AxisMillComp : Composition where
  top := abbeAndRuckigCompensatedMillLayer
  below := [uncompensated5AxisMillLayer]
  seed := seedMillFields

/-- **Closedness Certificate**: `cnc5AxisMillComp` and its unresolved flattening are closed. -/
theorem cnc5AxisMillComp_closed : cnc5AxisMillComp.closedB = true := by
  decide +kernel

/-- **Vtable Flattening Soundness (`flatten_sound`)**. -/
theorem cnc5AxisMill_flatten_sound (m : String) :
    .get cnc5AxisMillComp.flatten m ≈b .get cnc5AxisMillComp.object m :=
  flatten_sound cnc5AxisMillComp cnc5AxisMillComp_closed m

/-- **Leaf Book Emission Soundness (`book_sound`)**. -/
theorem cnc5AxisMill_book_sound (m : String) :
    .get (emit cnc5AxisMillComp).link m ≈b .get cnc5AxisMillComp.object m :=
  book_sound cnc5AxisMillComp cnc5AxisMillComp_closed m

/-! ## 3. Whole-Book Synthesis of `.obend` Userspace Physical Parts to FPGA RTL & AMD `CDNA3` GPU ISA -/

/-- **End-to-End Userspace `LcDrivesStatorUsd.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` GPU Theorem**. -/
theorem userspace_physical_stator_to_fpga_verified :
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
          readVgpr (runAmdGpuKernel [8] codeSdf) rSdf == 24
        | none => false)
     | none => false) = true := by
  decide +kernel

/-- **End-to-End Userspace `Cnc5AxisMill.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` GPU Theorem**. -/
theorem userspace_cnc_5axis_to_fpga_and_amd_gpu_verified :
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
          readVgpr (runAmdGpuKernel [6] codeCmd) rCmd == 10024 &&
          readVgpr (runAmdGpuKernel [6] codeErr) rErr == 26
        | _, _ => false)
     | none => false) = true := by
  decide +kernel

end Obend.Hardware.UserspacePhysical
end
