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
public import Obend.Leaf.Specialize
public import Obend.Leaf.Futamura
public import Obend.Leaf.BendTT
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
open Obend.Leaf.Futamura
open Obend.Leaf.BendTT
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

/-! ## 4. General Bridge from `Term.fix (Term.mix baseLayer.term overrideLayer.term) (.record seed)` to `Leaf.flatten_sound` -/

/-- A 2-layer `Core4` prototype hierarchy closed directly via `Term.fix (Term.mix baseSpec overrideSpec) (.record seed)`. -/
def fixMixObject (baseLayer overrideLayer : Layer) (seed : List (String × Term)) : Term :=
  .fix (.mix baseLayer.term overrideLayer.term) (.record seed)

/-- The corresponding 2-layer `Obend.Logic.Composition`. -/
def fixMixComp (baseLayer overrideLayer : Layer) (seed : List (String × Term)) : Composition where
  top := overrideLayer
  below := [baseLayer]
  seed := seed

/-- Closedness check for `fixMixObject` and its unresolved flattening. -/
def fixMixClosedB (baseLayer overrideLayer : Layer) (seed : List (String × Term)) : Bool :=
  Obend.Law.closedB (fixMixObject baseLayer overrideLayer seed) &&
  Obend.Law.closedB (flatObject (fixMixComp baseLayer overrideLayer seed).flatRaw)

/-- Base pair relating `fixMixObject` and `flatObject C.flatRaw`. -/
def fixMixPair (baseLayer overrideLayer : Layer) (seed : List (String × Term)) (o f : Term) : Prop :=
  o = fixMixObject baseLayer overrideLayer seed ∧
  f = flatObject (fixMixComp baseLayer overrideLayer seed).flatRaw

theorem fixMixObject_unfold (baseLayer overrideLayer : Layer) (seed : List (String × Term)) :
    Step (fixMixObject baseLayer overrideLayer seed)
      (.app (.app (.mix baseLayer.term overrideLayer.term) (fixMixObject baseLayer overrideLayer seed)) (.record seed)) :=
  .fix _ _

theorem fixMix_layers_record (baseLayer overrideLayer : Layer) (O : Term) (seed : List (String × Term)) :
    Steps (.app (.app (.mix baseLayer.term overrideLayer.term) O) (.record seed))
      (.record (rowOf O seed [overrideLayer, baseLayer])) := by
  refine steps_trans (mix_apply _ _ _ _) ?_
  refine steps_trans (layer_apply overrideLayer O (superBelow O seed [baseLayer])) ?_
  unfold Layer.provide
  simp only [rowOf]
  cases overrideLayer.flat
  · simp only [Bool.false_eq_true, ite_false]
    exact steps_trans (Obend.Logic.steps_extend _ (superBelow_record O seed [baseLayer]))
      (steps_one (.extendRecord _ _))
  · exact .refl _

theorem fixMixPair_closed {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) :
    ClosedPairs (fixMixPair baseLayer overrideLayer seed) := by
  rintro o f ⟨rfl, rfl⟩
  simp only [fixMixClosedB, Bool.and_eq_true] at hc
  exact ⟨closed_of_closedB hc.1, closed_of_closedB hc.2⟩

theorem fixMixPair_base {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) :
    Base (fixMixPair baseLayer overrideLayer seed) where
  closed := fixMixPair_closed hc
  unfold := by
    rintro o f ⟨rfl, rfl⟩
    let C := fixMixComp baseLayer overrideLayer seed
    obtain ⟨f₁, sf, sf'⟩ := flatObject_unfold C.flatRaw
    have ⟨names, rel⟩ := row_joins (fixMixPair_closed hc)
      (O := fixMixObject baseLayer overrideLayer seed)
      (F := flatObject C.flatRaw)
      (.base ⟨rfl, rfl⟩) seed [overrideLayer, baseLayer]
    exact ⟨_, _, f₁, _, fixMixObject_unfold baseLayer overrideLayer seed,
      fixMix_layers_record baseLayer overrideLayer _ seed, sf, sf', .record names rel⟩

/-- **`fix_mix_flatten_sound`**:
For any closed 2-layer prototype hierarchy `Term.fix (Term.mix baseLayer.term overrideLayer.term) (.record seed)`,
every member projection `.get (Term.fix (Term.mix baseLayer.term overrideLayer.term) (.record seed)) m`
is behaviorally equivalent (`≈b`) to `.get (fixMixComp baseLayer overrideLayer seed).flatten m`! -/
theorem fix_mix_flatten_sound {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) (m : String) :
    .get (fixMixObject baseLayer overrideLayer seed) m ≈b
      .get (fixMixComp baseLayer overrideLayer seed).flatten m := by
  let C := fixMixComp baseLayer overrideLayer seed
  exact BEquiv.trans
    (bequiv_of_joins (fixMixPair_base hc) (.get m (.base ⟨rfl, rfl⟩)))
    (bequiv_of_ahead (.get m (resolve_ahead C.flatRaw)))

/-- Transfer a `Nat` evaluation from `C.flatten` to `Term.fix (Term.mix baseSpec overrideSpec) (.record seed)` via `fix_mix_flatten_sound`. -/
theorem evaluates_nat_of_fix_mix_flatten {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) (m : String) (x res : Nat)
    (hev : Evaluates (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.nat res)) :
    Evaluates (.app (.get (fixMixObject baseLayer overrideLayer seed) m) (.nat x)) (.nat res) := by
  have hbeq := fix_mix_flatten_sound hc m
  have hruns := sameRuns_app_of_bequiv hbeq (.nat x)
  have hhalts : Halts (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.natural res) :=
    ⟨.nat res, hev, .natural res⟩
  obtain ⟨v, hev', hobs⟩ := (hruns.halts (.natural res)).2 hhalts
  cases hobs
  exact hev'

/-- Transfer a `Bool` evaluation from `C.flatten` to `Term.fix (Term.mix baseSpec overrideSpec) (.record seed)` via `fix_mix_flatten_sound`. -/
theorem evaluates_bool_of_fix_mix_flatten {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) (m : String) (x : Nat) (res : Bool)
    (hev : Evaluates (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.boolean res)) :
    Evaluates (.app (.get (fixMixObject baseLayer overrideLayer seed) m) (.nat x)) (.boolean res) := by
  have hbeq := fix_mix_flatten_sound hc m
  have hruns := sameRuns_app_of_bequiv hbeq (.nat x)
  have hhalts : Halts (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.boolean res) :=
    ⟨.boolean res, hev, .boolean res⟩
  obtain ⟨v, hev', hobs⟩ := (hruns.halts (.boolean res)).2 hhalts
  cases hobs
  exact hev'

theorem steps_binary_right {op : Primitive} {l r r' : Term} (hl : Value l) (hr : Steps r r') :
    Steps (.binary op l r) (.binary op l r') :=
  steps_congr (fun x => .binary op l x) (fun s => .binaryRight _ _ hl s) hr

theorem steps_binary_left {op : Primitive} {l l' r : Term} (hl : Steps l l') :
    Steps (.binary op l r) (.binary op l' r) :=
  steps_congr (fun x => .binary op x r) (fun s => .binaryLeft _ _ s) hl

theorem run_steps_of_termEq {fuel : Nat} {t v : Term}
    (h : (match Obend.Law.run fuel t with | some w => Obend.Law.termEq w v | none => false) = true) :
    Steps t v := by
  have hrun : Obend.Law.run fuel t = some v := by
    revert h
    cases Obend.Law.run fuel t with
    | none => intro h; cases h
    | some w =>
      intro h
      rw [Obend.Law.termEq_sound h]
  exact (Obend.Law.run_sound (fuel := fuel) (t := t) (v := v) hrun).1

/-! ## 5. Domain Object 1: Multi-Layer LC Drives In-Slot Stator (`statorBaseSpec` Mixed with `inSlotCoolingOverrideSpec`) -/

/-- Base `Core4` specification term `statorBaseSpec` (`OuterJacketStator`). -/
def statorBaseSpec : Term := outerJacketStatorLayer.term

/-- Override `Core4` specification term `inSlotCoolingOverrideSpec` (`LcDrivesInSlotUpgrade`). -/
def inSlotCoolingOverrideSpec : Term := lcDrivesInSlotUpgradeLayer.term

/-- **Domain Object 1 (`statorInSlotCore4Object`)**:
`Term.fix (Term.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`. -/
def statorInSlotCore4Object : Term :=
  .fix (.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)

/-- The 2-layer `Composition` for `statorInSlotCore4Object`. -/
def statorInSlotComp : Composition :=
  fixMixComp outerJacketStatorLayer lcDrivesInSlotUpgradeLayer seedStatorFields

theorem statorInSlot_closed :
    fixMixClosedB outerJacketStatorLayer lcDrivesInSlotUpgradeLayer seedStatorFields = true := by
  decide +kernel

@[simp] theorem statorInSlotFlatten_subst (σ : Nat → Term) :
    statorInSlotComp.flatten.substitute σ = statorInSlotComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem statorInSlotObject_subst (σ : Nat → Term) :
    statorInSlotCore4Object.substitute σ = statorInSlotCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def statorBaseSuperTerm : Term :=
  .app (.app statorBaseSpec statorInSlotCore4Object) (.record seedStatorFields)

@[simp] theorem statorBaseSuperTerm_subst (σ : Nat → Term) :
    statorBaseSuperTerm.substitute σ = statorBaseSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`statorInSlot_flatten_sound`**: `.get statorInSlotCore4Object m ≈b .get statorInSlotComp.flatten m`. -/
theorem statorInSlot_flatten_sound (m : String) :
    .get statorInSlotCore4Object m ≈b .get statorInSlotComp.flatten m :=
  fix_mix_flatten_sound statorInSlot_closed m

/-- **Universal Parametric Theorem 1a (`stator_in_slot_peak_temp_forall`)**:
For EVERY copper loss `loss : Nat`, evaluating `.app (.get statorInSlotCore4Object "peakWindingTemp") (.nat loss)`
on the open-recursive `Core4` object `Term.fix (Term.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`
late-binds `self.thermalResistance = 9` from `inSlotCoolingOverrideSpec` inside `statorBaseSpec`'s
`peakWindingTemp` method and evaluates constructively in `Core4` (`Evaluates`, `0 Classical.choice`) to `.nat (50 + loss * 9)`! -/
theorem stator_in_slot_peak_temp_forall (loss : Nat) :
    Evaluates (.app (.get statorInSlotCore4Object "peakWindingTemp") (.nat loss))
      (.nat (50 + loss * 9)) := by
  have hfn : Steps (.get statorInSlotCore4Object "peakWindingTemp")
      (.lam (.binary .add (.nat 50)
        (.binary .multiply (.bound 0) (.get statorInSlotCore4Object "thermalResistance")))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have htr : Steps (.get statorInSlotCore4Object "thermalResistance") (.nat 9) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (50 + loss * 9)⟩
  refine steps_trans (steps_app (.nat loss) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, statorInSlotObject_subst]
  refine steps_trans
    (steps_binary_right (.natural 50) (steps_binary_right (.natural loss) htr)) ?_
  refine .next (.binaryRight _ _ (.natural 50)
    (.primitive .multiply (.nat loss) (.nat 9) (.nat (loss * 9)) (.natural loss) (.natural 9) rfl)) ?_
  exact steps_one (.primitive .add (.nat 50) (.nat (loss * 9)) (.nat (50 + loss * 9))
    (.natural 50) (.natural (loss * 9)) rfl)

/-- **Universal Parametric Theorem 1b (`stator_in_slot_sdf_margin_forall`)**:
For EVERY radial coordinate `r : Nat`, evaluating `.app (.get statorInSlotCore4Object "sdfMargin") (.nat r)`
on `Term.fix (Term.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`
chains `inSlotCoolingOverrideSpec`'s `super.sdfMargin(r) + 6` with `statorBaseSpec`'s `r + 10`
and evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat ((r + 10) + 6)`! -/
theorem stator_in_slot_sdf_margin_forall (r : Nat) :
    Evaluates (.app (.get statorInSlotCore4Object "sdfMargin") (.nat r))
      (.nat ((r + 10) + 6)) := by
  have hfn : Steps (.get statorInSlotCore4Object "sdfMargin")
      (.lam (.binary .add (.app (.get statorBaseSuperTerm "sdfMargin") (.bound 0)) (.nat 6))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get statorBaseSuperTerm "sdfMargin")
      (.lam (.binary .add (.bound 0) (.nat 10))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural ((r + 10) + 6)⟩
  refine steps_trans (steps_app (.nat r) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, statorBaseSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat r) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.primitive .add (.nat r) (.nat 10) (.nat (r + 10)) (.natural r) (.natural 10) rfl)) ?_
  exact steps_one (.primitive .add (.nat (r + 10)) (.nat 6) (.nat ((r + 10) + 6))
    (.natural (r + 10)) (.natural 6) rfl)

def statorPeakBody : Term :=
  .lam (.binary .add (.nat 50) (.binary .multiply (.bound 0) (.get (.bound 1) "thermalResistance")))

/-- **Support Extraction Conservatism & Futamura 2 Commutation for Domain Object 1 (`stator_in_slot_support_and_futamura2`)**:
1. `extractReadMembers` on `peakWindingTemp`'s inner body extracts `["thermalResistance"]`, and by
   `extractReadMembers_mutation_invariant`, mutating `"massKg"` to any `newMass : Option Term` leaves
   specialized evaluation invariant.
2. `evalBook (specializeBook B pins) "peakWindingTemp" = evalBook B "peakWindingTemp"`.
3. `futamura2_compiler_generator_commutes` holds for `emit statorInSlotComp` under `bookCanonicalPins (emit statorInSlotComp)`
   for every runtime argument `loss : Nat`. -/
theorem stator_in_slot_support_and_futamura2 (env : String → Option Term) (newMass : Option Term) (loss : Nat) :
    let peakBody : Term := statorPeakBody
    let B := emit statorInSlotComp
    let pins := bookCanonicalPins B
    extractReadMembers peakBody = ["thermalResistance"] ∧
    substMemberEnv (mutateMemberEnv env "massKg" newMass) peakBody = substMemberEnv env peakBody ∧
    evalBook (specializeBook B pins) "peakWindingTemp" = evalBook B "peakWindingTemp" ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B pins) (encodePinsRecord pins))).bind
      (fun B_res => evalResidualBookAt B_res "peakWindingTemp" (.nat loss))) =
      evalBookUnderPinsAt B pins "peakWindingTemp" (.nat loss) := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant statorPeakBody env newMass (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel),
    (futamura2_compiler_generator_commutes (emit statorInSlotComp)
      (bookCanonicalPins (emit statorInSlotComp)) "peakWindingTemp" (.nat loss)).2.2.2⟩

/-! ## 6. Domain Object 2: `MS350` SiC Half-Bridge Phase Leg (`sicBaseSwitchSpec` Mixed with `deadtimeProtectionOverrideSpec`) -/

/-- Seed record for the `MS350` SiC Half-Bridge Phase Leg. -/
def seedSicSwitchFields : List (String × Term) :=
  [ ("deadtimeNs", .nat 0)
  , ("slewRateLimitVPerNs", .nat 0)
  , ("shootThroughSafe", .lam (.boolean false))
  , ("switchingLossUj", .lam (.nat 0))
  , ("effectiveGateDelayNs", .lam (.nat 0))
  ]

/-- Base layer: `spec SicBaseSwitch for Ms350PhaseLeg`. -/
def sicBaseSwitchLayer : Layer where
  name := "Ms350PhaseLeg.SicBaseSwitch"
  metadata := .label "Ms350PhaseLeg.SicBaseSwitch"
  fields :=
    [ ("deadtimeNs", .nat 40)
    , ("slewRateLimitVPerNs", .nat 50)
    , ("shootThroughSafe",
        .lam (.binary .lessEqual (.bound 0) (.get (.bound 2) "slewRateLimitVPerNs")))
    , ("switchingLossUj",
        .lam (.binary .add (.binary .multiply (.bound 0) (.nat 3)) (.get (.bound 2) "deadtimeNs")))
    , ("effectiveGateDelayNs",
        .lam (.binary .add (.bound 0) (.nat 12)))
    ]

/-- Override layer: `spec DeadtimeProtectionOverride for Ms350PhaseLeg`. -/
def deadtimeProtectionOverrideLayer : Layer where
  name := "Ms350PhaseLeg.DeadtimeProtectionOverride"
  metadata := .label "Ms350PhaseLeg.DeadtimeProtectionOverride"
  fields :=
    [ ("deadtimeNs", .nat 120)
    , ("slewRateLimitVPerNs", .nat 80)
    , ("effectiveGateDelayNs",
        .lam (.binary .add (.app (.get (.bound 1) "effectiveGateDelayNs") (.bound 0)) (.nat 25)))
    ]

/-- Base `Core4` specification term `sicBaseSwitchSpec`. -/
def sicBaseSwitchSpec : Term := sicBaseSwitchLayer.term

/-- Override `Core4` specification term `deadtimeProtectionOverrideSpec`. -/
def deadtimeProtectionOverrideSpec : Term := deadtimeProtectionOverrideLayer.term

/-- **Domain Object 2 (`ms350PhaseLegCore4Object`)**:
`Term.fix (Term.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)`. -/
def ms350PhaseLegCore4Object : Term :=
  .fix (.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)

/-- The 2-layer `Composition` for `ms350PhaseLegCore4Object`. -/
def ms350PhaseLegComp : Composition :=
  fixMixComp sicBaseSwitchLayer deadtimeProtectionOverrideLayer seedSicSwitchFields

theorem ms350PhaseLeg_closed :
    fixMixClosedB sicBaseSwitchLayer deadtimeProtectionOverrideLayer seedSicSwitchFields = true := by
  decide +kernel

@[simp] theorem ms350PhaseLegFlatten_subst (σ : Nat → Term) :
    ms350PhaseLegComp.flatten.substitute σ = ms350PhaseLegComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem ms350PhaseLegObject_subst (σ : Nat → Term) :
    ms350PhaseLegCore4Object.substitute σ = ms350PhaseLegCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def sicBaseSuperTerm : Term :=
  .app (.app sicBaseSwitchSpec ms350PhaseLegCore4Object) (.record seedSicSwitchFields)

@[simp] theorem sicBaseSuperTerm_subst (σ : Nat → Term) :
    sicBaseSuperTerm.substitute σ = sicBaseSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`ms350PhaseLeg_flatten_sound`**: `.get ms350PhaseLegCore4Object m ≈b .get ms350PhaseLegComp.flatten m`. -/
theorem ms350PhaseLeg_flatten_sound (m : String) :
    .get ms350PhaseLegCore4Object m ≈b .get ms350PhaseLegComp.flatten m :=
  fix_mix_flatten_sound ms350PhaseLeg_closed m

/-- **Universal Parametric Theorem 2a (`ms350_switching_loss_forall`)**:
For EVERY phase current `currentA : Nat`, evaluating `.app (.get ms350PhaseLegCore4Object "switchingLossUj") (.nat currentA)`
on `Term.fix (Term.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)`
late-binds `self.deadtimeNs = 120` from `deadtimeProtectionOverrideSpec` inside `sicBaseSwitchSpec`'s
`switchingLossUj` method and evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat (currentA * 3 + 120)`! -/
theorem ms350_switching_loss_forall (currentA : Nat) :
    Evaluates (.app (.get ms350PhaseLegCore4Object "switchingLossUj") (.nat currentA))
      (.nat (currentA * 3 + 120)) := by
  have hfn : Steps (.get ms350PhaseLegCore4Object "switchingLossUj")
      (.lam (.binary .add (.binary .multiply (.bound 0) (.nat 3))
        (.get ms350PhaseLegCore4Object "deadtimeNs"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hdt : Steps (.get ms350PhaseLegCore4Object "deadtimeNs") (.nat 120) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (currentA * 3 + 120)⟩
  refine steps_trans (steps_app (.nat currentA) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, ms350PhaseLegObject_subst]
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat currentA) (.nat 3) (.nat (currentA * 3))
      (.natural currentA) (.natural 3) rfl)) ?_
  refine steps_trans (steps_binary_right (.natural (currentA * 3)) hdt) ?_
  exact steps_one (.primitive .add (.nat (currentA * 3)) (.nat 120) (.nat (currentA * 3 + 120))
    (.natural (currentA * 3)) (.natural 120) rfl)

/-- **Universal Parametric Theorem 2b (`ms350_shoot_through_safe_forall`)**:
For EVERY slew rate `diDt : Nat`, evaluating `.app (.get ms350PhaseLegCore4Object "shootThroughSafe") (.nat diDt)`
on `Term.fix (Term.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)`
late-binds `self.slewRateLimitVPerNs = 80` from `deadtimeProtectionOverrideSpec` and evaluates constructively
in `Core4` (`0 Classical.choice`) to `.boolean (decide (diDt ≤ 80))`! -/
theorem ms350_shoot_through_safe_forall (diDt : Nat) :
    Evaluates (.app (.get ms350PhaseLegCore4Object "shootThroughSafe") (.nat diDt))
      (.boolean (decide (diDt ≤ 80))) := by
  have hfn : Steps (.get ms350PhaseLegCore4Object "shootThroughSafe")
      (.lam (.binary .lessEqual (.bound 0)
        (.get ms350PhaseLegCore4Object "slewRateLimitVPerNs"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsl : Steps (.get ms350PhaseLegCore4Object "slewRateLimitVPerNs") (.nat 80) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .boolean (decide (diDt ≤ 80))⟩
  refine steps_trans (steps_app (.nat diDt) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, ms350PhaseLegObject_subst]
  refine steps_trans (steps_binary_right (.natural diDt) hsl) ?_
  exact steps_one (.primitive .lessEqual (.nat diDt) (.nat 80) (.boolean (decide (diDt ≤ 80)))
    (.natural diDt) (.natural 80) rfl)

/-- **Universal Parametric Theorem 2c (`ms350_gate_delay_forall`)**:
For EVERY timing margin `margin : Nat`, evaluating `.app (.get ms350PhaseLegCore4Object "effectiveGateDelayNs") (.nat margin)`
on `Term.fix (Term.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)`
evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat ((margin + 12) + 25)`! -/
theorem ms350_gate_delay_forall (margin : Nat) :
    Evaluates (.app (.get ms350PhaseLegCore4Object "effectiveGateDelayNs") (.nat margin))
      (.nat ((margin + 12) + 25)) := by
  have hfn : Steps (.get ms350PhaseLegCore4Object "effectiveGateDelayNs")
      (.lam (.binary .add (.app (.get sicBaseSuperTerm "effectiveGateDelayNs") (.bound 0)) (.nat 25))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get sicBaseSuperTerm "effectiveGateDelayNs")
      (.lam (.binary .add (.bound 0) (.nat 12))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural ((margin + 12) + 25)⟩
  refine steps_trans (steps_app (.nat margin) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, sicBaseSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat margin) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.primitive .add (.nat margin) (.nat 12) (.nat (margin + 12)) (.natural margin) (.natural 12) rfl)) ?_
  exact steps_one (.primitive .add (.nat (margin + 12)) (.nat 25) (.nat ((margin + 12) + 25))
    (.natural (margin + 12)) (.natural 25) rfl)

def ms350LossBody : Term :=
  .lam (.binary .add (.binary .multiply (.bound 0) (.nat 3)) (.get (.bound 1) "deadtimeNs"))

/-- **Support Extraction Conservatism & Futamura 2 Commutation for Domain Object 2 (`ms350_support_and_futamura2`)**. -/
theorem ms350_support_and_futamura2 (env : String → Option Term) (newGate : Option Term) (currentA : Nat) :
    let lossBody : Term := ms350LossBody
    let B := emit ms350PhaseLegComp
    let pins := bookCanonicalPins B
    extractReadMembers lossBody = ["deadtimeNs"] ∧
    substMemberEnv (mutateMemberEnv env "effectiveGateDelayNs" newGate) lossBody = substMemberEnv env lossBody ∧
    evalBook (specializeBook B pins) "switchingLossUj" = evalBook B "switchingLossUj" ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B pins) (encodePinsRecord pins))).bind
      (fun B_res => evalResidualBookAt B_res "switchingLossUj" (.nat currentA))) =
      evalBookUnderPinsAt B pins "switchingLossUj" (.nat currentA) := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant ms350LossBody env newGate (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel),
    (futamura2_compiler_generator_commutes (emit ms350PhaseLegComp)
      (bookCanonicalPins (emit ms350PhaseLegComp)) "switchingLossUj" (.nat currentA)).2.2.2⟩

/-! ## 7. Domain Object 3: $Q_3$ Photonic Coupler Array (`planarWaveguideBaseSpec` Mixed with `krawtchoukCouplingOverrideSpec`) -/

/-- Seed record for the $Q_3$ Photonic Coupler Array. -/
def seedPhotonicFields : List (String × Term) :=
  [ ("couplingWeight", .nat 0)
  , ("hypercubeDim", .nat 0)
  , ("transferredPowerMw", .lam (.nat 0))
  , ("krawtchoukPhaseShiftMrad", .lam (.nat 0))
  ]

/-- Base layer: `spec PlanarWaveguideBase for Q3PhotonicCouplerArray`. -/
def planarWaveguideBaseLayer : Layer where
  name := "Q3Photonic.PlanarWaveguideBase"
  metadata := .label "Q3Photonic.PlanarWaveguideBase"
  fields :=
    [ ("couplingWeight", .nat 2)
    , ("hypercubeDim", .nat 3)
    , ("transferredPowerMw",
        .lam (.binary .add
          (.binary .multiply (.bound 0) (.get (.bound 2) "couplingWeight"))
          (.get (.bound 2) "hypercubeDim")))
    , ("krawtchoukPhaseShiftMrad",
        .lam (.binary .multiply (.bound 0) (.nat 15)))
    ]

/-- Override layer: `spec KrawtchoukCouplingOverride for Q3PhotonicCouplerArray`. -/
def krawtchoukCouplingOverrideLayer : Layer where
  name := "Q3Photonic.KrawtchoukCouplingOverride"
  metadata := .label "Q3Photonic.KrawtchoukCouplingOverride"
  fields :=
    [ ("couplingWeight", .nat 7)
    , ("krawtchoukPhaseShiftMrad",
        .lam (.binary .add (.app (.get (.bound 1) "krawtchoukPhaseShiftMrad") (.bound 0)) (.nat 45)))
    ]

/-- Base `Core4` specification term `planarWaveguideBaseSpec`. -/
def planarWaveguideBaseSpec : Term := planarWaveguideBaseLayer.term

/-- Override `Core4` specification term `krawtchoukCouplingOverrideSpec`. -/
def krawtchoukCouplingOverrideSpec : Term := krawtchoukCouplingOverrideLayer.term

/-- **Domain Object 3 (`q3PhotonicCore4Object`)**:
`Term.fix (Term.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)`. -/
def q3PhotonicCore4Object : Term :=
  .fix (.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)

/-- The 2-layer `Composition` for `q3PhotonicCore4Object`. -/
def q3PhotonicComp : Composition :=
  fixMixComp planarWaveguideBaseLayer krawtchoukCouplingOverrideLayer seedPhotonicFields

theorem q3Photonic_closed :
    fixMixClosedB planarWaveguideBaseLayer krawtchoukCouplingOverrideLayer seedPhotonicFields = true := by
  decide +kernel

@[simp] theorem q3PhotonicFlatten_subst (σ : Nat → Term) :
    q3PhotonicComp.flatten.substitute σ = q3PhotonicComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem q3PhotonicObject_subst (σ : Nat → Term) :
    q3PhotonicCore4Object.substitute σ = q3PhotonicCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def planarWaveguideSuperTerm : Term :=
  .app (.app planarWaveguideBaseSpec q3PhotonicCore4Object) (.record seedPhotonicFields)

@[simp] theorem planarWaveguideSuperTerm_subst (σ : Nat → Term) :
    planarWaveguideSuperTerm.substitute σ = planarWaveguideSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`q3Photonic_flatten_sound`**: `.get q3PhotonicCore4Object m ≈b .get q3PhotonicComp.flatten m`. -/
theorem q3Photonic_flatten_sound (m : String) :
    .get q3PhotonicCore4Object m ≈b .get q3PhotonicComp.flatten m :=
  fix_mix_flatten_sound q3Photonic_closed m

/-- **Universal Parametric Theorem 3a (`q3_photonic_transferred_power_forall`)**:
For EVERY input optical power `pIn : Nat`, evaluating `.app (.get q3PhotonicCore4Object "transferredPowerMw") (.nat pIn)`
on `Term.fix (Term.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)`
combines the overridden Krawtchouk coupling weight `self.couplingWeight = 7` from `krawtchoukCouplingOverrideSpec`
with the inherited hypercube dimension `self.hypercubeDim = 3` from `planarWaveguideBaseSpec` and
evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat (pIn * 7 + 3)`! -/
theorem q3_photonic_transferred_power_forall (pIn : Nat) :
    Evaluates (.app (.get q3PhotonicCore4Object "transferredPowerMw") (.nat pIn))
      (.nat (pIn * 7 + 3)) := by
  have hfn : Steps (.get q3PhotonicCore4Object "transferredPowerMw")
      (.lam (.binary .add
        (.binary .multiply (.bound 0) (.get q3PhotonicCore4Object "couplingWeight"))
        (.get q3PhotonicCore4Object "hypercubeDim"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hcw : Steps (.get q3PhotonicCore4Object "couplingWeight") (.nat 7) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hdim : Steps (.get q3PhotonicCore4Object "hypercubeDim") (.nat 3) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (pIn * 7 + 3)⟩
  refine steps_trans (steps_app (.nat pIn) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, q3PhotonicObject_subst]
  refine steps_trans
    (steps_binary_left (steps_binary_right (.natural pIn) hcw)) ?_
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat pIn) (.nat 7) (.nat (pIn * 7)) (.natural pIn) (.natural 7) rfl)) ?_
  refine steps_trans (steps_binary_right (.natural (pIn * 7)) hdim) ?_
  exact steps_one (.primitive .add (.nat (pIn * 7)) (.nat 3) (.nat (pIn * 7 + 3))
    (.natural (pIn * 7)) (.natural 3) rfl)

/-- **Universal Parametric Theorem 3b (`q3_photonic_phase_shift_forall`)**:
For EVERY hypercube eigenmode index `modeIdx : Nat`, evaluating
`.app (.get q3PhotonicCore4Object "krawtchoukPhaseShiftMrad") (.nat modeIdx)`
on `Term.fix (Term.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)`
evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat (modeIdx * 15 + 45)`! -/
theorem q3_photonic_phase_shift_forall (modeIdx : Nat) :
    Evaluates (.app (.get q3PhotonicCore4Object "krawtchoukPhaseShiftMrad") (.nat modeIdx))
      (.nat (modeIdx * 15 + 45)) := by
  have hfn : Steps (.get q3PhotonicCore4Object "krawtchoukPhaseShiftMrad")
      (.lam (.binary .add (.app (.get planarWaveguideSuperTerm "krawtchoukPhaseShiftMrad") (.bound 0)) (.nat 45))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get planarWaveguideSuperTerm "krawtchoukPhaseShiftMrad")
      (.lam (.binary .multiply (.bound 0) (.nat 15))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (modeIdx * 15 + 45)⟩
  refine steps_trans (steps_app (.nat modeIdx) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, planarWaveguideSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat modeIdx) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat modeIdx) (.nat 15) (.nat (modeIdx * 15))
      (.natural modeIdx) (.natural 15) rfl)) ?_
  exact steps_one (.primitive .add (.nat (modeIdx * 15)) (.nat 45) (.nat (modeIdx * 15 + 45))
    (.natural (modeIdx * 15)) (.natural 45) rfl)

def q3PowerBody : Term :=
  .lam (.binary .add (.binary .multiply (.bound 0) (.get (.bound 1) "couplingWeight")) (.get (.bound 1) "hypercubeDim"))

/-- **Support Extraction Conservatism & Futamura 2 Commutation for Domain Object 3 (`q3_photonic_support_and_futamura2`)**. -/
theorem q3_photonic_support_and_futamura2 (env : String → Option Term) (newPhase : Option Term) (pIn : Nat) :
    let powerBody : Term := q3PowerBody
    let B := emit q3PhotonicComp
    let pins := bookCanonicalPins B
    extractReadMembers powerBody = ["couplingWeight", "hypercubeDim"] ∧
    substMemberEnv (mutateMemberEnv env "krawtchoukPhaseShiftMrad" newPhase) powerBody = substMemberEnv env powerBody ∧
    evalBook (specializeBook B pins) "transferredPowerMw" = evalBook B "transferredPowerMw" ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B pins) (encodePinsRecord pins))).bind
      (fun B_res => evalResidualBookAt B_res "transferredPowerMw" (.nat pIn))) =
      evalBookUnderPinsAt B pins "transferredPowerMw" (.nat pIn) := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant q3PowerBody env newPhase (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel),
    (futamura2_compiler_generator_commutes (emit q3PhotonicComp)
      (bookCanonicalPins (emit q3PhotonicComp)) "transferredPowerMw" (.nat pIn)).2.2.2⟩

end Obend.Hardware.UserspacePhysical
end
