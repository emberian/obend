module
/-
# Obend.Hardware.UserspacePhysical — Verified `.obend` Userspace Open-Recursive Physical Standard Library Lowered Through `#import_obend` & `Obend.Leaf` Into FPGA SystemVerilog RTL & AMD `CDNA3` 64-Bit VOP64 GPU ISA

Elaborates the 4 canonical `.obend` physical standard library modules in `stdlib/physical/`
at compile time via `#import_obend` (with zero manual de Bruijn `Layer` transcription):
1. `stdlib/physical/LcDrivesStator.obend` (`PhysicalStator`: `OuterJacketStator` -> `LcDrivesInSlotUpgrade` -> `FiveAxisFinishMilled`)
2. `stdlib/physical/Ms350FcmlPhaseLeg.obend` (`Ms350PhaseLeg`: `SicBaseSwitch` -> `DeadtimeProtectionOverride`)
3. `stdlib/physical/CleanroomTcadStack.obend` (`CleanroomTcadStack`: `PlanarBulkMosfetBase` -> `HighKMetalGateFinFetUpgrade`, plus `Q3PhotonicCouplerArray`: `PlanarWaveguideBase` -> `KrawtchoukCouplingOverride`)
4. `stdlib/physical/Cnc5AxisMill.obend` (`Cnc5AxisMill`: `Uncompensated5AxisMill` -> `AbbeAndRuckigCompensatedMill`)

Connects the `#import_obend`-elaborated `Composition`s and `Book`s directly to:
- `Obend.Logic.Composition` & `Obend.Leaf.Flatten` (`flatten_sound`, `fix_mix_flatten_sound`),
- `Obend.Leaf.Emit` (`book_sound`),
- `Obend.Leaf.Static` (`specializeBook`, `evalBook_specializeBook_eq_evalBook`) & `Obend.Leaf.Specialize` (`extractReadMembers_mutation_invariant`),
- `Obend.Hardware.Compiler` (`compileBookToRtl`) & `Obend.Lower.Proofs.SelfAccelerate` (64-bit `compileRtlExprToAmdGpu` + `runAmdGpuVop64Prog`).
-/
public import Lean
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Logic.Program
public import Obend.Logic.Obligation
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Static
public import Obend.Lower.Proofs.SelfAccelerate
public import Obend.Hardware.Kinematics
public import Obend.Hardware.OpenUSD
public import Obend.Hardware.FluidThermal
public import Obend.Hardware.GeometryCAM
public import Obend.Hardware.Silicon
public import Obend.Hardware.Types
public import Obend.Elab.Workbook
public meta import Lean
public meta import Obend.Core.Term
public meta import Obend.Law
public meta import Obend.Spec.Syntax
public meta import Obend.Spec.Parse
public meta import Obend.Spec.Elaborate
public meta import Obend.Spec.FrontEnd
public meta import Obend.Spec.Capture
public meta import Obend.Spec.Sha256
public meta import Obend.Logic.LateBinding
public meta import Obend.Logic.Claim
public meta import Obend.Logic.Rewrite
public meta import Obend.Logic.Frame
public meta import Obend.Logic.Obligation
public meta import Obend.Logic.Program
public meta import Obend.Leaf.Flatten
public meta import Obend.Leaf.Emit
public meta import Obend.Elab.Workbook
@[expose] public section

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

set_option autoImplicit false

/-! ## 0. `#import_obend` is `Obend.Elab.Workbook`'s (the one importer, 2026-11-04); this module
only consumes the constants it emits (`<def>_comp`, `<def>_book`, `<def>_val`, `claim_*_{obj,just,holds}`,
`laws_count`). -/

/-! ## 1. Compile-Time Elaboration of the 4 Canonical `stdlib/physical/*.obend` Modules via `#import_obend` -/

#import_obend "stdlib/physical/LcDrivesStator.obend" as StdLcDrivesStator
#import_obend "stdlib/physical/Ms350FcmlPhaseLeg.obend" as StdMs350FcmlPhaseLeg
#import_obend "stdlib/physical/CleanroomTcadStack.obend" as StdCleanroomTcadStack
#import_obend "stdlib/physical/Cnc5AxisMill.obend" as StdCnc5AxisMill

/-! ## 2. `stdlib/physical/LcDrivesStator.obend` as an Open-Recursive `Obend.Logic.Composition` -/

/-- Seed record for `PhysicalStator`, elaborated directly from `stdlib/physical/LcDrivesStator.obend`. -/
def seedStatorFields : List (String × Term) :=
  StdLcDrivesStator.lcDrivesProductionStator_comp.seed

/-- Layer 0 (innermost): `spec OuterJacketStator for PhysicalStator`, elaborated from `stdlib/physical/LcDrivesStator.obend`. -/
def outerJacketStatorLayer : Layer :=
  StdLcDrivesStator.outerJacketStator_comp.top

/-- Layer 1 (middle): `spec LcDrivesInSlotUpgrade for PhysicalStator`, elaborated from `stdlib/physical/LcDrivesStator.obend`. -/
def lcDrivesInSlotUpgradeLayer : Layer :=
  StdLcDrivesStator.statorInSlot_comp.top

/-- Layer 2 (outermost): `spec FiveAxisFinishMilled for PhysicalStator`, elaborated from `stdlib/physical/LcDrivesStator.obend`. -/
def fiveAxisFinishMilledLayer : Layer :=
  StdLcDrivesStator.lcDrivesProductionStator_comp.top

/-- The full 3-layer open-recursive `Composition` for `lcDrivesProductionStator()`,
    matching `StdLcDrivesStator.lcDrivesProductionStator_comp` identically. -/
def lcDrivesStatorUsdComp : Composition where
  top := fiveAxisFinishMilledLayer
  below := [lcDrivesInSlotUpgradeLayer, outerJacketStatorLayer]
  seed := seedStatorFields

theorem lcDrivesStatorUsdComp_eq_imported :
    lcDrivesStatorUsdComp = StdLcDrivesStator.lcDrivesProductionStator_comp := rfl

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

/-! ## 3. `stdlib/physical/Cnc5AxisMill.obend` as an Open-Recursive `Obend.Logic.Composition` -/

/-- Seed record for `Cnc5AxisMill`, elaborated directly from `stdlib/physical/Cnc5AxisMill.obend`. -/
def seedMillFields : List (String × Term) :=
  StdCnc5AxisMill.compensated5AxisMill_comp.seed

/-- Layer 0 (innermost): `spec Uncompensated5AxisMill for Cnc5AxisMill`, elaborated from `stdlib/physical/Cnc5AxisMill.obend`. -/
def uncompensated5AxisMillLayer : Layer :=
  StdCnc5AxisMill.raw5AxisMill_comp.top

/-- Layer 1 (outermost): `spec AbbeAndRuckigCompensatedMill for Cnc5AxisMill`, elaborated from `stdlib/physical/Cnc5AxisMill.obend`. -/
def abbeAndRuckigCompensatedMillLayer : Layer :=
  StdCnc5AxisMill.compensated5AxisMill_comp.top

/-- The 2-layer open-recursive `Composition` for `compensated5AxisMill()` in `stdlib/physical/Cnc5AxisMill.obend`. -/
def cnc5AxisMillComp : Composition where
  top := abbeAndRuckigCompensatedMillLayer
  below := [uncompensated5AxisMillLayer]
  seed := seedMillFields

theorem cnc5AxisMillComp_eq_imported :
    cnc5AxisMillComp = StdCnc5AxisMill.compensated5AxisMill_comp := rfl

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

/-! ## 4. Whole-Book Synthesis of `stdlib/physical/*.obend` Parts to FPGA RTL & 64-Bit AMD `CDNA3` VOP64 GPU ISA -/

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

/-! ## 5. General Bridge from `Term.fix (Term.mix baseLayer.term overrideLayer.term) (.record seed)` to `Leaf.flatten_sound` -/

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

/-- Extract the inner method body (under the outer `λself.` binder) from a `Leaf.Book` slot. -/
def extractBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

/-! ## 6. Domain Object 1: Multi-Layer LC Drives In-Slot Stator (`stdlib/physical/LcDrivesStator.obend`) -/

/-- Base `Core4` specification term `statorBaseSpec` (`OuterJacketStator`). -/
def statorBaseSpec : Term := outerJacketStatorLayer.term

/-- Override `Core4` specification term `inSlotCoolingOverrideSpec` (`LcDrivesInSlotUpgrade`). -/
def inSlotCoolingOverrideSpec : Term := lcDrivesInSlotUpgradeLayer.term

/-- **Domain Object 1 (`statorInSlotCore4Object`)**:
`Term.fix (Term.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`. -/
def statorInSlotCore4Object : Term :=
  .fix (.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)

/-- The 2-layer `Composition` for `statorInSlotCore4Object`, matching `StdLcDrivesStator.statorInSlot_comp`. -/
def statorInSlotComp : Composition :=
  fixMixComp outerJacketStatorLayer lcDrivesInSlotUpgradeLayer seedStatorFields

theorem statorInSlotComp_eq_imported :
    statorInSlotComp = StdLcDrivesStator.statorInSlot_comp := rfl

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
  extractBookMethodInner (emit statorInSlotComp) "peakWindingTemp"

/-- **Support extraction conservatism and `specializeBook` commutation for domain object 1 (`stator_in_slot_support_and_specialize`)**. -/
theorem stator_in_slot_support_and_specialize (env : String → Option Term) (newMass : Option Term) (loss : Nat) :
    let peakBody : Term := statorPeakBody
    let B := emit statorInSlotComp
    let pins := bookCanonicalPins B
    extractReadMembers peakBody = ["thermalResistance"] ∧
    substMemberEnv (mutateMemberEnv env "massKg" newMass) peakBody = substMemberEnv env peakBody ∧
    evalBook (specializeBook B pins) "peakWindingTemp" = evalBook B "peakWindingTemp" := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant statorPeakBody env newMass (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel)⟩

/-! ## 7. Domain Object 2: `MS350` SiC Half-Bridge Phase Leg (`stdlib/physical/Ms350FcmlPhaseLeg.obend`) -/

/-- Seed record for the `MS350` SiC Half-Bridge Phase Leg, elaborated from `stdlib/physical/Ms350FcmlPhaseLeg.obend`. -/
def seedSicSwitchFields : List (String × Term) :=
  StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp.seed

/-- Base layer: `spec SicBaseSwitch for Ms350PhaseLeg`, elaborated from `stdlib/physical/Ms350FcmlPhaseLeg.obend`. -/
def sicBaseSwitchLayer : Layer :=
  StdMs350FcmlPhaseLeg.sicBasePhaseLeg_comp.top

/-- Override layer: `spec DeadtimeProtectionOverride for Ms350PhaseLeg`, elaborated from `stdlib/physical/Ms350FcmlPhaseLeg.obend`. -/
def deadtimeProtectionOverrideLayer : Layer :=
  StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp.top

/-- Base `Core4` specification term `sicBaseSwitchSpec`. -/
def sicBaseSwitchSpec : Term := sicBaseSwitchLayer.term

/-- Override `Core4` specification term `deadtimeProtectionOverrideSpec`. -/
def deadtimeProtectionOverrideSpec : Term := deadtimeProtectionOverrideLayer.term

/-- **Domain Object 2 (`ms350PhaseLegCore4Object`)**:
`Term.fix (Term.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)`. -/
def ms350PhaseLegCore4Object : Term :=
  .fix (.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)

/-- The 2-layer `Composition` for `ms350PhaseLegCore4Object`, matching `StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp`. -/
def ms350PhaseLegComp : Composition :=
  fixMixComp sicBaseSwitchLayer deadtimeProtectionOverrideLayer seedSicSwitchFields

theorem ms350PhaseLegComp_eq_imported :
    ms350PhaseLegComp = StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp := rfl

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

/-- **`ms350PhaseLeg_book_sound`**: `.get (emit ms350PhaseLegComp).link m ≈b .get ms350PhaseLegComp.object m`. -/
theorem ms350PhaseLeg_book_sound (m : String) :
    .get (emit ms350PhaseLegComp).link m ≈b .get ms350PhaseLegComp.object m :=
  book_sound ms350PhaseLegComp (by decide +kernel) m

/-- **Universal Parametric Theorem 2a (`ms350_switching_loss_forall`)**. -/
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

/-- **Universal Parametric Theorem 2b (`ms350_shoot_through_safe_forall`)**. -/
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

/-- **Universal Parametric Theorem 2c (`ms350_gate_delay_forall`)**. -/
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
  extractBookMethodInner (emit ms350PhaseLegComp) "switchingLossUj"

/-- **Support extraction conservatism and `specializeBook` commutation for domain object 2 (`ms350_support_and_specialize`)**. -/
theorem ms350_support_and_specialize (env : String → Option Term) (newGate : Option Term) (currentA : Nat) :
    let lossBody : Term := ms350LossBody
    let B := emit ms350PhaseLegComp
    let pins := bookCanonicalPins B
    extractReadMembers lossBody = ["deadtimeNs"] ∧
    substMemberEnv (mutateMemberEnv env "effectiveGateDelayNs" newGate) lossBody = substMemberEnv env lossBody ∧
    evalBook (specializeBook B pins) "switchingLossUj" = evalBook B "switchingLossUj" := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant ms350LossBody env newGate (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel)⟩

/-- **End-to-End Userspace `stdlib/physical/Ms350FcmlPhaseLeg.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
theorem userspace_ms350_phase_leg_to_fpga_and_amd_gpu_verified :
    (match compileBookToRtl "ms350_fcml_userspace_phase_leg" (emit ms350PhaseLegComp) with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 100#64) (fun _ => 0#64) ==
         [ ("out_deadtimeNs", 120#64)
         , ("out_slewRateLimitVPerNs", 80#64)
         , ("out_effectiveGateDelayNs", 137#64)
         , ("out_shootThroughSafe", 0#64)
         , ("out_switchingLossUj", 420#64)
         ]) &&
       (match m.wires[2]?, m.wires[3]?, m.wires[4]? with
        | some wGate, some wSafe, some wLoss =>
          let (rGate, _, codeGate) := compileRtlExprToAmdGpu 1 wGate.expr
          let (rSafe, _, codeSafe) := compileRtlExprToAmdGpu 1 wSafe.expr
          let (rLoss, _, codeLoss) := compileRtlExprToAmdGpu 1 wLoss.expr
          let vgprsGate :=
            runAmdGpuVop64Prog (fun _ => 10#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeGate
          let vgprsSafe60 :=
            runAmdGpuVop64Prog (fun _ => 60#64) (fun _ => 80#64) (fun _ => 0#64) (fun _ => 0#64) codeSafe
          let vgprsLoss100 :=
            runAmdGpuVop64Prog (fun _ => 100#64) (fun _ => 120#64) (fun _ => 0#64) (fun _ => 0#64) codeLoss
          vgprsGate rGate == 47#64 &&
          vgprsSafe60 rSafe == 1#64 &&
          vgprsLoss100 rLoss == 420#64
        | _, _, _ => false)
     | none => false) = true := by
  decide +kernel

/-! ## 8. Domain Object 3: $Q_3$ Photonic Coupler Array (`stdlib/physical/CleanroomTcadStack.obend`) -/

/-- Seed record for the $Q_3$ Photonic Coupler Array, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def seedPhotonicFields : List (String × Term) :=
  StdCleanroomTcadStack.q3KrawtchoukArray_comp.seed

/-- Base layer: `spec PlanarWaveguideBase for Q3PhotonicCouplerArray`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def planarWaveguideBaseLayer : Layer :=
  StdCleanroomTcadStack.planarWaveguideCoupler_comp.top

/-- Override layer: `spec KrawtchoukCouplingOverride for Q3PhotonicCouplerArray`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def krawtchoukCouplingOverrideLayer : Layer :=
  StdCleanroomTcadStack.q3KrawtchoukArray_comp.top

/-- Base `Core4` specification term `planarWaveguideBaseSpec`. -/
def planarWaveguideBaseSpec : Term := planarWaveguideBaseLayer.term

/-- Override `Core4` specification term `krawtchoukCouplingOverrideSpec`. -/
def krawtchoukCouplingOverrideSpec : Term := krawtchoukCouplingOverrideLayer.term

/-- **Domain Object 3 (`q3PhotonicCore4Object`)**:
`Term.fix (Term.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)`. -/
def q3PhotonicCore4Object : Term :=
  .fix (.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)

/-- The 2-layer `Composition` for `q3PhotonicCore4Object`, matching `StdCleanroomTcadStack.q3KrawtchoukArray_comp`. -/
def q3PhotonicComp : Composition :=
  fixMixComp planarWaveguideBaseLayer krawtchoukCouplingOverrideLayer seedPhotonicFields

theorem q3PhotonicComp_eq_imported :
    q3PhotonicComp = StdCleanroomTcadStack.q3KrawtchoukArray_comp := rfl

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

/-- **`q3Photonic_book_sound`**: `.get (emit q3PhotonicComp).link m ≈b .get q3PhotonicComp.object m`. -/
theorem q3Photonic_book_sound (m : String) :
    .get (emit q3PhotonicComp).link m ≈b .get q3PhotonicComp.object m :=
  book_sound q3PhotonicComp (by decide +kernel) m

/-- **Universal Parametric Theorem 3a (`q3_photonic_transferred_power_forall`)**. -/
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

/-- **Universal Parametric Theorem 3b (`q3_photonic_phase_shift_forall`)**. -/
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
  extractBookMethodInner (emit q3PhotonicComp) "transferredPowerMw"

/-- **Support extraction conservatism and `specializeBook` commutation for domain object 3 (`q3_photonic_support_and_specialize`)**. -/
theorem q3_photonic_support_and_specialize (env : String → Option Term) (newPhase : Option Term) (pIn : Nat) :
    let powerBody : Term := q3PowerBody
    let B := emit q3PhotonicComp
    let pins := bookCanonicalPins B
    extractReadMembers powerBody = ["couplingWeight", "hypercubeDim"] ∧
    substMemberEnv (mutateMemberEnv env "krawtchoukPhaseShiftMrad" newPhase) powerBody = substMemberEnv env powerBody ∧
    evalBook (specializeBook B pins) "transferredPowerMw" = evalBook B "transferredPowerMw" := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant q3PowerBody env newPhase (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel)⟩

/-! ## 9. Domain Object 4: Cleanroom-to-TCAD Semiconductor Wafer Stack (`stdlib/physical/CleanroomTcadStack.obend`) -/

/-- Seed record for `CleanroomTcadStack`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def seedTcadStackFields : List (String × Term) :=
  StdCleanroomTcadStack.cleanroomTcadStack_comp.seed

/-- Base layer: `spec PlanarBulkMosfetBase for CleanroomTcadStack`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def planarBulkMosfetBaseLayer : Layer :=
  StdCleanroomTcadStack.planarBulkTcadStack_comp.top

/-- Override layer: `spec HighKMetalGateFinFetUpgrade for CleanroomTcadStack`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def highKMetalGateFinFetUpgradeLayer : Layer :=
  StdCleanroomTcadStack.cleanroomTcadStack_comp.top

/-- Base `Core4` specification term `planarBulkMosfetBaseSpec`. -/
def planarBulkMosfetBaseSpec : Term := planarBulkMosfetBaseLayer.term

/-- Override `Core4` specification term `highKMetalGateFinFetUpgradeSpec`. -/
def highKMetalGateFinFetUpgradeSpec : Term := highKMetalGateFinFetUpgradeLayer.term

/-- **Domain Object 4 (`cleanroomTcadCore4Object`)**:
`Term.fix (Term.mix planarBulkMosfetBaseSpec highKMetalGateFinFetUpgradeSpec) (.record seedTcadStackFields)`. -/
def cleanroomTcadCore4Object : Term :=
  .fix (.mix planarBulkMosfetBaseSpec highKMetalGateFinFetUpgradeSpec) (.record seedTcadStackFields)

/-- The 2-layer `Composition` for `cleanroomTcadCore4Object`, matching `StdCleanroomTcadStack.cleanroomTcadStack_comp`. -/
def cleanroomTcadStackComp : Composition :=
  fixMixComp planarBulkMosfetBaseLayer highKMetalGateFinFetUpgradeLayer seedTcadStackFields

theorem cleanroomTcadStackComp_eq_imported :
    cleanroomTcadStackComp = StdCleanroomTcadStack.cleanroomTcadStack_comp := rfl

theorem cleanroomTcadStack_closed :
    fixMixClosedB planarBulkMosfetBaseLayer highKMetalGateFinFetUpgradeLayer seedTcadStackFields = true := by
  decide +kernel

@[simp] theorem cleanroomTcadFlatten_subst (σ : Nat → Term) :
    cleanroomTcadStackComp.flatten.substitute σ = cleanroomTcadStackComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem cleanroomTcadObject_subst (σ : Nat → Term) :
    cleanroomTcadCore4Object.substitute σ = cleanroomTcadCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def planarBulkSuperTerm : Term :=
  .app (.app planarBulkMosfetBaseSpec cleanroomTcadCore4Object) (.record seedTcadStackFields)

@[simp] theorem planarBulkSuperTerm_subst (σ : Nat → Term) :
    planarBulkSuperTerm.substitute σ = planarBulkSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`cleanroomTcadStack_flatten_sound`**: `.get cleanroomTcadCore4Object m ≈b .get cleanroomTcadStackComp.flatten m`. -/
theorem cleanroomTcadStack_flatten_sound (m : String) :
    .get cleanroomTcadCore4Object m ≈b .get cleanroomTcadStackComp.flatten m :=
  fix_mix_flatten_sound cleanroomTcadStack_closed m

/-- **`cleanroomTcadStack_book_sound`**: `.get (emit cleanroomTcadStackComp).link m ≈b .get cleanroomTcadStackComp.object m`. -/
theorem cleanroomTcadStack_book_sound (m : String) :
    .get (emit cleanroomTcadStackComp).link m ≈b .get cleanroomTcadStackComp.object m :=
  book_sound cleanroomTcadStackComp (by decide +kernel) m

/-- **Universal Parametric Theorem 4a (`cleanroom_tcad_drain_current_forall`)**:
For EVERY gate overdrive `vov : Nat`, evaluating `.app (.get cleanroomTcadCore4Object "drainCurrentUa") (.nat vov)`
late-binds `self.vthMilliV = 250` from `highKMetalGateFinFetUpgradeLayer` inside `planarBulkMosfetBaseLayer`'s
`drainCurrentUa` method and evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat (vov * 5 + 250)`! -/
theorem cleanroom_tcad_drain_current_forall (vov : Nat) :
    Evaluates (.app (.get cleanroomTcadCore4Object "drainCurrentUa") (.nat vov))
      (.nat (vov * 5 + 250)) := by
  have hfn : Steps (.get cleanroomTcadCore4Object "drainCurrentUa")
      (.lam (.binary .add (.binary .multiply (.bound 0) (.nat 5))
        (.get cleanroomTcadCore4Object "vthMilliV"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hvth : Steps (.get cleanroomTcadCore4Object "vthMilliV") (.nat 250) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (vov * 5 + 250)⟩
  refine steps_trans (steps_app (.nat vov) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, cleanroomTcadObject_subst]
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat vov) (.nat 5) (.nat (vov * 5))
      (.natural vov) (.natural 5) rfl)) ?_
  refine steps_trans (steps_binary_right (.natural (vov * 5)) hvth) ?_
  exact steps_one (.primitive .add (.nat (vov * 5)) (.nat 250) (.nat (vov * 5 + 250))
    (.natural (vov * 5)) (.natural 250) rfl)

/-- **Universal Parametric Theorem 4b (`cleanroom_tcad_gate_delay_forall`)**:
For EVERY fanout `fanout : Nat`, evaluating `.app (.get cleanroomTcadCore4Object "gateDelayPs") (.nat fanout)`
chains `super.gateDelayPs(fanout) + 4` with `fanout * 8 + 20` and evaluates constructively in `Core4`
(`0 Classical.choice`) to `.nat ((fanout * 8 + 20) + 4)`! -/
theorem cleanroom_tcad_gate_delay_forall (fanout : Nat) :
    Evaluates (.app (.get cleanroomTcadCore4Object "gateDelayPs") (.nat fanout))
      (.nat ((fanout * 8 + 20) + 4)) := by
  have hfn : Steps (.get cleanroomTcadCore4Object "gateDelayPs")
      (.lam (.binary .add (.app (.get planarBulkSuperTerm "gateDelayPs") (.bound 0)) (.nat 4))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get planarBulkSuperTerm "gateDelayPs")
      (.lam (.binary .add (.binary .multiply (.bound 0) (.nat 8)) (.nat 20))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural ((fanout * 8 + 20) + 4)⟩
  refine steps_trans (steps_app (.nat fanout) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, planarBulkSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat fanout) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.binaryLeft _ _
      (.primitive .multiply (.nat fanout) (.nat 8) (.nat (fanout * 8)) (.natural fanout) (.natural 8) rfl))) ?_
  refine .next (.binaryLeft _ _
    (.primitive .add (.nat (fanout * 8)) (.nat 20) (.nat (fanout * 8 + 20))
      (.natural (fanout * 8)) (.natural 20) rfl)) ?_
  exact steps_one (.primitive .add (.nat (fanout * 8 + 20)) (.nat 4) (.nat ((fanout * 8 + 20) + 4))
    (.natural (fanout * 8 + 20)) (.natural 4) rfl)

def tcadDrainCurrentBody : Term :=
  extractBookMethodInner (emit cleanroomTcadStackComp) "drainCurrentUa"

/-- **Support extraction conservatism and `specializeBook` commutation for domain object 4 (`cleanroom_tcad_support_and_specialize`)**. -/
theorem cleanroom_tcad_support_and_specialize (env : String → Option Term) (newEot : Option Term) (vov : Nat) :
    let drainBody : Term := tcadDrainCurrentBody
    let B := emit cleanroomTcadStackComp
    let pins := bookCanonicalPins B
    extractReadMembers drainBody = ["vthMilliV"] ∧
    substMemberEnv (mutateMemberEnv env "oxideEotPicometers" newEot) drainBody = substMemberEnv env drainBody ∧
    evalBook (specializeBook B pins) "drainCurrentUa" = evalBook B "drainCurrentUa" := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant tcadDrainCurrentBody env newEot (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel)⟩

/-- **End-to-End Userspace `stdlib/physical/CleanroomTcadStack.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
theorem userspace_cleanroom_tcad_and_q3_to_fpga_and_amd_gpu_verified :
    (match compileBookToRtl "cleanroom_tcad_userspace_stack" (emit cleanroomTcadStackComp),
           compileBookToRtl "q3_photonic_userspace_array" (emit q3PhotonicComp) with
     | some mTcad, some mQ3 =>
       checkRtlModule mTcad &&
       checkRtlModule mQ3 &&
       (evalModuleOutputs mTcad (fun _ => 200#64) (fun _ => 0#64) ==
         [ ("out_oxideEotPicometers", 700#64)
         , ("out_vthMilliV", 250#64)
         , ("out_gateDelayPs", 1624#64)
         , ("out_drainCurrentUa", 1250#64)
         ]) &&
       (evalModuleOutputs mQ3 (fun _ => 20#64) (fun _ => 0#64) ==
         [ ("out_couplingWeight", 7#64)
         , ("out_krawtchoukPhaseShiftMrad", 345#64)
         , ("out_hypercubeDim", 3#64)
         , ("out_transferredPowerMw", 143#64)
         ]) &&
       (match mTcad.wires[2]?, mQ3.wires[1]? with
        | some wDelay, some wPhase =>
          let (rDelay, _, codeDelay) := compileRtlExprToAmdGpu 1 wDelay.expr
          let (rPhase, _, codePhase) := compileRtlExprToAmdGpu 1 wPhase.expr
          let vgprsDelay :=
            runAmdGpuVop64Prog (fun _ => 4#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeDelay
          let vgprsPhase :=
            runAmdGpuVop64Prog (fun _ => 3#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codePhase
          vgprsDelay rDelay == 56#64 &&
          vgprsPhase rPhase == 90#64
        | _, _ => false)
     | _, _ => false) = true := by
  decide +kernel

/-! ## 10. Full-Stack `.obend` Bitwise, Shift, Signed Order & `Q32.32` Fixed-Point Surface Lowering -/

/-- Userspace `.obend` source exercising hex literals (`0xFF`, `0x0F`, `0x01`), bitwise operators (`&`, `|`, `^`),
shifts (`<<`, `>>`), and `Q32.32` fixed-point intrinsics (`q32FromInt`, `qmul32`, `q32ToInt`). -/
def obendBitwiseQ32Source : String :=
  "edition ObjectiveBend 1\n" ++
  "record BitwiseQ32Target:\n" ++
  "  maskVal() -> Nat\n" ++
  "  q32Scaled(x: Nat) -> Nat\n\n" ++
  "spec BitwiseQ32Base for BitwiseQ32Target:\n" ++
  "  requires maskVal() -> Nat\n" ++
  "  def maskVal() -> Nat:\n" ++
  "    (0xFFn & 0x0Fn) | (0x01n << 4n)\n" ++
  "  def q32Scaled(x: Nat) -> Nat:\n" ++
  "    q32ToInt(qmul32(q32FromInt(x), q32FromInt(3n))) ^ (self.maskVal >> 1n)\n\n" ++
  "def seedBitwiseQ32() -> BitwiseQ32Target:\n" ++
  "  {maskVal: 0n, q32Scaled: fn(x: Nat) -> Nat: 0n}\n\n" ++
  "def bitwiseQ32Inst() -> BitwiseQ32Target:\n" ++
  "  fix(BitwiseQ32Base, seedBitwiseQ32())\n"

#obend_decl StdBitwiseQ32 named "BitwiseQ32Mod"
  "edition ObjectiveBend 1\nrecord BitwiseQ32Target:\n  maskVal() -> Nat\n  q32Scaled(x: Nat) -> Nat\n\nspec BitwiseQ32Base for BitwiseQ32Target:\n  requires maskVal() -> Nat\n  def maskVal() -> Nat:\n    (0xFFn & 0x0Fn) | (0x01n << 4n)\n  def q32Scaled(x: Nat) -> Nat:\n    q32ToInt(qmul32(q32FromInt(x), q32FromInt(3n))) ^ (self.maskVal >> 1n)\n\ndef seedBitwiseQ32() -> BitwiseQ32Target:\n  {maskVal: 0n, q32Scaled: fn(x: Nat) -> Nat: 0n}\n\ndef bitwiseQ32Inst() -> BitwiseQ32Target:\n  fix(BitwiseQ32Base, seedBitwiseQ32())\n"
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

/-- Userspace `.obend` source exercising unary bitwise complement (`~`), logical right shift (`>>>` / `lshr`),
signed two's-complement comparisons (`<s`, `<=s`), named bitwise/shift intrinsics (`bitAnd`, `bitXor`, `shl`),
and a mixed 0-arg cell + 2-argument method `Book`. -/
def obendFullSurfaceSource : String :=
  "edition ObjectiveBend 1\n" ++
  "record FullSurfaceTarget:\n" ++
  "  negOneMask() -> Nat\n" ++
  "  lshrCheck(x: Nat) -> Nat\n" ++
  "  signedCmpBlend(a: Nat, b: Nat) -> Nat\n\n" ++
  "spec FullSurfaceBase for FullSurfaceTarget:\n" ++
  "  requires negOneMask() -> Nat\n" ++
  "  def negOneMask() -> Nat:\n" ++
  "    ~0n\n" ++
  "  def lshrCheck(x: Nat) -> Nat:\n" ++
  "    (self.negOneMask >>> 60n) + lshr(x, 2n)\n" ++
  "  def signedCmpBlend(a: Nat, b: Nat) -> Nat:\n" ++
  "    if (self.negOneMask <s a) && (a <=s b) then bitAnd(a, 0xFFn) | shl(b, 4n) else bitXor(a, b)\n\n" ++
  "def seedFullSurface() -> FullSurfaceTarget:\n" ++
  "  {negOneMask: 0n, lshrCheck: fn(x: Nat) -> Nat: 0n, signedCmpBlend: fn(a: Nat, b: Nat) -> Nat: 0n}\n\n" ++
  "def fullSurfaceInst() -> FullSurfaceTarget:\n" ++
  "  fix(FullSurfaceBase, seedFullSurface())\n"

#obend_decl StdFullSurface named "FullSurfaceRichMod"
  "edition ObjectiveBend 1\nrecord FullSurfaceTarget:\n  negOneMask() -> Nat\n  lshrCheck(x: Nat) -> Nat\n  signedCmpBlend(a: Nat, b: Nat) -> Nat\n\nspec FullSurfaceBase for FullSurfaceTarget:\n  requires negOneMask() -> Nat\n  def negOneMask() -> Nat:\n    ~0n\n  def lshrCheck(x: Nat) -> Nat:\n    (self.negOneMask >>> 60n) + lshr(x, 2n)\n  def signedCmpBlend(a: Nat, b: Nat) -> Nat:\n    if (self.negOneMask <s a) && (a <=s b) then bitAnd(a, 0xFFn) | shl(b, 4n) else bitXor(a, b)\n\ndef seedFullSurface() -> FullSurfaceTarget:\n  {negOneMask: 0n, lshrCheck: fn(x: Nat) -> Nat: 0n, signedCmpBlend: fn(a: Nat, b: Nat) -> Nat: 0n}\n\ndef fullSurfaceInst() -> FullSurfaceTarget:\n  fix(FullSurfaceBase, seedFullSurface())\n"
/-- **Theorem (`userspace_obend_full_surface_rich_and_stateful_verified`)**:
Elaborates `FullSurfaceRichMod` (`~`, `>>>`, `lshr`, `<s`, `<=s`, `bitAnd`, `bitXor`, `shl`, and a
mixed 0-arg cell + 2-argument method `Book`) and verifies:
1. `StdFullSurface` elaborates (the `#obend_decl` command succeeded),
2. `compileBookToRtl`, `compileBookToRtlSat`, and `compileRichBookToRtl` all synthesize valid
   2-input `RtlModule`s (`checkRtlModule = true`, `inputNames = ["arg0", "arg1"]`),
3. `~0n = 0xFFFFFFFFFFFFFFFF#64` (`-1` in signed two's complement), `(negOneMask >>> 60) + lshr(16, 2) = 19#64`,
   `signedCmpBlend(16, 20) = 336#64` (`-1 <s 16` and `16 <=s 20`), and `signedCmpBlend(9, 3) = 10#64`,
4. `Obend.Hardware.Silicon.emitHierarchicalSV` emits all hard-IP macro headers alongside the top module. -/
theorem userspace_obend_full_surface_rich_and_stateful_verified :
    let emptyCtx : Obend.Hardware.Types.RtlLayoutCtx :=
      { structSlices := [], unionTagBits := 8, unionArms := [] }
    (match compileBookToRtl "full_surface_wrap" StdFullSurface.fullSurfaceInst_book,
           compileBookToRtlSat "full_surface_sat" StdFullSurface.fullSurfaceInst_book,
           compileRichBookToRtl "full_surface_rich" emptyCtx StdFullSurface.fullSurfaceInst_book with
     | some mWrap, some mSat, some mRich =>
       let inA : Nat → BitVec 64 := fun i => if i == 0 then 16#64 else if i == 1 then 20#64 else 0#64
       let inB : Nat → BitVec 64 := fun i => if i == 0 then 9#64 else if i == 1 then 3#64 else 0#64
       let zEnv : Nat → BitVec 64 := fun _ => 0#64
       checkRtlModule mWrap &&
       checkRtlModule mSat &&
       checkRtlModule mRich &&
       (mWrap.inputNames == ["arg0", "arg1"]) &&
       (mSat.inputNames == ["arg0", "arg1"]) &&
       (mRich.inputNames == ["arg0", "arg1"]) &&
       (evalModuleOutputs mWrap inA zEnv ==
         [ ("out_negOneMask", 0xFFFFFFFFFFFFFFFF#64)
         , ("out_lshrCheck", 19#64)
         , ("out_signedCmpBlend", 336#64) ]) &&
       (evalModuleOutputs mSat inA zEnv ==
         [ ("out_negOneMask", 0xFFFFFFFFFFFFFFFF#64)
         , ("out_lshrCheck", 19#64)
         , ("out_signedCmpBlend", 336#64) ]) &&
       (evalModuleOutputs mRich inB zEnv ==
         [ ("out_negOneMask", 0xFFFFFFFFFFFFFFFF#64)
         , ("out_lshrCheck", 17#64)
         , ("out_signedCmpBlend", 10#64) ]) &&
       (let stepSpec : StatefulStepSpec :=
          { moduleName  := "full_surface_step"
          , inputNames  := ["din"]
          , stateRegs   := [{ regIdx := 0, name := "acc", initVal := 0#64,
                              nextExpr := .alu .add (.regRead 0) (.inputPort 0) }]
          , outputExprs := [("acc_out", .regRead 0)] }
        let mStep := compileStatefulStepToRtl stepSpec
        let inValid : Nat → BitVec 64 := fun i => if i == 0 then 9#64 else 1#64
        let st1 := stepModuleRegs mStep false inValid zEnv
        checkRtlModule mStep && (st1 0 == 9#64))
     | _, _, _ => false) = true := by
  decide +kernel

end Obend.Hardware.UserspacePhysical
end
