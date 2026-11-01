module
/-
# Obend.Teeth.Hardware.SiliconTeeth — Refusal Poles, HDL/Compiler/FabuBlox Verification & `#tooth` Mutations

Tests both the positive and negative poles of `Obend.Hardware` across all 7 modules
(`Silicon`, `Process`, `Fabric`, `HDL`, `Compiler`, `Synth`, `FabuBlox`):
* **Refusal Poles**:
  - `duplicated_affine_refused`: `QuantityDuplicated.obend` (`x + x` on `affine x`) is refused;
  - `sky130_overclock_500mhz_refused`: running Sky130 130nm CMOS at 500 MHz (`2000 ps < 2350 ps`) is
    refused by `checkTimingSignoff`;
  - `unregistered_slr_crossing_refused`: crossing an SLR super-logic-region boundary with `< 2` Laguna
    register stages is refused by `checkChannelHop`;
  - `combinational_loop_refused`: a self-referential wire (`w_0 := w_0 + 1`) is refused by `checkWireTableDAG`;
  - `unsynchronized_cdc_refused`: reading a `.coreClk` register from `.axiIoClk` without a 2-FF
    synchronizer is refused by `checkModuleCdc`;
  - `fabublox_under_and_over_etch_refused`: under-etching the `100 nm` ILD oxide (`80 nm`) or
    punching through the `20 nm` $\text{TiN}$ barrier (`350 nm` at `10:1` selectivity) is refused by
    FabuBlox `checkFacilityStep`.
* **Whole-Book Compilation (`Obend.Leaf.emit` → `Obend.Hardware.HDL.RtlModule`)**:
  - `review_book_compiled_rtl_verified`: compiles the actual `Obend.Leaf.emit (comp 1)` book of
    `ReviewMember.obend` via `compileBookToRtl`, verifies `checkRtlModule = true` (DAG + CDC), and
    proves its hardware evaluation yields `out_review = 1` and `out_twice(3) = 7`.
* **3-Tier Hardware Specialization Slot (`HwCandidate`: `.bitstream` → `.book` → `.machine`)**:
  - `bitstream_usable_7nm`, `override_blocks_bitstream`, `sky130_overclock_rejects_bitstream_keeps_book`.
* **10 `#tooth` Kernel Mutation Checks**:
  - Verifies that mutating Laguna crossings, `DSP48E2` `C`-input alignment, `URAM288` RAW collision
    bypass, `CARRY8` LUT2 `XOR` config, `Vault.Law` `writeOnce`, `HwCandidate` object-pin support,
    `HDL` CDC checking, `Compiler` primitive lowering, `Synth` `LUT3` mux config, or `FabuBlox`
    FEOL copper contamination rules causes the Lean kernel to reject the stored theorem proof.
-/
public import Obend.Tactic.Tooth
public import Obend.Teeth.Leaf.ReviewTeeth
import all Obend.Hardware.Silicon
import all Obend.Hardware.Process
import all Obend.Hardware.Fabric
import all Obend.Hardware.HDL
import all Obend.Hardware.Compiler
import all Obend.Hardware.Synth
import all Obend.Hardware.FabuBlox
public import Obend.Hardware
@[expose] public section

namespace Obend.Teeth.Hardware
open Obend.Core.Term Obend.Logic Obend.Leaf Obend.Slot Obend.Slot.World
open Obend.Hardware.Silicon Obend.Hardware.Process Obend.Hardware.Fabric
open Obend.Hardware.HDL Obend.Hardware.Compiler Obend.Hardware.Synth Obend.Hardware.FabuBlox
open Obend.Teeth.Leaf.Review (comp overridden view deadCells)
set_option autoImplicit false

/-! ## 1. Negative-Pole Refusal Checks -/

/-- `QuantityDuplicated.obend` (`affine x` used twice in `x + x`) is refused by the wire-fanout checker. -/
theorem duplicated_affine_refused :
    checkNetlistMult quantityDuplicatedInputs quantityDuplicatedNet = false :=
  rfl

/-- Overclocking SkyWater 130nm CMOS (`requiredPeriodPs = 2350 ps`) to 500 MHz (`2000 ps`) is refused. -/
theorem sky130_overclock_500mhz_refused :
    checkTimingSignoff corner130nm_SS 2000 obendStageCritPath = false :=
  rfl

/-- An inter-SLR die crossing with only 1 register stage (`regStages = 1 < 2`) is refused. -/
theorem unregistered_slr_crossing_refused :
    checkChannelHop ⟨"ch0", ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, 64, 1⟩ =
      .error (.illegalSlrCrossing "ch0" ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ 1) :=
  rfl

/-- A combinational wire table containing a self-loop (`w_0 := w_0 + 1`) is refused by `checkWireTableDAG`. -/
theorem combinational_loop_refused :
    checkWireTableDAG 1 0 [⟨0, "loop", .alu .add (.wireRef 0) (.const 1#64)⟩] = false :=
  rfl

/-- An unsynchronized clock-domain crossing from `.coreClk` (`reg 0`) to `.axiIoClk` (`reg 1`,
`isSynchronizer = false`) is refused by `checkModuleCdc`. -/
theorem unsynchronized_cdc_refused :
    let r0 : RegSpec := ⟨0, "core_r", .coreClk, .resetFree, false, .inputPort 0⟩
    let r1 : RegSpec := ⟨1, "axi_r", .axiIoClk, .resetFree, false, .regRead 0⟩
    checkModuleCdc [r0, r1] = false :=
  rfl

/-- FabuBlox `Facility OS` refuses both under-etching the `100 nm` ILD oxide (`80 nm`) and
over-etching through the `20 nm` $\text{TiN}$ landing pad (`350 nm` at `10:1` selectivity). -/
theorem fabublox_under_and_over_etch_refused :
    checkFacilityStep initialCmosWafer (.anisotropicRieOxide 80 10) =
      some (.viaUnderEtchUnopened 0 80 100) ∧
    checkFacilityStep initialCmosWafer (.anisotropicRieOxide 350 10) =
      some (.viaOverEtchPunchThrough 0 25 20) :=
  ⟨rfl, rfl⟩

/-! ## 2. End-to-End Compilation of `Obend.Leaf.emit (comp 1)` to `RtlModule` -/

/-- Compiling the actual `ReviewMember.obend` leaf book `emit (comp 1)` through `compileBookToRtl`
produces a valid `RtlModule` (`checkRtlModule = true`) whose hardware evaluation at `arg = 3` yields
`out_review = 5` (`(3 + 1) + 1`) and `out_twice = 7` (`review(review(3))`)! -/
theorem review_book_compiled_rtl_verified :
    (match compileBookToRtl "obend_review_compiled" (emit (comp 1)) with
    | some m =>
      checkRtlModule m &&
      (evalModuleOutputs m (fun _ => 3#64) (fun _ => 0#64) ==
        [("out_review", 5#64), ("out_twice", 7#64)])
    | none => false) = true := by
  decide +kernel

/-! ## 3. 3-Tier Hardware Specialization Slot Deoptimization (`bitstream` → `book` → `machine`) -/

def reviewBitstream7nm : HwCandidate :=
  .bitstream "twiceOfThree" (comp 1) corner7nm_SS 2000 obendStageCritPath

def reviewBitstream130nmOverclock : HwCandidate :=
  .bitstream "twiceOfThree" (comp 1) corner130nm_SS 2000 obendStageCritPath

def hwDeadCells : Reading LeafPin HwCandidate → List LeafCell
  | .blocked _ d => d.map (·.cell)
  | _ => []

/-- At 500 MHz (`2000 ps`) on 7nm FinFET SS, the `ReviewMember` bitstream is admitted and usable. -/
theorem bitstream_usable_7nm :
    hwSpecSlot.usable (holdsAt (view (comp 1) 0)) reviewBitstream7nm = true := by
  decide +kernel

/-- When `Override` is composed last, the 7nm bitstream is blocked naming `.object "twiceOfThree"`. -/
theorem override_blocks_bitstream :
    hwDeadCells (hwSpecSlot.read (holdsAt (view overridden 1)) (some reviewBitstream7nm)) =
      [.object "twiceOfThree"] := by
  decide +kernel

/-- When overclocked to 500 MHz (`2000 ps`) on 130nm CMOS, the `.bitstream` candidate fails
`checkTimingSignoff` (`usable = false`), while the software `.book` candidate remains usable! -/
theorem sky130_overclock_rejects_bitstream_keeps_book :
    hwSpecSlot.usable (holdsAt (view (comp 1) 0)) reviewBitstream130nmOverclock = false ∧
    hwSpecSlot.usable (holdsAt (view (comp 1) 0)) (.book "twiceOfThree" (comp 1)) = true := by
  decide +kernel

/-! ## 4. `#tooth` Kernel Mutation Checks (10 Mutations) -/

/-- Broken 2-stage Laguna crossing that copies `d` straight into both `s1` and `s2`. -/
def stepPipe2Broken {w : Nat} (_st : Pipe2State w) (d : BitVec w) : Pipe2State w :=
  { s1 := d, s2 := d }

#tooth Obend.Hardware.Silicon.pipe2_x_free by mutation Obend.Hardware.Silicon.stepPipe2 := stepPipe2Broken

/-- Broken `DSP48E2` MAC that forgets the `c2` pipeline register stage (`c3 := c_in` instead of `st.c2`). -/
def stepDspMacBroken {w : Nat} (st : DspMacState w) (a_in b_in c_in : BitVec w) : DspMacState w :=
  { a1   := a_in
  , b1   := b_in
  , a2   := st.a1
  , b2   := st.b1
  , c2   := c_in
  , mreg := st.a2 * st.b2
  , c3   := c_in
  , preg := st.mreg + st.c3 }

#tooth Obend.Hardware.Silicon.dspMac_latency_4 by mutation Obend.Hardware.Silicon.stepDspMac := stepDspMacBroken

/-- Broken `URAM288` / SRAM wrapper that ignores the RAW collision bypass mux and always reads `st.ram.dout`. -/
def readBypassRAMNoBypass {w : Nat} (st : BypassRAMState w) : Option (BitVec w) :=
  st.ram.dout

#tooth Obend.Hardware.Silicon.bypassRAM_exact_latest_write by mutation Obend.Hardware.Silicon.readBypassRAM := readBypassRAMNoBypass

-- Broken `CARRY8` LUT2 configuration that programs `LUT2_INIT_AND` (`0x8`) instead of `LUT2_INIT_XOR` (`0x6`).
#tooth Obend.Hardware.Process.carryBel_eq_fullAdderSpec by mutation Obend.Hardware.Process.LUT2_INIT_XOR := LUT2_INIT_AND

/-- Broken `DeosCounter` + `Vault.Law` register bank that allows overwriting non-zero `cfgTag` (`writeOnce` omitted). -/
def stepDeosHwNoWriteOnce (st : DeosHwState) : DeosCmd → DeosHwState
  | .inc d => { st with count := st.count + d, lastAccepted := true }
  | .dec d => { st with count := st.count - d, lastAccepted := true }
  | .reset hasCred =>
    if hasCred then { st with count := 0, lastAccepted := true }
    else { st with lastAccepted := false }
  | .writeTag tag => { st with cfgTag := tag, lastAccepted := true }

#tooth Obend.Hardware.Fabric.deosHw_writeOnce_immutable by mutation Obend.Hardware.Fabric.stepDeosHw := stepDeosHwNoWriteOnce

/-- Broken `HwCandidate.supports` that omits the object composition pin from `.bitstream`. -/
def hwSupportsLayersOnly : HwCandidate → List LeafPin
  | .bitstream _ C _ _ _ => C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .book name C         => ⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .machine             => []

#tooth Obend.Hardware.Fabric.hwBitstream_usable_sound by mutation Obend.Hardware.Fabric.HwCandidate.supports := hwSupportsLayersOnly

/-- Broken CDC checker that allows any cross-clock register read without checking `dstReg.isSynchronizer`. -/
def checkRegCdcPermissive (allRegs : List RegSpec) (dstReg : RegSpec) : Bool :=
  (exprReadRegs dstReg.nextExpr).all fun srcIdx =>
    (lookupRegDomain allRegs srcIdx).isSome

#tooth Obend.Hardware.HDL.cdcSafe_no_unsynchronized_crossing by mutation Obend.Hardware.HDL.checkRegCdc := checkRegCdcPermissive

/-- Broken `compilePrim` that compiles `.subtract` to `.add` instead of `.sub`. -/
def compilePrimSubAsAdd (op : Primitive) (l r : RtlExpr) : Option RtlExpr :=
  match op with
  | .add         => some (.alu .add l r)
  | .multiply    => some (.alu .mul l r)
  | .subtract    => some (.alu .add l r)
  | .equal       => some (.alu .eq l r)
  | .conjunction => some (.alu .bitAnd l r)
  | .less        => some (.alu .ult l r)
  | .lessEqual   => some (.mux (.alu .ult r l) (.const 0#64) (.const 1#64))
  | _            => none

#tooth Obend.Hardware.Compiler.compilePrim_sound by mutation Obend.Hardware.Compiler.compilePrim := compilePrimSubAsAdd

/-- Broken `LUT3` mux configuration (`0xAC` instead of `0xCA`, inverting the `sel` polarity). -/
def LUT3_INIT_MUX_INVERTED : BitVec 8 := 0xAC#8

#tooth Obend.Hardware.Synth.lut3_mux_sound by mutation Obend.Hardware.Synth.LUT3_INIT_MUX := LUT3_INIT_MUX_INVERTED

/-- Broken FabuBlox `checkFacilityStep` that forgets to check `hasExposedCuOrAu` before entering `.feolFurnace`. -/
def checkFacilityStepNoCuCheck (st : WaferState) (step : FabStep) : Option FacilityError :=
  let temp := stepTempC step
  if temp > 150 && hasPhotoresist st then
    some (.photoresistScorched temp)
  else
    none

#tooth Obend.Hardware.FabuBlox.facilityCheck_prevents_feol_contamination by mutation Obend.Hardware.FabuBlox.checkFacilityStep := checkFacilityStepNoCuCheck

end Obend.Teeth.Hardware
end
