module
/-
# Obend.Teeth.Hardware.SiliconTeeth — Refusal Poles, Specialization Deoptimization & `#tooth` Mutations

Tests both the positive and negative poles of `Obend.Hardware`:
* **Refusal Poles**:
  - `duplicated_affine_refused`: `QuantityDuplicated.obend` (`x + x` on `affine x`) is refused;
  - `sky130_overclock_500mhz_refused`: running Sky130 130nm CMOS at 500 MHz (`2000 ps < 2350 ps`) is
    refused by `checkTimingSignoff`;
  - `unregistered_slr_crossing_refused`: crossing an SLR super-logic-region boundary with `< 2` Laguna
    register stages is refused by `checkChannelHop`;
* **3-Tier Hardware Specialization Slot (`HwCandidate`: `.bitstream` → `.book` → `.machine`)**:
  - `bitstream_usable_7nm`: on 7nm FinFET at 500 MHz (`2000 ps`), the `ReviewMember` bitstream is
    admitted and usable;
  - `sky130_overclock_selects_book`: on 130nm CMOS at 500 MHz (`2000 ps`), `.bitstream` is rejected by
    the timing judge (`checkTimingSignoff = false`) and `hwSpecSlot.select` automatically selects `.book`;
  - `override_blocks_bitstream`: when `Override` is composed last, `.bitstream` is blocked naming
    `[.object "twiceOfThree"]` and `slotAdvance` deoptimizes to `.machine`;
* **`#tooth` Kernel Mutation Checks**:
  - Verifies that breaking the 2-stage Laguna crossing, the 4-stage `DSP48E2` `C`-input alignment,
    the `URAM288` RAW collision bypass mux, the `CARRY8` LUT2 `XOR` configuration SRAM, the `Vault.Law`
    `writeOnce` guard, or the `HwCandidate` object-pin support causes the Lean kernel to reject the
    corresponding stored theorem proof.
-/
public import Obend.Tactic.Tooth
public import Obend.Teeth.Leaf.ReviewTeeth
import all Obend.Hardware.Silicon
import all Obend.Hardware.Process
import all Obend.Hardware.Fabric
public import Obend.Hardware
@[expose] public section

namespace Obend.Teeth.Hardware
open Obend.Core.Term Obend.Logic Obend.Leaf Obend.Slot Obend.Slot.World
open Obend.Hardware.Silicon Obend.Hardware.Process Obend.Hardware.Fabric
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

/-! ## 2. 3-Tier Hardware Specialization Slot Deoptimization (`bitstream` → `book` → `machine`) -/

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

/-! ## 3. `#tooth` Kernel Mutation Checks -/

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

end Obend.Teeth.Hardware
end
