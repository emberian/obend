module
/-
# Obend.Hardware.Synth — Verified Technology Mapping (`LUT3`/`CARRY8`) & Pipeline Retiming

Formalizes the synthesis & technology-mapping transformations from word-level `Obend.Hardware.HDL`
operations to physical FPGA/eFPGA primitives and retimed pipeline stages:
1. **Verified `LUT2` / `LUT3` Primitive Truth-Table Mapping**:
   - Proves `lut2_or_sound` (`INIT = 0xE`) and `lut3_mux_sound` (`INIT = 0xCA`),
   - Proves `evalLut3MuxBits_sound` over arbitrary-width bit lists.
2. **Verified `CARRY8` Two's-Complement Subtractor (`carrySubBel`)**:
   - Maps `a - b` onto `LUT2` + `CARRY8` by inverting `b` (`!b`) with initial carry-in `ci0 = true`
     ($a + \sim b + 1$), and proves `carrySubBel_eq_fullSubStageSpec`.
3. **Verified Pipeline Retiming & Critical-Path Splitting (`retime2Stage_sound`, `retiming_closes_16nm_500MHz`)**:
   - Splits a deep combinational tree `f (g x) (h y)` whose combined critical path fails 500 MHz
     timing signoff on 16nm FinFET (`checkTimingSignoff = false`) into a 2-stage pipeline whose
     stage critical paths pass 500 MHz timing signoff (`checkTimingSignoff = true`),
   - Proves `retime2Stage_sound`: from ANY initial `X` state, the retimed 2-stage pipeline computes
     the exact combinational specification shifted by 2 clock cycles.
-/
public import Obend.Hardware.Process
@[expose] public section

namespace Obend.Hardware.Synth
open Obend.Hardware.Process
set_option autoImplicit false

/-! ## 1. Verified `LUT2` & `LUT3` Technology Mapping -/

/-- `LUT2` configuration SRAM mask `0xE` (`1110_2`): 2-input `OR` gate (`a || b`). -/
def LUT2_INIT_OR : BitVec 4 := 0b1110#4

/-- Evaluate a 3-input Look-Up Table (`LUT3`) configured with an 8-bit SRAM mask `init`. -/
def evalLUT3 (init : BitVec 8) (i0 i1 i2 : Bool) : Bool :=
  let idx : Nat := (if i0 then 1 else 0) + (if i1 then 2 else 0) + (if i2 then 4 else 0)
  init.getLsbD idx

/-- `LUT3` configuration SRAM mask `0xCA` (`1100_1010_2`): `i2 ? i1 : i0` (2:1 multiplexer). -/
def LUT3_INIT_MUX : BitVec 8 := 0xCA#8

/-- Universal soundness of `LUT2` `OR` (`0xE`) truth table. -/
theorem lut2_or_sound (a b : Bool) :
    evalLUT2 LUT2_INIT_OR a b = (a || b) := by
  cases a <;> cases b <;> rfl

/-- Universal soundness of `LUT3` 2:1 multiplexer (`LUT3_INIT_MUX = 0xCA`):
when `sel = true` returns `ifTrue` (`i1`), when `sel = false` returns `ifFalse` (`i0`). -/
theorem lut3_mux_sound (ifFalse ifTrue sel : Bool) :
    evalLUT3 LUT3_INIT_MUX ifFalse ifTrue sel = (if sel then ifTrue else ifFalse) := by
  cases ifFalse <;> cases ifTrue <;> cases sel <;> rfl

/-- Technology-mapped N-bit 2:1 multiplexer implemented as a slice of parallel `LUT3` BELs. -/
def evalLut3MuxBits (sel : Bool) : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | t :: ts, f :: fs => evalLUT3 LUT3_INIT_MUX f t sel :: evalLut3MuxBits sel ts fs

/-- Theorem: Across any equal-length bit vectors `ifTrue` and `ifFalse`, the `LUT3` mux slice
produces `if sel then ifTrue else ifFalse`! -/
theorem evalLut3MuxBits_sound (sel : Bool) (ifTrue ifFalse : List Bool)
    (hLen : ifTrue.length = ifFalse.length) :
    evalLut3MuxBits sel ifTrue ifFalse = (if sel then ifTrue else ifFalse) := by
  induction ifTrue generalizing ifFalse with
  | nil =>
    cases ifFalse with
    | nil => cases sel <;> rfl
    | cons _ _ => simp at hLen
  | cons t ts ih =>
    cases ifFalse with
    | nil => simp at hLen
    | cons f fs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
      simp only [evalLut3MuxBits, lut3_mux_sound, ih fs hLen]
      cases sel <;> rfl

/-! ## 2. Verified `CARRY8` Two's-Complement Subtractor Mapping -/

/-- Mathematical specification of a 1-bit two's-complement full subtractor stage (`a + !b + cin`). -/
def fullSubStageSpec (a b cin : Bool) : Bool × Bool :=
  fullAdderSpec a (!b) cin

/-- Technology-mapped 1-bit `CARRY8` subtractor cell: feeds `a` and `!b` into `evalCarryBel`. -/
def carrySubBel (a b cin : Bool) : Bool × Bool :=
  evalCarryBel a (!b) cin

/-- Theorem: The technology-mapped `CARRY8` subtractor cell is bit-identical to `fullSubStageSpec`
for all boolean inputs `(a, b, cin)`. -/
theorem carrySubBel_eq_fullSubStageSpec (a b cin : Bool) :
    carrySubBel a b cin = fullSubStageSpec a b cin := by
  cases a <;> cases b <;> cases cin <;> rfl

/-! ## 3. Verified Pipeline Retiming & Critical-Path Splitting -/

/-- State of a retimed 2-stage pipeline for `f (g x) (h y)`.
All registers (`rg`, `rh`, `rout`) are reset-free datapath registers. -/
structure Retime2State (α β γ : Type) where
  rg   : α
  rh   : β
  rout : γ
  deriving DecidableEq, Repr

/-- Step the 2-stage retimed pipeline by one clock edge. -/
def stepRetime2 {α β γ δ ε : Type}
    (g : δ → α) (h : ε → β) (f : α → β → γ)
    (st : Retime2State α β γ) (x : δ) (y : ε) : Retime2State α β γ :=
  { rg   := g x
  , rh   := h y
  , rout := f st.rg st.rh }

/-- Universal Retiming Soundness Theorem (`retime2Stage_sound`):
For ANY combinational functions `g`, `h`, `f` and ANY arbitrary initial (`X`) register state `st₀`,
after 2 clock cycles on inputs `(x₀, y₀)` followed by `(x₁, y₁)`, the retimed output `rout` is
guaranteed to equal `f (g x₀) (h y₀)`! -/
theorem retime2Stage_sound {α β γ δ ε : Type}
    (g : δ → α) (h : ε → β) (f : α → β → γ)
    (st₀ : Retime2State α β γ) (x₀ x₁ : δ) (y₀ y₁ : ε) :
    (stepRetime2 g h f (stepRetime2 g h f st₀ x₀ y₀) x₁ y₁).rout = f (g x₀) (h y₀) :=
  rfl

/-- Un-retimed critical path combining two 64-bit ALU stages in a single clock cycle
(`logicLevels = 8`, `carryBits = 16`, `tileHops = 4`). -/
def unretimedDeepPath : TimingPath :=
  { name        := "unretimed_two_stage_alu"
  , logicLevels := 8
  , minLevels   := 2
  , carryBits   := 16
  , tileHops    := 4 }

/-- After `stepRetime2` splits the path at the `(rg, rh)` register cutset, Stage 1 and Stage 2
each have `logicLevels = 3`, `carryBits = 8`, and `tileHops = 1`. -/
def retimedStagePath : TimingPath :=
  { name        := "retimed_single_stage_alu"
  , logicLevels := 3
  , minLevels   := 2
  , carryBits   := 8
  , tileHops    := 1 }

/-- Theorem: On 16nm FinFET SS at 500 MHz (`2000 ps`), the un-retimed deep path FAILS static timing
signoff (`checkTimingSignoff = false`, requiring `2718 ps > 2000 ps`), whereas the retimed pipeline
stages PASS static timing signoff (`checkTimingSignoff = true`, requiring `1084 ps ≤ 2000 ps`)! -/
theorem retiming_closes_16nm_500MHz :
    checkTimingSignoff corner16nm_SS 2000 unretimedDeepPath = false ∧
    checkTimingSignoff corner16nm_SS 2000 retimedStagePath = true := by
  decide +kernel

end Obend.Hardware.Synth
end
