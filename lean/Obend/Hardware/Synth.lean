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
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.Synth
open Obend.Hardware.Process Obend.Hardware.HDL
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
-- fixture kept (2026-11-04): a discriminating pair: the same path fails timing unretimed and closes retimed
example :
    checkTimingSignoff corner16nm_SS 2000 unretimedDeepPath = false ∧
    checkTimingSignoff corner16nm_SS 2000 retimedStagePath = true := by
  decide +kernel

/-! ## 4. General `RtlModule` → `BelNetlist` Technology Mapping & Soundness Theorems -/

/-- Physical FPGA Basic Element of Logic (BEL) primitive kinds targeted by technology mapping. -/
inductive BelKind where
  | constBel (val : BitVec 64)
  | portIn   (portIdx : Nat)
  | wireTap  (wireIdx : Nat)
  | lut1     (initMask : Nat)   -- 1-input LUT (e.g., `0x1` inverter for `.bitNot`, `0x2` buffer)
  | lut2     (initMask : Nat)   -- 2-input LUT (`0x8` AND, `0xE` OR, `0x6` XOR)
  | lut3     (initMask : Nat)   -- 3-input LUT (`0xCA` 2:1 MUX)
  | carry4                      -- Fast lookahead carry chain primitive (`CARRY4` / `CARRY8`)
  | dspMul                      -- Hard DSP multiplier slice (`DSP48E2` / `DSP58`)
  | ff       (resetKind : ResetKind) -- Synchronous flip-flop BEL (`FDRE` / `FDPE`)
  | route    (op : RtlWidthOp)  -- A width operator: routing, constant zeros and sign fan-out, no logic
  deriving DecidableEq, Repr

/-- A technology-mapped Basic Element of Logic (`BelCell`) in the post-synthesis FPGA netlist. -/
structure BelCell where
  dstName : String
  kind    : BelKind
  inputs  : List String
  deriving DecidableEq, Repr

/-- Complete technology-mapped BEL netlist synthesized from an `RtlModule`. -/
structure BelNetlist where
  moduleName  : String
  inputNames  : List String
  cells       : List BelCell
  outputNames : List String
  deriving DecidableEq, Repr

/-- Compute the binary truth-table address $\sum_k b_k 2^k$ of a list of boolean LUT inputs. -/
def lutInputIndex : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * lutInputIndex rest

/-- Evaluate an arbitrary $k$-input LUT with configuration mask `initMask` on `inputs`. -/
def evalLut (initMask : Nat) (inputs : List Bool) : Bool :=
  ((initMask >>> lutInputIndex inputs) &&& 1) == 1

/-- **Universal Bitwise `LUT2` Technology-Mapping Soundness (`lut2_bitwise_synth_sound`)**:
For all `a, b : Bool`, `LUT2` mask `0x8` computes `a && b`, `0xE` computes `a || b`, and `0x6`
computes `xor a b`. -/
theorem lut2_bitwise_synth_sound (a b : Bool) :
    evalLut 0x8 [a, b] = (a && b) ∧
    evalLut 0xE [a, b] = (a || b) ∧
    evalLut 0x6 [a, b] = xor a b := by
  cases a <;> cases b <;> decide

/-- **Universal 2:1 Multiplexer `LUT3` Technology-Mapping Soundness (`lut3_mux_synth_sound`)**:
For all `d0, d1, sel : Bool`, `LUT3` mask `0xCA` computes `if sel then d1 else d0`. -/
theorem lut3_mux_synth_sound (d0 d1 sel : Bool) :
    evalLut 0xCA [d0, d1, sel] = (if sel then d1 else d0) := by
  cases d0 <;> cases d1 <;> cases sel <;> decide

/-- Synthesize a combinational `RtlExpr` driving net `dstName` into a topologically ordered list of
FPGA `BelCell` primitives:
* `.alu .bitAnd` $\mapsto$ `BelKind.lut2 0x8`,
* `.alu .bitOr` $\mapsto$ `BelKind.lut2 0xE`,
* `.alu .bitXor` $\mapsto$ `BelKind.lut2 0x6`,
* `.alu .add` $\mapsto$ `BelKind.lut2 0x6` (propagate XOR) + `BelKind.carry4`,
* `.mux` $\mapsto$ `BelKind.lut3 0xCA`,
* `.bitNot` $\mapsto$ `BelKind.lut1 0x1`,
* `.resize` $\mapsto$ `BelKind.route` (a slice, extension or truncation is wiring). -/
def synthesizeExprToBels (dstName : String) : RtlExpr → List BelCell
  | .const v       => [{ dstName := dstName, kind := .constBel v, inputs := [] }]
  | .inputPort idx => [{ dstName := dstName, kind := .portIn idx, inputs := [s!"in_{idx}"] }]
  | .wireRef idx   => [{ dstName := dstName, kind := .wireTap idx, inputs := [s!"w_{idx}"] }]
  | .regRead idx   => [{ dstName := dstName, kind := .lut1 0x2, inputs := [s!"r_{idx}"] }]
  | .bitNot a      =>
    let aName := dstName ++ "_not_in"
    synthesizeExprToBels aName a ++
      [{ dstName := dstName, kind := .lut1 0x1, inputs := [aName] }]
  | .resize op a   =>
    let aName := dstName ++ "_route_in"
    synthesizeExprToBels aName a ++
      [{ dstName := dstName, kind := .route op, inputs := [aName] }]
  | .mux c t f     =>
    let fName := dstName ++ "_d0"
    let tName := dstName ++ "_d1"
    let cName := dstName ++ "_sel"
    synthesizeExprToBels fName f ++
      synthesizeExprToBels tName t ++
      synthesizeExprToBels cName c ++
      [{ dstName := dstName, kind := .lut3 0xCA, inputs := [fName, tName, cName] }]
  | .alu op a b    =>
    let aName := dstName ++ "_lhs"
    let bName := dstName ++ "_rhs"
    let subBels := synthesizeExprToBels aName a ++ synthesizeExprToBels bName b
    match op with
    | .bitAnd =>
      subBels ++ [{ dstName := dstName, kind := .lut2 0x8, inputs := [aName, bName] }]
    | .bitOr =>
      subBels ++ [{ dstName := dstName, kind := .lut2 0xE, inputs := [aName, bName] }]
    | .bitXor =>
      subBels ++ [{ dstName := dstName, kind := .lut2 0x6, inputs := [aName, bName] }]
    | .add =>
      let propName := dstName ++ "_xor"
      subBels ++
        [ { dstName := propName, kind := .lut2 0x6, inputs := [aName, bName] }
        , { dstName := dstName,  kind := .carry4,   inputs := [aName, bName, propName] } ]
    | .sub =>
      let invName := dstName ++ "_binv"
      let propName := dstName ++ "_xor"
      subBels ++
        [ { dstName := invName,  kind := .lut1 0x1, inputs := [bName] }
        , { dstName := propName, kind := .lut2 0x6, inputs := [aName, invName] }
        , { dstName := dstName,  kind := .carry4,   inputs := [aName, invName, propName] } ]
    | .mul =>
      subBels ++ [{ dstName := dstName, kind := .dspMul, inputs := [aName, bName] }]
    | .eq =>
      let xorName := dstName ++ "_xor"
      subBels ++
        [ { dstName := xorName, kind := .lut2 0x6, inputs := [aName, bName] }
        , { dstName := dstName, kind := .lut1 0x1, inputs := [xorName] } ]
    | .ult =>
      let invName := dstName ++ "_binv"
      subBels ++
        [ { dstName := invName, kind := .lut1 0x1, inputs := [bName] }
        , { dstName := dstName, kind := .carry4,   inputs := [aName, invName] } ]
    | .shl =>
      subBels ++ [{ dstName := dstName, kind := .lut2 0x8, inputs := [aName, bName] }]
    | .lshr =>
      subBels ++ [{ dstName := dstName, kind := .lut2 0x8, inputs := [aName, bName] }]
    | .ashr =>
      subBels ++ [{ dstName := dstName, kind := .lut2 0x8, inputs := [aName, bName] }]
    | .slt =>
      let invName := dstName ++ "_binv"
      subBels ++
        [ { dstName := invName, kind := .lut1 0x1, inputs := [bName] }
        , { dstName := dstName, kind := .carry4,   inputs := [aName, invName] } ]
    | .qmul32 =>
      subBels ++ [{ dstName := dstName, kind := .dspMul, inputs := [aName, bName] }]

/-- Synthesize an entire synchronous `RtlModule` into a technology-mapped `BelNetlist`, mapping all
internal wires, register next-state trees, and output trees via `synthesizeExprToBels`, and mapping
each sequential `RegSpec` to a dedicated `BelKind.ff` flip-flop BEL. -/
def synthesizeModuleToBels (m : RtlModule) : BelNetlist :=
  let wireBels := m.wires.flatMap (fun w => synthesizeExprToBels s!"w_{w.wireIdx}" w.expr)
  let regCombBels := m.regs.flatMap (fun r => synthesizeExprToBels s!"{r.name}_din" r.nextExpr)
  let outBels := m.outputs.flatMap (fun o => synthesizeExprToBels o.name o.expr)
  let ffBels : List BelCell :=
    m.regs.map (fun r => { dstName := r.name, kind := .ff r.resetKind, inputs := [s!"{r.name}_din"] })
  { moduleName  := m.name
  , inputNames  := m.inputNames
  , cells       := wireBels ++ regCombBels ++ outBels ++ ffBels
  , outputNames := m.outputs.map (·.name) }

/-- Check whether a `BelCell` is a sequential flip-flop (`BelKind.ff`). -/
def isFfBel (c : BelCell) : Bool :=
  match c.kind with
  | .ff _ => true
  | _     => false

/-- Count the number of sequential flip-flop (`BelKind.ff`) cells in a `BelNetlist`. -/
def countFfBels (nl : BelNetlist) : Nat :=
  (nl.cells.filter isFfBel).length

/-- Check whether a `BelCell` has a valid input pin arity for its `BelKind`. -/
def checkBelCellValid (c : BelCell) : Bool :=
  match c.kind with
  | .constBel _ => c.inputs.length == 0
  | .portIn _   => c.inputs.length == 1
  | .wireTap _  => c.inputs.length == 1
  | .lut1 _     => c.inputs.length == 1
  | .lut2 _     => c.inputs.length == 2
  | .lut3 _     => c.inputs.length == 3
  | .carry4     => c.inputs.length == 2 || c.inputs.length == 3
  | .dspMul     => c.inputs.length == 2
  | .ff _       => c.inputs.length == 1
  | .route _    => c.inputs.length == 1

/-- Check that every cell in a `BelNetlist` satisfies `checkBelCellValid`. -/
def checkBelNetlistValid (nl : BelNetlist) : Bool :=
  nl.cells.all checkBelCellValid

theorem synthesizeExprToBels_no_ff (dstName : String) (e : RtlExpr) :
    (synthesizeExprToBels dstName e).filter isFfBel = [] := by
  induction e generalizing dstName with
  | const _ => rfl
  | inputPort _ => rfl
  | wireRef _ => rfl
  | regRead _ => rfl
  | bitNot a iha =>
    simp [synthesizeExprToBels, List.filter_append, iha, isFfBel]
  | resize op a iha =>
    simp [synthesizeExprToBels, List.filter_append, iha, isFfBel]
  | mux c t f ihc iht ihf =>
    simp [synthesizeExprToBels, List.filter_append, ihc, iht, ihf, isFfBel]
  | alu op a b iha ihb =>
    cases op <;> simp [synthesizeExprToBels, List.filter_append, iha, ihb, isFfBel]

theorem flatMap_synthesizeExprToBels_no_ff {α : Type}
    (f : α → String) (g : α → RtlExpr) (xs : List α) :
    (xs.flatMap (fun x => synthesizeExprToBels (f x) (g x))).filter isFfBel = [] := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [List.flatMap_cons, List.filter_append, synthesizeExprToBels_no_ff, ih]

theorem map_reg_ff_filter (regs : List RegSpec) :
    (regs.map (fun r => ({ dstName := r.name, kind := .ff r.resetKind, inputs := [s!"{r.name}_din"] } : BelCell))).filter isFfBel =
      regs.map (fun r => { dstName := r.name, kind := .ff r.resetKind, inputs := [s!"{r.name}_din"] }) := by
  induction regs with
  | nil => rfl
  | cons r rest ih =>
    simp [List.map_cons, List.filter_cons, isFfBel, ih]

theorem synthesizeExprToBels_valid (dstName : String) (e : RtlExpr) :
    (synthesizeExprToBels dstName e).all checkBelCellValid = true := by
  induction e generalizing dstName with
  | const _ => rfl
  | inputPort _ => rfl
  | wireRef _ => rfl
  | regRead _ => rfl
  | bitNot a iha =>
    simp [synthesizeExprToBels, List.all_append, iha, checkBelCellValid]
  | resize op a iha =>
    simp [synthesizeExprToBels, List.all_append, iha, checkBelCellValid]
  | mux c t f ihc iht ihf =>
    simp [synthesizeExprToBels, List.all_append, ihc, iht, ihf, checkBelCellValid]
  | alu op a b iha ihb =>
    cases op <;> simp [synthesizeExprToBels, List.all_append, iha, ihb, checkBelCellValid]

theorem flatMap_synthesizeExprToBels_valid {α : Type}
    (f : α → String) (g : α → RtlExpr) (xs : List α) :
    (xs.flatMap (fun x => synthesizeExprToBels (f x) (g x))).all checkBelCellValid = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [List.flatMap_cons, List.all_append, synthesizeExprToBels_valid, ih]

theorem map_reg_ff_valid (regs : List RegSpec) :
    (regs.map (fun r => ({ dstName := r.name, kind := .ff r.resetKind, inputs := [s!"{r.name}_din"] } : BelCell))).all checkBelCellValid = true := by
  induction regs with
  | nil => rfl
  | cons r rest ih =>
    simp [List.map_cons, List.all_cons, checkBelCellValid, ih]

/-- **Universal BEL Netlist Validity & Flip-Flop Count Preservation (`synthesizeModuleToBels_valid_and_ff_count`)**:
For EVERY `m : RtlModule`, `synthesizeModuleToBels m` produces a structurally valid `BelNetlist`
(`checkBelNetlistValid (synthesizeModuleToBels m) = true`) whose sequential flip-flop count
`countFfBels (synthesizeModuleToBels m)` equals `m.regs.length`! -/
theorem synthesizeModuleToBels_valid_and_ff_count (m : RtlModule) :
    checkBelNetlistValid (synthesizeModuleToBels m) = true ∧
    countFfBels (synthesizeModuleToBels m) = m.regs.length := by
  refine ⟨?_, ?_⟩
  · dsimp only [checkBelNetlistValid, synthesizeModuleToBels]
    rw [List.all_append, List.all_append, List.all_append,
        flatMap_synthesizeExprToBels_valid, flatMap_synthesizeExprToBels_valid,
        flatMap_synthesizeExprToBels_valid, map_reg_ff_valid]
    rfl
  · simp [countFfBels, synthesizeModuleToBels, List.filter_append,
      flatMap_synthesizeExprToBels_no_ff, map_reg_ff_filter]

/-! ## 5. Verified RTL-to-BEL Signoff Gate (`checkSynthesizedRtlSignoff`) & Retimed MAC RTL Module -/

/-- Verify both `RtlModule` DAG/CDC well-formedness (`checkRtlModule`) and synthesized `BelNetlist`
cell-arity validity (`checkBelNetlistValid`). -/
def checkSynthesizedRtlSignoff (m : RtlModule) : Bool :=
  checkRtlModule m && checkBelNetlistValid (synthesizeModuleToBels m)

/-- **Theorem (`checkSynthesizedRtlSignoff_sound`)**:
Any `m : RtlModule` passing `checkSynthesizedRtlSignoff` satisfies `checkRtlModule m = true`,
produces a valid `BelNetlist`, and preserves exact sequential flip-flop count (`countFfBels = m.regs.length`). -/
theorem checkSynthesizedRtlSignoff_sound (m : RtlModule)
    (hOk : checkSynthesizedRtlSignoff m = true) :
    checkRtlModule m = true ∧
    checkBelNetlistValid (synthesizeModuleToBels m) = true ∧
    countFfBels (synthesizeModuleToBels m) = m.regs.length := by
  simp only [checkSynthesizedRtlSignoff, Bool.and_eq_true] at hOk
  exact ⟨hOk.1, hOk.2, (synthesizeModuleToBels_valid_and_ff_count m).2⟩

/-- Golden Leiserson–Saxe retimed 2-stage MAC `RtlModule` (`mulReg := a * b`, `cReg := c`,
`outReg := mulReg + cReg`). -/
def goldenRetimedMacRtl : RtlModule where
  name       := "obend_retimed_mac2"
  inputNames := ["a", "b", "c"]
  wires      :=
    [ { wireIdx := 0, name := "w_mul", expr := .alu .mul (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 1, name := "w_add", expr := .alu .add (.regRead 0) (.regRead 1) } ]
  regs       :=
    [ { regIdx := 0, name := "mulReg", domain := .coreClk, resetKind := .resetFree, isSynchronizer := false, nextExpr := .wireRef 0 }
    , { regIdx := 1, name := "cReg",   domain := .coreClk, resetKind := .resetFree, isSynchronizer := false, nextExpr := .inputPort 2 }
    , { regIdx := 2, name := "outReg", domain := .coreClk, resetKind := .resetFree, isSynchronizer := false, nextExpr := .wireRef 1 } ]
  outputs    :=
    [ { name := "mac_out", expr := .regRead 2 } ]

end Obend.Hardware.Synth
end
